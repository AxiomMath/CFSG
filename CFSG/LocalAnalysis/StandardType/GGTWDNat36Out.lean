module

public import CFSG.LocalAnalysis.StandardType.GGTWDNatWord
public import CFSG.LocalAnalysis.StandardType.GGTWDCells36Orb
public import Certificates.Data.TwoDepSmallN36

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmallN Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nDB_X_length (N : ℕ) : (ggDepANX N).length = N := by
  simp [ggDepANX]

private lemma l05nDB_toZ_X {p N : ℕ} :
    ggDepANToZ p N (ggDepANX N) = ggDepAx p N := by
  funext j
  have hj : j.val < (ggDepANX N).length := by simp [ggDepANX, j.isLt]
  rw [ggDepANToZ, List.getD_eq_getElem (l := ggDepANX N) (d := 0) (n := j.val) hj]
  simp only [ggDepANX, ggDepAx, List.getElem_map, List.getElem_range]
  split <;> simp

private lemma l05nDB_ext_basis {p N : ℕ} {T U : Module.End (ZMod p) (GGDepAE p N)}
    (h : ∀ k : Fin N, T (Pi.single k (1 : ZMod p)) = U (Pi.single k (1 : ZMod p))) :
    T = U := by
  apply (Pi.basisFun (ZMod p) (Fin N)).ext
  intro k
  simpa using h k

private lemma l05nDB_refVec_length {p N : ℕ} {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = N) (hv : v.length = N) : (ggTWDRefVec p q v).length = N := by
  simp only [ggTWDRefVec]
  exact l05nNC_sub_length hv (l05nNC_smul_length hq1)

private lemma l05nDB_refVec_toZ {p N : ℕ} [Fact p.Prime] {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = N) (hq2 : q.2.length = N) (hv : v.length = N) :
    ggDepANToZ p N (ggTWDRefVec p q v) =
      ggDepARefl (ggDepANToZ p N q.1) (ggDepANToZ p N q.2) (ggDepANToZ p N v) := by
  simp only [ggTWDRefVec]
  rw [l05nNC_toZ_sub hv (l05nNC_smul_length hq1), l05nNC_toZ_smul hq1,
    ggDepANDot_cast q.2 v hq2 hv, l05nNC_refl_apply]

private lemma l05nDB_wordVec_length {p N : ℕ} {qs : List GGDepANPair} {v : List ℕ}
    (hv : v.length = N) {w : List ℕ}
    (hlen : ∀ g ∈ w, (qs.getD g ([], [])).1.length = N) :
    (ggTWDWordVec p qs w v).length = N := by
  induction w generalizing v with
  | nil => simpa [ggTWDWordVec] using hv
  | cons g w ih =>
      change (ggTWDRefVec p (qs.getD g ([], [])) (ggTWDWordVec p qs w v)).length = N
      exact l05nDB_refVec_length (hlen g (by simp))
        (ih hv (fun g' hg' => hlen g' (by simp only [List.mem_cons]; exact Or.inr hg')))

private def l05nDB_wordEnd (p N : ℕ) (qs : List GGDepANPair) (w : List ℕ) :
    Module.End (ZMod p) (GGDepAE p N) :=
  w.foldr (fun g acc => ggTWDRflOf p N (qs.getD g ([], [])) * acc) 1

private lemma l05nDB_wordVec_toZ {p N : ℕ} [Fact p.Prime] {qs : List GGDepANPair} {w : List ℕ}
    {v : List ℕ} (hv : v.length = N)
    (hlen1 : ∀ g ∈ w, (qs.getD g ([], [])).1.length = N)
    (hlen2 : ∀ g ∈ w, (qs.getD g ([], [])).2.length = N) :
    ggDepANToZ p N (ggTWDWordVec p qs w v) = l05nDB_wordEnd p N qs w (ggDepANToZ p N v) := by
  induction w generalizing v with
  | nil => simp [ggTWDWordVec, l05nDB_wordEnd]
  | cons g w ih =>
      change ggDepANToZ p N (ggTWDRefVec p (qs.getD g ([], [])) (ggTWDWordVec p qs w v)) =
        (ggTWDRflOf p N (qs.getD g ([], [])) * l05nDB_wordEnd p N qs w)
          (ggDepANToZ p N v)
      rw [l05nDB_refVec_toZ (hlen1 g (by simp)) (hlen2 g (by simp))
        (l05nDB_wordVec_length hv
          (fun g' hg' => hlen1 g' (by simp only [List.mem_cons]; exact Or.inr hg')))]
      rw [ih hv
        (fun g' hg' => hlen1 g' (by simp only [List.mem_cons]; exact Or.inr hg'))
        (fun g' hg' => hlen2 g' (by simp only [List.mem_cons]; exact Or.inr hg'))]
      rfl

private lemma l05nDB_powVec_length {p N : ℕ} {qi qj : GGDepANPair} {v : List ℕ}
    (hi1 : qi.1.length = N) (hj1 : qj.1.length = N) (hv : v.length = N) (m : ℕ) :
    (ggTWDPowVec p qi qj m v).length = N := by
  induction m generalizing v with
  | zero => simpa [ggTWDPowVec] using hv
  | succ m ih =>
      simp only [ggTWDPowVec, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      exact l05nDB_refVec_length hi1 (l05nDB_refVec_length hj1 (ih hv))

private lemma l05nDB_powVec_toZ {p N : ℕ} [Fact p.Prime] {qi qj : GGDepANPair} {v : List ℕ}
    (hi1 : qi.1.length = N) (hi2 : qi.2.length = N)
    (hj1 : qj.1.length = N) (hj2 : qj.2.length = N) (hv : v.length = N) (m : ℕ) :
    ggDepANToZ p N (ggTWDPowVec p qi qj m v) =
      ((ggTWDRflOf p N qi * ggTWDRflOf p N qj) ^ m) (ggDepANToZ p N v) := by
  induction m generalizing v with
  | zero => simp [ggTWDPowVec]
  | succ m ih =>
      have hstep : ggTWDPowVec p qi qj (m + 1) v =
          ggTWDRefVec p qi (ggTWDRefVec p qj (ggTWDPowVec p qi qj m v)) := by
        simp [ggTWDPowVec, List.range_succ, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
      rw [hstep, l05nDB_refVec_toZ hi1 hi2
            (l05nDB_refVec_length hj1 (l05nDB_powVec_length hi1 hj1 hv m)),
          l05nDB_refVec_toZ hj1 hj2 (l05nDB_powVec_length hi1 hj1 hv m),
          ih hv, pow_succ']
      rfl

private lemma l05nDB_e6M (i j : Fin 6) :
    CoxeterMatrix.E₆.M i j = ggTWDE6M i.val j.val := by
  fin_cases i <;> fin_cases j <;> decide

private lemma l05nDB_getD_concat {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  exact List.getElem_concat_length rfl _

private lemma l05nDB_toZ_inj {p N : ℕ} {a b : List ℕ} (ha : a.length = N) (hb : b.length = N)
    (hat : ∀ x ∈ a, x < p) (hbt : ∀ x ∈ b, x < p)
    (h : ggDepANToZ p N a = ggDepANToZ p N b) : a = b := by
  apply List.ext_getElem
  · rw [ha, hb]
  · intro n hna hnb
    have hn := congrFun h ⟨n, by rw [← ha]; exact hna⟩
    simp only [ggDepANToZ] at hn
    rw [List.getD_eq_getElem _ _ hna, List.getD_eq_getElem _ _ hnb] at hn
    have hv := congrArg ZMod.val hn
    rw [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (hat _ (List.getElem_mem hna)),
      Nat.mod_eq_of_lt (hbt _ (List.getElem_mem hnb))] at hv
    exact hv

private lemma l05nDB_basis_length (N k : ℕ) : (ggTWDBasis N k).length = N := by
  simp [ggTWDBasis]

private lemma l05nDB_toZ_basis {p N : ℕ} (k : Fin N) :
    ggDepANToZ p N (ggTWDBasis N k.val) = Pi.single k (1 : ZMod p) := by
  funext j
  have hj : j.val < (ggTWDBasis N k.val).length := by simp [ggTWDBasis]
  rw [ggDepANToZ, List.getD_eq_getElem _ _ hj]
  simp only [ggTWDBasis, List.getElem_map, List.getElem_range, Pi.single_apply]
  by_cases h : j = k
  · subst h; simp
  · have hne : j.val ≠ k.val := fun hh => h (Fin.ext hh)
    rw [if_neg hne, if_neg h]
    simp

private lemma l05nDB_dot_of_valid {p N : ℕ} [Fact p.Prime] {q : GGDepANPair}
    (h : GGTWDValid p N q) :
    ggDepAdot (ggDepANToZ p N q.2) (ggDepANToZ p N q.1) = 2 := by
  have hcast := ggDepANDot_cast (p := p) (N := N) q.2 q.1 h.2.1 h.1
  rw [h.2.2, ZMod.natCast_mod] at hcast
  exact hcast.symm

private lemma l05nDB_gs_length (p N : ℕ) (news : List GGDepANPair) :
    (ggTWDGenList p N news).length = N - 1 + news.length := by
  simp [ggTWDGenList]

private lemma l05nDB_gs_getD {p N : ℕ} {news : List GGDepANPair} {g : ℕ} (hN : 1 ≤ N)
    (hg : g < N - 1 + news.length) :
    (ggTWDGenList p N news).getD g ([], []) = ggTWDGen p N news g := by
  rw [ggTWDGenList]
  by_cases h : g + 1 < N
  · have hg' : g < (List.map (fun g => (ggDepANH p N g, ggDepANA p N g))
        (List.range (N - 1))).length := by
      rw [List.length_map, List.length_range]; omega
    rw [List.getD_append _ _ _ _ hg', List.getD_eq_getElem _ _ hg']
    simp only [List.getElem_map, List.getElem_range, ggTWDGen, if_pos h]
  · have hle : (List.map (fun g => (ggDepANH p N g, ggDepANA p N g))
        (List.range (N - 1))).length ≤ g := by
      rw [List.length_map, List.length_range]; omega
    rw [List.getD_append_right _ _ _ _ hle, List.length_map, List.length_range]
    have hidx : g - (N - 1) = g + 1 - N := by omega
    rw [hidx, ggTWDGen, if_neg h]

private lemma l05nDB_gs_valid {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWDValid p N q) {g : ℕ}
    (hg : g < (ggTWDGenList p N news).length) :
    GGTWDValid p N ((ggTWDGenList p N news).getD g ([], [])) := by
  have hg' : g < N - 1 + news.length := by
    rwa [ggTWDGenList, List.length_append, List.length_map, List.length_range] at hg
  rw [l05nDB_gs_getD (by omega) hg']
  exact ggTWDGen_valid hN hnews hg'

private lemma l05nDB_valid_sw {G : ℕ} {O : GGTWDOut} (h : ggTWDOutValid G O = true) :
    O.sw.length = 6 ∧ (∀ e ∈ O.sw, e.1 < G ∧ ∀ g ∈ e.2, g < G) := by
  rw [ggTWDOutValid] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2⟩

private lemma l05nDB_valid_gw {G : ℕ} {O : GGTWDOut} (h : ggTWDOutValid G O = true) :
    O.gw.length = G ∧ (∀ e ∈ O.gw, e.1 < 6 ∧ ∀ i ∈ e.2, i < 6) := by
  rw [ggTWDOutValid] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1.2, h.1.1.2⟩

private lemma l05nDB_valid_ot {G : ℕ} {O : GGTWDOut} (h : ggTWDOutValid G O = true) :
    O.ot.length = 71 ∧ (∀ t < O.ot.length, (O.ot.getD t (0, 0)).1 ≤ t ∧
      (O.ot.getD t (0, 0)).2 < G) := by
  rw [ggTWDOutValid] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.2, h.2⟩

private lemma l05nDB_ss_get {p N : ℕ} {news : List GGDepANPair} {O : GGTWDOut} {i : ℕ}
    (hi : i < O.sw.length) :
    (ggTWDOutS p N news O).getD i ([], []) =
      ggTWDWord p N news (ggTWDGen p N news (O.sw.getD i (0, [])).1)
        (O.sw.getD i (0, [])).2 := by
  rw [ggTWDOutS, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi),
    List.getElem_map, List.getD_eq_getElem _ _ hi]

private lemma l05nDB_ss_valid {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWDValid 3 6 q) {O : GGTWDOut}
    (hsw : ∀ e ∈ O.sw, e.1 < 5 + news.length ∧ ∀ g ∈ e.2, g < 5 + news.length)
    (hswlen : O.sw.length = 6) (i : Fin 6) :
    GGTWDValid 3 6 ((ggTWDOutS 3 6 news O).getD i.val ([], [])) ∧
      ggTWDRflOf 3 6 ((ggTWDOutS 3 6 news O).getD i.val ([], [])) ∈
        Submonoid.closure (ggTWDGens 3 6 news) := by
  have hi : i.val < O.sw.length := by rw [hswlen]; exact i.isLt
  rw [l05nDB_ss_get (p := 3) (N := 6) (news := news) (O := O) hi]
  have he := hsw (O.sw[i.val]) (List.getElem_mem hi)
  have he1 : (O.sw.getD i.val (0, [])).1 < 5 + news.length := by
    rw [List.getD_eq_getElem _ _ hi]; exact he.1
  have he2 : ∀ g ∈ (O.sw.getD i.val (0, [])).2, g < 5 + news.length := by
    intro g hg
    rw [List.getD_eq_getElem _ _ hi] at hg
    exact he.2 g hg
  exact ggTWDWord_valid_mem (p := 3) (N := 6) (by norm_num) (by norm_num) hnews
    (ggTWDGen_valid (by norm_num) hnews he1)
    (ggTWDGen_mem (by norm_num) he1) he2

private lemma l05nDB_frame_getD {news : List GGDepANPair} {i : Fin 5} :
    (ggTWDGenList 3 6 news).getD i.val ([], []) =
      (ggDepANH 3 6 i.val, ggDepANA 3 6 i.val) := by
  rw [ggTWDGenList]
  have hi : i.val < (List.map (fun g => (ggDepANH 3 6 g, ggDepANA 3 6 g))
      (List.range (6 - 1))).length := by
    rw [List.length_map, List.length_range]; exact i.isLt
  rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp only [List.getElem_map, List.getElem_range]

private lemma l05nDB_frame_refl {news : List GGDepANPair} {i : Fin 5} :
    ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i) =
      ggTWDRflOf 3 6 ((ggTWDGenList 3 6 news).getD i.val ([], [])) := by
  rw [l05nDB_frame_getD]
  simp only [ggTWDRflOf]
  rw [l05nNC_toZ_H (p := 3) (N := 6) (i := i.val) (by omega),
    l05nNC_toZ_A (p := 3) (N := 6) (i := i.val) (by omega)]

private lemma l05nDB_news_getD {news : List GGDepANPair} {q : GGDepANPair} (hq : q ∈ news) :
    ∃ g : ℕ, g < (ggTWDGenList 3 6 news).length ∧
      (ggTWDGenList 3 6 news).getD g ([], []) = q := by
  obtain ⟨n, hn⟩ := List.get_of_mem hq
  refine ⟨5 + n.val, ?_, ?_⟩
  · rw [ggTWDGenList, List.length_append, List.length_map, List.length_range]
    have : n.val < news.length := n.isLt
    omega
  · rw [ggTWDGenList]
    have hle : (List.map (fun g => (ggDepANH 3 6 g, ggDepANA 3 6 g))
        (List.range (6 - 1))).length ≤ 5 + n.val := by
      rw [List.length_map, List.length_range]; simp
    rw [List.getD_append_right _ _ _ _ hle, List.length_map, List.length_range]
    have hidx : 5 + n.val - 5 = n.val := by omega
    rw [hidx, List.getD_eq_getElem _ _ n.isLt]
    rw [List.get_eq_getElem] at hn
    exact hn

private lemma l05nDB_wordEnd_mem {news : List GGDepANPair} {O : GGTWDOut}
    {s : Fin 6 → Module.End (ZMod 3) (GGDepAE 3 6)}
    (hs : ∀ i, s i = ggTWDRflOf 3 6 ((ggTWDOutS 3 6 news O).getD i.val ([], [])))
    {w : List ℕ} (hw : ∀ g ∈ w, g < 6) :
    l05nDB_wordEnd 3 6 (ggTWDOutS 3 6 news O) w ∈ Submonoid.closure (Set.range s) := by
  induction w with
  | nil => simp [l05nDB_wordEnd]
  | cons g w ih =>
      have hg := hw g (by simp)
      have hw' : ∀ g' ∈ w, g' < 6 := fun g' hg' =>
        hw g' (by simp only [List.mem_cons]; exact Or.inr hg')
      have hstep : l05nDB_wordEnd 3 6 (ggTWDOutS 3 6 news O) (g :: w) =
          ggTWDRflOf 3 6 ((ggTWDOutS 3 6 news O).getD g ([], [])) *
            l05nDB_wordEnd 3 6 (ggTWDOutS 3 6 news O) w := by
        simp [l05nDB_wordEnd, List.foldr_cons]
      rw [hstep]
      exact Submonoid.mul_mem _
        (Submonoid.subset_closure ⟨⟨g, hg⟩, hs ⟨g, hg⟩⟩) (ih hw')

private lemma l05nDB_word_letters {O : GGTWDOut}
    (hgw : ∀ e ∈ O.gw, e.1 < 6 ∧ ∀ i ∈ e.2, i < 6) {g : ℕ} (hg : g < O.gw.length) :
    ∀ l ∈ (O.gw.getD g (0, [])).2 ++ (O.gw.getD g (0, [])).1 ::
        (O.gw.getD g (0, [])).2.reverse, l < 6 := by
  have hge : O.gw.getD g (0, []) ∈ O.gw := by
    rw [List.getD_eq_getElem _ _ hg]; exact List.getElem_mem hg
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact (hgw _ hge).2 l hl
  · rcases List.mem_cons.mp hl with hl | hl
    · subst hl; exact (hgw _ hge).1
    · rw [List.mem_reverse] at hl; exact (hgw _ hge).2 l hl

private lemma l05nDB_gen_eq_word {news : List GGDepANPair} {O : GGTWDOut}
    (hnews : ∀ q ∈ news, GGTWDValid 3 6 q)
    (hswlen : O.sw.length = 6)
    (hsw : ∀ e ∈ O.sw, e.1 < 5 + news.length ∧ ∀ g ∈ e.2, g < 5 + news.length)
    (hgwlen : O.gw.length = (ggTWDGenList 3 6 news).length)
    (hgw : ∀ e ∈ O.gw, e.1 < 6 ∧ ∀ i ∈ e.2, i < 6)
    (hS : ∀ x < (ggTWDGenList 3 6 news).length, ∀ x1 < 6,
        ggTWDRefVec 3 ((ggTWDGenList 3 6 news).getD x ([], [])) (ggTWDBasis 6 x1) =
          ggTWDWordVec 3 (ggTWDOutS 3 6 news O)
            ((O.gw.getD x (0, [])).2 ++ (O.gw.getD x (0, [])).1 ::
              (O.gw.getD x (0, [])).2.reverse) (ggTWDBasis 6 x1))
    {g : ℕ} (hg : g < (ggTWDGenList 3 6 news).length) :
    ggTWDRflOf 3 6 ((ggTWDGenList 3 6 news).getD g ([], [])) =
      l05nDB_wordEnd 3 6 (ggTWDOutS 3 6 news O)
        ((O.gw.getD g (0, [])).2 ++ (O.gw.getD g (0, [])).1 ::
          (O.gw.getD g (0, [])).2.reverse) := by
  have hgvalid := l05nDB_gs_valid (p := 3) (N := 6) (by norm_num) hnews hg
  have hglen : g < O.gw.length := by rw [hgwlen]; exact hg
  have hge : O.gw.getD g (0, []) ∈ O.gw := by
    rw [List.getD_eq_getElem _ _ hglen]; exact List.getElem_mem hglen
  have hge1 : (O.gw.getD g (0, [])).1 < 6 := (hgw _ hge).1
  have hge2 : ∀ i ∈ (O.gw.getD g (0, [])).2, i < 6 := (hgw _ hge).2
  have hw_lt : ∀ l ∈ (O.gw.getD g (0, [])).2 ++ (O.gw.getD g (0, [])).1 ::
        (O.gw.getD g (0, [])).2.reverse, l < 6 := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hge2 l hl
    · rcases List.mem_cons.mp hl with hl | hl
      · subst hl; exact hge1
      · rw [List.mem_reverse] at hl; exact hge2 l hl
  set w := (O.gw.getD g (0, [])).2 ++ (O.gw.getD g (0, [])).1 ::
    (O.gw.getD g (0, [])).2.reverse with hwdef
  apply l05nDB_ext_basis
  intro k
  have hSg := hS g hg k.val k.isLt
  have h1 : ggDepANToZ 3 6 (ggTWDRefVec 3 ((ggTWDGenList 3 6 news).getD g ([], []))
      (ggTWDBasis 6 k.val)) =
      ggTWDRflOf 3 6 ((ggTWDGenList 3 6 news).getD g ([], [])) (Pi.single k (1 : ZMod 3)) := by
    rw [l05nDB_refVec_toZ hgvalid.1 hgvalid.2.1 (l05nDB_basis_length 6 k.val),
      l05nDB_toZ_basis]
  have h2 : ggDepANToZ 3 6 (ggTWDWordVec 3 (ggTWDOutS 3 6 news O) w (ggTWDBasis 6 k.val)) =
      l05nDB_wordEnd 3 6 (ggTWDOutS 3 6 news O) w (Pi.single k (1 : ZMod 3)) := by
    rw [l05nDB_wordVec_toZ (l05nDB_basis_length 6 k.val)
      (fun l hl => (l05nDB_ss_valid hnews hsw hswlen ⟨l, hw_lt l (by rw [hwdef]; exact hl)⟩).1.1)
      (fun l hl => (l05nDB_ss_valid hnews hsw hswlen ⟨l, hw_lt l (by rw [hwdef]; exact hl)⟩).1.2.1)]
    rw [l05nDB_toZ_basis]
  rw [← h1, ← h2]
  rw [show ggTWDRefVec 3 ((ggTWDGenList 3 6 news).getD g ([], [])) (ggTWDBasis 6 k.val) =
      ggTWDWordVec 3 (ggTWDOutS 3 6 news O) w (ggTWDBasis 6 k.val) from hSg]

private def l05nDB_stepW (p N : ℕ) (gs : List GGDepANPair)
    (acc : List (Module.End (ZMod p) (GGDepAE p N))) (e : ℕ × ℕ) :
    List (Module.End (ZMod p) (GGDepAE p N)) :=
  acc ++ [ggTWDRflOf p N (gs.getD e.2 ([], [])) * acc.getD e.1 1]

private def l05nDB_stepV (p N : ℕ) (gs : List GGDepANPair)
    (acc : List (List ℕ)) (e : ℕ × ℕ) : List (List ℕ) :=
  acc ++ [ggTWDRefVec p (gs.getD e.2 ([], [])) (acc.getD e.1 [])]

private def l05nDB_OW (p N : ℕ) (gs : List GGDepANPair) (ot : List (ℕ × ℕ)) :
    List (Module.End (ZMod p) (GGDepAE p N)) :=
  ot.foldl (l05nDB_stepW p N gs) [1]

private def l05nDB_OV (p N : ℕ) (gs : List GGDepANPair) (ot : List (ℕ × ℕ)) :
    List (List ℕ) :=
  ot.foldl (l05nDB_stepV p N gs) [ggDepANX N]

private lemma l05nDB_OV_eq_orbit (p N : ℕ) (news : List GGDepANPair) (ot : List (ℕ × ℕ)) :
    l05nDB_OV p N (ggTWDGenList p N news) ot = ggTWDOrbit p N news ot := by
  rfl

private lemma l05nDB_foldlW_length (p N : ℕ) (gs : List GGDepANPair) (l : List (ℕ × ℕ))
    (acc : List (Module.End (ZMod p) (GGDepAE p N))) :
    (l.foldl (l05nDB_stepW p N gs) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons e l ih =>
      rw [List.foldl_cons, ih]
      simp [l05nDB_stepW, List.length_append]
      omega

private lemma l05nDB_foldlV_length (p N : ℕ) (gs : List GGDepANPair) (l : List (ℕ × ℕ))
    (acc : List (List ℕ)) :
    (l.foldl (l05nDB_stepV p N gs) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons e l ih =>
      rw [List.foldl_cons, ih]
      simp [l05nDB_stepV, List.length_append]
      omega

private lemma l05nDB_OV_length (p N : ℕ) (gs : List GGDepANPair) (ot : List (ℕ × ℕ)) :
    (l05nDB_OV p N gs ot).length = ot.length + 1 := by
  rw [l05nDB_OV, l05nDB_foldlV_length]
  simp [Nat.add_comm]

private lemma l05nDB_foldlW_mem (p N : ℕ) (gs : List GGDepANPair) (l : List (ℕ × ℕ))
    (acc : List (Module.End (ZMod p) (GGDepAE p N)))
    {S : Submonoid (Module.End (ZMod p) (GGDepAE p N))}
    (hacc : ∀ x ∈ acc, x ∈ S) (h1 : 1 ∈ S)
    (hrefl : ∀ e ∈ l, ggTWDRflOf p N (gs.getD e.2 ([], [])) ∈ S) :
    ∀ w ∈ l.foldl (l05nDB_stepW p N gs) acc, w ∈ S := by
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons e l ih =>
      rw [List.foldl_cons]
      refine ih (l05nDB_stepW p N gs acc e) ?_ ?_
      · intro x hx
        rw [l05nDB_stepW] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hacc x hx
        · rw [List.mem_singleton] at hx; subst hx
          refine Submonoid.mul_mem S (hrefl e (by simp)) ?_
          by_cases he : e.1 < acc.length
          · exact hacc _ (by rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he)
          · rw [List.getD_eq_default _ _ (by omega)]; exact h1
      · intro e' he'
        exact hrefl e' (by simp only [List.mem_cons]; exact Or.inr he')

private lemma l05nDB_sub_entries_lt {p : ℕ} (hp : 0 < p) (a b : List ℕ) :
    ∀ x ∈ ggDepANSub p a b, x < p := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  simp only [ggDepANSub] at hxi
  rw [List.getElem_zipWith] at hxi
  rw [← hxi]
  exact Nat.mod_lt _ hp

private lemma l05nDB_refVec_entries_lt {p : ℕ} (hp : 0 < p) {q : GGDepANPair} {v : List ℕ} :
    ∀ x ∈ ggTWDRefVec p q v, x < p := by
  intro x hx
  simp only [ggTWDRefVec] at hx
  exact l05nDB_sub_entries_lt hp v _ x hx

private lemma l05nDB_X_entries_lt {p N : ℕ} (hp : 1 < p) : ∀ x ∈ ggDepANX N, x < p := by
  intro x hx
  rw [ggDepANX, List.mem_map] at hx
  obtain ⟨j, -, hjx⟩ := hx
  rw [← hjx]
  split <;> omega

private lemma l05nDB_foldlV_entries_lt (p N : ℕ) (hp : 0 < p) (gs : List GGDepANPair)
    (l : List (ℕ × ℕ)) (acc : List (List ℕ))
    (hacc : ∀ v ∈ acc, ∀ x ∈ v, x < p) :
    ∀ v ∈ l.foldl (l05nDB_stepV p N gs) acc, ∀ x ∈ v, x < p := by
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons e l ih =>
      rw [List.foldl_cons]
      apply ih
      intro v hv x hx
      simp only [l05nDB_stepV] at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hacc v hv x hx
      · rw [List.mem_singleton] at hv; subst hv
        exact l05nDB_refVec_entries_lt hp x hx

private lemma l05nDB_foldl_pt (p N : ℕ) [Fact p.Prime] (gs : List GGDepANPair)
    (hgl : ∀ g < gs.length, (gs.getD g ([], [])).1.length = N ∧
      (gs.getD g ([], [])).2.length = N) :
    ∀ (l : List (ℕ × ℕ)) (accW : List (Module.End (ZMod p) (GGDepAE p N)))
      (accV : List (List ℕ)),
      (∀ s < l.length, (l.getD s (0, 0)).1 < accW.length + s) →
      (∀ s < l.length, (l.getD s (0, 0)).2 < gs.length) →
      accW.length = accV.length →
      1 ≤ accW.length →
      (∀ v ∈ accV, v.length = N) →
      (∀ t < accW.length, accW.getD t 1 (ggDepAx p N) = ggDepANToZ p N (accV.getD t [])) →
      (l.foldl (l05nDB_stepW p N gs) accW).length =
          (l.foldl (l05nDB_stepV p N gs) accV).length ∧
      (∀ v ∈ l.foldl (l05nDB_stepV p N gs) accV, v.length = N) ∧
      (∀ t < (l.foldl (l05nDB_stepW p N gs) accW).length,
        (l.foldl (l05nDB_stepW p N gs) accW).getD t 1 (ggDepAx p N) =
          ggDepANToZ p N ((l.foldl (l05nDB_stepV p N gs) accV).getD t [])) := by
  intro l
  induction l with
  | nil =>
      intro accW accV hbnd hg2 hlen hpos hVlen hpt
      exact ⟨by simpa using hlen, by simpa using hVlen, by simpa using hpt⟩
  | cons e l ih =>
      intro accW accV hbnd hg2 hlen hpos hVlen hpt
      rw [List.foldl_cons, List.foldl_cons]
      have he1 : e.1 < accW.length := by
        have hh := hbnd 0 (by simp); simpa using hh
      have he2 : e.2 < gs.length := by
        have hh := hg2 0 (by simp); simpa using hh
      have haccVlen : e.1 < accV.length := by rw [← hlen]; exact he1
      have hparentV : (accV.getD e.1 []).length = N := by
        rw [List.getD_eq_getElem _ _ haccVlen]
        exact hVlen _ (List.getElem_mem haccVlen)
      have hVlen' : ∀ v ∈ l05nDB_stepV p N gs accV e, v.length = N := by
        intro v hv
        simp only [l05nDB_stepV] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hVlen v hv
        · rw [List.mem_singleton] at hv; subst hv
          exact l05nDB_refVec_length (hgl e.2 he2).1 hparentV
      have hpt' : ∀ t < (l05nDB_stepW p N gs accW e).length,
          (l05nDB_stepW p N gs accW e).getD t 1 (ggDepAx p N) =
            ggDepANToZ p N ((l05nDB_stepV p N gs accV e).getD t []) := by
        intro t ht
        simp only [l05nDB_stepW, l05nDB_stepV, List.length_append, List.length_singleton] at ht ⊢
        have htle : t ≤ accW.length := by omega
        rcases lt_or_eq_of_le htle with hlt | heq
        · rw [List.getD_append _ _ _ _ hlt]
          rw [List.getD_append _ _ _ _ (by rw [← hlen]; exact hlt)]
          exact hpt t hlt
        · subst heq
          rw [l05nDB_getD_concat accW _ 1]
          have hvget : (accV ++ [ggTWDRefVec p (gs.getD e.2 ([], []))
              (accV.getD e.1 [])]).getD accW.length [] =
              ggTWDRefVec p (gs.getD e.2 ([], [])) (accV.getD e.1 []) := by
            rw [hlen]; exact l05nDB_getD_concat accV _ []
          rw [hvget, Module.End.mul_apply, hpt e.1 he1]
          exact (l05nDB_refVec_toZ (hgl e.2 he2).1 (hgl e.2 he2).2 hparentV).symm
      have hbnd' : ∀ s < l.length, (l.getD s (0, 0)).1 <
          (l05nDB_stepW p N gs accW e).length + s := by
        intro s hs
        have hh := hbnd (s + 1) (by simp only [List.length_cons]; omega)
        rw [List.getD_cons_succ] at hh
        simp only [l05nDB_stepW, List.length_append, List.length_singleton]
        omega
      have hg2' : ∀ s < l.length, (l.getD s (0, 0)).2 < gs.length := by
        intro s hs
        have hh := hg2 (s + 1) (by simp only [List.length_cons]; omega)
        rwa [List.getD_cons_succ] at hh
      have hlen' : (l05nDB_stepW p N gs accW e).length =
          (l05nDB_stepV p N gs accV e).length := by
        simp only [l05nDB_stepW, l05nDB_stepV, List.length_append, List.length_singleton]
        rw [hlen]
      have hpos' : 1 ≤ (l05nDB_stepW p N gs accW e).length := by
        simp only [l05nDB_stepW, List.length_append, List.length_singleton]
        omega
      obtain ⟨ihlen, ihVlen, ihpt⟩ := ih (l05nDB_stepW p N gs accW e)
        (l05nDB_stepV p N gs accV e) hbnd' hg2' hlen' hpos' hVlen' hpt'
      exact ⟨ihlen, ihVlen, ihpt⟩

theorem ggTWDOutOK_sound {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWDValid 3 6 q)
    {O : GGTWDOut} (h : ggTWDOutOK 3 6 news O = true) : GGTWDE6Orbit (ggTWDGens 3 6 news) := by
  have h' := h
  rw [ggTWDOutOK] at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h'
  obtain ⟨⟨⟨hvalid, hR⟩, hS⟩, hOlen, hOnodup⟩ := h'
  obtain ⟨hswlen, hsw⟩ := l05nDB_valid_sw hvalid
  obtain ⟨hgwlen, hgw⟩ := l05nDB_valid_gw hvalid
  obtain ⟨hotlen, hot⟩ := l05nDB_valid_ot hvalid
  have hgslen : (ggTWDGenList 3 6 news).length = 5 + news.length := by
    rw [l05nDB_gs_length]
  have hsw' : ∀ e ∈ O.sw, e.1 < 5 + news.length ∧ ∀ g ∈ e.2, g < 5 + news.length := by
    intro e he
    have hh := hsw e he
    rw [hgslen] at hh
    exact hh
  let s : Fin 6 → Module.End (ZMod 3) (GGDepAE 3 6) :=
    fun i => ggTWDRflOf 3 6 ((ggTWDOutS 3 6 news O).getD i.val ([], []))
  let w : Fin 72 → Module.End (ZMod 3) (GGDepAE 3 6) :=
    fun k => (l05nDB_OW 3 6 (ggTWDGenList 3 6 news) O.ot).getD k.val 1
  have hs : ∀ i : Fin 6,
      s i = ggTWDRflOf 3 6 ((ggTWDOutS 3 6 news O).getD i.val ([], [])) := fun i => rfl
  have hgl : ∀ g < (ggTWDGenList 3 6 news).length,
      ((ggTWDGenList 3 6 news).getD g ([], [])).1.length = 6 ∧
      ((ggTWDGenList 3 6 news).getD g ([], [])).2.length = 6 := by
    intro g hg
    exact ⟨(l05nDB_gs_valid (by norm_num) hnews hg).1,
      (l05nDB_gs_valid (by norm_num) hnews hg).2.1⟩
  have hOWlen : (l05nDB_OW 3 6 (ggTWDGenList 3 6 news) O.ot).length = 72 := by
    rw [l05nDB_OW, l05nDB_foldlW_length, hotlen]; norm_num
  have hOVlen : (l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot).length = 72 := by
    rw [l05nDB_OV, l05nDB_foldlV_length, hotlen]; norm_num
  have hOVeq : l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot = ggTWDOrbit 3 6 news O.ot :=
    l05nDB_OV_eq_orbit 3 6 news O.ot
  have hOVnodup : (l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot).Nodup := by
    rw [hOVeq]; exact hOnodup
  have hOWmem : ∀ x ∈ l05nDB_OW 3 6 (ggTWDGenList 3 6 news) O.ot,
      x ∈ Submonoid.closure (ggTWDGens 3 6 news) := by
    refine l05nDB_foldlW_mem 3 6 (ggTWDGenList 3 6 news) O.ot [1] ?_ ?_ ?_
    · intro x hx; rw [List.mem_singleton] at hx; subst hx
      exact Submonoid.one_mem _
    · exact Submonoid.one_mem _
    · intro e he
      obtain ⟨t, ht, hte⟩ := List.getElem_of_mem he
      have he2 : e.2 < (ggTWDGenList 3 6 news).length := by
        rw [← hte, ← List.getD_eq_getElem (l := O.ot) (d := (0, 0)) ht]
        exact (hot t ht).2
      have he2' : e.2 < 6 - 1 + news.length := by rw [← hgslen]; exact he2
      rw [l05nDB_gs_getD (p := 3) (N := 6) (by omega) he2']
      exact ggTWDGen_mem (p := 3) (N := 6) (by norm_num) he2'
  have hbnd : ∀ t < O.ot.length, (O.ot.getD t (0, 0)).1 < [1].length + t := by
    intro t ht
    have hh := (hot t ht).1
    simp only [List.length_singleton]
    omega
  have hinit : ∀ t < [1].length,
      ([1].getD t (1 : Module.End (ZMod 3) (GGDepAE 3 6))) (ggDepAx 3 6) =
        ggDepANToZ 3 6 ([ggDepANX 6].getD t []) := by
    intro t ht
    have ht0 : t = 0 := by simp only [List.length_singleton] at ht; omega
    subst ht0
    simp [l05nDB_toZ_X]
  obtain ⟨hlenOW, hVlen, hpt⟩ := l05nDB_foldl_pt 3 6 (ggTWDGenList 3 6 news) hgl O.ot
    [1] [ggDepANX 6] hbnd (fun t ht => (hot t ht).2) (by simp) (by simp)
    (fun v hv => by rw [List.mem_singleton] at hv; subst hv; exact l05nDB_X_length 6) hinit
  have hVentries : ∀ v ∈ l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot,
      ∀ x ∈ v, x < 3 := by
    rw [l05nDB_OV]
    refine l05nDB_foldlV_entries_lt 3 6 (by norm_num) (ggTWDGenList 3 6 news) O.ot
      [ggDepANX 6] ?_
    intro v hv x hx
    rw [List.mem_singleton] at hv; subst hv
    exact l05nDB_X_entries_lt (by norm_num) x hx
  refine ⟨s, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨ggDepANToZ 3 6 ((ggTWDOutS 3 6 news O).getD i.val ([], [])).1,
      ggDepANToZ 3 6 ((ggTWDOutS 3 6 news O).getD i.val ([], [])).2, ?_, ?_⟩
    · exact l05nDB_dot_of_valid (l05nDB_ss_valid hnews hsw' hswlen i).1
    · rfl
  · intro i
    exact (l05nDB_ss_valid hnews hsw' hswlen i).2
  · intro g hg
    rcases hg with ⟨i, rfl⟩ | ⟨q, hq, rfl⟩
    · have hgi : i.val < (ggTWDGenList 3 6 news).length := by rw [hgslen]; omega
      change ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i) ∈ Submonoid.closure (Set.range s)
      rw [l05nDB_frame_refl (news := news) (i := i),
        l05nDB_gen_eq_word hnews hswlen hsw' hgwlen hgw hS hgi]
      refine l05nDB_wordEnd_mem (news := news) (O := O) (s := s) (fun j => rfl)
        (l05nDB_word_letters hgw (by rw [hgwlen]; exact hgi))
    · obtain ⟨g0, hg0, hgsq⟩ := l05nDB_news_getD (news := news) hq
      have heq := l05nDB_gen_eq_word hnews hswlen hsw' hgwlen hgw hS hg0
      rw [show ggTWDRflOf 3 6 q = ggTWDRflOf 3 6 ((ggTWDGenList 3 6 news).getD g0 ([], []))
        from by rw [hgsq], heq]
      refine l05nDB_wordEnd_mem (news := news) (O := O) (s := s) (fun j => rfl)
        (l05nDB_word_letters hgw (by rw [hgwlen]; exact hg0))
  · intro i j
    rw [l05nDB_e6M i j]
    apply l05nDB_ext_basis
    intro k
    have hvi := (l05nDB_ss_valid hnews hsw' hswlen i).1
    have hvj := (l05nDB_ss_valid hnews hsw' hswlen j).1
    have h1 : ggDepANToZ 3 6 (ggTWDPowVec 3 ((ggTWDOutS 3 6 news O).getD i.val ([], []))
        ((ggTWDOutS 3 6 news O).getD j.val ([], [])) (ggTWDE6M i.val j.val)
        (ggTWDBasis 6 k.val)) =
        ((s i * s j) ^ (ggTWDE6M i.val j.val)) (Pi.single k (1 : ZMod 3)) := by
      rw [l05nDB_powVec_toZ hvi.1 hvi.2.1 hvj.1 hvj.2.1 (l05nDB_basis_length 6 k.val),
        l05nDB_toZ_basis]
    have h2 : ggDepANToZ 3 6 (ggTWDBasis 6 k.val) = Pi.single k (1 : ZMod 3) :=
      l05nDB_toZ_basis k
    have hh := congrArg (ggDepANToZ 3 6) (hR i.val i.isLt j.val j.isLt k.val k.isLt)
    rw [h1, h2] at hh
    exact hh
  · intro k
    change (l05nDB_OW 3 6 (ggTWDGenList 3 6 news) O.ot).getD k.val 1 ∈
      Submonoid.closure (ggTWDGens 3 6 news)
    have hk : k.val < (l05nDB_OW 3 6 (ggTWDGenList 3 6 news) O.ot).length := by
      rw [hOWlen]; exact k.isLt
    rw [List.getD_eq_getElem _ _ hk]
    exact hOWmem _ (List.getElem_mem hk)
  · intro k j hkj
    have hwk : w k (ggDepAx 3 6) =
        ggDepANToZ 3 6 ((l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot).getD k.val []) := by
      have hk : k.val < (l05nDB_OW 3 6 (ggTWDGenList 3 6 news) O.ot).length := by
        rw [hOWlen]; exact k.isLt
      exact hpt k.val hk
    have hwj : w j (ggDepAx 3 6) =
        ggDepANToZ 3 6 ((l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot).getD j.val []) := by
      have hj : j.val < (l05nDB_OW 3 6 (ggTWDGenList 3 6 news) O.ot).length := by
        rw [hOWlen]; exact j.isLt
      exact hpt j.val hj
    have htoZ : ggDepANToZ 3 6 ((l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot).getD k.val []) =
        ggDepANToZ 3 6 ((l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot).getD j.val []) :=
      hwk.symm.trans (hkj.trans hwj)
    have hklt : k.val < (l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot).length := by
      rw [hOVlen]; exact k.isLt
    have hjlt : j.val < (l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot).length := by
      rw [hOVlen]; exact j.isLt
    rw [List.getD_eq_getElem _ _ hklt, List.getD_eq_getElem _ _ hjlt] at htoZ
    have hkey : (l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot)[k.val] =
        (l05nDB_OV 3 6 (ggTWDGenList 3 6 news) O.ot)[j.val] :=
      l05nDB_toZ_inj (hVlen _ (List.getElem_mem hklt)) (hVlen _ (List.getElem_mem hjlt))
        (hVentries _ (List.getElem_mem hklt)) (hVentries _ (List.getElem_mem hjlt)) htoZ
    exact Fin.ext ((List.Nodup.getElem_inj hOVnodup).mp hkey)

end CFSG.StandardType

end

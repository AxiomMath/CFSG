module

public import CFSG.LocalAnalysis.StandardType.GGTWLowMatMul
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nL8_dot_mod (p : ℕ) (a b : List ℕ) :
    ggDepANDot p a b % p = ggDepANDot p a b := by
  simp [ggDepANDot, Nat.mod_mod]

private lemma l05nL8_cartan_diag (i : ℕ) : ggTWLCartanE 3 i i = 2 % 3 := by
  simp [ggTWLCartanE]

private lemma l05nL8_cartan_cast (i j : Fin 8) :
    ((ggTWLCartanE 3 i.val j.val : ℕ) : ZMod 3) = ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) := by
  fin_cases i <;> fin_cases j <;> decide

private lemma l05nL8_Te_get (w : GGTWLE8) (k : ℕ) (hk : k < w.e.length) :
    (w.e.map (ggTWLMatOfPair 3 8)).getD k [] =
      ggTWLMatOfPair 3 8 (w.e.getD k ([], [])) := by
  rw [List.getD_eq_getElem (l := w.e.map (ggTWLMatOfPair 3 8)) (d := []) (n := k)
      (by rw [List.length_map]; exact hk),
    List.getElem_map, List.getD_eq_getElem (l := w.e) (d := ([], [])) (n := k) hk]

private lemma l05nL8_Tg_get (news : List GGDepANPair) (g : ℕ) (hg : g < 8 + news.length) :
    (ggTWLGenMats 3 9 news).getD g [] =
      ggTWLMatOfPair 3 8 (ggTWNGen 3 9 news g) := by
  have hlen : (ggTWLGenMats 3 9 news).length = 8 + news.length := by simp [ggTWLGenMats]
  rw [List.getD_eq_getElem (l := ggTWLGenMats 3 9 news) (d := []) (n := g)
      (by rw [hlen]; exact hg)]
  unfold ggTWLGenMats
  simp only [List.getElem_map, List.getElem_range]

private lemma l05nL8_word_wf {Ts : List (List (List ℕ))} (hT : ∀ t ∈ Ts, ggTWLMatWF 8 t)
    {u : List ℕ} (hu : ∀ k ∈ u, k < Ts.length) :
    ggTWLMatWF 8 (ggTWLWordMat 3 8 Ts u) :=
  (ggTWLWordMat_lin hT hu).1

private lemma l05nL8_test {news : List GGDepANPair} {w : GGTWLE8}
    (h : ggTWLE8Test 3 9 news w = true) :
    w.e.length = 8 ∧ w.gw.length = 8 + news.length ∧ w.sw.length = 8 ∧
    (∀ q ∈ w.e, q.1.length = 8 ∧ q.2.length = 8) ∧
    (∀ i < 8, ∀ j < 8, ggDepANDot 3 (w.e.getD i ([], [])).2 (w.e.getD j ([], [])).1 % 3
        = ggTWLCartanE 3 i j) ∧
    (∀ u ∈ w.gw, ∀ k ∈ u, k < 8) ∧
    (∀ u ∈ w.sw, ∀ k ∈ u, k < 8 + news.length) ∧
    (∀ g < 8 + news.length, ggTWLMatEq 3 ((ggTWLGenMats 3 9 news).getD g [])
        (ggTWLWordMat 3 8 (w.e.map (ggTWLMatOfPair 3 8)) (w.gw.getD g []))) ∧
    (∀ i < 8, ggTWLMatEq 3 ((w.e.map (ggTWLMatOfPair 3 8)).getD i [])
        (ggTWLWordMat 3 8 (ggTWLGenMats 3 9 news) (w.sw.getD i []))) := by
  simp only [ggTWLE8Test, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

private lemma l05nL8_valid {news : List GGDepANPair} {w : GGTWLE8}
    (h : ggTWLE8Test 3 9 news w = true) : ∀ q ∈ w.e, GGTWNValid 3 9 q := by
  obtain ⟨he_len, -, -, he_wf, hcartan, -, -, -, -⟩ := l05nL8_test h
  intro q hq
  obtain ⟨k, hk, hkq⟩ := List.mem_iff_getElem.mp hq
  have hk8 : k < 8 := by rw [he_len] at hk; exact hk
  obtain ⟨hq1, hq2⟩ := he_wf q hq
  refine ⟨?_, ?_, ?_⟩
  · simpa using hq1
  · simpa using hq2
  · have hd := hcartan k hk8 k hk8
    rw [List.getD_eq_getElem (l := w.e) (d := ([], [])) (n := k) hk,
      l05nL8_cartan_diag k, l05nL8_dot_mod 3] at hd
    rw [← hkq]; exact hd

private lemma l05nL8_Te_wf {news : List GGDepANPair} {w : GGTWLE8}
    (h : ggTWLE8Test 3 9 news w = true) :
    ∀ t ∈ w.e.map (ggTWLMatOfPair 3 8), ggTWLMatWF 8 t := by
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact (ggTWLMatOfPair_lin (l05nL8_valid h q hq)).1

private lemma l05nL8_Tg_wf {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid 3 9 q) :
    ∀ t ∈ ggTWLGenMats 3 9 news, ggTWLMatWF 8 t := by
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  have hkG : k < 8 + news.length := by rw [List.mem_range] at hk; exact hk
  exact (ggTWLMatOfPair_lin (ggTWNGen_valid (p := 3) (N := 9) (by norm_num) (by norm_num)
    hnews hkG)).1

private lemma l05nL8_refl_mem {news : List GGDepANPair} {w : GGTWLE8}
    (hnews : ∀ q ∈ news, GGTWNValid 3 9 q)
    (h : ggTWLE8Test 3 9 news w = true) (i : Fin 8) :
    ggTWNRflOf 3 9 (w.e.getD i.val ([], [])) ∈
      Submonoid.closure (ggTWGens 3 9 (ggTWNNews 3 9 news)) := by
  obtain ⟨he_len, -, hsw_len, -, -, -, hsw_lt, -, hTe_word⟩ := l05nL8_test h
  have hvalid := l05nL8_valid h
  have hTe_wf := l05nL8_Te_wf h
  have hTg_wf := l05nL8_Tg_wf (news := news) hnews
  have hvalid_get : ∀ k < 8, GGTWNValid 3 9 (w.e.getD k ([], [])) := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by rw [he_len]; exact hk)]
    exact hvalid _ (List.getElem_mem _)
  have hTglen : (ggTWLGenMats 3 9 news).length = 8 + news.length := by simp [ggTWLGenMats]
  have hswmem : w.sw.getD i.val [] ∈ w.sw := by
    rw [List.getD_eq_getElem _ _ (by rw [hsw_len]; exact i.isLt)]
    exact List.getElem_mem _
  have hw : ∀ k ∈ w.sw.getD i.val [], k < (ggTWLGenMats 3 9 news).length := by
    intro k hk; rw [hTglen]; exact hsw_lt (w.sw.getD i.val []) hswmem k hk
  have hTemem : (w.e.map (ggTWLMatOfPair 3 8)).getD i.val [] ∈ w.e.map (ggTWLMatOfPair 3 8) := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, he_len]; exact i.isLt)]
    exact List.getElem_mem _
  have hTe_lin : ggTWLMatLin 3 8 ((w.e.map (ggTWLMatOfPair 3 8)).getD i.val []) =
      ggTWNRflOf 3 9 (w.e.getD i.val ([], [])) := by
    rw [l05nL8_Te_get w i.val (by rw [he_len]; exact i.isLt)]
    exact (ggTWLMatOfPair_lin (hvalid_get i.val i.isLt)).2
  have hLin_eq : ggTWLMatLin 3 8 ((w.e.map (ggTWLMatOfPair 3 8)).getD i.val []) =
      ggTWLMatLin 3 8 (ggTWLWordMat 3 8 (ggTWLGenMats 3 9 news) (w.sw.getD i.val [])) :=
    (ggTWLMatEq_iff (hTe_wf _ hTemem) (l05nL8_word_wf hTg_wf hw)).mp
      (hTe_word i.val i.isLt)
  have hword : ggTWLMatLin 3 8
        (ggTWLWordMat 3 8 (ggTWLGenMats 3 9 news) (w.sw.getD i.val [])) =
      ((w.sw.getD i.val []).map fun k => ggTWNRflOf 3 9 (ggTWNGen 3 9 news k)).prod := by
    rw [(ggTWLWordMat_lin hTg_wf hw).2]
    congr 1
    apply List.map_congr_left
    intro k hk
    rw [l05nL8_Tg_get news k (by rw [← hTglen]; exact hw k hk)]
    exact (ggTWLMatOfPair_lin (ggTWNGen_valid (p := 3) (N := 9) (by norm_num) (by norm_num)
      hnews (by rw [← hTglen]; exact hw k hk))).2
  rw [← hTe_lin, hLin_eq, hword]
  exact Submonoid.list_prod_mem _ (fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact ggTWNGen_mem (p := 3) (N := 9) (by norm_num) (by norm_num)
      (g := k) (by rw [← hTglen]; exact hw k hk))

private lemma l05nL8_gen_mem {news : List GGDepANPair} {w : GGTWLE8}
    (hnews : ∀ q ∈ news, GGTWNValid 3 9 q)
    (h : ggTWLE8Test 3 9 news w = true) (g : ℕ) (hg : g < 8 + news.length) :
    ggTWNRflOf 3 9 (ggTWNGen 3 9 news g) ∈
      Submonoid.closure (Set.range fun i : Fin 8 => ggTWNRflOf 3 9 (w.e.getD i.val ([], []))) := by
  obtain ⟨he_len, hgw_len, -, -, -, hgw_lt, -, hTg_word, -⟩ := l05nL8_test h
  have hTe_wf := l05nL8_Te_wf h
  have hvalid_get : ∀ k < 8, GGTWNValid 3 9 (w.e.getD k ([], [])) := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by rw [he_len]; exact hk)]
    exact l05nL8_valid h _ (List.getElem_mem _)
  have hgwmem : w.gw.getD g [] ∈ w.gw := by
    rw [List.getD_eq_getElem _ _ (by rw [hgw_len]; exact hg)]
    exact List.getElem_mem _
  have hTelen : (w.e.map (ggTWLMatOfPair 3 8)).length = 8 := by simp [List.length_map, he_len]
  have hw : ∀ k ∈ w.gw.getD g [], k < (w.e.map (ggTWLMatOfPair 3 8)).length := by
    intro k hk; rw [hTelen]; exact hgw_lt (w.gw.getD g []) hgwmem k hk
  have hTg_wf_g : ggTWLMatWF 8 ((ggTWLGenMats 3 9 news).getD g []) := by
    rw [l05nL8_Tg_get news g hg]
    exact (ggTWLMatOfPair_lin (ggTWNGen_valid (p := 3) (N := 9) (by norm_num) (by norm_num)
      hnews hg)).1
  have hTg_lin : ggTWLMatLin 3 8 ((ggTWLGenMats 3 9 news).getD g []) =
      ggTWNRflOf 3 9 (ggTWNGen 3 9 news g) := by
    rw [l05nL8_Tg_get news g hg]
    exact (ggTWLMatOfPair_lin (ggTWNGen_valid (p := 3) (N := 9) (by norm_num) (by norm_num)
      hnews hg)).2
  have hLin_eq : ggTWLMatLin 3 8 ((ggTWLGenMats 3 9 news).getD g []) =
      ggTWLMatLin 3 8 (ggTWLWordMat 3 8 (w.e.map (ggTWLMatOfPair 3 8)) (w.gw.getD g [])) :=
    (ggTWLMatEq_iff hTg_wf_g (l05nL8_word_wf hTe_wf hw)).mp (hTg_word g hg)
  have hword : ggTWLMatLin 3 8
        (ggTWLWordMat 3 8 (w.e.map (ggTWLMatOfPair 3 8)) (w.gw.getD g [])) =
      ((w.gw.getD g []).map fun k => ggTWNRflOf 3 9 (w.e.getD k ([], []))).prod := by
    rw [(ggTWLWordMat_lin hTe_wf hw).2]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hk8 : k < 8 := by rw [← hTelen]; exact hw k hk
    rw [l05nL8_Te_get w k (by rw [he_len]; exact hk8)]
    exact (ggTWLMatOfPair_lin (hvalid_get k hk8)).2
  rw [← hTg_lin, hLin_eq, hword]
  exact Submonoid.list_prod_mem _ (fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact Submonoid.subset_closure
      ⟨⟨k, by rw [← hTelen]; exact hw k hk⟩, rfl⟩)

theorem ggTWLE8_sound {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid 3 9 q)
    (w : GGTWLE8) (h : ggTWLE8Test 3 9 news w = true) :
    GGTWLowE8Outcome (ggTWGens 3 9 (ggTWNNews 3 9 news)) := by
  obtain ⟨he_len, hgw_len, hsw_len, he_wf, hcartan, hgw_lt, hsw_lt, hTg_word, hTe_word⟩ :=
    l05nL8_test h
  have hcast : ∀ (a b : List ℕ), a.length = 8 → b.length = 8 →
      ((ggDepANDot 3 a b : ℕ) : ZMod 3) = ggDepAdot (ggTWNToZ 3 9 a) (ggTWNToZ 3 9 b) := by
    intro a b ha hb
    exact ggDepANDot_cast (p := 3) (N := 8) a b ha hb
  have hvalid_get : ∀ k < 8, GGTWNValid 3 9 (w.e.getD k ([], [])) := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by rw [he_len]; exact hk)]
    exact l05nL8_valid h _ (List.getElem_mem _)
  refine ⟨fun i => ggTWNToZ 3 9 (w.e.getD i.val ([], [])).1,
    fun i => ggTWNToZ 3 9 (w.e.getD i.val ([], [])).2, ?_, ?_, ?_⟩
  · intro i
    have hd : ggDepANDot 3 (w.e.getD i.val ([], [])).2 (w.e.getD i.val ([], [])).1 = 2 % 3 := by
      have h1 := hcartan i.val i.isLt i.val i.isLt
      rw [l05nL8_cartan_diag i.val, l05nL8_dot_mod 3] at h1
      exact h1
    have hlen1 : (w.e.getD i.val ([], [])).1.length = 8 := (he_wf _ (by
      rw [List.getD_eq_getElem _ _ (by rw [he_len]; exact i.isLt)]
      exact List.getElem_mem _)).1
    have hlen2 : (w.e.getD i.val ([], [])).2.length = 8 := (he_wf _ (by
      rw [List.getD_eq_getElem _ _ (by rw [he_len]; exact i.isLt)]
      exact List.getElem_mem _)).2
    change ggDepAdot (ggTWNToZ 3 9 (w.e.getD i.val ([], [])).2)
      (ggTWNToZ 3 9 (w.e.getD i.val ([], [])).1) = 2
    rw [← hcast _ _ hlen2 hlen1, hd]
    norm_num
  · intro i j
    have h1 := hcartan i.val i.isLt j.val j.isLt
    rw [l05nL8_dot_mod 3] at h1
    have hlen_i : (w.e.getD i.val ([], [])).2.length = 8 := (he_wf _ (by
      rw [List.getD_eq_getElem _ _ (by rw [he_len]; exact i.isLt)]
      exact List.getElem_mem _)).2
    have hlen_j : (w.e.getD j.val ([], [])).1.length = 8 := (he_wf _ (by
      rw [List.getD_eq_getElem _ _ (by rw [he_len]; exact j.isLt)]
      exact List.getElem_mem _)).1
    change ggDepAdot (ggTWNToZ 3 9 (w.e.getD i.val ([], [])).2)
      (ggTWNToZ 3 9 (w.e.getD j.val ([], [])).1) = ((CartanMatrix.E 8 i j : ℤ) : ZMod 3)
    rw [← hcast _ _ hlen_i hlen_j, h1]
    exact l05nL8_cartan_cast i j
  · change Submonoid.closure (Set.range fun i : Fin 8 =>
        ggTWNRflOf 3 9 (w.e.getD i.val ([], []))) =
      Submonoid.closure (ggTWGens 3 9 (ggTWNNews 3 9 news))
    apply le_antisymm
    · apply Submonoid.closure_le.mpr
      rintro x ⟨i, rfl⟩
      exact l05nL8_refl_mem hnews h i
    · apply Submonoid.closure_le.mpr
      rintro x (hx | hx)
      · rcases hx with ⟨i, rfl⟩
        change ggTWRefl (ggTWh 3 9 i) (ggTWα 3 9 i) ∈
          Submonoid.closure (Set.range fun i : Fin 8 => ggTWNRflOf 3 9 (w.e.getD i.val ([], [])))
        have hgen : ggTWRefl (ggTWh 3 9 i) (ggTWα 3 9 i) =
            ggTWNRflOf 3 9 (ggTWNGen 3 9 news i.val) := by
          show ggTWRefl (ggTWh 3 9 i) (ggTWα 3 9 i) =
            ggTWRefl (ggTWNToZ 3 9 (ggTWNGen 3 9 news i.val).1)
              (ggTWNToZ 3 9 (ggTWNGen 3 9 news i.val).2)
          rw [ggTWNGen, if_pos (by omega : i.val + 1 < 9)]
          simp only [ggTWNH_toZ, ggTWNA_toZ]
        rw [hgen]
        exact l05nL8_gen_mem hnews h i.val (by omega)
      · rcases hx with ⟨t, ht, rfl⟩
        rcases ht with ⟨q, hq, rfl⟩
        change ggTWNRflOf 3 9 q ∈
          Submonoid.closure (Set.range fun i : Fin 8 => ggTWNRflOf 3 9 (w.e.getD i.val ([], [])))
        obtain ⟨k, hk, hkq⟩ := List.mem_iff_getElem.mp hq
        have hg : 8 + k < 8 + news.length := by omega
        have hgen : ggTWNRflOf 3 9 q = ggTWNRflOf 3 9 (ggTWNGen 3 9 news (8 + k)) := by
          congr 1
          rw [ggTWNGen, if_neg (by omega), show 8 + k + 1 - 9 = k by omega,
            List.getD_eq_getElem _ _ hk, hkq]
        rw [hgen]
        exact l05nL8_gen_mem hnews h (8 + k) hg

end CFSG.StandardType

end

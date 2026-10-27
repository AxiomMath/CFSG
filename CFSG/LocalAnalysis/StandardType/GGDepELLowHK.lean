module

public import CFSG.LocalAnalysis.StandardType.GGDepELNatWord

public section

namespace CFSG.StandardType

open Certificates.DepED4Low Certificates.TwoDepSmall Certificates.DepASmall
  Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nHH_cast_eq_of_mod_eq {x y : ℕ} (h : x % 3 = y % 3) :
    (x : ZMod 3) = (y : ZMod 3) := (ZMod.natCast_eq_natCast_iff' x y 3).mpr h

private lemma l05nHH_mod_eq_of_cast_eq {x y : ℕ} (h : (x : ZMod 3) = (y : ZMod 3)) :
    x % 3 = y % 3 := (ZMod.natCast_eq_natCast_iff' x y 3).mp h

private lemma l05nHH_cast_eq_zero_of_mod_eq {x : ℕ} (h : x % 3 = 0) :
    (x : ZMod 3) = 0 :=
  (ZMod.natCast_eq_zero_iff x 3).mpr (Nat.dvd_of_mod_eq_zero h)

private lemma l05nHH_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]

private lemma l05nHH_refl_apply {p N : ℕ} (c f v : GGDepAE p N) :
    ggDepARefl c f v = v - ggDepAdot f v • c := by
  simp [ggDepARefl, l05nHH_form_apply]

private lemma l05nHH_length_of_veceq {a b : List ℕ} (h : ggTWLVecEq 3 a b = true) :
    a.length = b.length := by
  rw [ggTWLVecEq, Bool.and_eq_true] at h
  exact decide_eq_true_eq.mp h.1

private lemma l05nHH_toZ_of_veceq {a b : List ℕ} (h : ggTWLVecEq 3 a b = true) :
    ggDepELToZ a = ggDepELToZ b := by
  rw [ggTWLVecEq, Bool.and_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hlen' : a.length = b.length := decide_eq_true_eq.mp hlen
  funext j
  simp only [ggDepELToZ, ggDepANToZ]
  by_cases hj : j.val < a.length
  · have hkb : j.val < b.length := by rw [← hlen']; exact hj
    have hzip : j.val < (List.zipWith (fun x y => x % 3 == y % 3) a b).length := by
      rw [List.length_zipWith, ← hlen', min_self]; exact hj
    have hcoord := (List.all_eq_true.mp hall) _ (List.getElem_mem hzip)
    simp only [id_eq] at hcoord
    rw [List.getElem_zipWith, beq_iff_eq] at hcoord
    rw [List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hj,
      List.getD_eq_getElem (l := b) (d := 0) (n := j.val) hkb]
    exact l05nHH_cast_eq_of_mod_eq hcoord
  · rw [List.getD_eq_default (l := a) (d := 0) (n := j.val) (by omega),
      List.getD_eq_default (l := b) (d := 0) (n := j.val) (by omega)]

private lemma l05nHH_veceq_of_toZ_eq {a b : List ℕ} (ha : a.length = 6)
    (hb : b.length = 6) (h : ggDepELToZ a = ggDepELToZ b) :
    ggTWLVecEq 3 a b = true := by
  rw [ggTWLVecEq, Bool.and_eq_true]
  refine ⟨decide_eq_true_eq.mpr (by rw [ha, hb]), ?_⟩
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  change (List.zipWith (fun x y => x % 3 == y % 3) a b)[k] = true
  rw [List.getElem_zipWith, beq_iff_eq]
  apply l05nHH_mod_eq_of_cast_eq
  have hka : k < a.length := by rw [List.length_zipWith] at hk; omega
  have hkb : k < b.length := by rw [List.length_zipWith] at hk; omega
  have hk6 : k < 6 := by rw [← ha]; exact hka
  have hcong := congrFun h ⟨k, hk6⟩
  simp only [ggDepELToZ, ggDepANToZ] at hcong
  rw [List.getD_eq_getElem (l := a) (d := 0) (n := k) hka,
    List.getD_eq_getElem (l := b) (d := 0) (n := k) hkb] at hcong
  exact hcong

private lemma l05nHH_getD_og {α : Type*} (l : List α) (d : α) {k : ℕ} (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem (l := l) (d := d) (n := k) hk]
  exact List.getElem_mem hk

private lemma l05nHH_news_mem {news : List GGDepANPair} {q : GGDepANPair}
    (hq : q ∈ news) : q ∈ ggDepELNOGens news :=
  List.mem_append.mpr (Or.inr hq)

private lemma l05nHH_news_mem_fst {news : List GGDepANPair} {q : GGDepANPair}
    (hq : q ∈ news) : q.1 ∈ (ggDepELNOGens news).map (·.1) :=
  List.mem_map.mpr ⟨q, l05nHH_news_mem hq, rfl⟩

private lemma l05nHH_H_mem_fst {news : List GGDepANPair}
    (i : {i : Fin 6 // GGDepED4In i}) :
    ggDepELNH i.1.val ∈ (ggDepELNOGens news).map (·.1) := by
  obtain ⟨j, hj⟩ := i
  refine List.mem_map.mpr ⟨(ggDepELNH j.val, ggDepELNA j.val), ?_, rfl⟩
  rw [ggDepELNOGens, List.mem_append]
  refine Or.inl (List.mem_map.mpr ⟨j.val, ?_, rfl⟩)
  fin_cases j <;> simp_all [ggDepELNJ, GGDepED4In]

private lemma l05nHH_og_lengths {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGDepELNValid q) {q : GGDepANPair}
    (hq : q ∈ ggDepELNOGens news) :
    q.1.length = 6 ∧ q.2.length = 6 := by
  rw [ggDepELNOGens, List.mem_append] at hq
  rcases hq with hq | hq
  · rcases List.mem_map.mp hq with ⟨c, hc, hceq⟩
    rw [← hceq]
    have hc' : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by simpa [ggDepELNJ] using hc
    have hc6 : c < 6 := by rcases hc' with rfl | rfl | rfl | rfl <;> norm_num
    exact ⟨ggDepELNH_length hc6, ggDepELNA_length hc6⟩
  · exact ⟨(hnews q hq).1, (hnews q hq).2.1⟩

private lemma l05nHH_stable_implies {og : List GGDepANPair} {cs R : List (List ℕ)}
    (h : ggTWLStable 3 og cs R = true) :
    (∀ c ∈ cs, ∃ r ∈ R, ggTWLVecEq 3 c r = true) ∧
      (∀ u ∈ R, ∀ g ∈ og, ∃ r ∈ R, ggTWLVecEq 3 (ggTWNRefl 3 g u) r = true) := by
  rw [ggTWLStable, Bool.and_eq_true] at h
  refine ⟨fun c hc => List.any_eq_true.mp (List.all_eq_true.mp h.1 c hc),
    fun u hu g hg =>
      List.any_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h.2 u hu) g hg)⟩

private lemma l05nHH_gen_mem {news : List GGDepANPair} {q : GGDepANPair}
    (hq : q ∈ ggDepELNOGens news) :
    ggDepARefl (ggDepELToZ q.1) (ggDepELToZ q.2) ∈
      ggDepELOGens (ggDepELNNews news) := by
  rw [ggDepELNOGens, List.mem_append] at hq
  rcases hq with hq | hq
  · rcases List.mem_map.mp hq with ⟨c, hc, hceq⟩
    rw [← hceq]
    have hc' : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by simpa [ggDepELNJ] using hc
    have hc6 : c < 6 := by rcases hc' with rfl | rfl | rfl | rfl <;> norm_num
    have hcJ : GGDepED4In (⟨c, hc6⟩ : Fin 6) := by
      rcases hc' with rfl | rfl | rfl | rfl <;> simp [GGDepED4In]
    rw [ggDepELNH_toZ (⟨c, hc6⟩ : Fin 6), ggDepELNA_toZ (⟨c, hc6⟩ : Fin 6)]
    exact Or.inl ⟨⟨⟨c, hc6⟩, hcJ⟩, Set.mem_univ _, rfl⟩
  · exact Or.inr ⟨(ggDepELToZ q.1, ggDepELToZ q.2), ⟨q, hq, rfl⟩, rfl⟩

private lemma l05nHH_getD_centre {news : List GGDepANPair}
    {k : ℕ} (hk : k < (ggDepELNOGens news).length) :
    ggDepELToZ ((ggDepELNOGens news).getD k ([], [])).1 ∈
      ggDepELOCentres (ggDepELNNews news) := by
  set q : GGDepANPair := (ggDepELNOGens news).getD k ([], []) with hqdef
  have hqmem : q ∈ ggDepELNOGens news := by
    rw [hqdef]; exact l05nHH_getD_og _ _ hk
  rw [ggDepELNOGens, List.mem_append] at hqmem
  rcases hqmem with hq | hq
  · rcases List.mem_map.mp hq with ⟨c, hc, hceq⟩
    rw [← hceq]
    have hc' : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by simpa [ggDepELNJ] using hc
    have hc6 : c < 6 := by rcases hc' with rfl | rfl | rfl | rfl <;> norm_num
    have hcJ : GGDepED4In (⟨c, hc6⟩ : Fin 6) := by
      rcases hc' with rfl | rfl | rfl | rfl <;> simp [GGDepED4In]
    rw [ggDepELNH_toZ (⟨c, hc6⟩ : Fin 6)]
    exact Or.inl ⟨⟨⟨c, hc6⟩, hcJ⟩, Set.mem_univ _, rfl⟩
  · exact Or.inr ⟨(ggDepELToZ q.1, ggDepELToZ q.2), ⟨q, hq, rfl⟩, rfl⟩

private lemma l05nHH_isRefl {q : GGDepANPair} (hq : GGDepELNValid q) :
    GGDepELIsRefl (ggDepELNRflOf q) := by
  refine ⟨ggDepELToZ q.1, ggDepELToZ q.2, ?_, rfl⟩
  exact ggDepELNValid_dot hq

private abbrev l05nHH_P (Rl : List (List ℕ)) (v : GGDepAE 3 6) : Prop :=
  ∃ u0 ∈ Rl, ggDepELToZ u0 = v ∧ u0.length = 6

private lemma l05nHH_P_centres {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGDepELNValid q) {Rl : List (List ℕ)}
    (hcontains : ∀ a ∈ (ggDepELNOGens news).map (·.1), ∃ r ∈ Rl,
      ggTWLVecEq 3 a r = true) :
    ∀ c ∈ ggDepELOCentres (ggDepELNNews news), l05nHH_P Rl c := by
  intro c hc
  rw [ggDepELOCentres, Set.mem_union] at hc
  rcases hc with hc | hc
  · rcases hc with ⟨i, -, rfl⟩
    obtain ⟨r, hrR, hveq⟩ := hcontains (ggDepELNH i.1.val) (l05nHH_H_mem_fst i)
    refine ⟨r, hrR, ?_, ?_⟩
    · rw [← l05nHH_toZ_of_veceq hveq, ggDepELNH_toZ i.1]
    · rw [← l05nHH_length_of_veceq hveq]; exact ggDepELNH_length i.1.isLt
  · rcases hc with ⟨t, ht, rfl⟩
    rcases ht with ⟨q, hq, rfl⟩
    obtain ⟨r, hrR, hveq⟩ := hcontains q.1 (l05nHH_news_mem_fst hq)
    refine ⟨r, hrR, ?_, ?_⟩
    · rw [← l05nHH_toZ_of_veceq hveq]
    · rw [← l05nHH_length_of_veceq hveq]; exact (hnews q hq).1

private lemma l05nHH_P_step_q {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGDepELNValid q) {Rl : List (List ℕ)}
    (hstep : ∀ u ∈ Rl, ∀ g ∈ ggDepELNOGens news,
      ∃ r ∈ Rl, ggTWLVecEq 3 (ggTWNRefl 3 g u) r = true)
    {q : GGDepANPair} (hq : q ∈ ggDepELNOGens news) {v : GGDepAE 3 6}
    (hv : l05nHH_P Rl v) :
    l05nHH_P Rl (ggDepARefl (ggDepELToZ q.1) (ggDepELToZ q.2) v) := by
  obtain ⟨u0, hu0R, hu0eq, hu0len⟩ := hv
  obtain ⟨r, hrR, hveq⟩ := hstep u0 hu0R q hq
  obtain ⟨hq1, hq2⟩ := l05nHH_og_lengths hnews hq
  refine ⟨r, hrR, ?_, ?_⟩
  · rw [← l05nHH_toZ_of_veceq hveq, ggDepELToZ_refl hq1 hq2 hu0len, hu0eq]
  · rw [← l05nHH_length_of_veceq hveq]
    exact ggDepELRefl_length hq1 hu0len

private lemma l05nHH_P_gen {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGDepELNValid q) {Rl : List (List ℕ)}
    (hstep : ∀ u ∈ Rl, ∀ g ∈ ggDepELNOGens news,
      ∃ r ∈ Rl, ggTWLVecEq 3 (ggTWNRefl 3 g u) r = true)
    {g : Module.End (ZMod 3) (GGDepAE 3 6)}
    (hg : g ∈ ggDepELOGens (ggDepELNNews news)) {v : GGDepAE 3 6}
    (hv : l05nHH_P Rl v) :
    l05nHH_P Rl (g v) := by
  rw [ggDepELOGens, Set.mem_union] at hg
  rcases hg with hg | hg
  · rcases hg with ⟨i, -, rfl⟩
    have hq : (ggDepELNH i.1.val, ggDepELNA i.1.val) ∈ ggDepELNOGens news := by
      obtain ⟨j, hj⟩ := i
      rw [ggDepELNOGens, List.mem_append]
      refine Or.inl (List.mem_map.mpr ⟨j.val, ?_, rfl⟩)
      fin_cases j <;> simp_all [ggDepELNJ, GGDepED4In]
    have h := l05nHH_P_step_q hnews hstep hq hv
    rwa [ggDepELNH_toZ i.1, ggDepELNA_toZ i.1] at h
  · rcases hg with ⟨t, ht, rfl⟩
    rcases ht with ⟨q, hqnews, rfl⟩
    exact l05nHH_P_step_q hnews hstep (l05nHH_news_mem hqnews) hv

private lemma l05nHH_P_closure {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGDepELNValid q) {Rl : List (List ℕ)}
    (hstep : ∀ u ∈ Rl, ∀ g ∈ ggDepELNOGens news,
      ∃ r ∈ Rl, ggTWLVecEq 3 (ggTWNRefl 3 g u) r = true)
    {W : Module.End (ZMod 3) (GGDepAE 3 6)}
    (hW : W ∈ Submonoid.closure (ggDepELOGens (ggDepELNNews news))) :
    ∀ (v : GGDepAE 3 6), l05nHH_P Rl v → l05nHH_P Rl (W v) := by
  induction hW using Submonoid.closure_induction with
  | mem x hx => intro v hv; exact l05nHH_P_gen hnews hstep hx hv
  | one => intro v hv; simpa using hv
  | mul x y hx hy ihx ihy => intro v hv; exact ihx (y v) (ihy v hv)

private lemma l05nHH_roots_repr {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGDepELNValid q) {Rl : List (List ℕ)}
    (hcontains : ∀ a ∈ (ggDepELNOGens news).map (·.1), ∃ r ∈ Rl,
      ggTWLVecEq 3 a r = true)
    (hstep : ∀ u ∈ Rl, ∀ g ∈ ggDepELNOGens news,
      ∃ r ∈ Rl, ggTWLVecEq 3 (ggTWNRefl 3 g u) r = true)
    {v : GGDepAE 3 6}
    (hv : v ∈ ggDepELRoots (ggDepELOGens (ggDepELNNews news))
      (ggDepELOCentres (ggDepELNNews news))) : l05nHH_P Rl v := by
  rw [ggDepELRoots] at hv
  rcases hv with ⟨W, hW, c, hc, rfl⟩
  exact l05nHH_P_closure hnews hstep hW c (l05nHH_P_centres hnews hcontains c hc)

private lemma l05nHH_foldr_length (og : List GGDepANPair) (ow : List ℕ) (v0 : List ℕ)
    (hL : ∀ q ∈ og, q.1.length = 6) (how : ∀ k ∈ ow, k < og.length)
    (hv0 : v0.length = 6) :
    (ow.foldr (fun k acc => ggTWNRefl 3 (og.getD k ([], [])) acc) v0).length = 6 := by
  induction ow with
  | nil => simpa using hv0
  | cons k ow ih =>
      rw [List.foldr_cons]
      exact ggDepELRefl_length (hL _ (l05nHH_getD_og og ([], []) (how k (List.mem_cons_self ..))))
        (ih (fun k' hk' => how k' (List.mem_cons_of_mem k hk')))

private lemma l05nHH_foldr_roots {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGDepELNValid q) (ow : List ℕ) (v0 : List ℕ)
    (how : ∀ k ∈ ow, k < (ggDepELNOGens news).length) (hv0 : v0.length = 6) :
    ∃ W ∈ Submonoid.closure (ggDepELOGens (ggDepELNNews news)),
      ggDepELToZ
          (ow.foldr (fun k acc =>
            ggTWNRefl 3 ((ggDepELNOGens news).getD k ([], [])) acc) v0)
        = W (ggDepELToZ v0) := by
  let og := ggDepELNOGens news
  induction ow with
  | nil => exact ⟨1, Submonoid.one_mem _, by simp⟩
  | cons k ow ih =>
      have hk : k < og.length := how k (List.mem_cons_self ..)
      have how' : ∀ k' ∈ ow, k' < og.length := fun k' hk' => how k' (List.mem_cons_of_mem k hk')
      obtain ⟨W, hWmem, hWeq⟩ := ih how'
      set q : GGDepANPair := og.getD k ([], []) with hqdef
      have hqmem : q ∈ og := l05nHH_getD_og og ([], []) hk
      have hqlen := l05nHH_og_lengths hnews hqmem
      have hlen := l05nHH_foldr_length og ow v0
        (fun q hq => (l05nHH_og_lengths hnews hq).1) how' hv0
      refine ⟨ggDepARefl (ggDepELToZ q.1) (ggDepELToZ q.2) * W, ?_, ?_⟩
      · exact Submonoid.mul_mem _ (Submonoid.subset_closure (l05nHH_gen_mem hqmem)) hWmem
      · rw [List.foldr_cons, ggDepELToZ_refl hqlen.1 hqlen.2 hlen, hWeq]
        rfl

theorem ggDepELHKTest_sound {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGDepELNValid q)
    (y : List ℕ) (hy : y.length = 6) (w : GGTWLHK)
    (h : ggDepELHKTest news y w = true) :
    GGDepELKill .other (ggDepELNNews news) (ggDepELToZ y) := by
  classical
  let og := ggDepELNOGens news
  let Rl := ggTWLOrbit 3 og 40 (og.map (·.1))
  let sp := ggDepELNWord news (ggDepELNGen news w.g) w.w
  let vlist := w.ow.foldr (fun k acc => ggTWNRefl 3 (og.getD k ([], [])) acc)
    (og.getD w.oc ([], [])).1
  let sv := ggTWNRefl 3 sp vlist
  have hh := h
  dsimp only [ggDepELHKTest] at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hh
  obtain ⟨⟨⟨⟨⟨⟨hg1, hw1⟩, hoc⟩, how⟩, hstab⟩, hdot⟩, hpar⟩ := hh
  have hstab' : ggTWLStable 3 og (og.map (·.1)) Rl = true := hstab
  have hword := ggDepELNWord_valid_mem hnews
    (ggDepELNGen_valid hnews hg1)
    (ggDepELNGen_mem hg1) hw1
  have hsp : GGDepELNValid sp := hword.1
  refine Or.inr ⟨ggDepELNRflOf sp, hword.2, l05nHH_isRefl hsp, ?_, ?_⟩
  · have hdy : ggDepAdot (ggDepELToZ sp.2) (ggDepELToZ y) = 0 := by
      have hcast := ggDepELDot_cast hsp.2.1 hy
      rw [l05nHH_cast_eq_zero_of_mod_eq hdot] at hcast
      exact hcast.symm
    show ggDepARefl (ggDepELToZ sp.1) (ggDepELToZ sp.2) (ggDepELToZ y) = ggDepELToZ y
    rw [l05nHH_refl_apply, hdy, zero_smul, sub_zero]
  · obtain ⟨hcontains, hstep⟩ := l05nHH_stable_implies hstab'
    have hv0 : ((og.getD w.oc ([], [])).1).length = 6 :=
      (l05nHH_og_lengths hnews (l05nHH_getD_og og ([], []) hoc)).1
    have hvlen : vlist.length = 6 :=
      l05nHH_foldr_length og w.ow (og.getD w.oc ([], [])).1
        (fun q hq => (l05nHH_og_lengths hnews hq).1) how hv0
    refine ⟨ggDepELToZ vlist, ?_, ?_⟩
    · obtain ⟨W, hWmem, hWeq⟩ :=
        l05nHH_foldr_roots hnews w.ow (og.getD w.oc ([], [])).1 how hv0
      exact ⟨W, hWmem, ggDepELToZ (og.getD w.oc ([], [])).1,
        l05nHH_getD_centre hoc, hWeq⟩
    · intro w' hw' c d hc heq
      obtain ⟨u0, hu0R, hu0eq, hu0len⟩ := l05nHH_roots_repr hnews hcontains hstep hw'
      have hsv : ggDepELToZ sv = ggDepELNRflOf sp (ggDepELToZ vlist) := by
        show ggDepELToZ (ggTWNRefl 3 sp vlist) =
          ggDepARefl (ggDepELToZ sp.1) (ggDepELToZ sp.2) (ggDepELToZ vlist)
        exact ggDepELToZ_refl hsp.1 hsp.2.1 hvlen
      rw [← hsv] at heq
      rw [← hu0eq] at heq
      have hR : ggDepELToZ sv =
          ggDepELToZ (ggTWNAdd 3 (ggDepANSmul 3 c.val u0) (ggDepANSmul 3 d.val y)) := by
        rw [heq]
        rw [ggDepELToZ_add (ggDepELSmul_length c.val hu0len) (ggDepELSmul_length d.val hy),
            ggDepELToZ_smul hu0len c.val,
            ggDepELToZ_smul hy d.val,
            ZMod.natCast_zmod_val c, ZMod.natCast_zmod_val d]
      have hveceq : ggTWLVecEq 3 sv
          (ggTWNAdd 3 (ggDepANSmul 3 c.val u0) (ggDepANSmul 3 d.val y)) = true :=
        l05nHH_veceq_of_toZ_eq (ggDepELRefl_length hsp.1 hvlen)
          (ggDepELAdd_length (ggDepELSmul_length c.val hu0len)
            (ggDepELSmul_length d.val hy)) hR
      have hcval : c.val ≠ 0 := by
        intro h0
        apply hc
        rw [← ZMod.natCast_zmod_val c, h0, Nat.cast_zero]
      have hpar_true : ggTWLParMod 3 y u0 sv = true := by
        rw [ggTWLParMod]
        refine List.any_eq_true.mpr ⟨c.val, List.mem_range.mpr (ZMod.val_lt c), ?_⟩
        rw [Bool.and_eq_true]
        refine ⟨decide_eq_true_eq.mpr hcval, ?_⟩
        exact List.any_eq_true.mpr ⟨d.val, List.mem_range.mpr (ZMod.val_lt d), hveceq⟩
      have hh2 := hpar u0 hu0R
      rw [hpar_true] at hh2
      exact Bool.false_ne_true hh2

end CFSG.StandardType

end

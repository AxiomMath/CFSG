module

public import TauCeti.FieldTheory.Finite.Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {K : Type} [Field K] [Finite K]

@[expose] def s16c11_case5_ann (P : AddSubgroup (K × K)) : Set (K × K) :=
  {w | ∀ p ∈ P, p.1 * w.1 + p.2 * w.2 = 0}

private theorem s16c11_case5_alg_charP (hK : Nat.card K = 4) : CharP K 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num)

private def s16c11_case5_scalar (c : K) : K × K →+ K × K where
  toFun q := (c * q.1, c * q.2)
  map_zero' := by simp
  map_add' p q := by ext <;> simp [mul_add]

@[simp] private theorem s16c11_case5_scalar_apply (c : K) (q : K × K) :
    s16c11_case5_scalar c q = (c * q.1, c * q.2) := rfl

private def s16c11_case5_lineHom (x : K × K) : K →+ K × K where
  toFun c := (c * x.1, c * x.2)
  map_zero' := by simp
  map_add' c d := by ext <;> simp [add_mul]

@[simp] private theorem s16c11_case5_lineHom_apply (x : K × K) (c : K) :
    s16c11_case5_lineHom x c = (c * x.1, c * x.2) := rfl

private def s16c11_case5_line (x : K × K) : AddSubgroup (K × K) :=
  (s16c11_case5_lineHom x).range

private theorem s16c11_case5_mem_line {x w : K × K} :
    w ∈ s16c11_case5_line x ↔ ∃ c : K, (c * x.1, c * x.2) = w := by
  rw [s16c11_case5_line, AddMonoidHom.mem_range]
  simp only [s16c11_case5_lineHom_apply]

private theorem s16c11_case5_lineHom_injective {x : K × K} (hx : x ≠ 0) :
    Function.Injective (s16c11_case5_lineHom x) := by
  intro c d hcd
  have h1 : c * x.1 = d * x.1 := by
    simpa [s16c11_case5_lineHom_apply] using congrArg Prod.fst hcd
  have h2 : c * x.2 = d * x.2 := by
    simpa [s16c11_case5_lineHom_apply] using congrArg Prod.snd hcd
  rcases eq_or_ne x.1 0 with hx1 | hx1
  · have hx2 : x.2 ≠ 0 := by
      intro hx2
      exact hx (Prod.ext hx1 hx2)
    exact mul_right_cancel₀ hx2 h2
  · exact mul_right_cancel₀ hx1 h1

private theorem s16c11_case5_card_line (hK : Nat.card K = 4) {x : K × K} (hx : x ≠ 0) :
    Nat.card ↥(s16c11_case5_line x) = 4 := by
  rw [s16c11_case5_line, AddMonoidHom.range_eq_map,
    AddSubgroup.card_map_of_injective (s16c11_case5_lineHom_injective hx),
    AddSubgroup.card_top, hK]

private theorem s16c11_case5_card_line_dvd (hK : Nat.card K = 4) (x : K × K) :
    Nat.card ↥(s16c11_case5_line x) ∣ 4 := by
  simpa [s16c11_case5_line, hK] using
    AddSubgroup.card_range_dvd (s16c11_case5_lineHom x)

private def s16c11_case5_pairLeft (w : K × K) : K × K →+ K where
  toFun p := p.1 * w.1 + p.2 * w.2
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add]
    ring

@[simp] private theorem s16c11_case5_pairLeft_apply (w p : K × K) :
    s16c11_case5_pairLeft w p = p.1 * w.1 + p.2 * w.2 := rfl

private lemma s16c11_case5_pair_self_mem_ann_zmultiples [CharP K 2] (x : K × K) :
    (x.2, x.1) ∈ s16c11_case5_ann (AddSubgroup.zmultiples x) := by
  have hker : AddSubgroup.zmultiples x ≤ (s16c11_case5_pairLeft (x.2, x.1)).ker :=
    AddSubgroup.zmultiples_le.mpr (by
      rw [AddMonoidHom.mem_ker, s16c11_case5_pairLeft_apply]
      show x.1 * x.2 + x.2 * x.1 = 0
      rw [mul_comm x.1 x.2, CharTwo.add_self_eq_zero])
  intro p hp
  exact AddMonoidHom.mem_ker.mp (hker hp)

private lemma s16c11_case5_card_zmultiples [CharP K 2] {x : K × K} (hx : x ≠ 0) :
    Nat.card ↥(AddSubgroup.zmultiples x) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zmultiples]
  exact addOrderOf_eq_prime (p := 2) (CharTwo.two_nsmul x) hx

private lemma s16c11_case5_ann_subset_singleton_of_det_ne_zero {x y : K × K}
    (hxy : x.1 * y.2 - x.2 * y.1 ≠ 0) {P : AddSubgroup (K × K)} (hx : x ∈ P) (hy : y ∈ P) :
    ∀ w ∈ s16c11_case5_ann P, w = 0 := by
  intro w hw
  have h1 : x.1 * w.1 + x.2 * w.2 = 0 := hw x hx
  have h2 : y.1 * w.1 + y.2 * w.2 = 0 := hw y hy
  have hw1 : w.1 = 0 := by
    have h : (x.1 * y.2 - x.2 * y.1) * w.1 = 0 := by
      have h' : (x.1 * y.2 - x.2 * y.1) * w.1 =
          y.2 * (x.1 * w.1 + x.2 * w.2) - x.2 * (y.1 * w.1 + y.2 * w.2) := by ring
      rw [h', h1, h2]
      simp
    exact (mul_eq_zero.mp h).resolve_left hxy
  have hw2 : w.2 = 0 := by
    have h : (x.1 * y.2 - x.2 * y.1) * w.2 = 0 := by
      have h' : (x.1 * y.2 - x.2 * y.1) * w.2 =
          x.1 * (y.1 * w.1 + y.2 * w.2) - y.1 * (x.1 * w.1 + x.2 * w.2) := by ring
      rw [h', h1, h2]
      simp
    exact (mul_eq_zero.mp h).resolve_left hxy
  exact Prod.ext hw1 hw2

private lemma s16c11_case5_mem_line_of_det_eq_zero {q y : K × K} (hq : q ≠ 0)
    (hdet : q.1 * y.2 - q.2 * y.1 = 0) : y ∈ s16c11_case5_line q := by
  rw [s16c11_case5_mem_line]
  have hdet' : q.1 * y.2 = q.2 * y.1 := sub_eq_zero.mp hdet
  rcases eq_or_ne q.1 0 with hq1 | hq1
  · have hq2 : q.2 ≠ 0 := by
      intro hq2
      exact hq (Prod.ext hq1 hq2)
    have hy1 : y.1 = 0 := by
      have h := hdet'
      rw [hq1, zero_mul] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hq2
    refine ⟨y.2 / q.2, ?_⟩
    ext
    · rw [hq1, mul_zero, hy1]
    · exact div_mul_cancel₀ y.2 hq2
  · refine ⟨y.1 / q.1, ?_⟩
    ext
    · exact div_mul_cancel₀ y.1 hq1
    · refine mul_right_cancel₀ hq1 ?_
      rw [mul_assoc, mul_comm q.2 q.1, ← mul_assoc, div_mul_cancel₀ y.1 hq1,
        mul_comm y.2 q.1, hdet', mul_comm y.1 q.2]

private lemma s16c11_case5_exists_not_mem_ann {P : AddSubgroup (K × K)} (hP : P ≠ ⊥) :
    ∃ w : K × K, w ∉ s16c11_case5_ann P := by
  have hlt : (⊥ : AddSubgroup (K × K)) < P := bot_lt_iff_ne_bot.mpr hP
  obtain ⟨p, hpP, hp_not⟩ := (SetLike.lt_iff_le_and_exists.mp hlt).2
  have hp0 : p ≠ 0 := by
    intro h
    exact hp_not (by simpa [AddSubgroup.mem_bot] using h)
  rcases eq_or_ne p.1 0 with hp1 | hp1
  · have hp2 : p.2 ≠ 0 := by
      intro hp2
      exact hp0 (Prod.ext hp1 hp2)
    refine ⟨(0, p.2⁻¹), ?_⟩
    intro hmem
    have := hmem p hpP
    simp [hp1, hp2] at this
  · refine ⟨(p.1⁻¹, 0), ?_⟩
    intro hmem
    have := hmem p hpP
    simp [hp1] at this

private lemma s16c11_case5_det_eq_zero_of_ann_eq (hK : Nat.card K = 4) {P : AddSubgroup (K × K)}
    (hcard : Nat.card ↥P = 4)
    (h : ∀ P' : AddSubgroup (K × K), P' ≤ P → Nat.card ↥P ≤ 2 * Nat.card ↥P' →
      s16c11_case5_ann P' = s16c11_case5_ann P) :
    ∀ x ∈ P, ∀ y ∈ P, x.1 * y.2 - x.2 * y.1 = 0 := by
  intro x hx y hy
  by_contra hdet
  haveI : CharP K 2 := s16c11_case5_alg_charP hK
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hdet (by simp)
  have hP'le : AddSubgroup.zmultiples x ≤ P := AddSubgroup.zmultiples_le.mpr hx
  have hcard_z : Nat.card ↥(AddSubgroup.zmultiples x) = 2 :=
    s16c11_case5_card_zmultiples hx0
  have hann_eq : s16c11_case5_ann (AddSubgroup.zmultiples x) = s16c11_case5_ann P :=
    h _ hP'le (by simp [hcard, hcard_z])
  have hannP : ∀ w ∈ s16c11_case5_ann P, w = 0 :=
    s16c11_case5_ann_subset_singleton_of_det_ne_zero hdet hx hy
  have hxw : (x.2, x.1) ∈ s16c11_case5_ann (AddSubgroup.zmultiples x) :=
    s16c11_case5_pair_self_mem_ann_zmultiples x
  rw [hann_eq] at hxw
  have hne : (x.2, x.1) ≠ 0 := by
    intro h0
    exact hx0 (Prod.ext (congrArg Prod.snd h0) (congrArg Prod.fst h0))
  exact hne (hannP _ hxw)

theorem s16c11_case5_ann_card_ge (hK : Nat.card K = 4) {P : AddSubgroup (K × K)} (hP : P ≠ ⊥)
    (h : ∀ P' : AddSubgroup (K × K), P' ≤ P → Nat.card ↥P ≤ 2 * Nat.card ↥P' →
      s16c11_case5_ann P' = s16c11_case5_ann P) :
    4 ≤ Nat.card ↥P := by
  have hKprod : Nat.card (K × K) = 2 ^ 4 := by rw [Nat.card_prod, hK]; norm_num
  have hdvd : Nat.card ↥P ∣ 2 ^ 4 := by
    refine ⟨P.index, ?_⟩
    rw [← hKprod, P.card_mul_index]
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hne1 : Nat.card ↥P ≠ 1 := by
    intro h1
    exact hP (AddSubgroup.eq_bot_of_card_eq P h1)
  have hne2 : Nat.card ↥P ≠ 2 := by
    intro h2
    have hbot : s16c11_case5_ann (⊥ : AddSubgroup (K × K)) = s16c11_case5_ann P :=
      h ⊥ bot_le (by simp [h2, AddSubgroup.card_bot])
    have huniv : s16c11_case5_ann P = Set.univ := by
      rw [← hbot]
      ext w
      simp [s16c11_case5_ann]
    obtain ⟨w, hw⟩ := s16c11_case5_exists_not_mem_ann hP
    exact hw (by rw [huniv]; exact Set.mem_univ w)
  interval_cases k
  · exact absurd hk hne1
  · exact absurd hk hne2
  · rw [hk]; norm_num
  · rw [hk]; norm_num
  · rw [hk]; norm_num

theorem s16c11_case5_ann_card_four (hK : Nat.card K = 4) {P : AddSubgroup (K × K)}
    (hcard : Nat.card ↥P = 4)
    (h : ∀ P' : AddSubgroup (K × K), P' ≤ P → Nat.card ↥P ≤ 2 * Nat.card ↥P' →
      s16c11_case5_ann P' = s16c11_case5_ann P) :
    ∀ c : K, ∀ p ∈ P, (c * p.1, c * p.2) ∈ P := by
  intro c p hpP
  by_cases hp0 : p = 0
  · rw [hp0]
    have hzero : (c * (0 : K × K).1, c * (0 : K × K).2) = (0 : K × K) := by simp
    rw [hzero]
    exact P.zero_mem
  · have hle : P ≤ s16c11_case5_line p := fun y hyP =>
      s16c11_case5_mem_line_of_det_eq_zero hp0
        (s16c11_case5_det_eq_zero_of_ann_eq hK hcard h p hpP y hyP)
    have hcard_line : Nat.card ↥(s16c11_case5_line p) ≤ Nat.card ↥P := by
      rw [hcard]
      exact Nat.le_of_dvd (by norm_num) (s16c11_case5_card_line_dvd hK p)
    have hEq : P = s16c11_case5_line p := AddSubgroup.eq_of_le_of_card_ge hle hcard_line
    rw [hEq]
    exact (s16c11_case5_mem_line (x := p)).mpr ⟨c, rfl⟩

theorem s16c11_case5_ann_card_ne_eight (hK : Nat.card K = 4) {P : AddSubgroup (K × K)}
    (hcard : Nat.card ↥P = 8)
    (h : ∀ P' : AddSubgroup (K × K), P' ≤ P → Nat.card ↥P ≤ 2 * Nat.card ↥P' →
      s16c11_case5_ann P' = s16c11_case5_ann P) : False := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  letI : CharP K 2 := s16c11_case5_alg_charP hK
  obtain ⟨ω, hω⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_card_eq_four hK
  have hωsq : ω ^ 2 = ω + 1 := by
    have h : ω ^ 2 + (ω + 1) = 0 := by rw [← hω]; ring
    rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
  have hKprod : Nat.card (K × K) = 2 ^ 4 := by rw [Nat.card_prod, hK]; norm_num
  have hQ : Nat.card ((K × K) ⧸ P) = 2 := by
    have hindex : P.index = 2 := by
      have hmul := P.card_mul_index
      rw [hcard, hKprod] at hmul
      norm_num at hmul
      omega
    simpa only [AddSubgroup.index] using hindex
  let ψ : ↥P → ((K × K) ⧸ P) :=
    fun q => (QuotientAddGroup.mk' P) (s16c11_case5_scalar ω (q : K × K))
  have hcardψ : Fintype.card ((K × K) ⧸ P) < Fintype.card ↥P := by
    rw [← Nat.card_eq_fintype_card (α := (K × K) ⧸ P),
      ← Nat.card_eq_fintype_card (α := ↥P), hQ, hcard]
    norm_num
  obtain ⟨q₁, q₂, hq12, hψ⟩ := Fintype.exists_ne_map_eq_of_card_lt ψ hcardψ
  have hψ' : (QuotientAddGroup.mk' P) (s16c11_case5_scalar ω (q₁ : K × K)) =
      (QuotientAddGroup.mk' P) (s16c11_case5_scalar ω (q₂ : K × K)) := hψ
  let q : K × K := (q₁ : K × K) - (q₂ : K × K)
  have hqP : q ∈ P := sub_mem q₁.2 q₂.2
  have hq_ne : q ≠ 0 := by
    intro h0
    exact hq12 (Subtype.ext (sub_eq_zero.mp h0))
  have hTqP : s16c11_case5_scalar ω q ∈ P := by
    have hzero : (QuotientAddGroup.mk' P) (s16c11_case5_scalar ω q) = 0 := by
      have hsq : s16c11_case5_scalar ω q = s16c11_case5_scalar ω (q₁ : K × K) -
          s16c11_case5_scalar ω (q₂ : K × K) := by
        rw [show q = (q₁ : K × K) - (q₂ : K × K) from rfl, map_sub]
      rw [hsq, map_sub, hψ', sub_self]
    exact (QuotientAddGroup.eq_zero_iff (s16c11_case5_scalar ω q)).mp (by simpa using hzero)
  have hline_le : s16c11_case5_line q ≤ P := by
    intro w hw
    rw [s16c11_case5_mem_line] at hw
    obtain ⟨c, rfl⟩ := hw
    have hc : c ∈ ({0, 1, ω, ω ^ 2} : Finset K) := by
      rw [← TauCeti.univ_eq_zero_one_root_sq hK hω]
      exact Finset.mem_univ c
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · have hzero : (0 * q.1, 0 * q.2) = (0 : K × K) := by simp
      rw [hzero]
      exact P.zero_mem
    · simpa using hqP
    · simpa using hTqP
    · have h2 : (ω ^ 2 * q.1, ω ^ 2 * q.2) = s16c11_case5_scalar ω q + q := by
        ext <;> simp only [Prod.fst_add, Prod.snd_add, s16c11_case5_scalar_apply]
        · rw [hωsq, add_mul, one_mul]
        · rw [hωsq, add_mul, one_mul]
      rw [h2]
      exact add_mem hTqP hqP
  have hcard_line : Nat.card ↥(s16c11_case5_line q) = 4 := s16c11_case5_card_line hK hq_ne
  have hann_eq : s16c11_case5_ann (s16c11_case5_line q) = s16c11_case5_ann P :=
    h _ hline_le (by omega)
  have hlt : s16c11_case5_line q < P := by
    refine lt_of_le_of_ne hline_le ?_
    intro heq
    rw [← heq, hcard_line] at hcard
    norm_num at hcard
  obtain ⟨y, hyP, hy_not⟩ := (SetLike.lt_iff_le_and_exists.mp hlt).2
  have hdet : q.1 * y.2 - q.2 * y.1 ≠ 0 := fun hdet0 =>
    hy_not (s16c11_case5_mem_line_of_det_eq_zero hq_ne hdet0)
  have hannP : ∀ w ∈ s16c11_case5_ann P, w = 0 :=
    s16c11_case5_ann_subset_singleton_of_det_ne_zero hdet hqP hyP
  have hxw : (q.2, q.1) ∈ s16c11_case5_ann (s16c11_case5_line q) := by
    intro w hw
    rw [s16c11_case5_mem_line] at hw
    obtain ⟨c, rfl⟩ := hw
    have h2 : (c * q.1) * q.2 + (c * q.2) * q.1 =
        c * (q.1 * q.2) + c * (q.1 * q.2) := by ring
    rw [h2, CharTwo.add_self_eq_zero]
  have hne : (q.2, q.1) ≠ 0 := fun h0 =>
    hq_ne (Prod.ext (congrArg Prod.snd h0) (congrArg Prod.fst h0))
  rw [hann_eq] at hxw
  exact hne (hannP _ hxw)

theorem s16c11_case5_ann_kInv (hK : Nat.card K = 4) {P : AddSubgroup (K × K)} (hP : P ≠ ⊥)
    (h : ∀ P' : AddSubgroup (K × K), P' ≤ P → Nat.card ↥P ≤ 2 * Nat.card ↥P' →
      s16c11_case5_ann P' = s16c11_case5_ann P) :
    ∀ c : K, ∀ p ∈ P, (c * p.1, c * p.2) ∈ P := by
  have hge := s16c11_case5_ann_card_ge hK hP h
  have hKprod : Nat.card (K × K) = 2 ^ 4 := by rw [Nat.card_prod, hK]; norm_num
  have hdvd : Nat.card ↥P ∣ 2 ^ 4 := by
    refine ⟨P.index, ?_⟩
    rw [← hKprod, P.card_mul_index]
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk2 : 2 ≤ k := by
    have h24 : 2 ^ 2 ≤ 2 ^ k := by simpa [hk] using hge
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h24
  interval_cases k
  · exact s16c11_case5_ann_card_four hK (by rw [hk]; norm_num) h
  · exact False.elim (s16c11_case5_ann_card_ne_eight hK (by rw [hk]; norm_num) h)
  · intro c p hp
    have htop : P = ⊤ := AddSubgroup.eq_top_of_card_eq (G := K × K) (H := P) (by rw [hk, hKprod])
    rw [htop]
    exact trivial

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

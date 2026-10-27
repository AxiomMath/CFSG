module

public import CFSG.Quasithin.Background.C2Thirteen
public import CFSG.Quasithin.Background.C1PackC19

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Blocks

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isBlock2_conjByElt_of_normalizer1515c {H B : Subgroup G} (hB : IsBlock2 H B) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : IsBlock2 H (conjByElt g B) := by
  set H' : Subgroup G := H ⊔ Subgroup.zpowers g with hH'
  have hHH' : H ≤ H' := le_sup_left
  have hgH' : g ∈ H' := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hH'N : H' ≤ Subgroup.normalizer (H : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hg)
  have hsubH : IsSubnormal H H' :=
    A3.subnormal_of_normal hHH' ((Subgroup.normal_subgroupOf_iff_le_normalizer hHH').mpr hH'N)
  have hBH : B ≤ H := hB.2.1
  have hsubB : IsSubnormal B H' := A3.subnormal_trans (IsBlock2.isSubnormal hB) hsubH
  have hB' : IsBlock2 H' B :=
    ⟨hB.1, hBH.trans hHH', (isSubnormal_iff_subgroupOf (hBH.trans hHH')).mp hsubB⟩
  have hB'' : IsBlock2 H' (conjByElt g B) := IsBlock2.conjByElt_of_mem hB' hgH'
  have hle : conjByElt g B ≤ H := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ B := mem_conjByElt.mp hx
    have := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mp (hBH hx')
    simpa [mul_assoc] using this
  have hsub : IsSubnormal (conjByElt g B) H' := IsBlock2.isSubnormal hB''
  exact ⟨hB''.1, hle, (isSubnormal_iff_subgroupOf hle).mp (A3.subnormal_of_le_of_le hsub hle hHH')⟩

theorem conjByElt_eq_or_eq_or_eq1515c {H B : Subgroup G} (hH : IsSQTKIn H) (hCT : CharTwo H)
    (hB : IsBlock2 H B) {x : G} (hxB : x ∈ B) (hxo : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hxc : x ∉ centerOf B) {g₁ g₂ g₃ : G} (h₁ : g₁ ∈ Subgroup.normalizer (H : Set G))
    (h₂ : g₂ ∈ Subgroup.normalizer (H : Set G)) (h₃ : g₃ ∈ Subgroup.normalizer (H : Set G)) :
    conjByElt g₁ B = conjByElt g₂ B ∨ conjByElt g₁ B = conjByElt g₃ B ∨
      conjByElt g₂ B = conjByElt g₃ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n12, n13, n23⟩ := hcon
  have hcomm : ∀ {a b : G}, a ∈ Subgroup.normalizer (H : Set G) → b ∈ Subgroup.normalizer (H : Set G) →
      conjByElt a B ≠ conjByElt b B → ⁅conjByElt a B, conjByElt b B⁆ = ⊥ := fun ha hb hne =>
    distinctBlocksCommuteStatement H _ _ hCT (isBlock2_conjByElt_of_normalizer1515c hB ha)
      (isBlock2_conjByElt_of_normalizer1515c hB hb) hne
  have hle : ∀ {a : G}, a ∈ Subgroup.normalizer (H : Set G) → conjByElt a B ≤ H := fun ha =>
    (isBlock2_conjByElt_of_normalizer1515c hB ha).2.1
  have hrank : CFSG.Open.pRank (orderOf x) H ≤ 2 := by
    have : Fact (orderOf x).Prime := ⟨hxo⟩
    have h1 := sqt_iff.mp hH.1 (orderOf x) hxo hx2
    rw [pRank_top_subtype] at h1
    exact h1
  have h3 := C2Eleven.three_le_pRank hxo (hcomm h₁ h₂ n12) (hcomm h₁ h₃ n13) (hcomm h₂ h₃ n23)
    (hle h₁) (hle h₂) (hle h₃) (C2Eleven.conj_mem_conjByElt hxB) (C2Eleven.conj_mem_conjByElt hxB)
    (C2Eleven.conj_mem_conjByElt hxB) (C2Eleven.orderOf_conj_eq g₁ x) (C2Eleven.orderOf_conj_eq g₂ x)
    (C2Eleven.orderOf_conj_eq g₃ x) (C2Eleven.not_mem_centerOf_conjByElt hxc)
    (C2Eleven.not_mem_centerOf_conjByElt hxc) (C2Eleven.not_mem_centerOf_conjByElt hxc)
  omega

omit [Finite G] in
theorem eq_pow_sq_of_odd_orderOf1515c {y : G} (hy : Odd (orderOf y)) : ∃ m : ℕ, y = (y ^ 2) ^ m := by
  obtain ⟨k, hk⟩ := hy
  refine ⟨k + 1, ?_⟩
  rw [← pow_mul]
  have : y ^ (2 * (k + 1)) = y ^ orderOf y * y := by rw [← pow_succ, hk]; congr 1
  rw [this, pow_orderOf_eq_one, one_mul]

theorem mem_normalizer_of_odd1515c {H B : Subgroup G} (hH : IsSQTKIn H) (hCT : CharTwo H)
    (hB : IsBlock2 H B) {x : G} (hxB : x ∈ B) (hxo : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hxc : x ∉ centerOf B) {y : G} (hy : y ∈ Subgroup.normalizer (H : Set G))
    (hyo : Odd (orderOf y)) : y ∈ Subgroup.normalizer (B : Set G) := by
  have h1 : (1 : G) ∈ Subgroup.normalizer (H : Set G) := Subgroup.one_mem _
  have hy2 : y ^ 2 ∈ Subgroup.normalizer (H : Set G) := Subgroup.pow_mem _ hy 2
  have key := conjByElt_eq_or_eq_or_eq1515c hH hCT hB hxB hxo hx2 hxc h1 hy hy2
  rw [C2Eleven.conjByElt_one] at key
  rcases key with h | h | h
  · exact C2Eleven.mem_normalizer_iff_conjByElt.mpr h.symm
  · have hy2B : y ^ 2 ∈ Subgroup.normalizer (B : Set G) :=
      C2Eleven.mem_normalizer_iff_conjByElt.mpr h.symm
    obtain ⟨m, hm⟩ := eq_pow_sq_of_odd_orderOf1515c hyo
    rw [hm]
    exact Subgroup.pow_mem _ hy2B m
  · have hsq : conjByElt (y ^ 2) B = conjByElt y (conjByElt y B) := by
      rw [pow_two, C2Eleven.conjByElt_mul]
    rw [hsq] at h
    have := C2Thirteen.conjByElt_injective y h
    exact C2Eleven.mem_normalizer_iff_conjByElt.mpr this.symm

theorem commutator_mem_pCoreOf_of_odd1515c {X : Subgroup G} (ha : IsAltType X 3) {y : G}
    (hy : y ∈ Subgroup.normalizer (X : Set G)) (hyo : Odd (orderOf y)) {x : G} (hx : x ∈ X) :
    y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 X := by
  classical
  set N : Subgroup ↥X := CFSG.pCore 2 ↥X with hN
  have hNn : N.Normal := CFSG.pCore_normal
  have hNc : N.Characteristic := CFSG.pCore_characteristic
  have hcard : Nat.card (↥X ⧸ N) = 3 := C2Six.natCard_pCore_quotient_of_isAltType_three ha
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (↥X ⧸ N) := isCyclic_of_prime_card hcard
  let σ : MulAut ↥X := X.normalizerMonoidHom ⟨y, hy⟩
  have hσN : Subgroup.map σ.toMonoidHom N = N := Subgroup.characteristic_iff_map_eq.mp hNc σ
  let σ' : MulAut (↥X ⧸ N) := QuotientGroup.congr N N σ hσN
  have hσ'mk : ∀ a : ↥X, σ' (QuotientGroup.mk a) = QuotientGroup.mk (σ a) := fun a =>
    QuotientGroup.congr_mk N N σ hσN a
  have hord : orderOf σ' ∣ 2 := by
    have := orderOf_dvd_natCard σ'
    rwa [IsCyclic.card_mulAut, hcard, Nat.totient_prime Nat.prime_three] at this
  have hpow : ∀ (k : ℕ) (a : ↥X), (σ' ^ k) (QuotientGroup.mk a) = QuotientGroup.mk ((σ ^ k) a) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, hσ'mk, ih]
  have hσn : σ ^ orderOf y = 1 := by
    have h1 : (⟨y, hy⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ orderOf y = 1 := by
      apply Subtype.ext
      simp
    have := congrArg (X.normalizerMonoidHom) h1
    rw [map_pow, map_one] at this
    exact this
  have hσ'n : σ' ^ orderOf y = 1 := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H a => rw [hpow, hσn]; rfl
  have h1 : orderOf σ' ∣ orderOf y := orderOf_dvd_of_pow_eq_one hσ'n
  have hcop : Nat.Coprime 2 (orderOf y) := (Nat.coprime_two_left).mpr hyo
  have h2 : orderOf σ' = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord hcop) h1
  have hσ'1 : σ' = 1 := orderOf_eq_one_iff.mp h2
  have hmk : (QuotientGroup.mk (σ ⟨x, hx⟩) : ↥X ⧸ N) = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [← hσ'mk, hσ'1]
    rfl
  have hdiv : σ ⟨x, hx⟩ / ⟨x, hx⟩ ∈ N := QuotientGroup.eq_iff_div_mem.mp hmk
  have hmem := (C2Six.mem_pCore_two_iff (L := X) (y := σ ⟨x, hx⟩ / ⟨x, hx⟩)).mp hdiv
  have hcoe : (((σ ⟨x, hx⟩ / ⟨x, hx⟩ : ↥X)) : G) = y * x * y⁻¹ * x⁻¹ := by
    have h := X.normalizerMonoidHom_apply_apply_coe ⟨y, hy⟩ ⟨x, hx⟩
    simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show ((σ ⟨x, hx⟩ : ↥X) : G) = y * x * y⁻¹ from h]
  rw [← hcoe]
  exact hmem

end Blocks

end CFSG.Quasithin

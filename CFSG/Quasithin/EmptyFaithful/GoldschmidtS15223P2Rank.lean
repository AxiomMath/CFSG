module

public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem exists_mem_inf_ne_one [Finite G] {I X P : Subgroup G}
    (hrank : CFSG.Open.pRank 3 I ≤ 2) (hXI : X ≤ I) (hPI : P ≤ I)
    (hPN : P ≤ Subgroup.normalizer (X : Set G)) (hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9)
    (h3X : 3 ∣ Nat.card X) : ∃ k ∈ P ⊓ X, k ≠ 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hPX : ∀ k ∈ P, k ∈ X → k = 1 := fun k hkP hkX => hcon k ⟨hkP, hkX⟩
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  set H : Subgroup G := X ⊔ P with hH
  have hPH : P ≤ H := le_sup_right
  have hXH : X ≤ H := le_sup_left
  have hHN : H ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hPN
  have hnorm : (X.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHN
  obtain ⟨S₃, hS₃, hPS⟩ := exists_isSylowIn_ge 3 hPH hP3
  have hR : IsSylowIn 3 (S₃ ⊓ X) X := hS₃.inf_normal hXH hnorm
  set R : Subgroup G := S₃ ⊓ X with hRdef
  have hRcard : Nat.card R = 3 ^ (Nat.card X).factorization 3 := hR.card_eq
  have hfac : 1 ≤ (Nat.card X).factorization 3 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3X
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hgS : g ∈ Subgroup.normalizer (S₃ : Set G) := Subgroup.le_normalizer (hPS hg)
    have h1 := Subgroup.mem_normalizer_iff.mp hgS h
    have h2 := Subgroup.mem_normalizer_iff.mp (hPN hg) h
    simp only [hRdef, Subgroup.mem_inf]
    rw [h1, h2]
  let _ : MulAction P R := MulAction.compHom R (conjAut hPR)
  have hmod := hP3.card_modEq_card_fixedPoints (α := R)
  have h3R : 3 ∣ Nat.card R := by
    rw [hRcard]
    exact dvd_pow_self 3 (by omega)
  have h3F : 3 ∣ Nat.card (MulAction.fixedPoints P R) :=
    (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h3R)))
  have hFpos : 0 < Nat.card (MulAction.fixedPoints P R) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, fun m => map_one (conjAut hPR m)⟩⟩, inferInstance⟩
  have hF3 : 3 ≤ Nat.card (MulAction.fixedPoints P R) := Nat.le_of_dvd hFpos h3F
  obtain ⟨r, hrF, hr1⟩ : ∃ r : R, r ∈ MulAction.fixedPoints P R ∧ r ≠ 1 := by
    by_contra hne
    push Not at hne
    have : Nat.card (MulAction.fixedPoints P R) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      refine ⟨fun a b => Subtype.ext ?_⟩
      rw [hne a a.2, hne b b.2]
    omega
  have hrc : ∀ m ∈ P, (m : G) * (r : G) * (m : G)⁻¹ = (r : G) := by
    intro m hm
    have := MulAction.mem_fixedPoints.mp hrF ⟨m, hm⟩
    exact congrArg Subtype.val this
  have hR3 : IsPGroup 3 R := hR.isPGroup
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hR3 r
  have hj' : orderOf (r : G) = 3 ^ j := by rw [Subgroup.orderOf_coe]; exact hj
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hr1
    have : orderOf r = 1 := by simpa using hj
    exact orderOf_eq_one_iff.mp this
  set r₀ : G := (r : G) ^ 3 ^ (j - 1) with hr₀
  have hord : orderOf r₀ = 3 := by
    rw [hr₀, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
      (by rw [hj']; exact pow_dvd_pow 3 (by omega)), hj']
    have h3 : (3 : ℕ) ^ j = 3 ^ (j - 1) * 3 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h3, Nat.mul_div_cancel_left _ (by positivity)]
  have hr₀X : r₀ ∈ X := (inf_le_right : R ≤ X) (R.pow_mem r.2 _)
  have hcomm : ∀ e ∈ P, Commute e r₀ := by
    intro e he
    have h1 : Commute e (r : G) := by
      have := hrc e he
      exact mul_inv_eq_iff_eq_mul.mp this
    exact h1.pow_right _
  have hr₀P : r₀ ∉ P := by
    intro h
    have := hPX r₀ h hr₀X
    rw [this, orderOf_one] at hord
    omega
  obtain ⟨hE, hEcard⟩ := exists_elemAbelian_sup_zpowers hP hord hcomm hr₀P
  have hEI : P ⊔ Subgroup.zpowers r₀ ≤ I :=
    sup_le hPI ((Subgroup.zpowers_le).mpr (hXI hr₀X))
  have h3 := le_pRank Nat.prime_three hEI hE (k := 3) (by rw [hEcard, hP9]; norm_num)
  omega


end CFSG.Quasithin.S15223

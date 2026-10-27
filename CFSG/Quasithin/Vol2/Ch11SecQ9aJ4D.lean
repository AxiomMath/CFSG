module

public import CFSG.Sporadic.J4.QTOutNorm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.J4U

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem normal_Eg_P0 (hM : MatFacts) : ((Eg uJ 11).subgroupOf P0).Normal :=
  (Subgroup.normal_subgroupOf_iff Eg_le_P0).2 fun h g hh hg =>
    Hj_normalizes_Eg hM g (P0_le_Hj hg) h hh

theorem mem_Eg_of_comm (hM : MatFacts) (hF : J4Facts) {A : Subgroup J} (hAE : A ≤ Eg uJ 11)
    (hA : 128 < Nat.card A) {c : J} (hc : c ∈ P0) (hcA : ∀ y ∈ A, c * y = y * c) :
    c ∈ Eg uJ 11 := by
  by_contra hcE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := normal_Eg_P0 hM
  set N := (Eg uJ 11).subgroupOf P0 with hN
  have hmem : ∀ {g : J} (hg : g ∈ P0), QuotientGroup.mk' N ⟨g, hg⟩ = 1 ↔ g ∈ Eg uJ 11 :=
    fun {g} hg => by rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set x := QuotientGroup.mk' N ⟨c, hc⟩ with hx
  have hx1 : x ≠ 1 := fun h => hcE ((hmem hc).mp h)
  have hP0 : IsPGroup 2 P0 := IsPGroup.of_card (card_P0 hM hF)
  obtain ⟨n, hn⟩ := (hP0.to_quotient N) x
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := by
    rcases j with _ | m
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact absurd hj hx1
    · exact ⟨m, rfl⟩
  have hpow : ∀ k : ℕ, x ^ k = QuotientGroup.mk' N ⟨c ^ k, pow_mem hc k⟩ := fun k => by
    rw [hx, ← map_pow]
    exact congrArg _ (Subtype.ext (by simp))
  have hc'P : c ^ 2 ^ m ∈ P0 := pow_mem hc _
  have hc'E : c ^ 2 ^ m ∉ Eg uJ 11 := by
    intro h
    have h1 := (hmem hc'P).mpr h
    rw [← hpow (2 ^ m)] at h1
    exact pow_ne_one_of_lt_orderOf (by positivity)
      (by rw [hj]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)) h1
  have hc'2 : c ^ 2 ^ m * c ^ 2 ^ m ∈ Eg uJ 11 := by
    have h1 : c ^ 2 ^ m * c ^ 2 ^ m = c ^ 2 ^ (m + 1) := by
      rw [← pow_add, ← two_mul, ← pow_succ']
    rw [h1, ← hmem (pow_mem hc _), ← hpow, ← hj, pow_orderOf_eq_one]
  obtain ⟨t, htL, ht⟩ := table_of_mem hM _ hc'P
  have h1 : compT t t = idT := (ht.mul ht).unique hM (Acts.of_mem_Eg hM hc'2)
  have h2 : t ≠ idT := by
    rintro rfl
    apply hc'E
    refine centralizer_Hj hM hF _ (P0_le_Hj hc'P) fun y hy => ?_
    obtain ⟨d, hd, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
    have h3 := ht.2 d hd
    rw [actT_idT hd] at h3
    calc c ^ 2 ^ m * eta uJ 11 d = (c ^ 2 ^ m * eta uJ 11 d * (c ^ 2 ^ m)⁻¹) * c ^ 2 ^ m := by
          group
      _ = eta uJ 11 d * c ^ 2 ^ m := by rw [h3]
  have hfix := fixCount_le t htL h1 h2
  have hcomm : ∀ y ∈ A, c ^ 2 ^ m * y = y * c ^ 2 ^ m := fun y hy => by
    have h : ∀ n : ℕ, c ^ n * y = y * c ^ n := fun n => by
      induction n with
      | zero => rw [pow_zero, one_mul, mul_one]
      | succ n ih => rw [pow_succ, mul_assoc, hcA y hy, ← mul_assoc, ih, mul_assoc]
    exact h _
  have h4 := card_inf_le hM hcomm ht hfix
  rw [inf_eq_right.mpr hAE] at h4
  omega

theorem center_le_Eg (hM : MatFacts) (hF : J4Facts) {S₁ : Subgroup J} (hS₁ : S₁ ≤ P0)
    (hidx : S₁.relIndex P0 ≤ 8) : (Subgroup.center S₁).map S₁.subtype ≤ Eg uJ 11 := by
  rintro _ ⟨c, hc, rfl⟩
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have hne : S₁.relIndex P0 ≠ 0 := fun h => by
    have h3 := Subgroup.relIndex_mul_card (H := S₁) (K := P0)
    rw [h, zero_mul, card_P0 hM hF] at h3
    norm_num at h3
  have h1 : S₁.relIndex (Eg uJ 11) ≤ 8 :=
    (Subgroup.relIndex_le_of_le_right Eg_le_P0 hne).trans hidx
  have h2 := Subgroup.relIndex_mul_card (H := S₁) (K := Eg uJ 11)
  rw [card_Eg_uJ hM] at h2
  have hE1 : 128 < Nat.card ↥(Eg uJ 11 ⊓ S₁) := by
    rw [inf_comm]
    by_contra h
    push Not at h
    have h3 : S₁.relIndex (Eg uJ 11) * Nat.card ↥(S₁ ⊓ Eg uJ 11) ≤ 8 * 128 :=
      Nat.mul_le_mul h1 h
    rw [h2] at h3
    norm_num at h3
  refine mem_Eg_of_comm hM hF inf_le_left hE1 (hS₁ c.2) fun y hy => ?_
  have := Subgroup.mem_center_iff.mp hc ⟨y, (Subgroup.mem_inf.mp hy).2⟩
  exact (congrArg Subtype.val this).symm

noncomputable abbrev z0 : J := eta uJ 11 1131

theorem eq_z0_of_central (hM : MatFacts) (hF : J4Facts) {y : J} (hy : y ∈ P0)
    (hc : ∀ x ∈ P0, x * y = y * x) : y = 1 ∨ y = z0 := by
  have h1 : y ∈ Zc 1 := by
    refine ⟨hy, fun x hx => ?_⟩
    show y * x * y⁻¹ * x⁻¹ ∈ ({1} : Set J)
    rw [Set.mem_singleton_iff, ← hc x hx]
    group
  rw [Zc_eq hM hF 1 (by norm_num)] at h1
  obtain ⟨c, hc', rfl⟩ := h1
  have hl : ucsMasks.getD 1 [] = [0, 1131] := rfl
  rw [hl, List.mem_cons, List.mem_singleton] at hc'
  rcases hc' with rfl | rfl
  · exact Or.inl (eta_zero uJ 11)
  · exact Or.inr rfl

theorem z0_central (hM : MatFacts) (hF : J4Facts) : z0 ∈ P0 ∧ ∀ x ∈ P0, x * z0 = z0 * x := by
  have h1 : z0 ∈ Zc 1 := by
    rw [Zc_eq hM hF 1 (by norm_num)]
    exact ⟨1131, by decide, rfl⟩
  refine ⟨h1.1, fun x hx => ?_⟩
  have h2 : z0 * x * z0⁻¹ * x⁻¹ = 1 := h1.2 x hx
  calc x * z0 = (z0 * x * z0⁻¹ * x⁻¹)⁻¹ * z0 * x := by group
    _ = z0 * x := by rw [h2, inv_one, one_mul]

theorem z0_ne_one (hM : MatFacts) : z0 ≠ 1 := eta_ne_one hM (by norm_num) (by norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecS.J4U

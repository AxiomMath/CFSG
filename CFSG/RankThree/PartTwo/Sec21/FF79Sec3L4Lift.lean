module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

section Abstract

variable {H : Type*} [Group H] [Finite H]

theorem fix_lift (Q : Subgroup H) [Q.Normal] (hQ : Nat.Coprime 3 (Nat.card Q)) (σ : MulAut H)
    (h3 : ∀ x, σ (σ (σ x)) = x) (hσQ : ∀ q ∈ Q, σ q ∈ Q) (c₀ : H)
    (h : (σ c₀)⁻¹ * c₀ ∈ Q) : ∃ q ∈ Q, σ (c₀ * q) = c₀ * q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X : Type _ := {x : H // c₀⁻¹ * x ∈ Q}
  have hmem : ∀ x : X, c₀⁻¹ * σ x.1 ∈ Q := by
    intro x
    have h1 : c₀⁻¹ * σ x.1 = (c₀⁻¹ * σ c₀) * σ (c₀⁻¹ * x.1) := by
      simp [map_mul, mul_assoc]
    rw [h1]
    refine Q.mul_mem ?_ (hσQ _ x.2)
    have := Q.inv_mem h
    simpa [mul_assoc] using this
  let f : X → X := fun x => ⟨σ x.1, hmem x⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (σ.injective (congrArg Subtype.val hxy))
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  let π : Equiv.Perm X := Equiv.ofBijective f hfbij
  have hπ3 : π ^ 3 = 1 := by
    ext x
    show (π (π (π x))).1 = x.1
    exact h3 x.1
  have hXcard : Nat.card X = Nat.card Q := by
    refine Nat.card_congr
      { toFun := fun x => ⟨c₀⁻¹ * x.1, x.2⟩
        invFun := fun q => ⟨c₀ * q.1, by simpa using q.2⟩
        left_inv := fun x => by ext; simp
        right_inv := fun q => by ext; simp }
  haveI : Fintype X := Fintype.ofFinite X
  have hndvd : ¬ 3 ∣ Fintype.card X := by
    rw [← Nat.card_eq_fintype_card, hXcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hQ
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hndvd
    (by simpa using hπ3)
  refine ⟨c₀⁻¹ * x.1, x.2, ?_⟩
  have : σ x.1 = x.1 := congrArg Subtype.val hx
  simpa using this

end Abstract

section Lift

variable {G : Type} [Group G] [Finite G]

theorem conjAut_pow3 {N : Subgroup G} {b : G} (hb : b ∈ Nor N) (hb3 : b ^ 3 = 1) (x : ↥N) :
    conjAut N b hb (conjAut N b hb (conjAut N b hb x)) = x := by
  apply Subtype.ext
  show b * (b * (b * (x : G) * b⁻¹) * b⁻¹) * b⁻¹ = x
  have : b * (b * (b * (x : G) * b⁻¹) * b⁻¹) * b⁻¹ = b ^ 3 * x * (b ^ 3)⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  rw [this, hb3]; simp

theorem mk_conjAut_eq {U : Subgroup G} {b : G} (hb : b ∈ Nor U) (x : ↥(CenS U)) :
    cqβ U b hb (QuotientGroup.mk x : CQ U) =
      (QuotientGroup.mk (conjAut (CenS U) b (nor_cenS_of_nor hb) x) : CQ U) := by
  unfold cqβ
  rfl

theorem cq_lift_fixed {U : Subgroup G} {b : G} (hb : b ∈ Nor U) (hb3 : b ^ 3 = 1) {y : CQ U}
    (hy : cqβ U b hb y = y) :
    ∃ c : ↥(CenS U), (c : G) ∈ Cen b ∧ (QuotientGroup.mk c : CQ U) = y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (pPrimeCore 3 ↥(CenS U)).Normal := pPrimeCore_normal
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective y
  set σ := conjAut (CenS U) b (nor_cenS_of_nor hb) with hσ
  rw [mk_conjAut_eq] at hy
  have h1 : (σ c₀)⁻¹ * c₀ ∈ pPrimeCore 3 ↥(CenS U) := QuotientGroup.eq.mp hy
  have hσQ : ∀ q ∈ pPrimeCore 3 ↥(CenS U), σ q ∈ pPrimeCore 3 ↥(CenS U) := by
    intro q hq
    have := Subgroup.mem_map_of_mem σ.toMonoidHom hq
    rwa [pPrimeCore_map_iso 3 σ] at this
  obtain ⟨q, hq, hfix⟩ := fix_lift (pPrimeCore 3 ↥(CenS U)) pPrimeCore_coprime_card σ
    (conjAut_pow3 (nor_cenS_of_nor hb) hb3) hσQ c₀ h1
  refine ⟨c₀ * q, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := congrArg Subtype.val hfix
    change h * ((c₀ : G) * q) * h⁻¹ = (c₀ : G) * q at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · exact (QuotientGroup.eq.mpr (by simpa using hq)).symm

end Lift

end CFSG.RankThree.PartTwo.Sec21.FF79

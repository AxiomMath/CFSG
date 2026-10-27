module

public import CFSG.RankThree.GF2n.Stroth80.QuadIso
public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isA2_iff {Q Z : Subgroup G} {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (R : Tim79.GammaReg Q Z γ) (hcard : Nat.card K = Nat.card Z)
    (hK : 1 < Nat.card K) {a : G} (T : M₀.E ≃ₗ[K] M₀.E)
    (ha : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q) (ha' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q)
    (hT : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x)) :
    IsA2 Q Z a ↔ a ∉ Q ∧ a ^ 2 ∈ Q ∧
      Module.finrank K (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) = 2 ∧
      ∀ v ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf v = 0 := by
  have hnorm : a ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨ha h, fun hh => ?_⟩
    have := ha' _ hh
    rwa [show a⁻¹ * (a * h * a⁻¹) * a = h by group] at this
  have hSQ : ⁅Q, Subgroup.zpowers a⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro x hx z hz
    have hzn : z ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.zpowers_le.mpr hnorm) hz
    have h1 : z * x⁻¹ * z⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hzn _).mp (Q.inv_mem hx)
    rw [show ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) by rw [commutatorElement_def]; group]
    exact Q.mul_mem hx h1
  have himg : ∀ v, v ∈ M₀.img ⁅Q, Subgroup.zpowers a⁆ ↔
      v ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) :=
    fun v => Tim79.QuadModel.mem_img_commutator_zpowers T ha ha' hT
  have himg2 : ∀ v, v ∈ M₀.img (⁅Q, Subgroup.zpowers a⁆ ⊔ Z) ↔
      v ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro v
    rw [← himg v]
    constructor
    · rintro ⟨x, hx, hxQ, rfl⟩
      have hle : ⁅Q, Subgroup.zpowers a⁆ ⊔ Z ≤
          M₀.lift (M₀.img ⁅Q, Subgroup.zpowers a⁆) := by
        refine sup_le (fun y hy => ⟨hSQ hy, M₀.pi_mem_img hy (hSQ hy)⟩) (fun z hz => ?_)
        refine ⟨R.V_le hz, ?_⟩
        rw [(M₀.π_ker z (R.V_le hz)).mpr hz]
        exact AddSubgroup.zero_mem _
      exact (hle hx).2
    · exact fun h => M₀.img_mono le_sup_left h
  have hcardS : Nat.card ↥(⁅Q, Subgroup.zpowers a⁆ ⊔ Z) =
      Nat.card Z * Nat.card (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) := by
    rw [M₀.card_eq (sup_le hSQ R.V_le) le_sup_right]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => himg2 v)
  have hcardR : Nat.card (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) =
      Nat.card K ^ Module.finrank K (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) :=
    Module.natCard_eq_pow_finrank
  have hel : Assembly.IsElemAbelian 2 ⁅Q, Subgroup.zpowers a⁆ ↔
      ∀ v ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf v = 0 := by
    rw [M₀.isElemAbelian_iff R hSQ]
    exact ⟨fun h v hv => h v ((himg v).mpr hv), fun h v hv => h v ((himg v).mp hv)⟩
  have hcard3 : Nat.card ↥(⁅Q, Subgroup.zpowers a⁆ ⊔ Z) = Nat.card Z ^ 3 ↔
      Module.finrank K (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) = 2 := by
    rw [hcardS, hcardR, ← hcard]
    constructor
    · intro h
      have h2 : Nat.card K ^ (1 + Module.finrank K (LinearMap.range
          ((T : M₀.E →ₗ[K] M₀.E) - 1))) = Nat.card K ^ 3 := by rw [pow_add, pow_one]; exact h
      have := Nat.pow_right_injective hK h2
      omega
    · intro h
      rw [h]
      ring
  constructor
  · rintro ⟨-, h1, h2, h3, h4⟩
    exact ⟨h1, h2, hcard3.mp h3, hel.mp h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨hnorm, h1, h2, hcard3.mpr h3, hel.mpr h4⟩

end CFSG.RankThree.GF2n.Stroth80

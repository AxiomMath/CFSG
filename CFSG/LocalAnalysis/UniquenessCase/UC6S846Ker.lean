module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.GroupTheory.PCore.InfPCoreOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem rhoL_eq_one_of_mem_pCoreOf {X H : Subgroup G} (hXH : X ≤ H) {q : G}
    (hqN : q ∈ normalizer (X : Set G)) (hq : q ∈ pCoreOf 2 H) : rhoL X ⟨q, hqN⟩ = 1 := by
  apply MulEquiv.ext
  intro zbar
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) zbar
  rw [MulAut.one_apply]
  have hzN : (z : G) ∈ normalizer (pCoreOf 2 H : Set G) :=
    (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)) (hXH z.2)
  have hconj : (z : G) * q⁻¹ * (z : G)⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp hzN q⁻¹).mp ((pCoreOf 2 H).inv_mem hq)
  have hcommH : q * (z : G) * q⁻¹ * (z : G)⁻¹ ∈ pCoreOf 2 H := by
    simpa only [mul_assoc] using (pCoreOf 2 H).mul_mem hq hconj
  have hcommX : q * (z : G) * q⁻¹ * (z : G)⁻¹ ∈ X :=
    X.mul_mem ((Subgroup.mem_normalizer_iff.mp hqN z).mp z.2) (X.inv_mem z.2)
  exact (rhoL_fix_iff X ⟨q, hqN⟩ z).2
    (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hXH ⟨hcommX, hcommH⟩)

theorem mem_pCoreOf_sup_of_rhoL_eq_one {X T : Subgroup G} (hT : IsPGroup 2 T)
    (hTX : T ≤ normalizer (X : Set G))
    (hkerX : ∀ y ∈ X, ∀ hy : y ∈ normalizer (X : Set G), rhoL X ⟨y, hy⟩ = 1 →
      y ∈ pCoreOf 2 X)
    {x : G} (hxH : x ∈ X ⊔ T) (hxN : x ∈ normalizer (X : Set G))
    (hx : rhoL X ⟨x, hxN⟩ = 1) : x ∈ pCoreOf 2 (X ⊔ T) := by
  have hHN : X ⊔ T ≤ normalizer (X : Set G) := sup_le Subgroup.le_normalizer hTX
  let φ : ↥(X ⊔ T) →* MulAut (Bar2 X) := (rhoL X).comp (Subgroup.inclusion hHN)
  have hC2 : IsPGroup 2 φ.ker := by
    intro z
    obtain ⟨k, hk⟩ := CFSG.Quasithin.B6.isTwoQuotient_of_sup_eq (C := X) (D := X ⊔ T) hT hHN
      (sup_comm T X) (z.1 : G) z.1.2
    have hρ : rhoL X ⟨((z.1 : ↥(X ⊔ T)) : G) ^ 2 ^ k, Subgroup.le_normalizer hk⟩ = 1 := by
      have h1 : φ (z.1 ^ 2 ^ k) = 1 := by rw [map_pow, MonoidHom.mem_ker.mp z.2, one_pow]
      have heq : (⟨((z.1 : ↥(X ⊔ T)) : G) ^ 2 ^ k, Subgroup.le_normalizer hk⟩ :
          ↥(normalizer (X : Set G))) = Subgroup.inclusion hHN (z.1 ^ 2 ^ k) :=
        Subtype.ext (by simp)
      rw [heq]
      exact h1
    obtain ⟨j, hj⟩ := isPGroup_pCoreOf X ⟨_, hkerX _ hk _ hρ⟩
    refine ⟨k + j, ?_⟩
    have h3 : (((z.1 : ↥(X ⊔ T)) : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by
      simpa using congrArg (fun t : ↥(pCoreOf 2 X) => (t : G)) hj
    rw [← pow_mul, ← pow_add] at h3
    apply Subtype.ext
    apply Subtype.ext
    exact h3
  have hCle : φ.ker ≤ CFSG.pCore 2 ↥(X ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance hC2
  have hφ : φ ⟨x, hxH⟩ = 1 := hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hCle (MonoidHom.mem_ker.mpr hφ), rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6S846

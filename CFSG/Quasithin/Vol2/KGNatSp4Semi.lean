module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4Basic
public import CFSG.Quasithin.Vol2.KGNatSp4Sim

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K]

theorem spB_map (σ : K →+* K) (x y : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) (σ ∘ x) (σ ∘ y) = σ (Matrix.toBilin' (spJ K) x y) := by
  rw [toBilin'_spJ_apply, toBilin'_spJ_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_sub, map_mul]

theorem map_mem_statedSp (τ : K →+* K) {g : GL (Fin 2 ⊕ Fin 2) K} (hg : g ∈ StatedSp 2 K) :
    Matrix.GeneralLinearGroup.map τ g ∈ StatedSp 2 K :=
  CFSG.Open.StatedAPI.map_mem_statedSp τ hg

theorem orth_of_semilinear_normalizing [Finite K] {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    {σ : K →+* K} (hT : ∀ (c : K) (x : Fin 2 ⊕ Fin 2 → K), T (c • x) = σ c • T x)
    (hL : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ T x) :
    ∀ x y, Matrix.toBilin' (spJ K) x y = 0 → Matrix.toBilin' (spJ K) (T x) (T y) = 0 := by
  have hσbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  set e := RingEquiv.ofBijective σ hσbij with he
  set τ : K →+* K := e.symm.toRingHom with hτ
  have hστ : ∀ c, σ (τ c) = c := fun c => e.apply_symm_apply c
  have hτσ : ∀ c, τ (σ c) = c := fun c => e.symm_apply_apply c
  let L : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := fun x => T (τ ∘ x)
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        funext i
        simp [map_add]
      map_smul' := fun c x => by
        have h1 : τ ∘ (c • x) = τ c • (τ ∘ x) := by
          funext i
          simp [map_mul]
        change T (τ ∘ (c • x)) = c • T (τ ∘ x)
        rw [h1, hT, hστ] }
  have hLx : ∀ x, L x = T (τ ∘ x) := fun x => rfl
  have hLN : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      L (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) =
        ((γ' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ L x := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hL ⟨_, map_mem_statedSp τ γ.2⟩
    refine ⟨γ', fun x => ?_⟩
    rw [hLx, hLx]
    have h1 : τ ∘ (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) =
        mat 2 K ⟨_, map_mem_statedSp τ γ.2⟩ *ᵥ (τ ∘ x) := by
      funext i
      exact RingHom.map_mulVec τ _ x i
    rw [h1, hγ']
    rfl
  obtain ⟨c, hc⟩ := exists_similitude L hLN
  have hTL : ∀ v, T v = L (σ ∘ v) := fun v => by
    rw [hLx]
    congr 1
    funext i
    simp [hτσ]
  intro x y hxy
  rw [hTL x, hTL y, hc, spB_map, hxy, map_zero, mul_zero]

end CFSG.Quasithin.Vol2.KGNat

module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUHolds
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSUFrame
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open AutPSU InnerDiagSU

namespace UnitModel

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K) {n : ℕ}
  {G : Type*} [Group G] {ψ : SU (unitaryInvolution K 2 f) n →* G}

@[expose] noncomputable def autOfU (hn : 4 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    Subgroup.normalizer (ψ.range : Set G) →* MulAut (PJ h n) :=
  (MulAut.congr (projEquivU h hn hker hC)).symm.toMonoidHom.comp ψ.range.normalizerMonoidHom

variable (hn : 4 ≤ n) (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
  (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)

include hn hker hC in
theorem autOfU_injective : Function.Injective (autOfU h hn hker hC) := by
  have hφ : Function.Injective ψ.range.normalizerMonoidHom := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hC, Subgroup.bot_subgroupOf]
  exact (MulAut.congr (projEquivU h hn hker hC)).symm.injective.comp hφ

theorem isJUnitary_of_mem {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    IsJUnitary (unitaryInvolution K 2 f) A := by
  have h1 := mem_primeFormUnitary.mp hA
  rw [coe_gramJ] at h1
  have hσ : (⇑(unitaryInvolution K 2 f) : K → K) = ⇑h.bar :=
    funext fun c => by rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]
  unfold IsJUnitary conjTr
  rw [hσ]
  exact h1

include hn hker hC in
theorem mem_suInducedPairs_of_autOfU_eq {g : G} (hg : g ∈ Subgroup.normalizer (ψ.range : Set G))
    (A : primeFormUnitary h ((gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hα : autOfU h hn hker hC ⟨g, hg⟩ = primeFormConjHom h _ A) :
    (g, (A : GL (Fin n) K)) ∈ UFusion.suInducedPairs ψ := by
  have hA := isJUnitary_of_mem h A.2
  refine ⟨hA, fun u => ?_⟩
  have h1 : autOfU h hn hker hC ⟨g, hg⟩ (projU h u) =
      projU h (conjSU (A : GL (Fin n) K) hA u) := by
    rw [hα]
    change primeFormConjAut h _ A ((suEquiv h u : XJ h n) : PJ h n) = _
    rw [primeFormConjAut_mk]
    rfl
  have h2 : (projEquivU h hn hker hC (autOfU h hn hker hC ⟨g, hg⟩ (projU h u)) : G) =
      g * ψ u * g⁻¹ := by
    change ((projEquivU h hn hker hC ((projEquivU h hn hker hC).symm
      (ψ.range.normalizerMonoidHom ⟨g, hg⟩ (projEquivU h hn hker hC (projU h u))))) : G) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [← h2, h1]
  rfl

include h hn hker hC in
theorem exists_mem_suInducedPairs_of_pow_eq_one {p : ℕ} (hσ : ∀ φ : K ≃+* K, φ ^ p = 1 → φ = 1)
    {y : G} (hy : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hyp : y ^ p = 1) :
    ∃ A : GL (Fin n) K, (y, A) ∈ UFusion.suInducedPairs ψ := by
  have hαp : autOfU h hn hker hC ⟨y, hy⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hy⟩ : Subgroup.normalizer (ψ.range : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hyp)
    rw [h1, map_one]
  have hφ : primeFormFieldFactor h isPrimeFormGram_gramJ (by omega) (not_three_of_four hn)
      (autOfU h hn hker hC ⟨y, hy⟩) = 1 :=
    hσ _ (by rw [← map_pow, hαp, map_one])
  have hmem : autOfU h hn hker hC ⟨y, hy⟩ ∈
      primeFormD h ((gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← ker_primeFormFieldFactor h isPrimeFormGram_gramJ (by omega) (not_three_of_four hn)]
    exact hφ
  obtain ⟨A, hA⟩ := hmem
  exact ⟨A, mem_suInducedPairs_of_autOfU_eq h hn hker hC hy A hA.symm⟩

end UnitModel

end CFSG.StandardType

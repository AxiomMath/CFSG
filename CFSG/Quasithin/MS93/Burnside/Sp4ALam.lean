module

public import CFSG.Quasithin.MS93.S33LamM
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSp4A_lam_commutator_le_of_commSp_le (h : PUHyp M T L) {F : Type} [Field F]
    {A : Subgroup G} (hAM : A ≤ M) {α : ↥A →* ↥(StatedSp 2 F)}
    {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → MSP.V4 F)} (hβ : Function.Surjective β)
    (hβker : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L))
    (hAβ : ∀ a : ↥A, IsCoordAct β a (MSP.mat (α a)).mulVec)
    {E E' : Subgroup G} (hEA : E ≤ A) (hE'A : E' ≤ A)
    (hD : Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅Uq M T L, E'⁆)
    (hle : MSP.commSp ((E.subgroupOf A).map α) ≤ MSP.commSp ((E'.subgroupOf A).map α)) :
    ⁅Uq M T L, E⁆ ≤ ⁅Uq M T L, E'⁆ := by
  intro x hx
  have hxU : x ∈ Uq M T L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hEA.trans hAM).trans (le_normalizer_Uq h.le_normalizer)) hx
  obtain ⟨u, hu, huv⟩ := (S33.mem_commSp_iff_crd h hAM hβ hβker hAβ hE'A _).1
    (hle ((S33.mem_commSp_iff_crd h hAM hβ hβker hAβ hEA _).2 ⟨⟨x, hxU⟩, hx, rfl⟩))
  have hβeq : β ⟨x, hxU⟩ = β u := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [Subsingleton.elim i 0]
    exact huv.symm
  have hker : (⟨x, hxU⟩ : ↥(Uq M T L)) * u⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβeq, mul_inv_cancel]
  rw [hβker, Subgroup.mem_subgroupOf, h.Uq_inf_Zq] at hker
  have hmem := mul_mem (hD hker) hu
  simpa using hmem

end CFSG.Quasithin.MS93.S4L

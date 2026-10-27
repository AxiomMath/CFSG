module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresAssembly

public section

namespace CFSG.StandardType.A6Red.CoreShape

open Matrix CFSG.StandardType.LayerCores

theorem exists_core_of_factors_lie {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
    [∀ i, NeZero (d i)] {τ : PiMat D d → PiMat D d} {π : Fin r → Fin r}
    (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (hfix : ∀ b (hb : π b = b), HasCoreLie (matUnitary (isInvol_tauFix hτ hπ hb)))
    (hpair : ∀ b, π b ≠ b → HasCoreLie (⊤ : Subgroup (GL (Fin (d b)) (D b)))) :
    ∃ (β : Type) (S : β → Subgroup (PiMat D d)ˣ), IsCoreFamily (unitaryOf hτ) S ∧
      ∀ c, GGA6CharTwoLie ↥(S c) := by
  have hasCoreLie_factorGroup : ∀ b, HasCoreLie (factorGroup π hτ hπ b) := by
    intro b
    unfold factorGroup
    split_ifs with hb
    · exact hfix b hb
    · exact hpair b hb
  choose Sf hSle hSn hder hq using hasCoreLie_factorGroup
  refine ⟨{b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}, fun c => coreOf π hτ Sf c.1, ?_, ?_⟩
  · refine ⟨fun c => coreOf_le hτ Sf c.1, fun c u hu s hs => conj_mem_coreOf hτ hπ hSn hu hs,
      fun c => ?_, exists_ggDer_le_iSup_coreOf hτ hπ hSle hder,
      fun z hz hzc hz2 => eq_one_of_mem_iSup_coreOf hτ hπ hSle
        (fun b hb => ((hq b).resolve_left hb).2.1) hz hzc hz2⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MulEquiv.ofBijective _ (bijective_coreOf hτ hπ hSle c.1)).symm
      ((hq c.1).resolve_left c.2.2).1
  · intro c
    exact GGA6CharTwoLie.of_mulEquiv
      (MulEquiv.ofBijective _ (bijective_coreOf hτ hπ hSle c.1)).symm
      ((hq c.1).resolve_left c.2.2).2.2

end CFSG.StandardType.A6Red.CoreShape

end

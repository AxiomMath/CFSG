module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSetting
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.RankThree.PartOne (InClassG omegaOne)
open CFSG.QuasithinUnique.Setup.Campbell (Ecore IsSeed)
open Matrix (SpecialLinearGroup)

@[expose] def K339SeedBridge : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPGroup 2 S →
    Subgroup.centralizer (elemThompsonCenterTorsion S 2 : Set S) = ⊤ →
    ∀ (H : Type) [Group H] [Finite H] (ι : S →* H), InClassG S H ι →
      ⁅(⊤ : Subgroup H), (omegaOne 2 (Subgroup.center S)).map ι⁆ ≠ ⊥ →
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (P : Sylow 2 H)
        (ρ : H →* SpecialLinearGroup (Fin 2) k) (ψ : Ecore H →* Multiplicative (Fin 2 → k)),
        (P : Subgroup H) = ι.range ∧ IsSeed P ρ (Ecore H) ψ

theorem inClassG_exists_sylow {S H : Type} [Group S] [Group H] [Finite H] {ι : S →* H}
    (hG : InClassG S H ι) : ∃ T : Sylow 2 H, (T : Subgroup H) = ι.range := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ι.range := hG.sylow.2.1
  have hidx : ¬ 2 ∣ ι.range.index := by
    have := hG.sylow.2.2
    rwa [Subgroup.relIndex_top_right] at this
  exact ⟨hp.toSylow hidx, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

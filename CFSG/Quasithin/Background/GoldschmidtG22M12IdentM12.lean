module

public import CFSG.Quasithin.Background.F6CatRecogSetting
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog

public section

namespace CFSG.Quasithin.F6

open CFSG.Blueprint

theorem center_twoResidual_eq_bot_of_m12 {D : Type} [Group D] [Finite D]
    (hS : F618RecogSetting D) (e : TwoResidualQuot D ≃* ↥NativeSporadic.M12) :
    Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥ := by
  have : Group.IsPerfect ↥(twoResidual (⊤ : Subgroup D)) := hS.quasisimple.1
  let π : ↥(twoResidual (⊤ : Subgroup D)) →* ↥NativeSporadic.M12 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(twoResidual (⊤ : Subgroup D))))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker]
    obtain ⟨k, hk⟩ := hS.center.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  rw [← hker]
  exact SectionRank.M12_perfect_odd_cover_trivial π hπ hker.le hodd

theorem isM12_of_setting {D : Type} [Group D] [Finite D] (hS : F618RecogSetting D)
    (hL : twoResidual (⊤ : Subgroup D) = ⊤) (e : TwoResidualQuot D ≃* ↥NativeSporadic.M12) :
    IsM12 D :=
  ⟨(mulEquivTwoResidualQuot hL (center_twoResidual_eq_bot_of_m12 hS e)).trans e⟩

end CFSG.Quasithin.F6

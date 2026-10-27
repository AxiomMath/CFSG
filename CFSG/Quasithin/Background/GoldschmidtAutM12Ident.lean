module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.Quasithin.Background.F6CatRecogOut

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly.LowTwoRank

namespace AutM12Recog

variable {D : Type} [Group D] [Finite D]

noncomputable def mulEquivQuotKer (hS : F618RecogSetting D)
    (hZ : Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥) :
    D ≃* D ⧸ (conjQuotHom D).ker :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (by rw [ker_conjQuotHom hS, hZ, Subgroup.map_bot]))

theorem isAutM12_of_setting
    (hS : F618RecogSetting D)
    (e : TwoResidualQuot D ≃* ↥CFSG.Blueprint.NativeSporadic.M12)
    (hidx : (twoResidual (⊤ : Subgroup D)).index = 2) : IsAutM12 D := by
  have := twoResidual_top_normal (D := D)
  have hperf : Group.IsPerfect ↥(twoResidual (⊤ : Subgroup D)) := hS.quasisimple.1
  let π : ↥(twoResidual (⊤ : Subgroup D)) →* ↥CFSG.Blueprint.NativeSporadic.M12 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(twoResidual (⊤ : Subgroup D))))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) := by
    ext x
    simp [π]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker]
    obtain ⟨k, hk⟩ := hS.center.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have hZ : Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥ := by
    rw [← hker]
    exact CFSG.SectionRank.M12_perfect_odd_cover_trivial π hπ (by rw [hker]) hodd
  have hc : Nat.card (MulAut (TwoResidualQuot D)) =
      Nat.card (TwoResidualQuot D) * (twoResidual (⊤ : Subgroup D)).index := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv, hidx,
      CFSG.ComponentClassification.M12Cover.card_mulAut, CFSG.Sporadic.Mathieu.card_M12]
  obtain ⟨ψ⟩ := nonempty_quotient_mulEquiv_mulAut hS hc
  exact ⟨(mulEquivQuotKer hS hZ).trans (ψ.trans (MulAut.congr e))⟩

end AutM12Recog

end CFSG.Quasithin.F6

module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.OddL2Big
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.OddL3U3

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
  CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

theorem quotientCenterEquiv_of_simple {X : Type} [Group X] [hs : IsSimpleGroup X]
    (hperf : commutator X = ⊤) : Nonempty ((X ⧸ Subgroup.center X) ≃* X) := by
  have hc : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      have hcomm : commutator X = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        exact Subgroup.mem_centralizer_iff.2 fun g _ => by
          have := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top x) g
          exact this
      rw [hcomm] at hperf
      exact (hs.toNontrivial.exists_pair_ne.elim fun a ha => ha.elim fun b hb =>
        hb (by
          have h1 : a ∈ (⊥ : Subgroup X) := hperf ▸ Subgroup.mem_top a
          have h2 : b ∈ (⊥ : Subgroup X) := hperf ▸ Subgroup.mem_top b
          rw [Subgroup.mem_bot] at h1 h2
          rw [h1, h2]))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot⟩

theorem oneCompFor_famOddL3 : OneCompFor FamOddL3 := by
  intro V _ _ _ Γ A L m hs ⟨hsimp, p, hp, hp2, hX⟩
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have := hsimp
  obtain ⟨e⟩ := quotientCenterEquiv_of_simple (X := ↥L) hs.L_comp.2.2.1
  exact false_of_oddL3 hp2 (g93Hyp_of_oneCompSetting hs)
    (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hX)

theorem oneCompFor_famOddU3Big : OneCompFor FamOddU3Big := by
  intro V _ _ _ Γ A L m hs ⟨hsimp, p, hp, h5, hX⟩
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have := hsimp
  obtain ⟨e⟩ := quotientCenterEquiv_of_simple (X := ↥L) hs.L_comp.2.2.1
  have h3 := oddU3_reduce (p := p) (by omega) (g93Hyp_of_oneCompSetting hs)
    (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hX)
  omega

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

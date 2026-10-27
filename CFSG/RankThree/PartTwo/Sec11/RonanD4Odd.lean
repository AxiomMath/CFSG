module

public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddStd
public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddThree

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

section Support


theorem ronanD4Odd_of (hNF : GH74.GLS.Stage2.Bender.Thm1.D4CocycleNF)
    (hStd : D4OuterStdNoType424) (h3 : NoOuterType424D4Three) : NoOuterType424D4Odd := by
  intro Z _ _ hZ α J hα3 hαout hJ hJT
  obtain ⟨X, _, ⟨q, hqv, hp2, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  by_cases hp3 : q.p = 3
  · exact h3 Z ⟨X, inferInstance, ⟨q, hqv, hp3, ⟨f⟩⟩, ⟨e⟩⟩ α J hα3 hαout hJ hJT
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Item1118Res3Proof.exists_d4_model_pow f e
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set β := MulAut.congr E α with hβ
    have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
    have hβout : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
      fun h => hαout ((KFacts.isInnerAut_congr E α).mp h)
    have hβ1 : β ≠ 1 := fun h => hβout ⟨1, by rw [h, map_one]⟩
    have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
    have hHas : KS11Lie2Proof.HasType424 (Item426.fixSub α) :=
      KS11Lie2Proof.hasType424_of_mem hJ hJT
    have hfixα : Item426.fixSub α = Sec4.autFix α := by
      ext x
      rfl
    have hHasβ : KS11Lie2Proof.HasType424 (Sec4.autFix β) := by
      rw [hfixα] at hHas
      exact hHas.of_mulEquiv (Sec4.autFixCongrEquiv E α).symm
    have hfixinv : ∀ ρ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        Sec4.autFix ρ⁻¹ = Sec4.autFix ρ := by
      intro ρ
      ext x
      rw [Sec4.mem_autFix, Sec4.mem_autFix]
      constructor
      · intro h
        have := congrArg ρ h
        rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
        exact this.symm
      · intro h
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
        exact h.symm
    have hcongr : ∀ (γ ρ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        γ * ρ * γ⁻¹ = MulAut.congr γ ρ := by
      intro γ ρ
      ext x
      rfl
    obtain ⟨g, hg, hβg⟩ := GH74.GLS.Stage2.Bender.Thm1.d4_outer_three_normal_form q.prime_p hp2
      q.exponent_pos K hK σ hσ β hβord hβout
    obtain ⟨y, s', hs'σ, hs'3, hys⟩ :=
      hNF q.p q.exponent q.prime_p hp2 hp3 q.exponent_pos K hK σ hσ g hg
    have hHasg : KS11Lie2Proof.HasType424
        (Sec4.autFix (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ)) := by
      rcases hβg with h | h
      · rw [← h]
        exact hHasβ
      · rw [← h, hfixinv]
        exact hHasβ
    apply hStd q.p q.exponent q.prime_p hp2 hp3 q.exponent_pos K hK σ hσ s' hs'σ hs'3
    rw [← hys, hcongr]
    exact hHasg.of_mulEquiv (Sec4.autFixCongrEquiv (MulAut.conj y) _).symm

end Support

theorem noOuterType424D4Odd_holds :
    NoOuterType424D4Odd :=
  ronanD4Odd_of GH74.GLS.Stage2.Bender.Thm1.d4CocycleNF_holds d4OuterStdNoType424_holds
    noOuterType424D4Three_holds

end CFSG.RankThree.PartTwo.Sec11

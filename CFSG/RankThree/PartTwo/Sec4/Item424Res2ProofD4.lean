module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecIrred

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

@[expose] def K424TrialitySecond :
    Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ (γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Sec4.IsStdGraphFieldConj σ γ → γ y = y → orderOf y = 3 →
        ¬ Sec11.KS11Lie2Proof.HasType424 (Sec4.autFix (γ * MulAut.conj y))


namespace Item424Res2

open Sec11.KS11Lie2Proof

theorem not_hasType424_g2
    {k : Type} [Field k] [Finite k] :
    ¬ HasType424 (adjointGroup .G2 k) := by
  by_cases hk : 3 ≤ Nat.card k
  · have : IsSimpleGroup (adjointGroup .G2 k) := isSimpleGroup_g2 hk
    have : IsSimpleGroup (⊤ : Subgroup (adjointGroup .G2 k)) :=
      Subgroup.topEquiv.isSimpleGroup
    obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := g2_exists_e9 k
    have hc : ⁅u, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr huv
    exact not_hasType424_of_simple (⊤ : Subgroup (adjointGroup .G2 k))
      (fun _ _ => Subgroup.mem_top _) (Subgroup.mem_top u) (Subgroup.mem_top v) hu1 hu3 hv3
      (by rw [hc]; exact Commute.one_left _) (by rw [hc]; exact Commute.one_left _) hvu
  · have h1 : 1 < Nat.card k := Finite.one_lt_card
    exact Sec11.KS11Lie3Proof.not_hasType424_g2_two (by omega)

theorem not_hasType424_autFix_of_isStdGraphFieldConj
    {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) (σ : K ≃+* K)
    {γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hγ : Sec4.IsStdGraphFieldConj σ γ) : ¬ HasType424 (Sec4.autFix γ) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨φ⟩ := KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 σ hK2
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀
  have hfix : Sec4.autFix σ₀ = σ₀.toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext x
    rfl
  have hfixinv : Sec4.autFix σ₀⁻¹ = Sec4.autFix σ₀ := by
    ext x
    rw [Sec4.mem_autFix, Sec4.mem_autFix]
    constructor
    · intro h
      have := congrArg σ₀ h
      rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
      exact this.symm
    · intro h
      rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
      exact h.symm
  have h₀ : ¬ HasType424 (Sec4.autFix σ₀) := fun h =>
    not_hasType424_g2 (h.of_mulEquiv ((MulEquiv.subgroupCongr hfix).trans φ))
  have hcongr : ∀ (β ρ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      β * ρ * β⁻¹ = MulAut.congr β ρ := by
    intro β ρ
    ext x
    rfl
  obtain ⟨β, hβ | hβ⟩ := hγ
  · rw [hβ, hcongr]
    exact fun h => h₀ (h.of_mulEquiv (Sec4.autFixCongrEquiv β σ₀))
  · rw [hβ, hcongr]
    exact fun h => h₀ ((h.of_mulEquiv (Sec4.autFixCongrEquiv β σ₀⁻¹)).of_mulEquiv
      (MulEquiv.subgroupCongr hfixinv))

end Item424Res2

open Item424Res2

theorem k424TrialityOuter_of
    (h2 : K424TrialitySecond) :
    K424TrialityOuter := by
  intro G _ _ L K c n hD hout hc3 hK hT
  obtain ⟨hcN, hα⟩ := hout
  obtain ⟨K', _, _, σ, hK', hσ, ⟨E⟩⟩ := exists_mulEquiv_graphFixedRootGroup_D4 hD
  have hK2 := Sec8.Item8KFactsProof.ringChar_eq_two_of_card hK'
  have : Finite (ModGL TwistTag.D4.tag K') := finite_modGL
  set α := Item426.thetaAut L hcN with hαdef
  have hKL : K ≤ L := (mem_thetaComponentsIn_iff.mp hK).1.trans inf_le_left
  set J := (K.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) with hJ
  have hJα : J ∈ thetaComponentsIn (Item426.fixSub α) :=
    Item426.map_mem_thetaComponentsIn_fixSub L hcN hc3 hK
  obtain ⟨eK⟩ := Item426.nonempty_quotTheta_map_equiv L hKL
  have hJT : Sec11.IsType424 (J ⧸ aschbacherSolvableCore 3 J) :=
    Sec11.isType424_of_mulEquiv eK.symm hT
  have hHas : Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub α) :=
    Sec11.KS11Lie2Proof.hasType424_of_mem hJα hJT
  set β := MulAut.congr E α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, Item426.thetaAut_pow_eq_one L hcN hc3, map_one]
  have hβin : ¬ KFacts.IsInnerAut β := fun h => hα ((KFacts.isInnerAut_congr E α).mp h)
  have hfixα : Item426.fixSub α = Sec4.autFix α := by
    ext x
    rfl
  have hHasβ : Sec11.KS11Lie2Proof.HasType424 (Sec4.autFix β) := by
    rw [hfixα] at hHas
    exact hHas.of_mulEquiv (Sec4.autFixCongrEquiv E α).symm
  rcases Sec8.kF82D4OuterClasses_of_lang Sec8.kF82D4LangCoset_holds n K' σ hK' hσ β hβ3 hβin with
    hstd | ⟨γ, y, hγ, hγy, hy, hβγ⟩
  · exact Item424Res2.not_hasType424_autFix_of_isStdGraphFieldConj hK2 σ hstd hHasβ
  · rw [hβγ] at hHasβ
    exact h2 n K' σ hK' hσ γ y hγ hγy hy hHasβ

end CFSG.RankThree.PartTwo.Sec4

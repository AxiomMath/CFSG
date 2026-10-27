module

public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ExceptionalRoots


noncomputable def burnsideF45_topEquiv {E : Type} [Group E] {Gp : Subgroup E} (hGp : Gp = ⊤) :
    E ≃* ↥Gp :=
  Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hGp.symm)

theorem burnsideF45_simple_G2d {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2d p f Gp M₁ M₂) : IsSimpleGroup E := by
  have hGp : Gp = ⊤ := hyp.canonical (Or.inl rfl)
  obtain ⟨hp, hf, -⟩ := hyp.model
  subst hp hf
  obtain ⟨K, fK, finK, hK, marking, -, -⟩ := burnsideF4gG2Two_chart_G2d hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  haveI := CFSG.Quasithin.isSimpleGroup_u33Pres
  exact ((burnsideF45_topEquiv hGp).trans (marking.symm.trans
    (burnsideF4h_g2_psi K hK).symm)).isSimpleGroup

theorem burnsideF45_simple_Tits {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Tits p f Gp M₁ M₂) : IsSimpleGroup E := by
  have hGp : Gp = ⊤ := hyp.canonical (Or.inr rfl)
  obtain ⟨chart, -⟩ := hyp.toHypF_4_4g.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨-, -, he, marking, -, -, -, -, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · subst he
    letI := fK
    haveI := finK
    haveI := charK
    haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
    have hK : Nat.card K = 2 := by simpa [ChF.ExceptionalRoots.ReeScope] using scope
    obtain ⟨Φ, -⟩ := burnsideF4h_tits_gammaEquiv hK
    obtain ⟨Θ, -⟩ := burnsideF4h_tits_commutator_equiv (reeGroup K 0) Φ
    have hZ : Subgroup.center ↥⁅reeGroup K 0, reeGroup K 0⁆ = ⊥ :=
      burnsideF4h_tits_center_eq_bot_of_equiv Θ burnsideF4h_tits_center_titsD
    obtain ⟨eC, -⟩ := burnsideF4h_tits_exists_derivedEquiv (reeGroup K 0) _ rfl hZ
    haveI : IsSimpleGroup ↥CFSG.Sporadic.Schreier.Tits.titsD :=
      CFSG.Sporadic.Schreier.Tits.titsD_simple
    exact ((burnsideF45_topEquiv hGp).trans (marking.symm.trans (eC.trans Θ))).isSimpleGroup

theorem burnsideF45_simple : ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → (κ = .G2d ∨ κ = .Tits) → IsSimpleGroup E := by
  rintro κ p f E _ Gp M₁ M₂ hyp (rfl | rfl)
  · exact burnsideF45_simple_G2d hyp
  · exact burnsideF45_simple_Tits hyp

end CFSG.ASVolI

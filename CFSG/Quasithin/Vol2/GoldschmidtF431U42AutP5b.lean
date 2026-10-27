module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bB

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

@[expose] def FusionTStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G) (c : AutCtx G M₁ M₂ z)
    (t : Bh), (t : Ah) ∈ TAh → (t : Ah) * (t : Ah) = 1 → (t : Ah) ≠ 1 → ¬ IsConj (t : Ah) xA →
      ¬ IsConj (c.iso.toG t) z

theorem u42AutFusionT : U42AutSylow → U42AutFusionZ → FusionTStmt := by
  intro h2 h5 G _ _ M₁ M₂ z c t htS ht2 ht1 htx hconj
  obtain ⟨j, hj, g, hg, hgeq⟩ := inner_inv_type htS ht2 ht1
  have hj1 : j = 1 := by
    rcases hj with rfl | rfl
    · exfalso
      have e : repA 0 = xA := by simp [repA]
      rw [e] at hgeq
      exact htx (isConj_iff.2 ⟨g, hgeq⟩)
    · rfl
  subst hj1
  have e : repA 1 = t0A := by simp [repA]
  rw [e] at hgeq
  have hconj0 : IsConj (c.iso.toG t0B) z :=
    (c.iso.isConj_toG hg (v := t0B) hgeq).symm.trans hconj
  have hnx : ¬ IsConj t0A xA := fun h =>
    htx ((isConj_iff.2 ⟨g, hgeq⟩ : IsConj (t : Ah) t0A).trans h)
  have hT₀ : IsSylowTwoOf (c.iso.imgG That) (M₁ ⊓ M₂) := isSylowTwoOf_imgG_That c.iso
  have hTG := h2 G M₁ M₂ z c _ hT₀
  by_cases hweak : ∀ y : G, (∀ a ∈ c.iso.imgG VA, y * a * y⁻¹ ∈ c.iso.imgG That) →
      ∀ a ∈ c.iso.imgG VA, y * a * y⁻¹ ∈ c.iso.imgG VA
  · exact caseA c hTG hnx hconj0 hweak
  · push Not at hweak
    obtain ⟨y, hy, a₀, ha₀, hna⟩ := hweak
    exact caseB c h5 hconj0 hy ha₀ hna

end CFSG.Quasithin.H13.F431.U42Aut

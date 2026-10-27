module

public import CFSG.Milestones.ASVolI.F45.Six
public import CFSG.Milestones.ASVolI.F45.D4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

@[expose] def burnsideF45_HasSystem {E : Type} [Group E] (κ : GLKind) (p : ℕ) (Gp : Subgroup E) :
    Prop :=
  ∃ (X : Type) (_ : Group X) (_ : X ≃* ↥Gp) (n : ℕ) (D : CFSG.GH74.BNPair.RankTwoSystem X n),
    n = κ.m ∧ ChF.IsSylowOf p D.U ⊤

section Generic

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF45_C6_of_hasSystem (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (hGp : Gp = ⊤)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (h : burnsideF45_HasSystem κ p Gp) :
    ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj u v → burnsideF45_C6Body p Gp M₁ M₂ u v := by
  obtain ⟨X, _, θ₀, n, D, hn, hU⟩ := h
  exact burnsideF45_C6_of_system hyp hp hm hGp hP θ₀ D hn hU

end Generic

section G2

theorem burnsideF45_hasSystem_G2 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 p f Gp M₁ M₂) (hp : p.Prime) : burnsideF45_HasSystem .G2 p Gp := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, fK, finK, hcard, marking, -, -⟩ := burnsideF45_chart_G2 hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  have hf : 1 ≤ f := hyp.model.2.1
  haveI : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hcard
  exact ⟨_, inferInstance, marking, 6, burnsideF4h_g2_sys K, rfl,
    burnsideF4h_g2_sys_U_sylow (K := K) p⟩

end G2

section F4tw

open CFSG.ASVolI.ChF.ExceptionalRoots

theorem burnsideF45_hasSystem_F4tw {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw p f Gp M₁ M₂) : burnsideF45_HasSystem .F4tw p Gp := by
  have hp2 : p = 2 := hyp.model.1
  subst hp2
  obtain ⟨a, K, fK, finK, charK, hscope, -, marking, -, -⟩ :=
    burnsideF4g_chart_F4tw hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  haveI := charK
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hscope
  obtain ⟨Φ, -⟩ := burnsideF4h_ree_exists_iso hK
  have hU2 := CFSG.Quasithin.H13.F431.TwoF4.isSylowTwoOf_Ug hK
  exact ⟨_, inferInstance, Φ.trans marking, 8, burnsideF4h_ree_system hK, rfl, hU2⟩

end F4tw

section D4tw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.BNPair CFSG.GH74.GLS.Stage4.Hex
  CFSG.ASVolI.ChF.ExceptionalRoots

theorem burnsideF45_hasSystem_D4tw {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw p f Gp M₁ M₂) (hp : p.Prime) : burnsideF45_HasSystem .D4tw p Gp := by
  obtain ⟨chart, -⟩ := hyp.toHypF_4_4g.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, -, -, K, fK, finK, sigma, hscope, marking, -, -, -, -, -⟩ |
    ⟨-, exponent, K', fK', finK', charK', scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · letI := fK
    haveI := finK
    obtain ⟨hp', hd, hK, hσ⟩ := hscope
    obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = sigma :=
      ⟨RingEquiv.ofBijective sigma ⟨sigma.injective,
        Finite.surjective_of_injective sigma.injective⟩, rfl⟩
    have hσ' : ∀ c, σ.toRingHom c = c ^ (p ^ f) := hσ
    have hq : 2 ≤ p ^ f := burnsideF45_two_le_q σ hp hd hK hσ'
    obtain ⟨f₀, hf₀, hrange, -⟩ := burnsideF4h_tri_exists_embedding hp hd hK σ hσ
    let e₁ : CFSG.Blueprint.DerivedCentralQuotient
        (CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K σ.toRingHom) ≃*
          ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      (MonoidHom.ofInjective hf₀).trans (MulEquiv.subgroupCongr hrange)
    obtain ⟨e₂⟩ := burnsideF45_d4Model_equiv σ hp hd hK hσ'
    exact ⟨_, inferInstance, e₂.trans (e₁.symm.trans marking), 6,
      d4ModelSystem σ.toRingHom hq hK hσ', rfl,
      burnsideF45_d4ModelSystem_isSylow σ hp hd hK hσ' hq⟩
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

end D4tw

section C6

theorem burnsideF45_C6_exc {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .G2 ∨ κ = .D4tw ∨ κ = .F4tw) (hGp : Gp = ⊤) :
    ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj u v → burnsideF45_C6Body p Gp M₁ M₂ u v := by
  have hp := burnsideF4a_prime_of_isGenLie hyp.model
  have hP := burnsideF45_parabolics hyp.toHypF_4_4g
  have hm := burnsideF45_three_le_m κ
  rcases hκ with rfl | rfl | rfl
  · exact burnsideF45_C6_of_hasSystem hyp hp hm hGp hP (burnsideF45_hasSystem_G2 hyp hp)
  · exact burnsideF45_C6_of_hasSystem hyp hp hm hGp hP (burnsideF45_hasSystem_D4tw hyp hp)
  · exact burnsideF45_C6_of_hasSystem hyp hp hm hGp hP (burnsideF45_hasSystem_F4tw hyp)

end C6

end CFSG.ASVolI

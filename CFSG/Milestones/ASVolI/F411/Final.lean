module

public import CFSG.Milestones.ASVolI.F411.Main
public import CFSG.Milestones.ASVolI.F411.SwapU
public import CFSG.Milestones.ASVolI.F411.aL3
public import CFSG.Milestones.ASVolI.F411.aSp4
public import CFSG.Milestones.ASVolI.F411.aU
public import CFSG.Milestones.ASVolI.F411.Complete
public import CFSG.Milestones.ASVolI.F411.aG2
public import CFSG.Milestones.ASVolI.F411.aD4
public import CFSG.Milestones.ASVolI.F411.aF4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

@[expose] def burnsideF411_AutInputKind (κ : GLKind) : Prop :=
  ∀ (p f : ℕ) (H : Type) [Group H] [Finite H], IsGenLie H κ p f → burnsideF411_AutCentSylow H p

theorem burnsideF411_autInputKind_L3 : burnsideF411_AutInputKind .L3 := by
  intro p f H _ _ h
  obtain ⟨hp, -, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  exact burnsideF411_autCentSylow_of_mulEquiv e.symm (burnsideF411a_autCentSylow_L3 K p)

theorem burnsideF411_autInputKind_Sp4 : burnsideF411_AutInputKind .Sp4 := by
  intro p f H _ _ h
  obtain ⟨hp, -, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  exact burnsideF411_autCentSylow_of_mulEquiv e.symm (burnsideF411a_autCentSylow_Sp4 K p)

theorem burnsideF411_autInputKind_U4 : burnsideF411_AutInputKind .U4 := by
  intro p f H _ _ h
  obtain ⟨hp, -, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hK
  exact burnsideF411_autCentSylow_of_mulEquiv e.symm (burnsideF411a_autCentSylow_U4 K p f hK)

theorem burnsideF411_autInputKind_U5 : burnsideF411_AutInputKind .U5 := by
  intro p f H _ _ h
  obtain ⟨hp, -, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hK
  exact burnsideF411_autCentSylow_of_mulEquiv e.symm (burnsideF411a_autCentSylow_U5 K p f hK)

@[expose] def burnsideF411_AutInputG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p], 3 ≤ Nat.card K →
    burnsideF411_AutCentSylow (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 K) p

section G2Bridge


theorem burnsideF411_autInputKind_G2_of (hG2 : burnsideF411_AutInputG2) :
    burnsideF411_AutInputKind .G2 := by
  intro p f H _ _ h
  obtain ⟨hp, hf, hm⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hq : p ^ f = 2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    rw [hq] at hK
    exact burnsideF411_autCentSylow_of_mulEquiv e.symm (burnsideF411_autCentSylow_g2Two hK p)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hm
    haveI : CharP K p := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have h3 : 3 ≤ Nat.card K := by omega
    exact burnsideF411_autCentSylow_of_mulEquiv e.symm (hG2 K p h3)


theorem burnsideF411_autInputG2 : burnsideF411_AutInputG2 :=
  fun K _ _ p _ _ hK => burnsideF411a_autCentSylow_G2 K p hK

end G2Bridge

section D4F4Bridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Chevalley


@[expose] def burnsideF411_AutInputD4 : Prop :=
  ∀ (p d : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    1 ≤ d → Nat.card K = (p ^ d) ^ 3 → (∀ c, σ c = c ^ (p ^ d)) →
      burnsideF411_AutCentSylow ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) p

theorem burnsideF411_autInputKind_D4tw_of (hD4 : burnsideF411_AutInputD4) :
    burnsideF411_AutInputKind .D4tw := by
  intro p f H _ _ h
  obtain ⟨hp, hf, K, _, _, hK, sigma, hσ, ⟨e⟩⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = (p ^ f) ^ 3 := hK
  obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = sigma :=
    ⟨RingEquiv.ofBijective sigma ⟨sigma.injective,
      Finite.surjective_of_injective sigma.injective⟩, rfl⟩
  have hσ' : ∀ c, σ c = c ^ (p ^ f) := hσ
  obtain ⟨f₀, hf₀, hrange, -⟩ := burnsideF4h_tri_exists_embedding hp hf hK' σ hσ'
  let e₁ : DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (MonoidHom.ofInjective hf₀).trans (MulEquiv.subgroupCongr hrange)
  exact burnsideF411_autCentSylow_of_mulEquiv (e.trans e₁).symm (hD4 p f K σ hf hK' hσ')

theorem burnsideF411_autInputD4 : burnsideF411_AutInputD4 :=
  fun p d _ K _ _ σ hd hK hσ => burnsideF411a_autCentSylow_D4 p d K σ hd hK hσ

@[expose] def burnsideF411_AutInputF4 : Prop :=
  ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], 1 ≤ a →
    Nat.card K = 2 ^ (2 * a + 1) → burnsideF411_AutCentSylow ↥(ReeTag.F4.reeGamma K a) 2

theorem burnsideF411_autInputKind_F4tw_of (hF4 : burnsideF411_AutInputF4) :
    burnsideF411_AutInputKind .F4tw := by
  intro p f H _ _ h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨rfl, -, ⟨rfl, K, _, _, hK, ⟨e⟩⟩ | ⟨-, hm⟩⟩ := h
  · haveI : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (f := 1) (by rw [hK, pow_one])
    exact burnsideF411_autCentSylow_of_mulEquiv e.symm (burnsideF411_autCentSylow_twoF4Two hK 2)
  · obtain ⟨-, -, -, -, ⟨a', ha', hfa'⟩, hall⟩ := ReeTag.large_Ree_model_Schreier H 2 f hm
    obtain ⟨-, a, hfa, K, _, _, hK, ⟨e₀⟩⟩ := hm
    haveI : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
    haveI : CharP K ReeTag.F4.prime := inferInstanceAs (CharP K 2)
    obtain ⟨e⟩ := hall a K hfa hK ⟨e₀⟩
    have ha : 1 ≤ a := by omega
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    exact burnsideF411_autCentSylow_of_mulEquiv e.symm (hF4 a K ha hK')

theorem burnsideF411_autInputF4 : burnsideF411_AutInputF4 :=
  fun a K _ _ _ ha hK => burnsideF411a_autCentSylow_F4 a K ha hK

end D4F4Bridge

@[expose] def burnsideF411_SwapInputKind (κ : GLKind) : Prop :=
  ∀ (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → Gp ≠ ⊤ → burnsideF411_Swap M₁ M₂

section SwapKinds


theorem burnsideF411_swapInputKind_D4tw : burnsideF411_SwapInputKind .D4tw :=
  fun _ _ _ _ _ _ _ hyp _ => burnsideF411_swap_D4tw hyp

theorem burnsideF411_swapInputKind_F4tw : burnsideF411_SwapInputKind .F4tw :=
  fun _ _ _ _ _ _ _ hyp _ => burnsideF411_swap_F4tw hyp

theorem burnsideF411_swapInputKind_U4 : burnsideF411_SwapInputKind .U4 :=
  fun _ _ _ _ _ _ _ hyp _ => burnsideF411_swap_U4 hyp

theorem burnsideF411_swapInputKind_U5 : burnsideF411_SwapInputKind .U5 :=
  fun _ _ _ _ _ _ _ hyp _ => burnsideF411_swap_U5 hyp

end SwapKinds

theorem burnsideF411_rigidExt_of_swap
    (hSL3 : burnsideF411_SwapInputKind .L3) (hSSp4 : burnsideF411_SwapInputKind .Sp4)
    (hSG2 : burnsideF411_SwapInputKind .G2) : burnsideF4n_F411RigidExt := by
  refine burnsideF411_rigidExt_of_inputs fun κ p f E _ Gp M₁ M₂ hyp hGp => ?_
  haveI : Finite E := hyp.finite
  haveI : Fact p.Prime := ⟨burnsideF4a_prime_of_isGenLie hyp.model⟩
  have hκ : κ.IsLie := not_or.mp fun h' => hGp (hyp.canonical h')
  have hA : burnsideF411_AutInputKind κ := by
    cases κ with
    | L3 => exact burnsideF411_autInputKind_L3
    | Sp4 => exact burnsideF411_autInputKind_Sp4
    | G2 => exact burnsideF411_autInputKind_G2_of burnsideF411_autInputG2
    | D4tw => exact burnsideF411_autInputKind_D4tw_of burnsideF411_autInputD4
    | F4tw => exact burnsideF411_autInputKind_F4tw_of burnsideF411_autInputF4
    | U4 => exact burnsideF411_autInputKind_U4
    | U5 => exact burnsideF411_autInputKind_U5
    | G2d => exact absurd rfl hκ.1
    | Tits => exact absurd rfl hκ.2
  refine ⟨burnsideF411_centSylow_of_aut hyp.normal hyp.centralizer_trivial
    (hA p f ↥Gp hyp.model), ?_⟩
  cases κ with
  | L3 => exact hSL3 p f E Gp M₁ M₂ hyp hGp
  | Sp4 => exact hSSp4 p f E Gp M₁ M₂ hyp hGp
  | G2 => exact hSG2 p f E Gp M₁ M₂ hyp hGp
  | D4tw => exact burnsideF411_swapInputKind_D4tw p f E Gp M₁ M₂ hyp hGp
  | F4tw => exact burnsideF411_swapInputKind_F4tw p f E Gp M₁ M₂ hyp hGp
  | U4 => exact burnsideF411_swapInputKind_U4 p f E Gp M₁ M₂ hyp hGp
  | U5 => exact burnsideF411_swapInputKind_U5 p f E Gp M₁ M₂ hyp hGp
  | G2d => exact absurd rfl hκ.1
  | Tits => exact absurd rfl hκ.2

end CFSG.ASVolI

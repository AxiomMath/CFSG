module

public import CFSG.Milestones.ASVolI.F411.SwapCard
public import CFSG.Milestones.ASVolI.F45.BNSix
public import CFSG.Milestones.ASVolI.F4TISets
public import CFSG.Milestones.ASVolI.F45.D4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN

section System

variable {E : Type} [Group E]

theorem burnsideF411_relIndex_ne_of_system [Finite E] {p : ℕ} (hp : p.Prime)
    {Gp M₁ M₂ : Subgroup E} (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    {X : Type} [Group X] (θ₀ : X ≃* ↥Gp) {n : ℕ} (D : RankTwoSystem X n)
    (hU : ChF.IsSylowOf p D.U ⊤) (hne : D.B.relIndex (P D true) ≠ D.B.relIndex (P D false)) :
    (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₁) ≠ (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₂) := by
  obtain ⟨g, b, hgb⟩ := burnsideF45_conj_parabolics hp hP θ₀ D hU
  let ψ : X ≃* ↥Gp := (MulAut.conj g⁻¹).trans θ₀
  have hψ : ∀ y, ψ y = θ₀ (g⁻¹ * y * g) := fun y => by
    show θ₀ (g⁻¹ * y * g⁻¹⁻¹) = _
    rw [inv_inv]
  have hmem : ∀ (M : Subgroup E) (Q : Subgroup X),
      (∀ y : X, ((θ₀ (g⁻¹ * y * g) : ↥Gp) : E) ∈ M ↔ y ∈ Q) →
        (Gp ⊓ M).subgroupOf Gp = Q.map ψ.toMonoidHom := by
    intro M Q hMQ
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, ← hMQ, ← hψ, MulEquiv.apply_symm_apply]
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  have h1 := hmem M₁ (P D b) fun y => (hgb y).1
  have h2 := hmem M₂ (P D (!b)) fun y => (hgb y).2
  have h12 : (Gp ⊓ (M₁ ⊓ M₂)).subgroupOf Gp = D.B.map ψ.toMonoidHom := by
    rw [← burnsideF45_bn_P_inf D b, Subgroup.map_inf_eq _ _ _ ψ.injective, ← h1, ← h2]
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    tauto
  have hr : ∀ (M : Subgroup E) (Q : Subgroup X), (Gp ⊓ M).subgroupOf Gp = Q.map ψ.toMonoidHom →
      (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M) = D.B.relIndex Q := by
    intro M Q hMQ
    rw [← Subgroup.relIndex_subgroupOf (inf_le_left : Gp ⊓ M ≤ Gp), hMQ, h12,
      Subgroup.relIndex_map_map_of_injective _ _ ψ.injective]
  rw [hr M₁ _ h1, hr M₂ _ h2]
  cases b
  · exact fun h => hne h.symm
  · exact hne

end System

section F4tw


theorem burnsideF411_relIndex_ne_F4tw {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw p f Gp M₁ M₂) :
    (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₁) ≠ (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₂) := by
  haveI : Finite E := hyp.finite
  have hp2 : p = 2 := hyp.model.1
  subst hp2
  have hP := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
  obtain ⟨a, K, fK, finK, charK, hscope, -, marking, -, -⟩ :=
    burnsideF4g_chart_F4tw hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  haveI := charK
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hscope
  obtain ⟨Φ, -⟩ := burnsideF4h_ree_exists_iso hK
  have hU2 := CFSG.Quasithin.H13.F431.TwoF4.isSylowTwoOf_Ug hK
  refine burnsideF411_relIndex_ne_of_system Nat.prime_two hP (Φ.trans marking)
    (burnsideF4h_ree_system hK) hU2 ?_
  rw [P_true, P_false, burnsideF4h_ree_relIndex_one hK, burnsideF4h_ree_relIndex_two hK]
  have hq : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
  intro h
  have : (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (2 * a + 1) := by omega
  have h1 : 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) = 2 ^ (2 * a + 1) * 1 := by
    rw [mul_one, ← pow_two, this]
  have := Nat.eq_of_mul_eq_mul_left (by omega) h1
  omega

theorem burnsideF411_swap_F4tw {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw p f Gp M₁ M₂) : burnsideF411_Swap M₁ M₂ := by
  haveI : Finite E := hyp.finite
  exact burnsideF411_swap_of_relIndex_ne hyp.normal hyp.split (burnsideF411_relIndex_ne_F4tw hyp)

end F4tw

section D4tw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.Stage4.Hex CFSG.ASVolI.ChF.ExceptionalRoots


theorem burnsideF411_relIndex_ne_D4tw {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw p f Gp M₁ M₂) :
    (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₁) ≠ (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₂) := by
  haveI : Finite E := hyp.finite
  have hp : p.Prime := burnsideF4a_prime_of_isGenLie hyp.model
  have hP := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
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
    haveI : Finite (twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) :=
      Finite.of_equiv _ (e₂.trans (e₁.symm.trans marking)).symm.toEquiv
    refine burnsideF411_relIndex_ne_of_system hp hP (e₂.trans (e₁.symm.trans marking))
      (d4ModelSystem σ.toRingHom hq hK hσ') (burnsideF45_d4ModelSystem_isSylow σ hp hd hK hσ' hq) ?_
    rw [P_true, P_false, burnsideF4h_ree_relIndex_P₁, burnsideF4h_ree_relIndex_P₂,
      card_d4ModelSystem_root σ.toRingHom hq hK hσ' (by norm_num) (by norm_num),
      card_d4ModelSystem_root σ.toRingHom hq hK hσ' (by norm_num) (by norm_num)]
    simp only [show ((1 : ℤ) % 2 = 1) from rfl, show ((6 : ℕ) : ℤ) % 2 = 0 from rfl, if_true,
      show ((0 : ℤ) = 1) ↔ False from by decide, if_false]
    intro h
    have h3 : (p ^ f) ^ 3 = p ^ f := by omega
    have : p ^ f * (p ^ f) ^ 2 = p ^ f * 1 := by rw [mul_one, ← pow_succ', h3]
    have := Nat.eq_of_mul_eq_mul_left (by omega) this
    have : p ^ f ≤ 1 := by nlinarith
    omega
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

theorem burnsideF411_swap_D4tw {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw p f Gp M₁ M₂) : burnsideF411_Swap M₁ M₂ := by
  haveI : Finite E := hyp.finite
  exact burnsideF411_swap_of_relIndex_ne hyp.normal hyp.split (burnsideF411_relIndex_ne_D4tw hyp)

end D4tw

end CFSG.ASVolI

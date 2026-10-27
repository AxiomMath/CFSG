module

public import CFSG.Milestones.ASVolI.F45.Lie
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2CardU

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
  (hK : Nat.card K = (p ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (p ^ f))

include hp hf hK hσq

theorem burnsideF45_two_le_q : 2 ≤ p ^ f :=
  calc 2 ≤ p := hp.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf

theorem burnsideF45_d4Model_equiv :
    Nonempty ((twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hq : 2 ≤ p ^ f := burnsideF45_two_le_q σ hp hf hK hσq
  have hZ := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
    (σ := σ.toRingHom) hq hK hσq
  have hm : (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [← commutator_twistedFixedGroup_eq_map σ.toRingHom hq hK hσq]
    exact (finite_fixed_root_group_perfect TwistTag.D4 hp hf K hK σ.toRingHom hσq).2.2.1
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot (G := twistedGroup σ.toRingHom))).trans
    ((Subgroup.equivMapOfInjective (twistedGroup σ.toRingHom) (adjointGroup d4 K).subtype
        Subtype.val_injective).trans (MulEquiv.subgroupCongr hm))⟩

theorem burnsideF45_not_dvd_d4_index :
    ¬ p ∣ ((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1)) := by
  have hdq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have h2 : p ∣ (p ^ f) ^ 2 := dvd_pow hdq (by norm_num)
  have h6 : p ∣ (p ^ f) ^ 6 := dvd_pow hdq (by norm_num)
  have h4 : p ∣ (p ^ f) ^ 4 := dvd_pow hdq (by norm_num)
  have h8 : p ∣ (p ^ f) ^ 8 := dvd_pow hdq (by norm_num)
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq6 : 1 ≤ (p ^ f) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have o2 : ¬ p ∣ (p ^ f) ^ 2 - 1 := by
    intro h
    have : p ∣ (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) := Nat.dvd_sub h2 h
    rw [show (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have o6 : ¬ p ∣ (p ^ f) ^ 6 - 1 := by
    intro h
    have : p ∣ (p ^ f) ^ 6 - ((p ^ f) ^ 6 - 1) := Nat.dvd_sub h6 h
    rw [show (p ^ f) ^ 6 - ((p ^ f) ^ 6 - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have o8 : ¬ p ∣ (p ^ f) ^ 8 + (p ^ f) ^ 4 + 1 := by
    intro h
    have : p ∣ (p ^ f) ^ 8 + (p ^ f) ^ 4 + 1 - ((p ^ f) ^ 8 + (p ^ f) ^ 4) :=
      Nat.dvd_sub h (dvd_add h8 h4)
    rw [show (p ^ f) ^ 8 + (p ^ f) ^ 4 + 1 - ((p ^ f) ^ 8 + (p ^ f) ^ 4) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact o2 h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact o6 h
    · exact o8 h

theorem burnsideF45_d4ModelSystem_isSylow (hq : 2 ≤ p ^ f) :
    ChF.IsSylowOf p (d4ModelSystem σ.toRingHom hq hK hσq).U ⊤ := by
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    sigma_three_of_card hK hσq
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨eC⟩ := burnsideF45_d4Model_equiv σ hp hf hK hσq
  have hU : Nat.card (d4ModelSystem σ.toRingHom hq hK hσq).U = (p ^ f) ^ 12 := by
    have h := (hexQuotRGD2 (twistedData σ.toRingHom hσ3)).card_U
    rw [show (d4ModelSystem σ.toRingHom hq hK hσq).U =
      (posUnipotent (g2Shape (twistedX σ.toRingHom))).map (hexProj ↥(twistedGroup σ.toRingHom))
        from rfl, h]
    have hr : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ((hexGroup (twistedX σ.toRingHom) i).map
        (hexProj ↥(twistedGroup σ.toRingHom))) = if i % 2 = 1 then (p ^ f) ^ 3 else p ^ f :=
      fun i h1 h6 => card_d4ModelSystem_root σ.toRingHom hq hK hσq h1 h6
    have hl : intList 1 ((6 : ℕ) : ℤ) = [1, 2, 3, 4, 5, 6] := by decide
    rw [hl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    rw [hr 1 (by norm_num) (by norm_num), hr 2 (by norm_num) (by norm_num),
      hr 3 (by norm_num) (by norm_num), hr 4 (by norm_num) (by norm_num),
      hr 5 (by norm_num) (by norm_num), hr 6 (by norm_num) (by norm_num)]
    norm_num
    ring
  have hpg : IsPGroup p ↥(d4ModelSystem σ.toRingHom hq hK hσq).U :=
    IsPGroup.of_card (n := f * 12) (by rw [hU, ← pow_mul])
  have hX : Nat.card (twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) =
      (p ^ f) ^ 12 *
        (((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1))) := by
    rw [Nat.card_congr eC.toEquiv]
    have hσ' : ∀ c, σ.toRingHom c = c ^ ((p ^ f) ^ 1) := fun c => by rw [pow_one]; exact hσq c
    have h := (triality_both_orientations_exact_finite_order p f hp hf K hK 1
      (Or.inl rfl) σ.toRingHom hσ').1
    rw [h]
    ring
  have hidx : (d4ModelSystem σ.toRingHom hq hK hσq).U.index =
      ((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1)) := by
    have h := Subgroup.card_mul_index (d4ModelSystem σ.toRingHom hq hK hσq).U
    rw [hU, hX] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  refine ⟨le_top, hpg, ?_⟩
  rw [Subgroup.relIndex_top_right, hidx]
  exact burnsideF45_not_dvd_d4_index σ hp hf hK hσq

end Model

section Facts

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.BNPair CFSG.GH74.GLS.Stage4.Hex
  CFSG.ASVolI.ChF.ExceptionalRoots


theorem burnsideF45_facts45L_D4tw {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ GLKind.D4tw.m) :
    (burnsideF45_setting hyp hp hm).Facts45L := by
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
    have hU := burnsideF45_d4ModelSystem_isSylow σ hp hd hK hσ' hq
    exact burnsideF45_facts45L_of_system hyp hp hm (burnsideF45_parabolics hyp.toHypF_4_4g)
      (e₂.trans (e₁.symm.trans marking)) (d4ModelSystem σ.toRingHom hq hK hσ') rfl hU
      (fun i => burnsideF45_bn_modelBase (d4ModelSystem σ.toRingHom hq hK hσ') hp hU i)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

end Facts

end CFSG.ASVolI

module

public import CFSG.Milestones.ASVolI.F48.Id
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2CardU
public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open

theorem burnsideF48_D4tw_marking {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : ChF.HypF_4_4g .D4tw p f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (sigma : K →+* K),
      ChF.ExceptionalRoots.TrialityScope K sigma p f ∧
      Nonempty (CFSG.Blueprint.DerivedCentralQuotient
        (CFSG.Blueprint.twistedFixedGroup .D4 K sigma) ≃* ↥Gp) := by
  obtain ⟨chart, -, -, -⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨hk, hp, hd, K, fK, finK, sigma, scope, marking, h1, h2, h3, h4, h5⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact ⟨K, fK, finK, sigma, scope, ⟨marking⟩⟩
  all_goals exact absurd hk (by decide)

theorem burnsideF48_not_dvd_pred {p m : ℕ} (hm : p ∣ m) (hm1 : 1 ≤ m) (hp : p.Prime) :
    ¬ p ∣ m - 1 := by
  intro h
  have h2 : p ∣ (m - 1) + 1 := by
    rw [Nat.sub_add_cancel hm1]
    exact hm
  have : p ∣ 1 := (Nat.dvd_add_right h).1 h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

section D4Model


set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
  (hK : Nat.card K = (p ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (p ^ f))

include hp hf hK hσq

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.QuasithinUnique CFSG.GH74.BNPair CFSG.GH74.GLS.SP
  CFSG.GH74.GLS.Stage4.Hex in
theorem burnsideF48_d4Model_equiv :
    Nonempty ((twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hq : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
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

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.QuasithinUnique CFSG.GH74.BNPair CFSG.GH74.GLS.SP
  CFSG.GH74.GLS.Stage4.Hex in
theorem burnsideF48_d4ModelSystem_isSylow (hq : 2 ≤ p ^ f) :
    ChF.IsSylowOf p (d4ModelSystem σ.toRingHom hq hK hσq).U ⊤ := by
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    sigma_three_of_card hK hσq
  have : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨eC⟩ := burnsideF48_d4Model_equiv σ hp hf hK hσq
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
  have hpG : IsPGroup p ↥(d4ModelSystem σ.toRingHom hq hK hσq).U :=
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
  refine ⟨le_top, hpG, ?_⟩
  rw [Subgroup.relIndex_top_right, hidx]
  have h2 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hq1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hq6 : 1 ≤ (p ^ f) ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have e2 : p ∣ (p ^ f) ^ 2 := dvd_pow h2 (by norm_num)
  have e6 : p ∣ (p ^ f) ^ 6 := dvd_pow h2 (by norm_num)
  have e8 : p ∣ (p ^ f) ^ 8 := dvd_pow h2 (by norm_num)
  have e4 : p ∣ (p ^ f) ^ 4 := dvd_pow h2 (by norm_num)
  have o2 := burnsideF48_not_dvd_pred e2 hq1 hp
  have o6 := burnsideF48_not_dvd_pred e6 hq6 hp
  have o8 : ¬ p ∣ (p ^ f) ^ 8 + (p ^ f) ^ 4 + 1 := fun h =>
    hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right (dvd_add e8 e4)).1 h))
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact o2 h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact o6 h
    · exact o8 h

end D4Model

section D4Cartan


set_option linter.unusedSectionVars false

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.GH74.BNPair CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.D4q.F48 CFSG.LieType.Steinberg.TwistedD4 in
theorem burnsideF48_cartanFPF_D4tw {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .D4tw p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ ChF.GLKind.D4tw.m)
    (hq : 4 ≤ p ^ f)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 6) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite E := hyp.finite
  obtain ⟨K, fK, finK, σ, scope, ⟨marking⟩⟩ := burnsideF48_D4tw_marking hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  obtain ⟨σE, rfl⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      RingHom.ext fun _ => rfl⟩
  obtain ⟨-, hf, hK, hσq⟩ := scope
  have hq2 : 2 ≤ p ^ f := by omega
  have hσ3 : ∀ c, σE.toRingHom (σE.toRingHom (σE.toRingHom c)) = c := sigma_three_of_card hK hσq
  have hU := burnsideF48_d4ModelSystem_isSylow σE hp hf hK hσq hq2
  have hX := burnsideF4h_g2_isLieParabolics (d4ModelSystem σE.toRingHom hq2 hK hσq) hU
  obtain ⟨eC⟩ := burnsideF48_d4Model_equiv σE hp hf hK hσq
  obtain ⟨eD, -⟩ := burnsideF4h_tri_exists_equiv hp hf hK σE hσq
  obtain ⟨ε, -, hcases⟩ := burnsideF48_identify (eC.trans (eD.symm.trans marking)) hX hP
  obtain ⟨s, t, hw⟩ := exists_fpf hq hK hσq
  have hcart := modelTor_mem_cartan hq2 hK hσq hσ3 s t
  have hfix := fun y (hy : y ∈ (d4ModelSystem σE.toRingHom hq2 hK hσq).U) hf' =>
    modelTor_fix_U hq2 hK hσq hσ3 s t hw hy hf'
  have key : ∀ b : Bool, burnsideF48_img ε (P (d4ModelSystem σE.toRingHom hq2 hK hσq) b) =
      Gp ⊓ M₁ → burnsideF48_img ε (P (d4ModelSystem σE.toRingHom hq2 hK hσq) (!b)) = Gp ⊓ M₂ →
      (burnsideF48_setting hyp hp hm).CartanFPF := by
    intro b e1 e2
    obtain ⟨m, w, hm1, hm2, hh1, hh2, hh3, hh4, hw'⟩ :=
      burnsideF48_bn_cartan_data (d4ModelSystem σE.toRingHom hq2 hK hσq) (by norm_num) hcart b
    have hP₁ : ∀ g, ((ε g : ↥Gp) : E) ∈ M₁ ↔
        g ∈ P (d4ModelSystem σE.toRingHom hq2 hK hσq) b := fun g => by
      rw [← burnsideF48_mem_img ε _ g, e1]
      exact ⟨fun h => Subgroup.mem_inf.2 ⟨(ε g).2, h⟩, fun h => (Subgroup.mem_inf.1 h).2⟩
    have hP₂ : ∀ g, ((ε g : ↥Gp) : E) ∈ M₂ ↔
        g ∈ P (d4ModelSystem σE.toRingHom hq2 hK hσq) (!b) := fun g => by
      rw [← burnsideF48_mem_img ε _ g, e2]
      exact ⟨fun h => Subgroup.mem_inf.2 ⟨(ε g).2, h⟩, fun h => (Subgroup.mem_inf.1 h).2⟩
    exact burnsideF48_cartanFPF_of_data_six hyp hp hm rfl hpoly ε
      (P (d4ModelSystem σE.toRingHom hq2 hK hσq) b)
      (P (d4ModelSystem σE.toRingHom hq2 hK hσq) (!b))
      (d4ModelSystem σE.toRingHom hq2 hK hσq).U hP₁ hP₂
      (burnsideF48_isSylowOf_of_equiv_top ε hU)
      ((d4ModelSystem σE.toRingHom hq2 hK hσq).U_le_B.trans (B_le_P _ b)) m w _ hm1 hm2 hh1 hh2
      hh3 hh4 hw' (fun q hq _ hc => hfix q hq hc)
  rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact key true e1 e2
  · exact key false e2 e1

theorem burnsideF48_simple_D4tw {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .D4tw p f Gp M₁ M₂) (hq : 2 ≤ p ^ f) : IsSimpleGroup ↥Gp := by
  obtain ⟨K, fK, finK, σ, scope, ⟨marking⟩⟩ := burnsideF48_D4tw_marking hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  obtain ⟨σE, rfl⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      RingHom.ext fun _ => rfl⟩
  obtain ⟨hp, hf, hK, hσq⟩ := scope
  haveI := CFSG.GH74.GLS.Stage4.Hex.isSimpleGroup_d4Model σE.toRingHom hq hK hσq
  obtain ⟨eC⟩ := burnsideF48_d4Model_equiv σE hp hf hK hσq
  obtain ⟨eD, -⟩ := burnsideF4h_tri_exists_equiv hp hf hK σE hσq
  exact (eC.trans (eD.symm.trans marking)).symm.isSimpleGroup

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_concl_D4tw (hF : F_4_5) (hcompat : ChF.NativeChartCompatibilityGoal)
    {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .D4tw p f Gp M₁ M₂) (hq : 4 ≤ p ^ f) :
    ChF.F48Concl .D4tw p f Gp M₁ M₂ := by
  have hP := burnsideF48_parabolics_of_compat hcompat hyp
  have hp := ChF.burnsideF4a_prime_of_isGenLie hyp.model
  have hm := burnsideF48_three_le_m .D4tw
  have hL : ChF.GLKind.D4tw.IsLie :=
    show ChF.GLKind.D4tw ≠ ChF.GLKind.G2d ∧ ChF.GLKind.D4tw ≠ ChF.GLKind.Tits from
      ⟨by decide, by decide⟩
  refine burnsideF48_concl_of_F45_cartan hF hyp hL (burnsideF48_simple_D4tw hyp (by omega)) hP ?_
  exact burnsideF48_cartanFPF_D4tw hyp hp hm hq hP
    (burnsideF48_facts45L_of_F45 hF hyp hL hp hm hP).poly

end D4Cartan

end CFSG.ASVolI

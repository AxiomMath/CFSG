module

public import CFSG.Milestones.ASVolI.F431.BCoreGen
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructAut
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4Trans
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocBase
import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.Loc
open scoped commutatorElement

section D4

set_option linter.unusedSectionVars false


section Model

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem burnsideF4m_D4_out_comm {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) (α β : MulAut (Cm σ)) :
    ⁅α, β⁆ ∈ (MulAut.conj : Cm σ →* MulAut (Cm σ)).range := by
  rw [← theta_ker σ hf hK hσq, MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2
    (CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K _ _)

variable [CharP K 2]

theorem burnsideF4m_D4_P0_center_le (hσ : ∀ c, σ (σ (σ c)) = c) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    centerOf (perfectCore (Pst0 σ)) ≤ ctr (oPPrime 2 (Pst0 σ)) := by
  rw [(burnsideF4gD4Inv_oPPrime_eq σ hσ hf hK hσq).2]
  exact le_rfl

theorem burnsideF4m_D4_four_le_fixed {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom) := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨-, -, -, -, -, k, hk, hcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two (by omega : 1 ≤ f) K hK
  have hσ' : ∀ c, σ c = c ^ (2 ^ f) := hσq
  have hkeq : trialityFixedField K σ.toRingHom = k := by
    apply SetLike.ext'
    rw [hk]
    ext c
    simp [mem_trialityFixedField, hσ']
  rw [hkeq, hcard]
  exact hq4

theorem burnsideF4m_D4_P1_center_eq_bot (hσ : ∀ c, σ (σ (σ c)) = c) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    centerOf (perfectCore (Pst1 σ)) = ⊥ := by
  have hσ3 : σ.toRingHom ^ 3 = 1 :=
    RingHom.ext fun c => (ringHom_pow_three_apply σ.toRingHom c).trans (hσ c)
  have hk4 := burnsideF4m_D4_four_le_fixed σ hf hK hσq
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hP1C : CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.P1 σ ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedParabolic_le _ _ _ _
  have hx' := (H13.Sec53F.TriD4.mem_centerOf_subgroupOf_iff hP1C x).1 hx
  obtain ⟨c, hc⟩ := H13.Sec53F.TriD4.centerOf_perfectCore_P1_form σ hσ3 hk4 hx'
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx1
    apply Subtype.ext
    rw [hc, CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.ox₆_zero σ hσ3]
    rfl
  obtain ⟨m, hm, hmx⟩ := H13.Sec53F.TriD4.exists_torus_conj_ox₆ σ hσ3 1 c one_ne_zero hc0
  obtain ⟨R, -, -, hRW, hMP, -⟩ := CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.levi_package σ
    CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.fa1
    (CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.isPGroup_posUnipotent σ hσ3)
    (H13.Sec53F.TriD4.exists_card_four_fa1 σ hk4)
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K
    (TwistTag.D4.orbitReflection CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.fa1) with hn_def
  have hn : n ∈ perfectCore (CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.P1 σ) :=
    hMP ⟨CFSG.LieType.Chevalley.WSL, hRW⟩
  have hxn : n * (x : ModGL TwistTag.D4.tag K) = (x : ModGL TwistTag.D4.tag K) * n :=
    Subgroup.mem_centralizer_iff.1 hx'.2 n hn
  rw [hc, ← hmx] at hxn
  have hmB := graphFixedRootTorus_le_graphFixedRootBorel hm
  have hmC : m ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedRootBorel_le _ _ _ hmB
  have hnC : n ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    canonicalRep_orbitReflection_mem_graphFixedRootGroup _
  let g : Cm σ := ⟨m⁻¹ * n * m, mul_mem (mul_mem (inv_mem hmC) hnC) hmC⟩
  have hg : g * zC σ = zC σ * g := by
    apply Subtype.ext
    show m⁻¹ * n * m * CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.ox₆ σ 1 =
      CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.ox₆ σ 1 * (m⁻¹ * n * m)
    calc m⁻¹ * n * m * CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.ox₆ σ 1
        = m⁻¹ * (n * (m * CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.ox₆ σ 1 * m⁻¹)) * m := by
          group
      _ = m⁻¹ * (m * CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.ox₆ σ 1 * m⁻¹ * n) * m := by
          rw [hxn]
      _ = CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.ox₆ σ 1 * (m⁻¹ * n * m) := by group
  have hgP0 := centralizer_zC_le_Pst0 σ hσ hg
  have hmP0 : m ∈ CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.P0 σ :=
    graphFixedRootBorel_le_graphFixedParabolic _ _ _ _ hmB
  have hnP0 : n ∈ CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.P0 σ := by
    have hg' : m⁻¹ * n * m ∈ CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.P0 σ := hgP0
    have := mul_mem (mul_mem hmP0 hg') (inv_mem hmP0)
    simpa [mul_assoc] using this
  have hle : CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.P1 σ ≤
      CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.P0 σ := by
    refine sup_le (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
      ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨a, ha, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact hnP0
  exact absurd (congrArg Fin.val ((graphFixedParabolic_le_iff σ.surjective).1 hle
    (Set.mem_singleton _))) (by decide)

end Model

theorem burnsideF4m_D4_chart {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .D4tw 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (σ : K ≃+* K),
      (∀ c, σ (σ (σ c)) = c) ∧ 1 ≤ f ∧ Nat.card K = (2 ^ f) ^ 3 ∧
      (∀ c, σ.toRingHom c = c ^ (2 ^ f)) ∧
      ∃ Ψ : Cm σ ≃* ↥Gp,
        M₁.subgroupOf Gp = (Pst0 σ).map Ψ.toMonoidHom ∧
        M₂.subgroupOf Gp = (Pst1 σ).map Ψ.toMonoidHom := by
  obtain ⟨K, fK, finK, sigma, scope, marking, h1, h2⟩ := burnsideF4g_chart_D4tw h
  obtain ⟨-, hf, hK, hσ⟩ := scope
  obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = sigma :=
    ⟨RingEquiv.ofBijective sigma
      ⟨sigma.injective, Finite.surjective_of_injective sigma.injective⟩, rfl⟩
  have hσ' : ∀ c, σ c = c ^ (2 ^ f) := hσ
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ'
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI hCharP : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hΓ := twistedFixedGroup_eq_graphFixedRootGroup_triality σ hσ3 (Or.inl hchar)
  obtain ⟨-, -, -, -, -, hD, hZ, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ'
  obtain ⟨e, he⟩ := burnsideF4gD4_exists_derivedEquiv _ _ hD hZ
  let φ : Cm σ ≃* ↥Gp := e.symm.trans marking
  have hmap0 : ∀ P : Subgroup (ModGL TwistTag.D4.tag K),
      ((derivedImage (twistedFixedGroup TwistTag.D4 K σ.toRingHom) P).map marking.toMonoidHom) =
        (P.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom := by
    intro P
    have hcomp : φ.toMonoidHom.comp e.toMonoidHom = marking.toMonoidHom := by
      refine MonoidHom.ext fun q => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, φ]
    rw [← burnsideF4gD4_map_derivedImage _ _ P hD e he, Subgroup.map_map, hcomp]
  have h0 := burnsideF4gD4_trialityParabolic_zero σ.toRingHom hΓ
  have h1' := burnsideF4gD4_trialityParabolic_one σ.toRingHom hΓ
  refine ⟨K, fK, finK, hCharP, σ, hσ3, hf, hK, hσ, φ, ?_, ?_⟩
  · calc M₁.subgroupOf Gp = _ := h1
      _ = ((trialityParabolic K σ.toRingHom 0).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom := hmap0 _
      _ = (Pst0 σ).map φ.toMonoidHom := by rw [h0]; rfl
  · calc M₂.subgroupOf Gp = _ := h2
      _ = ((trialityParabolic K σ.toRingHom 1).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom := hmap0 _
      _ = (Pst1 σ).map φ.toMonoidHom := by rw [h1']; rfl

theorem burnsideF4m_core12_D4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    (∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∧
    (∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      GLKind.D4tw = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) := by
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, σ, hσ3, hf1, hK, hσq, Ψ, h1, h2⟩ :=
    burnsideF4m_D4_chart hyp.toHypF_4_4g
  have hc : ∀ a b : E, ⁅a, b⁆ ∈ Gp := burnsideF4m_commutator_mem_of_out hyp.centralizer_trivial
    (burnsideF4m_out_transport Ψ (burnsideF4m_D4_out_comm σ hf1 hK hσq))
  have hφ : Function.Injective (Gp.subtype.comp Ψ.toMonoidHom) :=
    Gp.subtype_injective.comp Ψ.injective
  refine ⟨burnsideF4m_core1_of_model hc _ hφ (burnsideF4m_inf_eq_map Ψ h1)
    (burnsideF4m_D4_P0_center_le σ hσ3 hf1 hK hσq), ?_⟩
  intro x hx hx1 _
  rw [burnsideF4m_centerOf_perfectCore_eq_bot_of_model hc _ hφ (burnsideF4m_inf_eq_map Ψ h2)
    (burnsideF4m_D4_P1_center_eq_bot σ hσ3 hf hK hσq)] at hx
  exact absurd (Subgroup.mem_bot.1 hx) hx1

end D4

end CFSG.ASVolI

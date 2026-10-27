module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridge
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityLayerPGL
public import CFSG.RankThree.PartTwo.KFacts.K71D4G2Group
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Steinberg.G2.Perfect
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.StandardType

namespace TriBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.Triality
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Groups

theorem commutator_eq_top_of_simple {S : Type*} [Group S] (hs : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) : commutator S = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hm : ⁅a, b⁆ ∈ commutator S := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hab hm
  · exact h

theorem isQuasisimple_of_simple_noncomm {S : Type*} [Group S] (hs : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) : CFSG.Assembly.IsQuasisimple S :=
  OrdPTriLayer.isQuasisimple_of_simple_perfect hs (commutator_eq_top_of_simple hs hnc)

theorem isQuasisimple_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : CFSG.IsQuasisimple G) : CFSG.IsQuasisimple H := by
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (φ := e.toMonoidHom) hG
    e.surjective ?_
  obtain ⟨-, -, a, b, hab⟩ := hG
  by_contra h
  push Not at h
  apply hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ b
  have hx : x = 1 := e.injective (by simpa using h x)
  have hy : y = 1 := e.injective (by simpa using h y)
  simp [hx, hy]

end Groups

section Frob

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_frob_of_orderOf_three (σ : K ≃+* K) (hσ : orderOf σ = 3) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card K = (2 ^ d) ^ 3 ∧
      ∃ r : ℕ, (r = 1 ∨ r = 2) ∧ ∀ c, σ c = c ^ ((2 ^ d) ^ r) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  set f : ℕ := (n : ℕ) with hfdef
  have hf : 1 ≤ f := n.pos
  have hK : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨φ, hφ, hφord, hφtop, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφtop⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have h3f : 3 ∣ f := by
    rw [← hσ, ← hcardAut]
    exact orderOf_dvd_natCard σ
  set d := f / 3 with hd
  have hd3 : d * 3 = f := Nat.div_mul_cancel h3f
  have hd1 : 1 ≤ d := by omega
  set T := φ ^ d with hTdef
  have hit : ∀ (m : ℕ) (c : K), (⇑φ)^[m] c = c ^ (2 ^ m) := by
    intro m c
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, hφ, ← pow_mul, ← pow_succ]
  have hTpow : ∀ (r : ℕ) (c : K), (T ^ r) c = c ^ ((2 ^ d) ^ r) := by
    intro r c
    rw [hTdef, ← pow_mul, CFSG.LieType.Chevalley.ringEquiv_pow_apply, hit, pow_mul]
  have hTord : orderOf T = 3 := by
    rw [hTdef, orderOf_pow' φ (by omega), hφord, Nat.gcd_eq_right ⟨3, hd3.symm⟩, ← hd3,
      Nat.mul_div_cancel_left _ (by omega)]
  have hzz : Subgroup.zpowers T = Subgroup.zpowers σ :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hTord, hσ])
  obtain ⟨m, hm⟩ : ∃ m : ℕ, T ^ m = σ := by
    have h : σ ∈ Subgroup.zpowers T := hzz ▸ Subgroup.mem_zpowers σ
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  have hT3 : T ^ 3 = 1 := by rw [← hTord]; exact pow_orderOf_eq_one T
  have hmod : T ^ (m % 3) = σ := by
    rw [← hm, ← Nat.mod_add_div m 3, pow_add, pow_mul, hT3, one_pow, mul_one, Nat.mod_add_div]
  have hne : m % 3 ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hmod
    rw [← hmod, orderOf_one] at hσ
    omega
  refine ⟨d, hd1, by rw [hK, ← hd3, pow_mul], m % 3, by omega, fun c => ?_⟩
  rw [← hmod, hTpow]

end Frob

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_ggFix_eq_twistedFixedGroup (σ : K ≃+* K) :
    (ggFix (theta * AutOm.fieldAutP 4 σ)).map
        ((adjointGroup TwistTag.D4.tag K).subtype.comp (bridge (K := K)).toMonoidHom) =
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : theta (AutOm.fieldAutP 4 σ x) = x := hx
    refine ⟨(bridge x).2, ?_⟩
    change twistHom TwistTag.D4 K σ.toRingHom (bridge x) = (bridge x : ModGL TwistTag.D4.tag K)
    rw [← coe_bridge_theta_fieldAutP, hx']
  · rintro ⟨hg, hgF⟩
    have hgF' : twistHom TwistTag.D4 K σ.toRingHom g = g := hgF
    refine ⟨bridge.symm ⟨g, hg⟩, ?_, ?_⟩
    · change theta (AutOm.fieldAutP 4 σ (bridge.symm ⟨g, hg⟩)) = bridge.symm ⟨g, hg⟩
      apply (bridge (K := K)).injective
      apply Subtype.ext
      rw [coe_bridge_theta_fieldAutP, MulEquiv.apply_symm_apply]
      exact hgF'
    · change ((bridge (bridge.symm ⟨g, hg⟩) : adjointGroup TwistTag.D4.tag K) :
        ModGL TwistTag.D4.tag K) = g
      rw [MulEquiv.apply_symm_apply]

@[expose] noncomputable def ggFixEquiv (σ : K ≃+* K) :
    ggFix (theta * AutOm.fieldAutP 4 σ) ≃* twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
  ((ggFix (theta * AutOm.fieldAutP 4 σ)).equivMapOfInjective
    ((adjointGroup TwistTag.D4.tag K).subtype.comp (bridge (K := K)).toMonoidHom)
    (Subtype.val_injective.comp (bridge (K := K)).injective)).trans
    (MulEquiv.subgroupCongr (map_ggFix_eq_twistedFixedGroup σ))

end Fixed

section Inputs


theorem ggD4GraphFixQuasisimpleInput_holds : GGD4GraphFixQuasisimpleInput := by
  intro K _ _ _ h3
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hK2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hK3 : 3 ≤ Nat.card K := by
    obtain ⟨m, hm⟩ := h3
    rcases m with _ | m
    · omega
    · omega
  have hθ : (theta : MulAut (Om8 K)) = theta * AutOm.fieldAutP 4 1 := by
    rw [map_one, mul_one]
  have hG2 := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK3
  have e : ggFix (theta : MulAut (Om8 K)) ≃* adjointGroup Tag.G2 K :=
    ((MulEquiv.subgroupCongr (congrArg ggFix hθ)).trans (ggFixEquiv (K := K) 1)).trans
      (CFSG.RankThree.PartTwo.KFacts.d4FixedG2Equiv K h2)
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
    (isQuasisimple_of_mulEquiv e.symm hG2)

theorem ggD4GraphFieldFixQuasisimpleInput_holds : GGD4GraphFieldFixQuasisimpleInput := by
  intro K _ _ _ σ hσ
  obtain ⟨d, hd, hK, r, hr, hσr⟩ := exists_frob_of_orderOf_three σ hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨-, -, hfix, hsimple, x, y, hxy⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group 2 d Nat.prime_two hd K hK
      (AlgebraicClosure K) r hr σ.toRingHom hσr (iterateFrobenius (AlgebraicClosure K) 2 d)
      (fun c => iterateFrobenius_def 2 d c)
  let e : ggFix (theta * AutOm.fieldAutP 4 σ) ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (ggFixEquiv σ).trans (MulEquiv.subgroupCongr hfix)
  have hs : IsSimpleGroup (ggFix (theta * AutOm.fieldAutP 4 σ)) := e.isSimpleGroup
  refine isQuasisimple_of_simple_noncomm hs ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
  have h' := congrArg e h
  simpa only [map_mul, MulEquiv.apply_symm_apply] using h'

end Inputs

end TriBridge

end CFSG.StandardType

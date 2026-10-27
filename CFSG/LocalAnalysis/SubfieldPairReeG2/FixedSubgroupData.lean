module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeG2Outer
public import CFSG.LocalAnalysis.SubfieldPairReeG2.GammaFacts

public section

open CFSG CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.Walter.Ree.Model (smallReeH smallReeU smallReeH_neg_one_mem_reeGamma)

namespace CFSG.LocalAnalysis.SubfieldPairReeG2

section ReeData


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K G2.prime]

theorem torusInvolution_mem_fixedSubgroup (hK : Nat.card K = 3 ^ (2 * a + 1)) (σ : K ≃+* K) :
    (⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ : G2.reeGamma K a) ∈
      fixedSubgroup (G2.reeGammaFieldAut K a σ) :=
  CFSG.ComponentClassification.OutcomeLocal.reeGammaFieldAut_smallReeH hK σ

theorem fixedSubgroup_equiv (hK : Nat.card K = 3 ^ (2 * a + 1)) {β : K ≃+* K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p) :
    ∃ (b : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k G2.prime),
      Nat.card k = 3 ^ (2 * b + 1) ∧
      Nonempty (↥(fixedSubgroup (G2.reeGammaFieldAut K a β)) ≃* G2.reeGamma k b) := by
  obtain ⟨b, -, hk, hchar, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hK hp hp2 hβ
  exact ⟨b, fixSubfield β, inferInstance, inferInstance, hchar, hk, ⟨e⟩⟩

theorem fixedSubgroup_involution_conj (hK : Nat.card K = 3 ^ (2 * a + 1)) {β : K ≃+* K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p) {t : G2.reeGamma K a}
    (htR : t ∈ fixedSubgroup (G2.reeGammaFieldAut K a β)) (ht2 : orderOf t = 2) :
    ∀ u ∈ fixedSubgroup (G2.reeGammaFieldAut K a β), orderOf u = 2 →
      ∃ r ∈ fixedSubgroup (G2.reeGammaFieldAut K a β), r * t * r⁻¹ = u := by
  intro u huR hu2
  obtain ⟨b, k, _, _, _, hkcard, ⟨e⟩⟩ := fixedSubgroup_equiv hK hp hp2 hβ
  let t' : ↥(fixedSubgroup (G2.reeGammaFieldAut K a β)) := ⟨t, htR⟩
  let u' : ↥(fixedSubgroup (G2.reeGammaFieldAut K a β)) := ⟨u, huR⟩
  have ht' : orderOf (e t') = 2 := by
    rw [MulEquiv.orderOf_eq]; exact (Subgroup.orderOf_mk t htR).trans ht2
  have hu' : orderOf (e u') = 2 := by
    rw [MulEquiv.orderOf_eq]; exact (Subgroup.orderOf_mk u huR).trans hu2
  obtain ⟨g, hg⟩ := reeGamma_involution_conj hkcard ht' hu'
  refine ⟨((e.symm g : ↥(fixedSubgroup (G2.reeGammaFieldAut K a β))) : G2.reeGamma K a),
    (e.symm g).2, ?_⟩
  have h1 : e.symm g * t' * (e.symm g)⁻¹ = u' := by
    apply e.injective
    simp [hg]
  exact congrArg Subtype.val h1

theorem exists_eight_subgroup_le_fixedSubgroup (hK : Nat.card K = 3 ^ (2 * a + 1))
    {β : K ≃+* K} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p) :
    ∃ S : Subgroup (G2.reeGamma K a), S ≤ fixedSubgroup (G2.reeGammaFieldAut K a β) ∧
      Nat.card S = 8 ∧ ∀ x ∈ S, x ^ 2 = 1 := by
  classical
  obtain ⟨b, k, _, _, _, hkcard, ⟨e⟩⟩ := fixedSubgroup_equiv hK hp hp2 hβ
  obtain ⟨S₀, h8, hexp⟩ := reeGamma_exists_sylow_two hkcard
  set R := fixedSubgroup (G2.reeGammaFieldAut K a β) with hR
  let SR : Subgroup ↥R := (S₀ : Subgroup (G2.reeGamma k b)).map e.symm.toMonoidHom
  have hSR : Nat.card SR = 8 := by
    rw [Subgroup.card_map_of_injective e.symm.injective]; exact h8
  refine ⟨SR.map R.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective R.subtype_injective]; exact hSR
  · rintro _ ⟨r, ⟨s, hs, rfl⟩, rfl⟩
    have h1 := hexp s hs
    have h2 : (e.symm s) ^ 2 = 1 := by rw [← map_pow, h1, map_one]
    have h3 := congrArg Subtype.val h2
    simpa using h3

theorem exists_sylow_two_le_fixedSubgroup (hK : Nat.card K = 3 ^ (2 * a + 1)) {β : K ≃+* K}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p) :
    ∃ S : Sylow 2 (G2.reeGamma K a),
      (S : Subgroup (G2.reeGamma K a)) ≤ fixedSubgroup (G2.reeGammaFieldAut K a β) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSR, h8, -⟩ := exists_eight_subgroup_le_fixedSubgroup hK hp hp2 hβ
  obtain ⟨T⟩ : Nonempty (Sylow 2 (G2.reeGamma K a)) := inferInstance
  have hT : Nat.card T = 8 := reeGamma_sylow_two_card hK T
  have hTm := Sylow.card_eq_multiplicity T
  refine ⟨Sylow.ofCard S (by rw [h8, ← hTm, hT]), ?_⟩
  rw [Sylow.coe_ofCard]
  exact hSR

theorem exists_kleinFour_le_fixedSubgroup (hK : Nat.card K = 3 ^ (2 * a + 1)) {β : K ≃+* K}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p) :
    ∃ E : Subgroup (G2.reeGamma K a), E ≤ fixedSubgroup (G2.reeGammaFieldAut K a β) ∧
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  classical
  obtain ⟨S, hSR, h8, hexp⟩ := exists_eight_subgroup_le_fixedSubgroup hK hp hp2 hβ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥S) 2 (n := 2)
    (by rw [h8]; norm_num)
  refine ⟨E₀.map S.subtype, (Subgroup.map_subtype_le _).trans hSR, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective S.subtype_injective, hE₀]; norm_num
  · rintro _ ⟨x, -, rfl⟩
    exact hexp x x.2

theorem exists_simple_le_fixedSubgroup (hK : Nat.card K = 3 ^ (2 * a + 1)) {β : K ≃+* K}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p) :
    ∃ W : Subgroup (G2.reeGamma K a), W ≤ fixedSubgroup (G2.reeGammaFieldAut K a β) ∧
      IsSimpleGroup W ∧ (∃ x y : W, x * y ≠ y * x) ∧ ∃ s ∈ W, orderOf s = 2 := by
  classical
  obtain ⟨b, k, _, _, _, hkcard, ⟨e⟩⟩ := fixedSubgroup_equiv hK hp hp2 hβ
  obtain ⟨W₀, hW₀s, ⟨x, y, hxy⟩, ⟨s, hsW, hs2⟩⟩ := reeGamma_exists_simple hkcard
  set R := fixedSubgroup (G2.reeGammaFieldAut K a β) with hR
  let W₁ : Subgroup ↥R := W₀.map e.symm.toMonoidHom
  let W : Subgroup (G2.reeGamma K a) := W₁.map R.subtype
  let e₂ : ↥W₀ ≃* ↥W :=
    (W₀.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (W₁.equivMapOfInjective R.subtype R.subtype_injective)
  refine ⟨W, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · haveI := hW₀s
    exact e₂.symm.isSimpleGroup
  · exact ⟨e₂ x, e₂ y, fun h => hxy (e₂.injective (by rw [map_mul, map_mul]; exact h))⟩
  · refine ⟨((e.symm s : ↥R) : G2.reeGamma K a), ⟨e.symm s, ⟨s, hsW, rfl⟩, rfl⟩, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hs2

end ReeData

end CFSG.LocalAnalysis.SubfieldPairReeG2

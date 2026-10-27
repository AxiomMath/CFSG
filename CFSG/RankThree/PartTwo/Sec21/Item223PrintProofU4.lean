module

public import CFSG.RankThree.PartTwo.Sec21.Item229Orders
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Item47WitnessU4
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223PrintProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

theorem card_projSU_four_ge {m : ℕ} (hm : 2 ≤ m) : 2 ^ 13 ≤ Nat.card (projSU 4 2 m) := by
  rw [card_projSU le_rfl (by omega), ordTwistedA_three_eq (by omega)]
  have hq : 4 ≤ 2 ^ m := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  have h1 : 2 ^ 12 ≤ (2 ^ m) ^ 6 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ≤ ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1) := by
    have a1 : 2 ≤ (2 ^ m) ^ 2 - 1 := by
      have : 16 ≤ (2 ^ m) ^ 2 := by nlinarith
      omega
    have a2 : 1 ≤ (2 ^ m) ^ 3 + 1 := by omega
    have a3 : 1 ≤ (2 ^ m) ^ 4 - 1 := by
      have : 256 ≤ (2 ^ m) ^ 4 := by
        calc 256 = 4 ^ 4 := by norm_num
          _ ≤ (2 ^ m) ^ 4 := Nat.pow_le_pow_left hq 4
      omega
    calc 2 = 2 * 1 * 1 := by norm_num
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul a1 a2) a3
  calc 2 ^ 13 = 2 ^ 12 * 2 := by norm_num
    _ ≤ _ := Nat.mul_le_mul h1 h2

theorem exceptionalOrders_PSU_four {m : ℕ} (hm1 : m ≠ 1) :
    Blueprint.Multiplier.exceptionalOrders .PSU 4 2 m = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem center_eq_bot_of_quotient_projSU_four
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y : Type} [Group Y] (hY : Group.IsPerfect Y) {m : ℕ} (hm : 2 ≤ m)
    (e : Y ⧸ Subgroup.center Y ≃* projSU 4 2 m) : Subgroup.center Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .PSU 4 2 m := by
    refine ⟨Nat.prime_two, by omega, ?_⟩
    change 3 ≤ 4 ∧ (4, 2 ^ m) ≠ (3, 2)
    exact ⟨by norm_num, by simp⟩
  refine KFacts.KS21Mult.center_eq_bot_of_table hGA hY
    (KFacts.KS21Mult.lieModel_of_mulEquiv e (KFacts.KS21Mult.lieModel_projSU hadm)) ?_
    (exceptionalOrders_PSU_four (by omega))
  change (Nat.gcd 4 (2 ^ m + 1), 1) = (1, 1)
  have hodd : Odd (2 ^ m + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have : Nat.Coprime (2 ^ 2) (2 ^ m + 1) := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  rw [show Nat.gcd 4 (2 ^ m + 1) = 1 by simpa using this]

theorem exists_elemAbelian_of_mulEquiv_projSL {G : Type*} [Group G] {X : Subgroup G} {m : ℕ}
    (hm : 1 ≤ m) (e : X ≃* projSL 2 (GaloisField 2 m)) :
    ∃ E : Subgroup G, E ≤ X ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ m := by
  set F := GaloisField 2 m
  have hF : Nat.card F = 2 ^ m := GaloisField.card 2 m (by omega)
  set ι : Multiplicative F →* G :=
    X.subtype.comp (e.symm.toMonoidHom.comp ((projSLTwoEquivSL F).symm.toMonoidHom.comp
      SL2MinimalFaithful.unipotentHom)) with hι
  have hinj : Function.Injective ι :=
    X.subtype_injective.comp (e.symm.injective.comp ((projSLTwoEquivSL F).symm.injective.comp
      SL2MinimalFaithful.unipotentHom_injective))
  have hsq : ∀ t : Multiplicative F, t ^ 2 = 1 := by
    intro t
    apply Multiplicative.toAdd.injective
    rw [sq, toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero]
  refine ⟨ι.range, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact (e.symm _).2
  · obtain ⟨a', ha'⟩ := a.2
    obtain ⟨b', hb'⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha', ← hb', ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hsq, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← hF]
    exact Nat.card_congr Multiplicative.toAdd

theorem not_inducesOuterTheta_of_projSU_four {H : Type} [Group H] [Finite H]
    (hH : SectionFourHyp H) (h3 : 3 ∣ Nat.card (Subgroup.center H)) {L : Subgroup H}
    (hq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) {m : ℕ} (hm : 1 ≤ m)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 2 m) {a : H} (ha3 : a ^ 3 = 1) :
    ¬ Sec4.InducesOuterTheta a L := by
  intro hout
  have : IsSimpleGroup (projSU 4 2 m) := isSimpleGroup_projSU le_rfl hm
  have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq e
  exact Sec4.false_of_hasLocalWitness_inducedAutHom hH h3 ha3 hout hZ e fun ha =>
    Sec4.inputs47Core_witnessU4 m hm _ (KFacts.inducedAutHom_pow_eq_one L e ha ha3)
      ((KFacts.not_isInnerAut_inducedAutHom_iff L e ha).mpr hout)

theorem exists_sub_of_mem_thetaComponentsAt {G : Type} [Group G] [Finite G]
    (hG : TheoremFourHyp G) {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 a) :
    ∃ X' : Subgroup (Subgroup.centralizer ({a} : Set G)),
      SectionFourHyp (Subgroup.centralizer ({a} : Set G)) ∧
      3 ∣ Nat.card (Subgroup.center (Subgroup.centralizer ({a} : Set G))) ∧
      X' ∈ thetaComponents 3 (Subgroup.centralizer ({a} : Set G)) ∧
      X'.map (Subgroup.centralizer ({a} : Set G)).subtype = X := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  obtain ⟨X', hX', rfl⟩ := hX
  have hC4 : SectionFourHyp C := hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG ha1)
  set a' : C := ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with ha'
  have ha'Z : a' ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have ha'o : orderOf a' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime ha3 ha1
  have h3 : 3 ∣ Nat.card (Subgroup.center C) := by
    rw [← ha'o, show orderOf a' = orderOf (⟨a', ha'Z⟩ : Subgroup.center C) from
      (Subgroup.orderOf_mk a' ha'Z).symm]
    exact orderOf_dvd_natCard _
  exact ⟨X', hC4, h3, hX', rfl⟩

theorem not_inducesOuterTheta_of_mem_thetaComponentsAt {G : Type} [Group G] [Finite G]
    (hG : TheoremFourHyp G) {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 a) {m : ℕ} (hm : 1 ≤ m)
    (e : X ⧸ aschbacherSolvableCore 3 X ≃* projSU 4 2 m) {x : G} (hxa : x * a = a * x)
    (hx3 : x ^ 3 = 1) : ¬ Sec4.InducesOuterTheta x X := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  obtain ⟨X', hC4, h3, hX', rfl⟩ := exists_sub_of_mem_thetaComponentsAt hG ha3 ha1 hX
  set x' : C := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr hxa⟩ with hx'
  intro hout
  have hout' : Sec4.InducesOuterTheta x' X' :=
    (Sec8.Item82OneProof.inducesOuterTheta_sub_iff C X' x').mpr hout
  exact not_inducesOuterTheta_of_projSU_four hC4 h3 hX'.2.2 hm
    ((Sec13.thetaQuotEquivSub C X').trans e) (Subtype.ext (by simpa using hx3)) hout'

end CFSG.RankThree.PartTwo.Sec21.Item223PrintProof

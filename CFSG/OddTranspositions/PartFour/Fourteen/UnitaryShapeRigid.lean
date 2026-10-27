module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.Timmesfeld.Bridge.Asc72Defs
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
import CFSG.LieType.Steinberg.CentralExt.SUTwo
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfPSU
import CFSG.LocalAnalysis.WeakClosure81.TimTI.BenderTransv
import CFSG.OddTranspositions.PartFour.Fourteen.SpShapeRigid
import CFSG.OddTranspositions.PartFour.Fourteen.TableMeetsSq
import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
import CFSG.Open.Defs
import CFSG.Open.StatedAPI
import CFSG.RankThree.GF2n.Smith81.InspKSpCard
import CFSG.RankThree.PartOne.S12K.OrdRigid
import CFSG.Timmesfeld.Bridge.Asc72Theorem
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.CGT.Timmesfeld75.Cfg214Gen
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.Form2
import CFSG.CGT.Timmesfeld75.Main
import CFSG.LargeExtraspecial.S9TIXC
import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81

private theorem card_quotient_center_eq_ordTwistedA {X : Type} [Group X] {k f : ℕ}
    {s : X} (hk : 2 ≤ k) (hf : 1 ≤ f) (h : SevenK.IsUnitaryTransvection X k f s) :
    Nat.card (X ⧸ Subgroup.center X) = ordTwistedA (k - 1) (2 ^ f) := by
  obtain ⟨F, _, _, hF, e, -⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU
    Nat.prime_two hf hF hk, ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ k),
    mul_comm (k - 1) k]

private theorem card_quotient_center_eq_ordBC {X : Type} [Group X] {m f : ℕ}
    {s : X} (hf : 1 ≤ f) (h : SevenK.IsSymplecticTransvection X m f s) :
    ∃ j : ℕ, m = 2 * j ∧ Nat.card (X ⧸ Subgroup.center X) = ordBC j (2 ^ f) := by
  obtain ⟨j, hm, F, _, _, hcard, e, -⟩ := h
  refine ⟨j, hm, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.GF2n.Smith81.Insp.KFact.card_statedSp_eq_ordBC hf hcard j

theorem not_isSymplecticTransvection_of_isUnitaryTransvection {X : Type} [Group X] {s s' : X}
    {k f m f' : ℕ} (hk : 3 ≤ k) (hf : 2 ≤ f) (hf' : 2 ≤ f') (hm : 2 ≤ m)
    (h : SevenK.IsUnitaryTransvection X k f s) :
    ¬ SevenK.IsSymplecticTransvection X m f' s' := by
  intro h'
  obtain ⟨j, rfl, hj⟩ := card_quotient_center_eq_ordBC (by omega) h'
  have heq : ordTwistedA (k - 1) (2 ^ f) = ordBC j (2 ^ f') :=
    (card_quotient_center_eq_ordTwistedA (by omega) (by omega) h).symm.trans hj
  rcases Nat.lt_or_ge j 3 with hj3 | hj3
  · obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
    · have h1 : ordBC 1 (2 ^ f') = ordA 1 (2 ^ f') := by simp [ordBC, ordA]
      rw [h1] at heq
      exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA le_rfl (by omega) (by omega) (by omega)
        heq.symm
    · exact CFSG.RankThree.PartOne.S12K.ordTwistedA_ne_ordBC_two (by omega) (by omega)
        (by omega) heq
  · exact CFSG.Timmesfeld.Orders.ordBC_ne_ordTwistedA hj3 (by omega) (by omega) (by omega)
      heq.symm

theorem not_isFiveReflectionModel_of_isUnitaryTransvection {X : Type} [Group X]
    {E : Set X} (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥)
    {s : X} (hs : s ∈ E) {k f : ℕ} (hf : 2 ≤ f) (h : SevenK.IsUnitaryTransvection X k f s)
    {r : ℕ} (hr : 3 ≤ r) {ε π : Bool} : ¬ PartThree.IsFiveReflectionModel r ε π E := by
  intro hM
  obtain ⟨b, hsym, hnd, hM'⟩ := PartThree.fischerModel_of_isFiveReflectionModel hM
  exact not_meetsSq_of_fischerCentralQuotientModel_five (by omega) hsym hnd hM'
    (meetsSq_of_isUnitaryTransvection hcls hZ hs hf h)

section SUTwo

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

private theorem nonempty_mulEquiv_statedSU_two (hF : Nat.card F = (2 ^ f) ^ 2) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield F 2 f) ≃*
      StatedSU 2 (2 ^ f) F) := by
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hF
  exact ⟨(CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
    (CFSG.LieType.Universal.Unitary.equivStatedSU hF 2)⟩

omit [Finite F] in
private theorem statedScalars_subgroupOf_statedSU_two_eq_bot (q : ℕ) :
    (StatedScalars (Fin 2) F).subgroupOf (StatedSU 2 q F) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨(x : GL (Fin 2) F), StatedAPI.statedSU_le_statedSL 2 q F x.2⟩ :
      StatedSL 2 F) ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx)
  rw [StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot, Subgroup.mem_bot] at hx'
  exact Subtype.ext (congrArg (fun y : StatedSL 2 F => (y : GL (Fin 2) F)) hx')

end SUTwo

theorem isSymplecticTransvection_of_isUnitaryTransvection_two {X : Type} [Group X] {f : ℕ}
    {s : X} (h : SevenK.IsUnitaryTransvection X 2 f s) :
    SevenK.IsSymplecticTransvection X 2 f s := by
  obtain ⟨F, _, _, hF, e, g, hg, hr⟩ := h
  have : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := f) hF
  obtain ⟨eSU⟩ := nonempty_mulEquiv_statedSU_two hF
  let F₀ := CFSG.LieType.Steinberg.fixedSubfield F 2 f
  have hF₀ : Nat.card F₀ = 2 ^ f := CFSG.LieType.Steinberg.card_fixedSubfield hF
  have : Fintype F₀ := Fintype.ofFinite F₀
  have : CharP F₀ 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hF₀])
  let eSp : StatedSU 2 (2 ^ f) F ≃* StatedSp 1 F₀ :=
    eSU.symm.trans (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne F₀)
  let eP : StatedProj (StatedSU 2 (2 ^ f) F) ≃* StatedSp 1 F₀ :=
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSU_two_eq_bot (F := F)
      (2 ^ f))).trans (QuotientGroup.quotientBot.trans eSp)
  have hg2 : g * g = 1 := statedSU_mul_self_of_rank_one hF g hr
  have hg1 : g ≠ 1 := by
    rintro rfl
    simp at hr
  refine ⟨1, rfl, F₀, inferInstance, inferInstance, hF₀, e.trans eP, ?_⟩
  have hsg : (e.trans eP) (QuotientGroup.mk s) = eSp g := by
    rw [MulEquiv.trans_apply, ← hg]
    rfl
  rw [hsg]
  exact TimTI.isSymplecticTransvectionIn_one_of_mul_self (by rw [← map_mul, hg2, map_one])
    (fun h1 => hg1 (eSp.injective (h1.trans (map_one eSp).symm)))

theorem isPerfect_statedProj_statedSU {F : Type} [Field F] [Finite F] {k f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hk : 2 ≤ k) (hf : 2 ≤ f) :
    Group.IsPerfect (StatedProj (StatedSU k (2 ^ f) F)) := by
  classical
  have : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := f) hF
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hSU : Group.IsPerfect (StatedSU k (2 ^ f) F) := by
    rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
    · obtain ⟨e⟩ := nonempty_mulEquiv_statedSU_two hF
      have : Fintype (CFSG.LieType.Steinberg.fixedSubfield F 2 f) := Fintype.ofFinite _
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (CFSG.LieType.Steinberg.fixedSubfield F 2 f))) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
          CFSG.LieType.Steinberg.card_fixedSubfield hF]; exact h4)
      have := CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨t, ht⟩
      exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    · refine CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF hk3 fun h => ?_
      have := (Prod.mk.inj h).2
      omega
  exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)

theorem isPerfect_of_isUnitaryTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {k f : ℕ} (hk : 2 ≤ k) (hf : 2 ≤ f)
    (h : SevenK.IsUnitaryTransvection X k f s) : Group.IsPerfect X := by
  obtain ⟨F, _, _, hF, e, -⟩ := h
  have := isPerfect_statedProj_statedSU hF hk hf
  let eX : X ≃* StatedProj (StatedSU k (2 ^ f) F) :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm).trans e
  exact Group.IsPerfect.ofSurjective (f := eX.symm.toMonoidHom) eX.symm.surjective

theorem not_nonempty_mulEquiv_l2Wreath_of_isUnitaryTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {k f : ℕ} (hk : 2 ≤ k) (hf : 2 ≤ f)
    (h : SevenK.IsUnitaryTransvection X k f s) {f' n : ℕ} (hn : 2 ≤ n) :
    ¬ Nonempty (X ≃* CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f' n) := by
  rintro ⟨φ⟩
  have hperf := isPerfect_of_isUnitaryTransvection hZ hk hf h
  exact CFSG.Timmesfeld.Bridge.Asc72.commutator_ne_top_of_l2Wreath hn φ
    hperf.commutator_eq_top

end CFSG.OddTranspositions.PartFour

end

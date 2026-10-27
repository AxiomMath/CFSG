module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSylow
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_11
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorusMatrices
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace CFSG
end CFSG
open CFSG

/-!
# Split tori in PSL(2,q)

This module isolates Huppert II.8.3 and its concrete diagonal/antidiagonal
matrix calculations from the rest of Dickson's classification.
-/

namespace CFSG.Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open BenderSuzuki.External
open scoped Pointwise
open scoped LinearAlgebra.Projectivization

universe u v


/-- Huppert II.8.3(a,c), retaining the Weyl reflection and its inversion
action on the standard split torus. -/
public theorem huppert_II_8_3_split_torus_reflection_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ U : Subgroup (PSL2MatrixGroup F),
      ∃ w : PSL2MatrixGroup F,
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      w ∈ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) ∧
      w ∉ U ∧
      w * w = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ U → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (U ⊔ Subgroup.zpowers w :
        Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card U ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          U ⊔ Subgroup.zpowers w := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hcard_roots :
        Nat.card (rootsOfUnity 2 F) =
          Nat.gcd (Nat.card F - 1) 2 := by
      let e :=
        Equiv.Set.image ((↑) : Fˣ → F) (rootsOfUnity 2 F : Set Fˣ)
          Units.val_injective
      have he :
          Nat.card (rootsOfUnity 2 F) =
            Nat.card (((↑) : Fˣ → F) '' (rootsOfUnity 2 F : Set Fˣ)) :=
        Nat.card_congr e
      rw [Units.val_set_image_rootsOfUnity_two] at he
      by_cases hp_two : p = 2
      · have htwo : (2 : F) = 0 := by
          subst p
          exact CharP.cast_eq_zero F 2
        have hneg_one : (-1 : F) = 1 := by
          apply (neg_eq_iff_add_eq_zero).2
          have hone_add_one : (1 : F) + 1 = 0 := by
            rw [show (1 : F) + 1 = 2 by norm_num, htwo]
          exact hone_add_one
        have hleft : Nat.card (rootsOfUnity 2 F) = 1 := by
          simpa [hneg_one] using he
        have hq_even : Even (Nat.card F) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf_ne_zero
          rw [hFcard, hp_two, hk, pow_succ]
          use 2 ^ k
          ring
        have hq_sub_one_odd : Odd (Nat.card F - 1) := by
          rw [← Nat.not_even_iff_odd]
          intro heven
          have hparity :=
            (Nat.even_sub (show 1 ≤ Nat.card F from (Finite.one_lt_card (α := F)).le)).mp
              heven
          exact Nat.not_even_one (hparity.mp hq_even)
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 :=
          Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
        rw [hleft, hgcd]
      · have hring_char_ne_two : ringChar F ≠ 2 := by
          rw [ringChar.eq F p]
          exact hp_two
        have hneg_one : (-1 : F) ≠ 1 :=
          Ring.neg_one_ne_one_of_char_ne_two hring_char_ne_two
        have hleft : Nat.card (rootsOfUnity 2 F) = 2 := by
          simpa [hneg_one, Ne.symm hneg_one] using he
        have hq_odd : Odd (Nat.card F) := by
          rw [hFcard]
          exact ((Fact.out : p.Prime).odd_of_ne_two hp_two).pow
        have htwo_dvd : 2 ∣ Nat.card F - 1 := by
          rcases hq_odd with ⟨k, hk⟩
          use k
          omega
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
          Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
            (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
        rw [hleft, hgcd]
  let splitTorusSL : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    splitTorusSLHom F
  let splitTorus : Fˣ →* PSL2MatrixGroup F :=
    (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp splitTorusSL
  have hsplit_mem_ker_iff (a : Fˣ) :
      a ∈ splitTorus.ker ↔ a ∈ rootsOfUnity 2 F := by
    rw [MonoidHom.mem_ker, mem_rootsOfUnity]
    constructor
    · intro ha
      have hcenter :
          splitTorusSL a ∈
            Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (QuotientGroup.eq_one_iff (splitTorusSL a)).mp ha
      have hscalar :=
        Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
      have ha_inv_val := congrFun (congrFun hscalar (1 : Fin 2)) (1 : Fin 2)
      have ha_inv : a = a⁻¹ := by
        apply Units.ext
        simpa [splitTorusSL] using ha_inv_val
      simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp ha_inv)
    · intro ha
      apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨(a : F), ?_, ?_⟩
      · simpa using congrArg Units.val ha
      · have ha_inv : a = a⁻¹ :=
          eq_inv_iff_mul_eq_one.mpr (by simpa [pow_two] using ha)
        have ha_inv_val : (a : F) = (a⁻¹ : F) := by
          simpa using congrArg Units.val ha_inv
        simpa [splitTorusSL] using
          splitTorusSLHom_eq_scalar_of_val_eq_inv a ha_inv_val
  have hsplit_ker_eq : splitTorus.ker = rootsOfUnity 2 F := by
    ext a
    exact hsplit_mem_ker_iff a
  have hsplit_ker_card :
      Nat.card splitTorus.ker = Nat.gcd (Nat.card F - 1) 2 := by
    rw [hsplit_ker_eq, hcard_roots]
  have hsplit_range_mul :
      Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F - 1 := by
    calc
      Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          splitTorus.ker.index * Nat.card splitTorus.ker := by
        rw [Subgroup.index_ker, hsplit_ker_card]
      _ = Nat.card Fˣ := splitTorus.ker.index_mul_card
      _ = Nat.card F - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := F))
  have hsplit_range_card :
      Nat.card splitTorus.range =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    apply Nat.eq_div_of_mul_eq_left
    · rw [← hcard_roots]
      exact Nat.ne_of_gt Nat.card_pos
    · exact hsplit_range_mul
  have hsplit_range_cyclic : IsCyclic splitTorus.range := by
    have hUnitsCyclic : IsCyclic Fˣ := by
      let : IsCyclic (⊤ : Subgroup Fˣ) := isCyclic_subgroup_units ⊤
      exact isCyclic_of_surjective
        ((⊤ : Subgroup Fˣ).subtype) (by
          intro a
          exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩)
    let : IsCyclic Fˣ := hUnitsCyclic
    exact isCyclic_of_surjective splitTorus.rangeRestrict
      splitTorus.rangeRestrict_surjective
  let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
    QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) F))
  let splitWeylSL : Matrix.SpecialLinearGroup (Fin 2) F :=
    standardSplitWeylSL F
  let splitWeyl : PSL2MatrixGroup F := qSL splitWeylSL
  have hsplitWeylSL_conj (a : Fˣ) :
      splitWeylSL * splitTorusSL a * splitWeylSL⁻¹ =
        splitTorusSL a⁻¹ := by
    simpa [splitWeylSL, splitTorusSL] using standardSplitWeylSL_conj a
  have hsplitWeylSL_sq_center :
      splitWeylSL * splitWeylSL ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    simpa [splitWeylSL] using standardSplitWeylSL_sq_mem_center F
  have hsplitWeyl_sq : splitWeyl * splitWeyl = 1 := by
    change qSL splitWeylSL * qSL splitWeylSL = 1
    rw [← map_mul]
    change QuotientGroup.mk (splitWeylSL * splitWeylSL) =
      QuotientGroup.mk 1
    apply Quotient.sound
    change QuotientGroup.leftRel
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
        (splitWeylSL * splitWeylSL) 1
    rw [QuotientGroup.leftRel_eq]
    simpa using
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).inv_mem
        hsplitWeylSL_sq_center
  have hsplitWeyl_inv : splitWeyl⁻¹ = splitWeyl := by
    calc
      splitWeyl⁻¹ = splitWeyl⁻¹ * 1 := (mul_one _).symm
      _ = splitWeyl⁻¹ * (splitWeyl * splitWeyl) := by
        rw [hsplitWeyl_sq]
      _ = splitWeyl := by
        rw [← mul_assoc]
        simp
  have hsplitWeyl_conj (a : Fˣ) :
      splitWeyl * splitTorus a * splitWeyl⁻¹ =
        splitTorus a⁻¹ := by
    have hqWsq : qSL (splitWeylSL * splitWeylSL) = 1 := by
      change QuotientGroup.mk (splitWeylSL * splitWeylSL) =
        QuotientGroup.mk 1
      apply Quotient.sound
      change QuotientGroup.leftRel
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
          (splitWeylSL * splitWeylSL) 1
      rw [QuotientGroup.leftRel_eq]
      simpa using
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).inv_mem
          hsplitWeylSL_sq_center
    have hsource :
        splitWeylSL * splitTorusSL a * splitWeylSL =
          (splitWeylSL * splitTorusSL a * splitWeylSL⁻¹) *
            (splitWeylSL * splitWeylSL) := by
      group
    rw [hsplitWeyl_inv]
    change qSL splitWeylSL * qSL (splitTorusSL a) *
        qSL splitWeylSL = qSL (splitTorusSL a⁻¹)
    calc
      qSL splitWeylSL * qSL (splitTorusSL a) *
          qSL splitWeylSL =
          qSL (splitWeylSL * splitTorusSL a * splitWeylSL) := by
            rw [map_mul, map_mul]
      _ = qSL ((splitWeylSL * splitTorusSL a * splitWeylSL⁻¹) *
            (splitWeylSL * splitWeylSL)) :=
        congrArg qSL hsource
      _ = qSL (splitTorusSL a⁻¹ *
            (splitWeylSL * splitWeylSL)) := by
        rw [hsplitWeylSL_conj]
      _ = qSL (splitTorusSL a⁻¹) *
            qSL (splitWeylSL * splitWeylSL) := by rw [map_mul]
      _ = qSL (splitTorusSL a⁻¹) := by rw [hqWsq, mul_one]
  have hsplitWeyl_not_mem : splitWeyl ∉ splitTorus.range := by
    rintro ⟨a, ha⟩
    change qSL (splitTorusSL a) = qSL splitWeylSL at ha
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp ha with
      ⟨z, hz, hzeq⟩
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeq
    change (splitTorusSL a : Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) =
      (splitWeylSL : Matrix (Fin 2) (Fin 2) F) at hmat
    rw [← hscalar] at hmat
    have h01 := congrFun (congrFun hmat (0 : Fin 2)) (1 : Fin 2)
    have hneg_one_zero : (-1 : F) = 0 := by
      simpa [splitTorusSL, splitWeylSL, Matrix.mul_apply] using h01.symm
    exact one_ne_zero (neg_eq_zero.mp hneg_one_zero)
  have hsplitWeyl_mem_normalizer :
      splitWeyl ∈
        Subgroup.normalizer (splitTorus.range : Set (PSL2MatrixGroup F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a⁻¹, (hsplitWeyl_conj a).symm⟩
    · rintro ⟨a, ha⟩
      refine ⟨a⁻¹, ?_⟩
      calc
        splitTorus a⁻¹ =
            splitWeyl⁻¹ *
              (splitWeyl * splitTorus a⁻¹ * splitWeyl⁻¹) *
                splitWeyl := by group
        _ = splitWeyl⁻¹ * splitTorus a * splitWeyl := by
          rw [hsplitWeyl_conj]
          group
        _ = y := by rw [ha]; group
  have hreflection_candidate_data
      (T : Subgroup (PSL2MatrixGroup F)) (w : PSL2MatrixGroup F)
      (hw_normalizer : w ∈ Subgroup.normalizer (T : Set _))
      (hw_sq : w * w = 1) (hw_not_mem : w ∉ T) :
      Nat.card (Subgroup.zpowers w) = 2 ∧
        Disjoint T (Subgroup.zpowers w) ∧
        Nat.card (T ⊔ (Subgroup.zpowers w : Subgroup (PSL2MatrixGroup F)) : Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card T := by
    let Z : Subgroup (PSL2MatrixGroup F) := Subgroup.zpowers w
    have hw_ne_one : w ≠ 1 := by
      intro hw_one
      apply hw_not_mem
      rw [hw_one]
      exact Subgroup.one_mem T
    have hw_zpowers_card : Nat.card Z = 2 := by
      change Nat.card (Subgroup.zpowers w) = 2
      rw [Nat.card_zpowers]
      have hw_pow : w ^ 2 = 1 := by
        simpa [pow_two] using hw_sq
      have hord_dvd : orderOf w ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hw_pow
      rcases (Nat.dvd_prime Nat.prime_two).mp hord_dvd with hord | hord
      · exact False.elim (hw_ne_one (orderOf_eq_one_iff.mp hord))
      · exact hord
    have hdisjoint : Disjoint T Z := by
      let R : Subgroup Z := T.comap Z.subtype
      let : Fact (Nat.card Z).Prime := ⟨by
        rw [show Nat.card Z = 2 by exact hw_zpowers_card]
        exact Nat.prime_two⟩
      rcases R.eq_bot_or_eq_top_of_prime_card with hR | hR
      · rw [disjoint_iff, eq_bot_iff]
        intro x hx
        have hxR : (⟨x, hx.2⟩ : Z) ∈ R := hx.1
        rw [hR] at hxR
        have hxone : (⟨x, hx.2⟩ : Z) = 1 := by simpa using hxR
        exact congrArg Subtype.val hxone
      · exfalso
        apply hw_not_mem
        have hwR : (⟨w, Subgroup.mem_zpowers w⟩ : Z) ∈ R := by
          rw [hR]
          simp
        exact hwR
    let D : Subgroup (PSL2MatrixGroup F) := T ⊔ Z
    have hD_le_normalizer : D ≤ Subgroup.normalizer (T : Set _) := by
      apply sup_le Subgroup.le_normalizer
      exact Subgroup.zpowers_le.2 hw_normalizer
    let TD : Subgroup D := T.subgroupOf D
    let ZD : Subgroup D := Z.subgroupOf D
    let : TD.Normal := by
      change (T.subgroupOf D).Normal
      exact Subgroup.normal_subgroupOf_of_le_normalizer hD_le_normalizer
    have hTDZD : Disjoint TD ZD := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hxAmbient : (x : PSL2MatrixGroup F) ∈ T ⊓ Z := by
        change (x : PSL2MatrixGroup F) ∈ T ∧ (x : PSL2MatrixGroup F) ∈ Z
        exact ⟨hx.1, hx.2⟩
      have hxone : (x : PSL2MatrixGroup F) = 1 := by
        rw [hdisjoint.eq_bot] at hxAmbient
        simpa using hxAmbient
      apply Subtype.ext
      exact hxone
    have hsup : TD ⊔ ZD = ⊤ := by
      change T.subgroupOf D ⊔ Z.subgroupOf D = ⊤
      rw [← Subgroup.subgroupOf_sup (show T ≤ D from le_sup_left)
        (show Z ≤ D from le_sup_right)]
      exact Subgroup.subgroupOf_self D
    have hZD_le_normalizer : ZD ≤ Subgroup.normalizer (TD : Set D) := by
      rw [Subgroup.normalizer_eq_top TD]
      exact le_top
    have hmul : (ZD : Set D) * (TD : Set D) = Set.univ := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right ZD TD
        hZD_le_normalizer, sup_comm, hsup]
      rfl
    have hcomp : ZD.IsComplement' TD :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hTDZD.symm hmul
    have hZDcard : Nat.card ZD = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Z ≤ D from le_sup_right)).toEquiv
    have hTDcard : Nat.card TD = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show T ≤ D from le_sup_left)).toEquiv
    refine ⟨hw_zpowers_card, hdisjoint, ?_⟩
    calc
      Nat.card (T ⊔ Z : Subgroup (PSL2MatrixGroup F)) = Nat.card D := rfl
      _ = Nat.card ZD * Nat.card TD := hcomp.card_mul_card.symm
      _ = 2 * Nat.card T := by
        rw [hZDcard, hTDcard, hw_zpowers_card]
  let splitWeylZ : Subgroup (PSL2MatrixGroup F) := Subgroup.zpowers splitWeyl
  rcases hreflection_candidate_data splitTorus.range splitWeyl
      hsplitWeyl_mem_normalizer hsplitWeyl_sq hsplitWeyl_not_mem with
    ⟨hsplitWeyl_zpowers_card, hsplit_torus_zpowers_disjoint,
      hsplitCandidate_card_raw⟩
  have hsplitCandidate_card :
      Nat.card (splitTorus.range ⊔ splitWeylZ : Subgroup (PSL2MatrixGroup F)) =
        2 * ((Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) := by
    have hraw :
        Nat.card (splitTorus.range ⊔ splitWeylZ : Subgroup (PSL2MatrixGroup F)) =
          2 * Nat.card splitTorus.range := by
      simpa [splitWeylZ] using hsplitCandidate_card_raw
    rw [hsplit_range_card] at hraw
    exact hraw
  have hsplit_normalizer_sub_candidate
      (R : Subgroup (PSL2MatrixGroup F))
      (hR_le : R ≤ splitTorus.range) (hR_ne : R ≠ ⊥) :
      Subgroup.normalizer (R : Set _) ≤
        splitTorus.range ⊔ splitWeylZ := by
    obtain ⟨r, hr_ne_one⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne
    rcases hR_le r.property with ⟨a, ha⟩
    have ha_not_ker : a ∉ splitTorus.ker := by
      intro hak
      apply hr_ne_one
      apply Subtype.ext
      change (r : PSL2MatrixGroup F) = 1
      rw [← ha]
      exact hak
    have ha_ne_inv : (a : F) ≠ (a⁻¹ : F) := by
      intro hai
      apply ha_not_ker
      apply (hsplit_mem_ker_iff a).2
      rw [mem_rootsOfUnity]
      have haiU : a = a⁻¹ := by
        apply Units.ext
        simpa using hai
      simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp haiU)
    intro g
    refine QuotientGroup.induction_on g ?_
    intro A hA_normalizes
    have hr_conj_R :
        qSL A * (r : PSL2MatrixGroup F) * (qSL A)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hA_normalizes
        (r : PSL2MatrixGroup F)).mp r.property
    rcases hR_le hr_conj_R with ⟨b, hb⟩
    have hq :
        qSL (splitTorusSL b) = qSL (A * splitTorusSL a * A⁻¹) := by
      simpa [splitTorus, qSL, ← ha] using hb
    rcases (QuotientGroup.mk'_eq_mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA :
        splitTorusSL b * z * A = A * splitTorusSL a := by
      calc
        splitTorusSL b * z * A =
            (A * splitTorusSL a * A⁻¹) * A := by rw [hzeq]
        _ = A * splitTorusSL a := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeqA
    change (!![(b : F), 0; 0, (b⁻¹ : F)] :
          Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) *
          (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) *
        !![(a : F), 0; 0, (a⁻¹ : F)] at hmat
    rw [← hscalar] at hmat
    rcases split_matrix_diag_or_antidiag A a b
        ((z : Matrix (Fin 2) (Fin 2) F) 0 0)
        ha_ne_inv hmat with hdiag | hanti
    · rcases hdiag with ⟨h01, h10⟩
      obtain ⟨u, hAeq⟩ :=
        eq_splitTorusSLHom_of_offDiagonal_eq_zero A h01 h10
      have hAeq : A = splitTorusSL u := by
        simpa [splitTorusSL] using hAeq
      rw [hAeq]
      exact (show splitTorus.range ≤
        splitTorus.range ⊔ splitWeylZ from le_sup_left)
          ⟨u, rfl⟩
    · rcases hanti with ⟨h00, h11⟩
      obtain ⟨u, hAeq⟩ :=
        eq_standardSplitWeylSL_mul_splitTorusSLHom_of_diagonal_eq_zero
          A h00 h11
      have hAeq : A = splitWeylSL * splitTorusSL u := by
        simpa [splitWeylSL, splitTorusSL] using hAeq
      have hw :
          splitWeyl ∈
            splitTorus.range ⊔ splitWeylZ :=
        (show splitWeylZ ≤
          splitTorus.range ⊔ splitWeylZ from le_sup_right)
            (Subgroup.mem_zpowers splitWeyl)
      have hu :
          splitTorus u ∈
            splitTorus.range ⊔ splitWeylZ :=
        (show splitTorus.range ≤
          splitTorus.range ⊔ splitWeylZ from le_sup_left)
            ⟨u, rfl⟩
      change qSL A ∈ splitTorus.range ⊔ splitWeylZ
      rw [hAeq, map_mul]
      exact (splitTorus.range ⊔ splitWeylZ).mul_mem hw hu
  have hsplit_normalizer_eq_candidate
      (R : Subgroup (PSL2MatrixGroup F))
      (hR_le : R ≤ splitTorus.range) (hR_ne : R ≠ ⊥) :
      Subgroup.normalizer (R : Set _) =
        splitTorus.range ⊔ splitWeylZ := by
    apply le_antisymm
    · exact hsplit_normalizer_sub_candidate R hR_le hR_ne
    · apply sup_le
      · intro t ht
        have hsplit_comm {x y : PSL2MatrixGroup F}
            (hx : x ∈ splitTorus.range)
            (hy : y ∈ splitTorus.range) : Commute x y := by
          rcases hx with ⟨a, rfl⟩
          rcases hy with ⟨b, rfl⟩
          change splitTorus a * splitTorus b =
            splitTorus b * splitTorus a
          simp only [← map_mul]
          rw [mul_comm]
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hcomm := hsplit_comm ht (hR_le hy)
          simpa [hcomm.eq, mul_assoc] using hy
        · intro hy
          have hy' : y = t⁻¹ * (t * y * t⁻¹) * t := by
            simp [mul_assoc]
          have hconjR : t * y * t⁻¹ ∈ R := hy
          have hcomm := hsplit_comm
            (splitTorus.range.inv_mem ht) (hR_le hconjR)
          have hfixed :
              t⁻¹ * (t * y * t⁻¹) * t = t * y * t⁻¹ := by
            calc
              t⁻¹ * (t * y * t⁻¹) * t =
                  (t * y * t⁻¹) * t⁻¹ * t := by rw [hcomm.eq]
              _ = t * y * t⁻¹ := by group
          rw [hy', hfixed]
          exact hconjR
      · apply Subgroup.zpowers_le.2
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rcases hR_le hy with ⟨a, ha⟩
          have hy_inv : y⁻¹ ∈ R := R.inv_mem hy
          have hconj :
              splitWeyl * y * splitWeyl⁻¹ = y⁻¹ := by
            rw [← ha]
            simpa using hsplitWeyl_conj a
          rw [hconj]
          exact hy_inv
        · intro hy
          have hyT :
              splitWeyl * y * splitWeyl⁻¹ ∈ splitTorus.range :=
            hR_le hy
          rcases hyT with ⟨a, ha⟩
          have hrecover : y = splitTorus a⁻¹ := by
            calc
              y = splitWeyl⁻¹ *
                  (splitWeyl * y * splitWeyl⁻¹) * splitWeyl := by
                    simp [mul_assoc]
              _ = splitWeyl⁻¹ * splitTorus a * splitWeyl := by
                    rw [← ha]
              _ = splitTorus a⁻¹ := by
                calc
                  splitWeyl⁻¹ * splitTorus a * splitWeyl =
                      splitWeyl⁻¹ *
                        (splitWeyl * splitTorus a⁻¹ * splitWeyl⁻¹) *
                          splitWeyl := by rw [hsplitWeyl_conj]; simp
                  _ = splitTorus a⁻¹ := by simp [mul_assoc]
          have hy_inv :
              (splitWeyl * y * splitWeyl⁻¹)⁻¹ ∈ R := R.inv_mem hy
          rw [hrecover]
          rw [← ha] at hy_inv
          simpa using hy_inv
  refine ⟨splitTorus.range, splitWeyl, hsplit_range_cyclic,
    hsplit_range_card, hsplitWeyl_mem_normalizer, hsplitWeyl_not_mem,
    hsplitWeyl_sq, ?_, ?_, ?_⟩
  · intro t ht
    rcases ht with ⟨a, rfl⟩
    simpa using hsplitWeyl_conj a
  · simpa [splitWeylZ] using hsplitCandidate_card_raw
  · intro R hR hRne
    simpa [splitWeylZ] using
      hsplit_normalizer_eq_candidate R hR hRne

/-- Huppert II.8.3(a,c), in the normalizer-card form used in II.8.22. -/
public theorem huppert_II_8_3_split_torus_normalizer_card
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ U : Subgroup (PSL2MatrixGroup F),
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Nat.card (Subgroup.normalizer (R : Set (PSL2MatrixGroup F))) =
          2 * Nat.card U := by
  obtain ⟨U, w, hUcyclic, hUcard, _hwN, _hwU, _hwsq, _hwinv,
      hcandidate_card, hnormalizer⟩ :=
    huppert_II_8_3_split_torus_reflection_data hFcard
  refine ⟨U, hUcyclic, hUcard, ?_⟩
  intro R hR hRne
  rw [hnormalizer R hR hRne, hcandidate_card]


end Dickson
end CFSG.Glauberman

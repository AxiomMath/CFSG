module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.Open.StatedDefs
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitComm
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Open.StatedAPI
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU)

private theorem typeGU_commutator_le_heldSU {r : ℕ} {E : Type} [Field E] {τ : E ≃+* E}
    {hτ : ∀ y, τ (τ y) = y} :
    ⁅(heldGU r E τ hτ : Subgroup (GL (Fin r) E)), heldGU r E τ hτ⁆ ≤ heldSU r E τ hτ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_heldSU hx hy

private noncomputable def typeGU_commutator_equiv_self {G : Type} [Group G] (A : Subgroup G) :
    ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
  (Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))

private theorem typeGU_isSolvable_commutator_of_isSolvable_heldSU {r : ℕ} {E : Type} [Field E]
    {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y} (h : Group.IsSolvable ↥(heldSU r E τ hτ)) :
    Group.IsSolvable ↥(commutator (heldGU r E τ hτ)) := by
  haveI := h
  have hle := typeGU_commutator_le_heldSU (r := r) (E := E) (τ := τ) (hτ := hτ)
  haveI : Group.IsSolvable ↥⁅(heldGU r E τ hτ : Subgroup (GL (Fin r) E)), heldGU r E τ hτ⁆ :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact Group.isSolvable_of_surjective
    (f := (typeGU_commutator_equiv_self (heldGU r E τ hτ)).symm.toMonoidHom)
    (typeGU_commutator_equiv_self (heldGU r E τ hτ)).symm.surjective

theorem GGNbrLSideKit.commutator_heldGU_eq_heldSU_of_isPerfect {r : ℕ} {E : Type} [Field E]
    {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y} (hperf : Group.IsPerfect ↥(heldSU r E τ hτ)) :
    ⁅(heldGU r E τ hτ : Subgroup (GL (Fin r) E)), heldGU r E τ hτ⁆ = heldSU r E τ hτ := by
  refine le_antisymm ?_ ?_
  · exact typeGU_commutator_le_heldSU
  · rw [← Subgroup.isPerfect_iff.mp hperf]
    exact Subgroup.commutator_mono inf_le_left inf_le_left

theorem GGNbrLSideKit.lieModel_commutator_heldGU {n r : ℕ} {K E : Type} [Field K] [Finite K]
    [Field E] [Finite E] {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hEc : Nat.card E = Nat.card K ^ 2)
    (hτQ : ∀ y, τ y = y ^ Nat.card K)
    (hq : CFSG.IsQuasisimple ↥(commutator (heldGU r E τ hτ))) :
    ∃ (t : StatedLieTag) (m : ℕ), ((t = .PSU ∧ m = r) ∨ (t = .PSL ∧ m = 2)) ∧
      CFSG.Blueprint.LieModel
        (↥(commutator (heldGU r E τ hτ)) ⧸
          Subgroup.center ↥(commutator (heldGU r E τ hτ))) t m 2 n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEcard : Nat.card E = (2 ^ n) ^ 2 := by rw [hEc, hK]
  have hτn : ∀ x, τ x = x ^ 2 ^ n := fun x => by rw [hτQ x, hK]
  haveI : CharP E 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hEcard
  have hq_notsolv : ¬ Group.IsSolvable ↥(commutator (heldGU r E τ hτ)) := by
    haveI : Nontrivial ↥(commutator (heldGU r E τ hτ)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hq
    haveI : Group.IsPerfect ↥(commutator (heldGU r E τ hτ)) := hq.1
    exact Group.IsPerfect.not_isSolvable ↥(commutator (heldGU r E τ hτ))
  have hr2 : 2 ≤ r := by
    by_contra hlt
    have hrle : r ≤ 1 := by omega
    have hsolSU : Group.IsSolvable ↥(heldSU r E τ hτ) := by
      have hcomm : ∀ a b : ↥(heldSU r E τ hτ), a * b = b * a := by
        intro a b
        exact Subtype.ext (CFSG.LieType.SemisimpleCentralizers.Held.mul_comm_GL_of_le_one
          (M := E) hrle (a : GL (Fin r) E) (b : GL (Fin r) E))
      exact Group.isSolvable_of_comm hcomm
    exact hq_notsolv (typeGU_isSolvable_commutator_of_isSolvable_heldSU hsolSU)
  have hbad : ¬ (r = 3 ∧ Nat.card K = 2) := by
    rintro ⟨rfl, hK2⟩
    have hEcard31 : Nat.card E = (2 ^ 1) ^ 2 := by rw [hEc, hK2]; norm_num
    have hcard : Nat.card (StatedSU 3 (2 ^ 1) E) = 216 := by
      rw [CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two hEcard31]
      norm_num
    haveI hsol : Group.IsSolvable ↥(heldSU 3 E τ hτ) := by
      rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ, hK2]
      exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
        (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
        (by
          have h216 : Nat.card ↥(StatedSU 3 2 E) = 216 := by simpa using hcard
          rw [h216]; norm_num)
    exact hq_notsolv (typeGU_isSolvable_commutator_of_isSolvable_heldSU hsol)
  have hQ4or : 4 ≤ Nat.card K ∨ 3 ≤ r := by
    by_cases hr3 : 3 ≤ r
    · exact Or.inr hr3
    · left
      have hr : r = 2 := by omega
      subst hr
      by_contra hlt
      have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
      have hQ2 : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
      have hcard : Nat.card (StatedSU 2 (Nat.card K) E) =
          Nat.card K * (Nat.card K ^ 2 - 1) := by
        rw [hK]
        exact CFSG.RankThree.SubgroupLists.card_statedSU_two (K := E) (r := 2) (f := n) hEcard
      have hsolSU : Group.IsSolvable ↥(heldSU 2 E τ hτ) := by
        rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ]
        rcases hQ2 with h | h
        · exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
            (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
            (by rw [hcard, h]; norm_num)
        · exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
            (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
            (by rw [hcard, h]; norm_num)
      exact hq_notsolv (typeGU_isSolvable_commutator_of_isSolvable_heldSU hsolSU)
  have ham : (r, 2 ^ n) ≠ (3, 2) := by
    intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact hbad ⟨h1, by rw [hK, h2]⟩
  have hperfSU : Group.IsPerfect ↥(heldSU r E τ hτ) := by
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · have hr : r = 2 := by omega
      subst hr
      have hQ4 : 4 ≤ Nat.card K := by rcases hQ4or with h | h <;> omega
      have hq4 : 4 ≤ 2 ^ n := by rw [← hK]; exact hQ4
      rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ, hK]
      exact CFSG.RankThree.SubgroupLists.isPerfect_statedSU_two hEcard hq4
    · rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ, hK]
      exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hEcard hr3 ham
  have hcomm_eq := GGNbrLSideKit.commutator_heldGU_eq_heldSU_of_isPerfect (r := r) (E := E)
    (τ := τ) (hτ := hτ) hperfSU
  have e : ↥(commutator (heldGU r E τ hτ)) ≃* ↥(heldSU r E τ hτ) :=
    (typeGU_commutator_equiv_self (heldGU r E τ hτ)).trans (MulEquiv.subgroupCongr hcomm_eq)
  obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv e
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  ·
    have hr : r = 2 := by omega
    subst hr
    have hQ4 : 4 ≤ Nat.card K := by rcases hQ4or with h | h <;> omega
    obtain ⟨k, hkfield, hkfin, hkcard, ⟨ψ⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_quot_heldSU_two_equiv_psl τ hτ hτn hEcard
    refine ⟨.PSL, 2, Or.inr ⟨rfl, rfl⟩, Or.inl ⟨by decide, ?_⟩⟩
    refine ⟨⟨Nat.prime_two, hn, le_rfl, ?_, ?_⟩, k, hkfield, hkfin, hkcard, ⟨eZ.trans ψ⟩⟩
    · intro h
      have h2 : 2 ^ n = 2 := (Prod.mk.inj h).2
      have h4 : 4 ≤ 2 ^ n := by rw [← hK]; exact hQ4
      omega
    · intro h
      have h3 : 2 ^ n = 3 := (Prod.mk.inj h).2
      have hdvd : 2 ∣ 3 := by rw [← h3]; exact dvd_pow_self 2 (by omega)
      norm_num at hdvd
  ·
    obtain ⟨ψ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ hτ hτn hEcard hr3 ham
    refine ⟨.PSU, r, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨by decide, ?_⟩⟩
    exact ⟨⟨Nat.prime_two, hn, hr3, ham⟩, E, inferInstance, inferInstance, hEcard, ⟨eZ.trans ψ⟩⟩

theorem ggNbrLSideSp_typeGU {n : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {A : Subgroup G} {r : ℕ}
    {E : Type} [Field E] [Finite E] {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hEc : Nat.card E = Nat.card K ^ 2)
    (hτQ : ∀ y, τ y = y ^ Nat.card K) (φ : ↥A ≃* heldGU r E τ hτ)
    (hq : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    ∃ (t : StatedLieTag) (m : ℕ), ((t = .PSU ∧ m = r) ∨ (t = .PSL ∧ m = 2)) ∧
      CFSG.Blueprint.LieModel (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) t m 2 n := by
  have hqB : CFSG.IsQuasisimple ↥(commutator (heldGU r E τ hτ)) :=
    (GGNbrLSideKit.quasisimple_commutator_iff φ).1 hq
  obtain ⟨t, m, htm, hmodel⟩ := GGNbrLSideKit.lieModel_commutator_heldGU hK hn hEc hτQ hqB
  exact ⟨t, m, htm, GGNbrLSideKit.lieModel_quot_commutator_of_mulEquiv φ hmodel⟩

end CFSG.StandardType

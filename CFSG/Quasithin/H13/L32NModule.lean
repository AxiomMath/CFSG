module

public import CFSG.Quasithin.H13.L32NItems143
public import CFSG.Quasithin.Recognition.HSTypeModels
public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.Vol2.Ch12Sec8OneExist
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.Quasithin.H13.A6NotU33
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Quasithin.Background.F420Orders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint HSType
open scoped IsMulCommutative

theorem card_of_lieModel_PSU_three_three {X : Type} [Group X] (h : LieModel X .PSU 3 3 1) :
    Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three (h.statedClassicalModel (by decide))

theorem card_eq_of_surjective_of_isSimpleGroup {S A : Type*} [Group S] [Group A]
    [IsSimpleGroup S] (π : S →* A) (hπ : Function.Surjective π) (hA : Nontrivial A) :
    Nat.card A = Nat.card S := by
  have hker : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha⟩ := exists_ne (1 : A)
      obtain ⟨s, rfl⟩ := hπ a
      exact ha (π.mem_ker.mp (h ▸ Subgroup.mem_top s))
  exact (Nat.card_eq_of_bijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp hker, hπ⟩).symm

variable {G : Type} [Group G]

theorem not_five_dvd_card_autOn [Finite G] {L V : Subgroup G}
    (hlin : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) : ¬ 5 ∣ Nat.card (autOn L V) := by
  intro h5
  rw [card_autOn_eq_relIndex hLV] at h5
  have hdvd := Subgroup.relIndex_dvd_card (L ⊓ Subgroup.centralizer (V : Set G)) L
  have hL : Nat.card ↥L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hlin
  rw [Nat.card_congr e.toEquiv, card_SL_three_two] at hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  rw [hk] at hL
  have h5L : 5 ∣ 168 * 2 ^ k := hL ▸ h5.trans hdvd
  have hp5 : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul hp5).mp h5L with h | h
  · norm_num at h
  · have := Nat.Prime.dvd_of_dvd_pow hp5 h
    norm_num at this

theorem card_autOn_of_alt [Finite G] {L V : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (hne : autOn L V ≠ ⊥) (π : ↥(alternatingGroup (Fin n)) →* ↥(autOn L V))
    (hπ : Function.Surjective π) : Nat.card (autOn L V) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  rw [card_eq_of_surjective_of_isSimpleGroup π hπ
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hne), nat_card_alternatingGroup, Nat.card_fin]

theorem modules13_3_2_of_L32 [Finite G] {L V : Subgroup G} [IsMulCommutative ↥V]
    (hlin : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hne : ¬ L ≤ Subgroup.centralizer (V : Set G))
    (h : Modules13_3_2 L V) :
    BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1 ∧ V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hA := autOn_ne_bot_of_not_le_centralizer hLV hne
  have h5 := not_five_dvd_card_autOn hlin hLV
  rcases h with ⟨⟨π, hπ, -⟩, -⟩ | ⟨⟨π, hπ, -⟩, -⟩ | ⟨-, -, ⟨π, hπ, -⟩⟩ | hd | ⟨he, -⟩
  · rw [card_autOn_of_alt (by norm_num) hA π hπ] at h5
    exact absurd (by decide) h5
  · rw [card_autOn_of_alt (by norm_num) hA π hπ] at h5
    exact absurd (by decide) h5
  · rw [card_autOn_of_alt (by norm_num) hA π hπ] at h5
    exact absurd (by decide) h5
  · exact hd.2
  · obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hlin
    have h1 := card_of_lieModel_PSU_three_three he
    rw [Nat.card_congr e.toEquiv, card_SL_three_two] at h1
    norm_num at h1

theorem stmt13_3_2_two_of_stmt13_3_2 (h : Stmt13_3_2) : Stmt13_3_2_two :=
  fun G _ _ T L hL K hK => (h G T L hL K hK).2.1

theorem stmtL32NModule_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    StmtL32NModule := by
  intro G _ _ T L V hyp hF
  have hL := h1332 G T L hyp.h13 L hyp.h13.faithful
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hL.2.1.1
  have hcc : conjClosure L T = L :=
    le_antisymm
      (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (hTL ht) l).1 hl)
      (le_conjClosure L T)
  have hIrr : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V := by
    have := hF.irrPlus
    rwa [hcc] at this
  obtain ⟨-, hTV, -, hc, hmod⟩ := hL.2.2.1.2 V hIrr
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hIrr.2.2.1
  have hne : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    have h1 : ⁅V, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
    exact hIrr.2.1 (hIrr.2.2.2.1.symm.trans h1)
  obtain ⟨hnat, hCV⟩ := modules13_3_2_of_L32 hyp.linear hLV hne hmod
  obtain ⟨hcard, hsq⟩ := card_and_sq_of_binaryNaturalSL hnat
  obtain ⟨⟨-, hV1, -⟩, -, -⟩ := h1334 G T L V hyp.h13 hIrr
  refine ⟨⟨hc, fun v hv => ?_⟩, hcard, sup_le hLV hTV, ?_, hc, hnat⟩
  · simpa using congrArg Subtype.val (hsq ⟨v, hv⟩)
  · rw [hV1, hCV, Subgroup.card_bot]

end CFSG.Quasithin.H13

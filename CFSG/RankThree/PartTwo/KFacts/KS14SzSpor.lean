module

public import CFSG.RankThree.PartTwo.KFacts.KS14SzSporTwo
public import CFSG.RankThree.PartTwo.KFacts.KS14SzSporMulti
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterM
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterB
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterFi23
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterFi24
public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.Bridge.M22
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open TauCeti CFSG.Blueprint

theorem three_dvd_card_of_card_eq_three_pow {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    {r : ℕ} (hr : 1 ≤ r) (hE : Nat.card E = 3 ^ r) : 3 ∣ Nat.card G :=
  (dvd_pow_self 3 (by omega)).trans (hE ▸ Subgroup.card_subgroup_dvd_card E)

theorem sporThreeDvd_M : SporThreeDvd .M := by
  intro G _ _ _ hnab ⟨e⟩
  obtain ⟨E, -, hE⟩ :=
    CFSG.QuasithinUnique.SQTK.exists_isElemAbelian_three_of_mulEquiv_M e hnab (r := 1)
      (by norm_num)
  exact three_dvd_card_of_card_eq_three_pow le_rfl hE

theorem sporThreeDvd_B : SporThreeDvd .B := by
  intro G _ _ _ hnab ⟨e⟩
  obtain ⟨E, -, hE⟩ :=
    CFSG.QuasithinUnique.SQTK.exists_isElemAbelian_three_of_mulEquiv_B e hnab (r := 1)
      (by norm_num)
  exact three_dvd_card_of_card_eq_three_pow le_rfl hE

theorem sporThreeDvd_Fi23 : SporThreeDvd .Fi23 := by
  intro G _ _ _ hnab ⟨e⟩
  obtain ⟨E, -, hE⟩ :=
    CFSG.QuasithinUnique.SQTK.exists_isElemAbelian_three_pow_three_of_mulEquiv_Fi23 e hnab
  exact three_dvd_card_of_card_eq_three_pow (by norm_num) hE

theorem sporThreeDvd_Fi24Prime : SporThreeDvd .Fi24Prime := by
  intro G _ _ _ hnab ⟨e⟩
  obtain ⟨E, -, hE⟩ :=
    CFSG.QuasithinUnique.SQTK.exists_isElemAbelian_three_of_mulEquiv_Fi24Prime e hnab (r := 1)
      (by norm_num)
  exact three_dvd_card_of_card_eq_three_pow le_rfl hE

theorem three_dvd_card_of_mulEquiv_subgroup {α G : Type*} [Group α] [Group G] [Finite G]
    {H : Subgroup α} (e : G ≃* H) {w : α} (hw : w ∈ H) (h3 : w ^ 3 = 1) (h1 : w ≠ 1) :
    3 ∣ Nat.card G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (⟨w, hw⟩ : H) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using h3)) fun h => h1 (congrArg Subtype.val h)
  rw [← ho, ← MulEquiv.orderOf_eq e.symm]
  exact orderOf_dvd_natCard _

abbrev m11A : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]

abbrev m11B : Equiv.Perm (Fin 11) := List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]

theorem m11_word_pow_three :
    (m11A * m11B * m11B * m11A * m11B * m11B) ^ 3 = 1 ∧
      m11A * m11B * m11B * m11A * m11B * m11B ≠ 1 := by
  decide +kernel

theorem m11_word_mem :
    m11A * m11B * m11B * m11A * m11B * m11B ∈ NativeSporadic.M11 := by
  have ha : m11A ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m11B ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ha hb) hb) ha) hb) hb

theorem sporThreeDvd_M11 : SporThreeDvd .M11 := by
  intro G _ _ _ _ ⟨e⟩
  obtain ⟨φ⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact three_dvd_card_of_mulEquiv_subgroup (e.trans φ.symm) m11_word_mem m11_word_pow_three.1
    m11_word_pow_three.2

abbrev pm22A : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

abbrev pm22B : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem m22_word_pow_three :
    (pm22A * pm22B * pm22A * pm22B * pm22A * pm22B⁻¹ * pm22A * pm22B⁻¹) ^ 3 = 1 ∧
      pm22A * pm22B * pm22A * pm22B * pm22A * pm22B⁻¹ * pm22A * pm22B⁻¹ ≠ 1 := by
  decide +kernel

theorem m22_word_mem :
    pm22A * pm22B * pm22A * pm22B * pm22A * pm22B⁻¹ * pm22A * pm22B⁻¹ ∈ NativeSporadic.M22 := by
  have ha : pm22A ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : pm22B ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hbi := inv_mem hb
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ha hb) ha) hb) ha) hbi)
    ha) hbi

theorem sporThreeDvd_M22 : SporThreeDvd .M22 := by
  intro G _ _ _ _ ⟨e⟩
  obtain ⟨φ⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  exact three_dvd_card_of_mulEquiv_subgroup (e.trans φ.symm) m22_word_mem m22_word_pow_three.1
    m22_word_pow_three.2

theorem sporThreeDvd (s : SporadicName) : SporThreeDvd s := by
  cases s with
  | M11 => exact sporThreeDvd_M11
  | M12 => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => m12_commute h3 e
  | M22 => exact sporThreeDvd_M22
  | M23 => exact sporThreeDvd_of_commute _ fun G _ _ _ hnab h3 e => m23_commute hnab h3 e
  | M24 => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => m24_commute h3 e
  | J1 => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => j1_commute h3 e
  | J2 => exact sporThreeDvd_of_commute _ fun G _ _ _ hnab h3 e => j2_commute hnab h3 e
  | J3 => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => j3_commute h3 e
  | J4 => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => j4_commute h3 e
  | HS => exact sporThreeDvd_of_commute _ fun G _ _ _ hnab h3 e => hs_commute hnab h3 e
  | McL => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => mcl_commute h3 e
  | He => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => he_commute h3 e
  | Ru => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => ru_commute h3 e
  | Suz => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => suz_commute h3 e
  | ONan => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => on_commute h3 e
  | Co1 => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => co1_commute h3 e
  | Co2 => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => co2_commute h3 e
  | Co3 => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => co3_commute h3 e
  | Fi22 => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => fi22_commute h3 e
  | Fi23 => exact sporThreeDvd_Fi23
  | Fi24Prime => exact sporThreeDvd_Fi24Prime
  | HN => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => hn_commute h3 e
  | Ly => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => ly_commute h3 e
  | Th => exact sporThreeDvd_of_commute _ fun G _ _ _ _ h3 e => th_commute h3 e
  | B => exact sporThreeDvd_B
  | M => exact sporThreeDvd_M

end CFSG.RankThree.PartTwo.KFacts.KS14

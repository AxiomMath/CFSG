module

public import CFSG.RankThree.PartTwo.Sec21.Item22DStar
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.RankThree.PartTwo.Sec21.Item233ComponentsOf
import CFSG.RankThree.PartTwo.Sec21.Item233Skeleton
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
public import CFSG.RankThree.PartTwo.Sec21.Item233Pieces

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

namespace Item233One

theorem centralizer_sup_zpowers (B : Subgroup G) (x : G) :
    Subgroup.centralizer ((B ⊔ Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))))
  · have h := centralizer_inf_le_centralizer_sup B (Subgroup.zpowers x)
    rwa [Sec6.centralizer_zpowers_eq] at h

theorem centralizer_ne_top [Finite G] (hG : TheoremFourHyp G) {B : Subgroup G} (hB : B ≠ ⊥) :
    Subgroup.centralizer (B : Set G) ≠ ⊤ := by
  obtain ⟨⟨b, hbB⟩, hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have hb1 : b ≠ 1 := fun h => hb' (Subtype.ext h)
  intro hC
  have := hG.isSimpleGroup
  obtain ⟨x, y, hxy⟩ := hG.nonabelian
  have hz : b ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (hC ▸ Subgroup.mem_top g) b hbB).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact hb1 hz
  · exact hxy (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top x) y).symm

theorem exists_le_mem_thetaComponentsIn_of_le [Finite G] (h48 : Sec4.Item4_8)
    (hG : TheoremFourHyp G) {A : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) {B' : Subgroup G} (hB'A : B' ≤ A) :
    ∀ B : Subgroup G, B ≤ B' → B ≠ ⊥ →
      ∀ Y ∈ thetaComponentsIn (Subgroup.centralizer (B' : Set G)),
        ∃ X₀ ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)), Y ≤ X₀ := by
  suffices key : ∀ m : ℕ, ∀ B : Subgroup G, B ≤ B' → B ≠ ⊥ →
      Nat.card B' - Nat.card B = m → ∀ Y ∈ thetaComponentsIn (Subgroup.centralizer (B' : Set G)),
        ∃ X₀ ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)), Y ≤ X₀ from
    fun B hBB' hB1 => key _ B hBB' hB1 rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro B hBB' hB1 hm Y hY
    by_cases hEq : B = B'
    · subst hEq
      exact ⟨Y, hY, le_rfl⟩
    · obtain ⟨x, hxB', hxB⟩ : ∃ x ∈ B', x ∉ B := by
        by_contra h
        push Not at h
        exact hEq (le_antisymm hBB' h)
      have hBB₁ : B ≤ B ⊔ Subgroup.zpowers x := le_sup_left
      have hB₁B' : B ⊔ Subgroup.zpowers x ≤ B' := sup_le hBB' (Subgroup.zpowers_le.mpr hxB')
      have hxB₁ : x ∈ B ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
      have hlt : Nat.card B < Nat.card (B ⊔ Subgroup.zpowers x : Subgroup G) := by
        by_contra hle
        push Not at hle
        have heq := Subgroup.eq_of_le_of_card_ge hBB₁ hle
        exact hxB (heq ▸ hxB₁)
      have hle' : Nat.card (B ⊔ Subgroup.zpowers x : Subgroup G) ≤ Nat.card B' :=
        Subgroup.card_le_of_le hB₁B'
      have hB₁1 : B ⊔ Subgroup.zpowers x ≠ ⊥ := fun h => hB1 (le_bot_iff.mp (h ▸ hBB₁))
      obtain ⟨Y₁, hY₁, hYY₁⟩ := ih _ (by omega) (B ⊔ Subgroup.zpowers x) hB₁B' hB₁1 rfl Y hY
      have hM : SectionFourHyp (Subgroup.centralizer (B : Set G)) :=
        hG.sectionFourHyp (centralizer_ne_top hG hB1)
      have hAM : A ≤ Subgroup.centralizer (B : Set G) :=
        le_centralizer_of_isElemAbelian hAe (hBB'.trans hB'A)
      have hY₁' : Y₁ ∈ thetaComponentsIn
          (Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) := by
        rw [← centralizer_sup_zpowers]
        exact hY₁
      have hx1 : x ≠ 1 := fun h => hxB (h ▸ B.one_mem)
      obtain ⟨X₀, hX₀, hY₁X₀⟩ := Sec6.exists_le_mem_thetaComponentsIn h48 hM hAM hAe hAn
        (hB'A hxB') hx1 hY₁'
      exact ⟨X₀, hX₀, hYY₁.trans hY₁X₀⟩

theorem le_fixedInG_of_kOf_le_centralizer [Finite G] (h222 : Item222) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A}
    (hφ : φ ∈ dStar A) {B : Subgroup G} (hBA : B ≤ A)
    (hKB : kOf A φ ≤ Subgroup.centralizer (B : Set G)) : B ≤ fixedInG A φ := by
  obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
  intro b hb
  refine ⟨⟨b, hBA hb⟩, (mem_fixedSubgroupOf φ _).mpr ?_, rfl⟩
  have hjb : (j : G) * b = b * j := (Subgroup.mem_centralizer_iff.mp (hKB hjK) b hb).symm
  apply Subtype.ext
  rw [← hj, wConj_apply]
  change (j : G) * b * (j : G)⁻¹ = b
  rw [hjb, mul_inv_cancel_right]

theorem exists_two_le_mulEquiv_kOf [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {φ : MulAut A} (hφ : φ ∈ dStar A) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 n)) := by
  obtain ⟨-, X, hX, hφX⟩ := id hφ
  obtain ⟨-, E', hE', U', hU', c', hXpair⟩ := hX
  have hcase := (h222 G A E' U' c' X ⟨hpair.toSec21Std, hE', hU', hXpair⟩).2.2 φ hφX hφ
  rcases hcase with ⟨-, n, hn, ⟨k, hk⟩, -, hKn, -⟩ | ⟨-, n, hn, ⟨k, hk⟩, -, hKn, -⟩ |
      ⟨-, n, hn, ⟨k, hk⟩, -, hKn | hKn, -⟩ | ⟨-, -, hKn | hKn, -⟩ | ⟨-, n, hn, -, -, hKn, -⟩
  · exact ⟨n, by omega, hKn⟩
  · exact ⟨n, by omega, hKn⟩
  · exact ⟨n, by omega, hKn⟩
  · exact ⟨2 * n, by omega, hKn⟩
  · exact ⟨2, le_rfl, hKn⟩
  · exact ⟨4, by norm_num, hKn⟩
  · exact ⟨n, hn, hKn⟩

theorem isSimpleGroup_kZero [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A} (hφ : φ ∈ dStar A) :
    IsSimpleGroup (kZero A φ) ∧ ∃ a b : kZero A φ, a * b ≠ b * a := by
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_two_le_mulEquiv_kOf h222 hpair hφ
  obtain ⟨a, b, hab⟩ := exists_not_commute_of_mulEquiv_projSL e
  have hle := kOf_le_kZero hK hφ
  have hnc : ∃ a b : kZero A φ, a * b ≠ b * a := by
    refine ⟨⟨a, hle a.2⟩, ⟨b, hle b.2⟩, fun h => ?_⟩
    have h' : (a : G) * b = b * a := congrArg Subtype.val h
    exact hab (Subtype.ext h')
  refine ⟨?_, hnc⟩
  by_cases hU : StatedClassicalModel (kZero A φ) .PSU 3 2 2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 2 hU).2
  · have := isSimpleGroup_projSL_two hn
    exact ((MulEquiv.subgroupCongr (kOf_eq_kZero hU)).symm.trans e).isSimpleGroup

theorem centralizer_le_normalizer_kZero [Finite G] (A : Subgroup G) (φ : MulAut A) :
    Subgroup.centralizer (fixedInG A φ : Set G) ≤ Subgroup.normalizer (kZero A φ : Set G) := by
  intro h hh
  apply mem_normalizer_of_map_conj_eq_self'
  have hC : (Subgroup.centralizer (fixedInG A φ : Set G)).map (MulAut.conj h).toMonoidHom =
      Subgroup.centralizer (fixedInG A φ : Set G) := map_conj_eq_self (Subgroup.le_normalizer hh)
  rw [kZero, map_oPrimeResidualOf, map_inSubgroup_layer, hC]

theorem kZero_mem_thetaComponentsIn [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A} (hφ : φ ∈ dStar A) :
    kZero A φ ∈ thetaComponentsIn (Subgroup.centralizer (fixedInG A φ : Set G)) := by
  have hKC : kZero A φ ≤ Subgroup.centralizer (fixedInG A φ : Set G) := kZero_le_centralizer A φ
  obtain ⟨hs, hnc⟩ := isSimpleGroup_kZero h222 hpair hK hφ
  have hn : ((kZero A φ).subgroupOf (Subgroup.centralizer (fixedInG A φ : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr (centralizer_le_normalizer_kZero A φ)
  have hq : IsQuasisimple
      ((kZero A φ).subgroupOf (Subgroup.centralizer (fixedInG A φ : Set G))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  exact mem_thetaComponentsIn_iff.mpr
    ⟨hKC, Sec4.mem_thetaComponents_of_isComponent3 ⟨hq, hn.isSubnormal⟩⟩

theorem exists_mem_thetaComponentsIn_kOf_le [Finite G] (h48 : Sec4.Item4_8) (h222 : Item222)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A)
    {B : Subgroup G} (hBA : B ≤ A) (hB1 : B ≠ ⊥) {φ : MulAut A} (hφ : φ ∈ dStar A)
    (hKB : kOf A φ ≤ Subgroup.centralizer (B : Set G)) :
    ∃ X₀ ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)), kOf A φ ≤ X₀ := by
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hBφ := le_fixedInG_of_kOf_le_centralizer h222 hpair hK hφ hBA hKB
  obtain ⟨X₀, hX₀, hle⟩ := exists_le_mem_thetaComponentsIn_of_le h48
    hpair.standing.toTheoremFourHyp hAe (Sec6.exists_card_eq_of_mem_partTwoF hpair.mem_S.1)
    (Subgroup.map_subtype_le _ : fixedInG A φ ≤ A) B hBφ hB1 (kZero A φ)
    (kZero_mem_thetaComponentsIn h222 hpair hK hφ)
  exact ⟨X₀, hX₀, (kOf_le_kZero hK hφ).trans hle⟩

end Item233One

end CFSG.RankThree.PartTwo.Sec21

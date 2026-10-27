module

public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
public import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem hasFaithfulE9_of_le {L Y E : Subgroup G} (hLY : L ≤ Y) (hEL : E ≤ L)
    (hEab : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEc : Late.sectionCentralizer E L ((aschbacherSolvableCore 3 ↥L).map L.subtype) ⊆ {1}) :
    HasFaithfulE9 Y := by
  obtain ⟨hθN, hθs, hθ3⟩ := map_aschbacherSolvableCore_facts Y
  refine ⟨E, hEL.trans hLY, hEab, hE9, fun e he => hEc ⟨he.1, fun l hl => ?_⟩⟩
  have heL : e ∈ L := hEL he.1
  have h1 : e * l * e⁻¹ * l⁻¹ ∈ (aschbacherSolvableCore 3 ↥Y).map Y.subtype := he.2 l (hLY hl)
  have h2 : e * l * e⁻¹ * l⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem heL hl) (L.inv_mem heL)) (L.inv_mem hl)
  exact inf_le_map_aschbacherSolvableCore (hLY.trans hθN) hθs hθ3 ⟨h1, h2⟩

theorem sectionCentralizer_subset_of_center_eq_bot {L E : Subgroup G} (hEL : E ≤ L)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥) :
    Late.sectionCentralizer E L ((aschbacherSolvableCore 3 ↥L).map L.subtype) ⊆ {1} := by
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
  rintro e ⟨he, hc⟩
  set ê : ↥L := ⟨e, hEL he⟩ with hê
  have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ê ∈
      Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) g
    have hθ : ⁅ê, l⁆ ∈ aschbacherSolvableCore 3 ↥L := by
      obtain ⟨y, hy, hyeq⟩ := hc l l.2
      have hy' : y = ⁅ê, l⁆ := by
        apply Subtype.ext
        rw [commutatorElement_def]
        exact hyeq
      rwa [← hy']
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⁅ê, l⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hθ
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [hZ, Subgroup.mem_bot] at hcen
  have hθê : ê ∈ aschbacherSolvableCore 3 ↥L := (QuotientGroup.eq_one_iff _).mp hcen
  have hê1 : ê = 1 := eq_one_of_mem_of_pow_three hθ3 hθê (Subtype.ext (hE3 e he))
  exact congrArg Subtype.val hê1

theorem exists_le_isElemAbelian_card_nine_of_quotient {L : Subgroup G}
    {E' : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hE' : CFSG.Assembly.IsElemAbelian 3 E') (h9 : Nat.card E' = 9) :
    ∃ E : Subgroup G, E ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE' (by rw [h9]; norm_num)
  rw [CFSG.SectionRank.pRank_quotient_eq _ hθ3] at h2
  obtain ⟨E₀, -, hE₀, hcard⟩ := Late.exists_elemAbelian_le_of_le_pRank_three h2
  refine ⟨E₀.map L.subtype, Subgroup.map_subtype_le _,
    CFSG.SectionRank.isElemAbelian_map hE₀ _, ?_⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective, hcard]
  norm_num

theorem exists_e9_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ E : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, h9⟩ := h
  exact ⟨E.map e.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hE _, by
    rw [Subgroup.card_map_of_injective e.symm.injective, h9]⟩

theorem hasFaithfulE9_of_mulEquiv {Y : Subgroup G} {K : Type*} [Group K]
    (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* K)
    (hZ : Subgroup.center K = ⊥)
    (hE : ∃ E : Subgroup K, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9) :
    HasFaithfulE9 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZQ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ := by
    have hmap := Subgroup.map_center_eq φ
    rw [hZ] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
  obtain ⟨E', hE', h9'⟩ := exists_e9_of_mulEquiv φ hE
  have hP3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥Y) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE' (by rw [h9']; norm_num)
  rw [CFSG.SectionRank.pRank_quotient_eq _ hP3] at h2
  obtain ⟨E₀, -, hE₀, hcard⟩ := Late.exists_elemAbelian_le_of_le_pRank_three h2
  refine ⟨E₀.map Y.subtype, Subgroup.map_subtype_le _,
    CFSG.SectionRank.isElemAbelian_map hE₀ _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hcard]
    norm_num
  obtain ⟨hθs, hθc, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  have hθQ : (aschbacherSolvableCore 3 ↥Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = ⊥ := by
    have hn : ((aschbacherSolvableCore 3 ↥Y).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).Normal :=
      (Subgroup.normal_of_characteristic _).map _ (QuotientGroup.mk'_surjective _)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with htop | hle
    · exfalso
      have hsol : Group.IsSolvable ↥((aschbacherSolvableCore 3 ↥Y).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) :=
        Group.isSolvable_of_surjective
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).subgroupMap_surjective _)
      rw [htop] at hsol
      have hsolQ : Group.IsSolvable (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.topEquiv (G := ↥Y ⧸ CFSG.pCore 2 ↥Y)).symm.toMonoidHom)
          (Subgroup.topEquiv (G := ↥Y ⧸ CFSG.pCore 2 ↥Y)).symm.injective
      have := CFSG.LocalCores.isQuasisimple_nontrivial hq
      have := hq.1
      exact Group.IsPerfect.not_isSolvable _ hsolQ
    · rw [hZQ] at hle
      exact le_bot_iff.mp hle
  rintro e ⟨he, hc⟩
  obtain ⟨ê, hê, rfl⟩ := he
  have hcen : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ê ∈
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) g
    have h1 : ⁅ê, y⁆ ∈ aschbacherSolvableCore 3 ↥Y := by
      obtain ⟨w, hw, hweq⟩ := hc y y.2
      have hw' : w = ⁅ê, y⁆ := by
        apply Subtype.ext
        rw [commutatorElement_def]
        exact hweq
      rwa [← hw']
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⁅ê, y⁆ = 1 := by
      have : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⁅ê, y⁆ ∈
          (aschbacherSolvableCore 3 ↥Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) :=
        Subgroup.mem_map_of_mem _ h1
      rwa [hθQ, Subgroup.mem_bot] at this
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  rw [hZQ, Subgroup.mem_bot] at hcen
  have hêP : ê ∈ CFSG.pCore 2 ↥Y := (QuotientGroup.eq_one_iff _).mp hcen
  have hê1 : ê = 1 := eq_one_of_mem_of_pow_three hP3 hêP (hE₀.2 ê hê)
  rw [hê1]
  exact Set.mem_singleton _

@[expose] def KS153ThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨ IsLThreePi X ∨
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12)) →
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9

theorem exists_faithfulE9_of_ks153 (hK : KS153ThreeRank) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) :
    ∃ E : Subgroup G, E ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      Late.sectionCentralizer E L ((aschbacherSolvableCore 3 ↥L).map L.subtype) ⊆ {1} := by
  have htypes := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1
  obtain ⟨E', hE', h9⟩ := hK _ htypes
  obtain ⟨E, hEL, hEab, hE9⟩ := exists_le_isElemAbelian_card_nine_of_quotient hE' h9
  exact ⟨E, hEL, hEab, hE9, sectionCentralizer_subset_of_center_eq_bot hEL hEab.2
    (center_eq_bot_of_types h.toSec13Data.mem_thetaComponentsAt htypes)⟩

theorem hasFaithfulE9_of_le_of_ks153 (hK : KS153ThreeRank) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {Y : Subgroup G} (hLY : L ≤ Y) :
    HasFaithfulE9 Y := by
  obtain ⟨E, hEL, hEab, hE9, hEc⟩ := exists_faithfulE9_of_ks153 hK h
  exact hasFaithfulE9_of_le hLY hEL hEab hE9 hEc

end CFSG.RankThree.PartTwo.Sec15

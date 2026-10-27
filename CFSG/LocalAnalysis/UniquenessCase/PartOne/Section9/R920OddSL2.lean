module

import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93j
import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal
public import CFSG.GH74.Uniqueness.SU.SU5Q8D8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped MatrixGroups

theorem exists_mul_ne_of_isL2Odd {Y : Type} [Group Y] {q : ℕ} (hq : 5 < q) (hY : IsL2Odd Y q) :
    ∃ a b : Y, a * b ≠ b * a := by
  haveI hs : IsSimpleGroup Y :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hY
  have hqp : q.Prime := hY.admissible.1
  have hcard : 2 * Nat.card Y = q * (q ^ 2 - 1) := by
    rw [show Nat.card Y = ordA 1 q from by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hY.card_eq_lieOrd (by norm_num)]
    exact UC6.N588.two_mul_ordA_one (hqp.odd_of_ne_two (by omega))
  by_contra h
  push Not at h
  haveI : IsMulCommutative Y := ⟨⟨h⟩⟩
  have hpr : (Nat.card Y).Prime := Group.is_simple_iff_prime_card.mp hs
  have hqd : q ∣ Nat.card Y := by
    rcases (Nat.Prime.dvd_mul hqp).mp (Dvd.intro _ hcard.symm) with h2 | h2
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact h2
  rcases hpr.eq_one_or_self_of_dvd q hqd with h1 | h1
  · exact hqp.one_lt.ne' h1
  · rw [← h1] at hcard
    have h3 : 2 = q ^ 2 - 1 :=
      Nat.eq_of_mul_eq_mul_left (show 0 < q by omega) (by rw [mul_comm q 2]; exact hcard)
    have h36 : 36 ≤ q ^ 2 := by nlinarith
    omega

theorem card_eq_of_surjective_sl2 {Y : Type} [Group Y] {q : ℕ} (hq : 5 < q) (hY : IsL2Odd Y q)
    {F : Type} [Field F] [Fintype F] (φ : SL(2, F) →* Y) (hφ : Function.Surjective φ) :
    Fintype.card F = q ∧ (2 : F) ≠ 0 := by
  classical
  haveI hs : IsSimpleGroup Y :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hY
  have hqp : q.Prime := hY.admissible.1
  have hcard : 2 * Nat.card Y = q * (q ^ 2 - 1) := by
    rw [show Nat.card Y = ordA 1 q from by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hY.card_eq_lieOrd (by norm_num)]
    exact UC6.N588.two_mul_ordA_one (hqp.odd_of_ne_two (by omega))
  have hq36 : 36 ≤ q ^ 2 := by nlinarith
  have hq48 : 6 * 35 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hZ : Subgroup.center SL(2, F) ≤ φ.ker := by
    intro z hz
    have hc : φ z ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := hφ y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) y']
    rwa [CFSG.SignalizerFunctorTheorem.Diagonal.center_eq_bot (exists_mul_ne_of_isL2Odd hq hY),
      Subgroup.mem_bot] at hc
  have h4 : 4 ≤ Nat.card F := by
    by_contra h4
    have hle := Nat.card_le_card_of_surjective φ hφ
    have hSL := F09.card_sl_two_le_of_card_le_three (F := F) (by omega)
    omega
  haveI := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Y :=
    CFSG.QuasithinUnique.SQTK.mulEquivOfSurjective (QuotientGroup.lift _ φ hZ)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφ hZ)
  by_cases h2 : (2 : F) = 0
  · exfalso
    haveI : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h2)
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    rw [← Nat.card_eq_fintype_card] at hn
    refine not_isL2_of_isL2Odd hq hY (n := n) (Or.inl ⟨by decide,
      ⟨Nat.prime_two, n.one_le, le_rfl, fun h => ?_, fun h => ?_⟩, F, inferInstance,
      inferInstance, hn,
      ⟨e.symm.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩⟩)
    · have h' := congrArg Prod.snd h
      simp only at h'
      rw [← hn] at h'
      omega
    · have h' := congrArg Prod.snd h
      simp only at h'
      rw [← hn] at h'
      omega
  · refine ⟨?_, h2⟩
    have hP := CFSG.PSL2Table.card_PSL (F := F) h2
    rw [Nat.card_congr e.toEquiv] at hP
    have ha4 : 4 ≤ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
    have heq : Fintype.card F * (Fintype.card F ^ 2 - 1) = q * (q ^ 2 - 1) := by omega
    have key : ∀ {a b : ℕ}, a < b → 2 ≤ b → a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
      intro a b hab hb
      have h1 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab.le 2
      have h2 : 0 < b ^ 2 - 1 := by
        have : 4 ≤ b ^ 2 := by nlinarith
        omega
      calc a * (a ^ 2 - 1) ≤ a * (b ^ 2 - 1) := Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h1 1)
        _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hab h2
    rcases lt_trichotomy (Fintype.card F) q with hlt | heq' | hgt
    · exact absurd heq (key hlt (by omega)).ne
    · exact heq'
    · exact absurd heq (key hgt (by omega)).ne'

theorem exists_sl2_of_quot_cases {Γ Y : Type} [Group Γ] [Finite Γ] [Group Y] {q : ℕ}
    (hq : 5 < q) (hY : IsL2Odd Y q) (ψ : Γ →* Y) (hψ : Function.Surjective ψ)
    (hcases : (∃ (F : Type) (_ : Field F) (_ : Finite F), Nonempty (Γ ≃* SL(2, F))) ∨
      (∃ n : ℕ, CFSG.Blueprint.LieModel Γ .PSL 2 2 n) ∨
      CFSG.Quasithin.IsExt Γ (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
        (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Nonempty (Γ ≃* SL(2, F)) ∧
      Fintype.card F = q ∧ (2 : F) ≠ 0 := by
  classical
  haveI hs : IsSimpleGroup Y :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hY
  have hqp : q.Prime := hY.admissible.1
  have hcard : 2 * Nat.card Y = q * (q ^ 2 - 1) := by
    rw [show Nat.card Y = ordA 1 q from by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hY.card_eq_lieOrd (by norm_num)]
    exact UC6.N588.two_mul_ordA_one (hqp.odd_of_ne_two (by omega))
  have hq36 : 36 ≤ q ^ 2 := by nlinarith
  have hq48 : 6 * 35 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rcases hcases with ⟨F, hF, hFin, ⟨e⟩⟩ | ⟨n, hn⟩ | ⟨E, hEn, hE, ⟨eA⟩⟩
  · letI : Fintype F := Fintype.ofFinite F
    obtain ⟨h1, h2⟩ := card_eq_of_surjective_sl2 hq hY (ψ.comp e.symm.toMonoidHom)
      (hψ.comp e.symm.surjective)
    exact ⟨F, hF, inferInstance, ⟨e⟩, h1, h2⟩
  · exfalso
    haveI := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hn
    exact not_isL2_of_isL2Odd hq hY
      (CFSG.Blueprint.LieModel.of_mulEquiv (CFSG.QuasithinUnique.SQTK.mulEquivOfSurjective ψ hψ) hn)
  · exfalso
    have hE32 : Nat.card E = 32 := by
      have h := (CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8.facts hE).1
      rwa [Subgroup.card_top] at h
    have hEψ : E ≤ ψ.ker := by
      haveI : (E.map ψ).Normal := hEn.map ψ hψ
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E.map ψ) with h | h
      · exact (Subgroup.map_eq_bot_iff E).mp h
      · exfalso
        have hle := Nat.le_of_dvd (by omega) (Subgroup.card_map_dvd E ψ)
        rw [h, Subgroup.card_top] at hle
        omega
    have hle := Nat.card_le_card_of_surjective (QuotientGroup.lift E ψ hEψ)
      (QuotientGroup.lift_surjective_of_surjective E ψ hψ hEψ)
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hle
    norm_num at hle
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

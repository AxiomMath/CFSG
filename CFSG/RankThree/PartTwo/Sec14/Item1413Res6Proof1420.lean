module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3Proof1419
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3Proof1420

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

open Proof1413Res3 Proof1413Res6 in
theorem step1420A7TwoR_of_c
    (h1413 : Item1413CR) (h142 : Concl142S14)
    (hbot : Item145BotS14) (h131 : Item131) (h1418 : Item1418R) (h1419 : Item1419R)
    (hSne : Step1420A7SneR) : Step1420A7TwoR := by
  intro G _ _ A c₀ L₀ hR hfail c hcΓ L hL hA7 h2
  have hS := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hA : IsE27 A := hS.isE27
  have hcA : c ∈ A := hD.mem_A
  obtain ⟨φ⟩ := hA7
  have hnL3 : ¬ IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven
  have hnPGL : ∀ (x : G) (Lx : Subgroup G), Sec13Data G A x Lx →
      Nonempty (↥Lx ⧸ aschbacherSolvableCore 3 ↥Lx ≃* alternatingGroup (Fin 7)) →
        ¬ Sec8.IsZ3PGLThreePi (lBarA x Lx A) := by
    rintro x Lx hDx ⟨φx⟩ hP
    exact not_isLThreePi_of_mulEquiv φx not_isoLThreePi_alternating_seven
      (Sec13.facts_of_isZ3PGLThreePi hDx hP).1
  have htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    Or.inl ⟨φ⟩
  have hcL : c ∉ L := not_mem_of_type hD (type_four_of_three htype)
  obtain ⟨h9, hAa⟩ := facts_of_type h131 hD hcL (hnPGL c L hD ⟨φ⟩)
  have h3 : 3 ∣ Nat.card L := three_dvd_card_of_card_inf h9
  have h2' := h2
  obtain ⟨-, -, hcard, horb, -⟩ := h2'
  obtain ⟨R, hR'⟩ := Proof1413Res2.exists_mem_scriptQPiStar A L (lB A) (piOf 2)
  have hRnot := hSne G A c₀ L₀ hR hfail c hcΓ L hL ⟨φ⟩ h2 R hR'
  obtain ⟨hB, hset⟩ := h1419 G A c₀ L₀ hR hfail c hcΓ L hL htype R hR'
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hBdef
  have hRL : R ≤ L := hR'.prop.1.2
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := hRL.trans hD.le_centralizer
  have hcB : c ∈ B := ⟨hcA, Subgroup.mem_centralizer_iff.mpr fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)⟩
  obtain ⟨e, heBL, he3, hBL, -⟩ :=
    exists_point_of_hyperplane hA.1 hA.2 hcA hD.orderOf_eq hcL hAa hB hcB
  have heΓ : Subgroup.zpowers e ∈ gammaA A (lB A) := by
    have hmem : B ⊓ L ∈ {F | F ∈ gammaA A (lB A) ∧ F ≤ B} := by
      rw [hset]
      exact Set.mem_insert_of_mem _ rfl
    rw [← hBL]
    exact hmem.1
  have heA : e ∈ A := heBL.1.1
  have hRe : R ≤ Subgroup.centralizer ({e} : Set G) := le_centralizer_of_mem_inf heBL.1
  have hec : Subgroup.zpowers e ≠ Subgroup.zpowers c := by
    intro h
    apply hcL
    have h1 : c ∈ Subgroup.zpowers e := h ▸ Subgroup.mem_zpowers c
    rw [← hBL] at h1
    exact h1.2
  obtain ⟨w, hw, hew⟩ := horb _ heΓ.1
  have hLe : L.map (MulAut.conj w).toMonoidHom ∈ lA A e := by
    have h1 : L.map (MulAut.conj w).toMonoidHom ∈ lA A (w * c * w⁻¹) :=
      (map_conj_mem_lA_iff hw).mpr hL
    have h2 : Subgroup.zpowers (w * c * w⁻¹) = Subgroup.zpowers e := by
      rw [hew, MonoidHom.map_zpowers]
      rfl
    rwa [lA_eq_of_zpowers_eq h2] at h1
  set Le := L.map (MulAut.conj w).toMonoidHom with hLedef
  obtain ⟨χ⟩ := nonempty_thetaQuot_map_conj L w
  have hA7e : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)) :=
    ⟨χ.symm.trans φ⟩
  have hSe := Proof1413.sec14Std_at hR.toSec14Std heΓ.1 hLe
  have hDe := hSe.toSec13Data
  have htypee : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    Or.inl hA7e
  have heLe : e ∉ Le := not_mem_of_type hDe (type_four_of_three htypee)
  obtain ⟨h9e, hAae⟩ := facts_of_type h131 hDe heLe (hnPGL e Le hDe hA7e)
  have h3e : 3 ∣ Nat.card Le := three_dvd_card_of_card_inf h9e
  obtain ⟨S, hS', hRS⟩ := Proof1413.exists_scriptQPiStar_top hR'.prop
  have hSR : S ≠ R := fun h => hRnot (h ▸ hS')
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS'.prop.1.1.1.2.2
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS'.prop
  have hAcent : ∀ x ∈ A, A ≤ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) :=
    fun x hx => (show A ≤ Subgroup.centralizer ({x} : Set G) from fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hy hx)).trans Subgroup.le_normalizer
  have hScR : S ⊓ Subgroup.centralizer ({c} : Set G) ≤ R := by
    have hle := le_of_le_centralizer_gammaC h1413 h142 hbot hR hfail hcΓ hL h3 hAa
      (inf_le_right : S ⊓ Subgroup.centralizer ({c} : Set G) ≤ _)
      (le_normalizer_inf hAS (hAcent c hcA)) (hS2.to_le inf_le_left)
    have hmem := Proof1413Res2.mem_scriptQPi_of_concl142 h142 hR.toSec14Std hcΓ.1 hL hle
      (le_normalizer_inf hAS (hAcent c hcA)) (hS2.to_le inf_le_left)
    exact (hR'.eq_of_le hmem (le_inf hRS hRc)).symm.le
  have hSeR : S ⊓ Subgroup.centralizer ({e} : Set G) ≤ R := by
    have hAQ := le_normalizer_inf hAS (hAcent e heA)
    have hQ2 : IsPGroup 2 (S ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :=
      hS2.to_le inf_le_left
    have hle := le_of_le_centralizer_gammaC h1413 h142 hbot hR hfail heΓ hLe h3e hAae
      (inf_le_right : S ⊓ Subgroup.centralizer ({e} : Set G) ≤ _) hAQ hQ2
    have hmem := Proof1413Res2.mem_scriptQPi_of_concl142 h142 hR.toSec14Std heΓ.1 hLe hle
      hAQ hQ2
    obtain ⟨Re, hQRe, hRe'⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) Le (piOf 2))) hmem
    have hBe := (h1419 G A c₀ L₀ hR hfail e heΓ Le hLe htypee Re hRe').1
    have hRRe : R ≤ Re := (le_inf hRS hRe).trans hQRe
    have hle2 : A ⊓ Subgroup.centralizer (Re : Set G) ≤ B :=
      inf_le_inf_left A (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRRe))
    have heq : A ⊓ Subgroup.centralizer (Re : Set G) = B :=
      Subgroup.eq_of_le_of_card_ge hle2 (by have := hB.2; have := hBe.2; omega)
    have hRec : Re ≤ Subgroup.centralizer ({c} : Set G) := by
      have h1 : c ∈ A ⊓ Subgroup.centralizer (Re : Set G) := heq ▸ hcB
      exact le_centralizer_of_mem_inf h1
    have hAR : A ≤ Subgroup.normalizer (Re : Set G) := hRe'.prop.1.1.1.2.2
    have hRe2 : IsPGroup 2 Re := isPGroup_of_mem_scriptQPi Nat.prime_two hRe'.prop
    have hReL :=
      le_of_le_centralizer_gammaC h1413 h142 hbot hR hfail hcΓ hL h3 hAa hRec hAR hRe2
    have hRemem := Proof1413Res2.mem_scriptQPi_of_concl142 h142 hR.toSec14Std hcΓ.1 hL hReL hAR
      hRe2
    have hReq : R = Re := hR'.eq_of_le hRemem hRRe
    exact hQRe.trans hReq.symm.le
  obtain ⟨D, hD', hSD, hcD, heD⟩ : ∃ D, IsHyperplane A D ∧
      S ⊓ Subgroup.centralizer (D : Set G) ≠ ⊥ ∧ c ∉ D ∧ e ∉ D := by
    by_contra hall
    push Not at hall
    apply hSR
    refine le_antisymm (le_of_forall_hyperplane hA hAS (not_three_dvd_of_isPGroup_two hS2)
      fun D hD hSD => ?_) hRS
    by_cases hcD : c ∈ D
    · exact (inf_le_inf_left S (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr hcD))).trans hScR
    · exact (inf_le_inf_left S (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr (hall D hD hSD hcD)))).trans hSeR
  obtain ⟨F₁, hF₁, F₂, hF₂, hne, hF₁D, hF₂D⟩ := h1418 G A c₀ L₀ hR hfail S hS' D hD' hSD
  have hF₁c : F₁ ≠ Subgroup.zpowers c := fun h => hcD (mem_of_zpowers_le (h ▸ hF₁D))
  have hF₂c : F₂ ≠ Subgroup.zpowers c := fun h => hcD (mem_of_zpowers_le (h ▸ hF₂D))
  have hF₁e : F₁ ≠ Subgroup.zpowers e := fun h => heD (mem_of_zpowers_le (h ▸ hF₁D))
  have hF₂e : F₂ ≠ Subgroup.zpowers e := fun h => heD (mem_of_zpowers_le (h ▸ hF₂D))
  have hsub : ({Subgroup.zpowers c, Subgroup.zpowers e, F₁, F₂} : Set (Subgroup G)) ⊆
      omegaA A := by
    intro F hF
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF
    rcases hF with rfl | rfl | rfl | rfl
    · exact hcΓ.1
    · exact heΓ.1
    · exact hF₁.1
    · exact hF₂.1
  have h4 : ({Subgroup.zpowers c, Subgroup.zpowers e, F₁, F₂} : Set (Subgroup G)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hne]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hF₁e.symm, hF₂e.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hec.symm, hF₁c.symm, hF₂c.symm⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

end CFSG.RankThree.PartTwo.Sec14

module

public import CFSG.RankThree.PartOne.KS.HeKit
public import CFSG.RankThree.PartOne.KS.HeSevenCheck0
public import CFSG.RankThree.PartOne.KS.HeSevenCheck1
public import CFSG.RankThree.PartOne.KS.HeSevenCheck2
public import CFSG.RankThree.PartOne.KS.HeSevenCheckQ

public noncomputable section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Sporadic.HeldB
open scoped commutatorElement

theorem heSevenKeys_lt : ∀ p ∈ heSevenKeys, p < 8330 := by decide

theorem heSeven_lines_ok :
    linesOKG 7 343 57 8330 heSevenQGens heSevenKeys heSevenQCert heSevenLines = true :=
  heSeven_Q_check.1

theorem rep_heSevenLine (j : Fin 57) : Rep 8330 heSevenLines[(j : ℕ)]! (heSevenLine j) :=
  linesOKG_rep heSeven_lines_ok j

theorem mem_heAut_of_sift7 {g : Array ℕ} {G : Equiv.Perm (Fin 8330)} (hG : Rep 8330 g G)
    (h : siftA 8330 heSevenRLevels heSevenCase0BaseArr 0 g = true) : G ∈ heAutGroup := by
  rw [← closure_three_eq_heAutGroup]
  exact mem_closure_three_of_siftG (S := heSevenCase0Arrs) (bs := heSevenCase0Base)
    (W := heSevenCase0Words) (by norm_num) (by simp [heSevenCase0Arrs]) (by decide)
    (rep_heGen (by norm_num)) (rep_heGen (by norm_num)) rep_heU heSeven_case0_check.1 hG h

theorem heSevenQ_le_P : heSevenQ ≤ heP :=
  closure_le_of_siftG (fun _ hl => enumOK_gens_valid (linesOKG_parts heSeven_lines_ok).1 hl)
    heSeven_Q_check.2.1 mem_heP_of_siftHe

theorem card_heSevenQ : Nat.card heSevenQ = 343 :=
  linesOKG_card heSevenKeys_lt heSeven_lines_ok

theorem heSevenQ_sylow :
    ∃ S : Sylow 7 heP, (S : Subgroup heP) = heSevenQ.subgroupOf heP :=
  linesOKG_sylow_of_card (k := 3) (m := 11750400) (by norm_num) heSevenKeys_lt heSeven_lines_ok
    heSevenQ_le_P (by simp [card_heP]) (by norm_num) (by norm_num)

theorem heSevenTransporter_spec (j : Fin 57) :
    heSevenTransporter j ∈ heAutGroup ∧
      heSevenTransporter j * heSevenLine (heSevenRecordOf j) * (heSevenTransporter j)⁻¹ =
        heSevenLine j :=
  trans_spec (L := heSevenLines) mem_heAut_of_sift7 (linesOKG_valid heSeven_lines_ok)
    heSeven_Q_check.2.2.1 j.2

theorem heSevenRecordOf_mem (j : Fin 57) : (heSevenRecordOf j : ℕ) ∈ ({0, 1, 2} : Finset ℕ) := by
  have h := rec_mod_memG (cs := List.range 3) heSeven_Q_check.2.2.2.1
    (fun i hi => by simp only [List.mem_range] at hi; omega) j.2
  have h' : heSevenRec.getD j 0 % 57 < 3 := List.mem_range.1 h
  change heSevenRec.getD j 0 % 57 ∈ ({0, 1, 2} : Finset ℕ)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem heSevenRecordOf_reps :
    heSevenRecordOf 0 = 0 ∧ heSevenRecordOf 1 = 1 ∧ heSevenRecordOf 2 = 2 := by
  obtain ⟨-, -, -, -, h0, h1, h2⟩ := heSeven_Q_check
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
  · change heSevenRec.getD 0 0 % 57 = 0
    rw [h0]
  · change heSevenRec.getD 1 0 % 57 = 1
    rw [h1]
  · change heSevenRec.getD 2 0 % 57 = 2
    rw [h2]

theorem heSevenC0_spec :
    heSevenC0 = centralizer {heSevenLine 0} ⊓ heAutGroup ∧ Nat.card heSevenC0 = 2058 := by
  obtain ⟨hchain, hcent, -⟩ := heSeven_case0_check
  have h := case_centralizerP (S := heSevenCase0Arrs) (bs := heSevenCase0Base)
    (W := heSevenCase0Words) (by norm_num) (by simp [heSevenCase0Arrs]) (by decide)
    (rep_heGen (by norm_num)) (rep_heGen (by norm_num)) rep_heU hchain (rep_heSevenLine 0)
    heSevenKeys_lt hcent
  rw [closure_three_eq_heAutGroup] at h
  exact h

theorem heSevenC1_spec :
    heSevenC1 = centralizer {heSevenLine 1} ⊓ heAutGroup ∧ Nat.card heSevenC1 = 1176 := by
  obtain ⟨hchain, hcent, -⟩ := heSeven_case1_check
  have h := case_centralizerP (S := heSevenCase1Arrs) (bs := heSevenCase1Base)
    (W := heSevenCase1Words) (by norm_num) (by simp [heSevenCase1Arrs]) (by decide)
    (rep_heGen (by norm_num)) (rep_heGen (by norm_num)) rep_heU hchain (rep_heSevenLine 1)
    heSevenKeys_lt hcent
  rw [closure_three_eq_heAutGroup] at h
  exact h

theorem heSevenC2_spec :
    heSevenC2 = centralizer {heSevenLine 2} ⊓ heAutGroup ∧ Nat.card heSevenC2 = 98 := by
  obtain ⟨hchain, hcent, -⟩ := heSeven_case2_check
  have h := case_centralizerP (S := heSevenCase2Arrs) (bs := heSevenCase2Base)
    (W := heSevenCase2Words) (by norm_num) (by simp [heSevenCase2Arrs]) (by decide)
    (rep_heGen (by norm_num)) (rep_heGen (by norm_num)) rep_heU hchain (rep_heSevenLine 2)
    heSevenKeys_lt hcent
  rw [closure_three_eq_heAutGroup] at h
  exact h

theorem heSevenA0_spec :
    heSevenA0 ≤ heSevenC0 ∧ (heSevenA0.subgroupOf heSevenC0).Normal ∧ heSevenA0 ≤ heP ∧
      Nat.card heSevenA0 = 343 ∧ Monoid.exponent heSevenA0 = 7 ∧
      Nat.card (centralizer (heSevenA0 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC0 :
        Subgroup (Equiv.Perm (Fin 8330))) = 7 ∧
      centralizer (heSevenA0 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC0 ≤ heSevenA0 := by
  obtain ⟨-, hcent, hxz, hN, hz⟩ := heSeven_case0_check
  exact recordA_spec_zcent (by norm_num) heSevenKeys_lt (centOKP_enum hcent) heSevenC0_spec.1 hN
    mem_heP_of_siftHe (by norm_num) (rep_heSevenLine 0) (by simp [heSevenC0Gens]) hxz hz
    (linesOKG_orderOf (by norm_num) heSeven_lines_ok 0)

theorem heSevenD1_spec :
    IsSimpleGroup heSevenD1 ∧ (∃ g ∈ heSevenD1, ∃ h ∈ heSevenD1, g * h ≠ h * g) ∧
      Nat.card heSevenD1 = 168 ∧ heSevenD1 ≤ heP ∧
      centralizer (heSevenD1 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC1 =
        zpowers (heSevenLine 1) ∧
      Nat.card (centralizer (heSevenD1 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC1 :
        Subgroup (Equiv.Perm (Fin 8330))) = 7 := by
  obtain ⟨-, hcent, hxz, hD⟩ := heSeven_case1_check
  exact recordD_spec_commQ rfl heSevenKeys_lt (centOKP_enum hcent) heSevenC1_spec.1 hD rfl
    (by simp [heSevenC1Gens]) (by norm_num) mem_heP_of_siftHe (rep_heSevenLine 1) hxz
    (linesOKG_orderOf (by norm_num) heSeven_lines_ok 1)

theorem heSevenA2_spec :
    heSevenA2 ≤ heSevenC2 ∧ (heSevenA2.subgroupOf heSevenC2).Normal ∧ heSevenA2 ≤ heP ∧
      Nat.card heSevenA2 = 49 ∧ Monoid.exponent heSevenA2 = 7 ∧
      centralizer (heSevenA2 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC2 ≤ heSevenA2 := by
  obtain ⟨-, hcent, -, hN, hS⟩ := heSeven_case2_check
  exact recordA_spec_self (by norm_num) heSevenKeys_lt (centOKP_enum hcent) hN
    mem_heP_of_siftHe (by norm_num) hS

theorem R3E_He_full_seven_centralizer_structures :
    (heSevenQ ≤ heP ∧ (∃ S : Sylow 7 heP, (S : Subgroup heP) = heSevenQ.subgroupOf heP) ∧
      Nat.card heSevenQ = 343 ∧ Monoid.exponent heSevenQ = 7) ∧
    ({H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heSevenQ ∧ Nat.card H = 7} =
        Set.range (fun j : Fin 57 => zpowers (heSevenLine j)) ∧
      Function.Injective (fun j : Fin 57 => zpowers (heSevenLine j))) ∧
    (∀ j : Fin 57, heSevenTransporter j ∈ heAutGroup ∧
      heSevenTransporter j * heSevenLine (heSevenRecordOf j) * (heSevenTransporter j)⁻¹ =
        heSevenLine j) ∧
    (∀ j : Fin 57, (heSevenRecordOf j : ℕ) ∈ ({0, 1, 2} : Finset ℕ)) ∧
    (heSevenRecordOf 0 = 0 ∧ heSevenRecordOf 1 = 1 ∧ heSevenRecordOf 2 = 2) ∧
    (heSevenC0 = centralizer {heSevenLine 0} ⊓ heAutGroup ∧ Nat.card heSevenC0 = 2058) ∧
    (heSevenC1 = centralizer {heSevenLine 1} ⊓ heAutGroup ∧ Nat.card heSevenC1 = 1176) ∧
    (heSevenC2 = centralizer {heSevenLine 2} ⊓ heAutGroup ∧ Nat.card heSevenC2 = 98) ∧
    (heSevenA0 ≤ heSevenC0 ∧ (heSevenA0.subgroupOf heSevenC0).Normal ∧ heSevenA0 ≤ heP ∧
      Nat.card heSevenA0 = 343 ∧ Monoid.exponent heSevenA0 = 7 ∧
      Nat.card (centralizer (heSevenA0 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC0 :
        Subgroup (Equiv.Perm (Fin 8330))) = 7 ∧
      centralizer (heSevenA0 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC0 ≤ heSevenA0) ∧
    (IsSimpleGroup heSevenD1 ∧ (∃ g ∈ heSevenD1, ∃ h ∈ heSevenD1, g * h ≠ h * g) ∧
      Nat.card heSevenD1 = 168 ∧ heSevenD1 ≤ heP ∧
      centralizer (heSevenD1 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC1 =
        zpowers (heSevenLine 1) ∧
      Nat.card (centralizer (heSevenD1 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC1 :
        Subgroup (Equiv.Perm (Fin 8330))) = 7) ∧
    (heSevenA2 ≤ heSevenC2 ∧ (heSevenA2.subgroupOf heSevenC2).Normal ∧ heSevenA2 ≤ heP ∧
      Nat.card heSevenA2 = 49 ∧ Monoid.exponent heSevenA2 = 7 ∧
      centralizer (heSevenA2 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC2 ≤ heSevenA2) :=
  ⟨⟨heSevenQ_le_P, heSevenQ_sylow, card_heSevenQ,
      linesOKG_exponent (by norm_num) (by norm_num) heSevenKeys_lt heSeven_lines_ok⟩,
    linesOKG_lines (by norm_num) heSevenKeys_lt heSeven_lines_ok, heSevenTransporter_spec,
    heSevenRecordOf_mem, heSevenRecordOf_reps, heSevenC0_spec, heSevenC1_spec, heSevenC2_spec,
    heSevenA0_spec, heSevenD1_spec, heSevenA2_spec⟩

end CFSG.RankThree.PartOne

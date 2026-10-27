module

public import CFSG.RankThree.PartOne.KS.HeFiveCheck
public import CFSG.RankThree.PartOne.KS.HeKit

public noncomputable section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Sporadic.HeldB
open scoped commutatorElement

theorem heFiveKeys_lt : ∀ p ∈ heFiveKeys, p < 8330 := by decide

theorem heFive_lines_ok :
    linesOKG 5 25 6 8330 heFiveQGens heFiveKeys heFiveQCert heFiveLines = true :=
  heFive_Q_check.1

theorem rep_heFiveLine (j : Fin 6) : Rep 8330 heFiveLines[(j : ℕ)]! (heFiveLine j) :=
  linesOKG_rep heFive_lines_ok j

theorem mem_heAut_of_sift5 {g : Array ℕ} {G : Equiv.Perm (Fin 8330)} (hG : Rep 8330 g G)
    (h : siftA 8330 heFiveRLevels heFiveCase0BaseArr 0 g = true) : G ∈ heAutGroup := by
  rw [← closure_three_eq_heAutGroup]
  exact mem_closure_three_of_siftG (S := heFiveCase0Arrs) (bs := heFiveCase0Base)
    (W := heFiveCase0Words) (by norm_num) (by simp [heFiveCase0Arrs]) (by decide)
    (rep_heGen (by norm_num)) (rep_heGen (by norm_num)) rep_heU heFive_case0_check.1 hG h

theorem heFiveQ_le_P : heFiveQ ≤ heP :=
  closure_le_of_siftG (fun _ hl => enumOK_gens_valid (linesOKG_parts heFive_lines_ok).1 hl)
    heFive_Q_check.2.1 mem_heP_of_siftHe

theorem card_heFiveQ : Nat.card heFiveQ = 25 :=
  linesOKG_card heFiveKeys_lt heFive_lines_ok

theorem heFiveQ_sylow :
    ∃ S : Sylow 5 heP, (S : Subgroup heP) = heFiveQ.subgroupOf heP :=
  linesOKG_sylow_of_card (k := 2) (m := 161215488) (by norm_num) heFiveKeys_lt heFive_lines_ok
    heFiveQ_le_P (by simp [card_heP]) (by norm_num) (by norm_num)

theorem heFiveTransporter_spec (j : Fin 6) :
    heFiveTransporter j ∈ heAutGroup ∧
      heFiveTransporter j * heFiveLine (heFiveRecordOf j) * (heFiveTransporter j)⁻¹ =
        heFiveLine j :=
  trans_spec (L := heFiveLines) mem_heAut_of_sift5 (linesOKG_valid heFive_lines_ok)
    heFive_Q_check.2.2.1 j.2

theorem heFiveRecordOf_eq (j : Fin 6) : heFiveRecordOf j = 0 := by
  have h := rec_mod_memG (cs := List.range 1) heFive_Q_check.2.2.2.1
    (fun i hi => by simp only [List.mem_range] at hi; omega) j.2
  have h' : heFiveRec.getD j 0 % 6 < 1 := List.mem_range.1 h
  exact Fin.ext (by change heFiveRec.getD j 0 % 6 = 0; omega)

theorem heFiveC0_spec :
    heFiveC0 = centralizer {heFiveLine 0} ⊓ heAutGroup ∧ Nat.card heFiveC0 = 600 := by
  obtain ⟨hchain, hcent, -⟩ := heFive_case0_check
  have h := case_centralizerP (S := heFiveCase0Arrs) (bs := heFiveCase0Base)
    (W := heFiveCase0Words) (by norm_num) (by simp [heFiveCase0Arrs]) (by decide)
    (rep_heGen (by norm_num)) (rep_heGen (by norm_num)) rep_heU hchain (rep_heFiveLine 0)
    heFiveKeys_lt hcent
  rw [closure_three_eq_heAutGroup] at h
  exact h

theorem heFiveD0_spec :
    IsSimpleGroup heFiveD0 ∧ (∃ g ∈ heFiveD0, ∃ h ∈ heFiveD0, g * h ≠ h * g) ∧
      Nat.card heFiveD0 = 60 ∧ heFiveD0 ≤ heP ∧
      centralizer (heFiveD0 : Set (Equiv.Perm (Fin 8330))) ⊓ heFiveC0 =
        zpowers (heFiveLine 0) ∧
      Nat.card (centralizer (heFiveD0 : Set (Equiv.Perm (Fin 8330))) ⊓ heFiveC0 :
        Subgroup (Equiv.Perm (Fin 8330))) = 5 := by
  obtain ⟨-, hcent, hxz, hD⟩ := heFive_case0_check
  exact recordD_spec_comm rfl heFiveKeys_lt (centOKP_enum hcent) heFiveC0_spec.1 hD rfl
    (by simp [heFiveC0Gens]) (by norm_num) mem_heP_of_siftHe (rep_heFiveLine 0) hxz
    (linesOKG_orderOf (by norm_num) heFive_lines_ok 0)

theorem R3E_He_full_five_centralizer_structures :
    (heFiveQ ≤ heP ∧ (∃ S : Sylow 5 heP, (S : Subgroup heP) = heFiveQ.subgroupOf heP) ∧
      Nat.card heFiveQ = 25 ∧ Monoid.exponent heFiveQ = 5) ∧
    ({H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heFiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 6 => zpowers (heFiveLine j)) ∧
      Function.Injective (fun j : Fin 6 => zpowers (heFiveLine j))) ∧
    (∀ j : Fin 6, heFiveTransporter j ∈ heAutGroup ∧
      heFiveTransporter j * heFiveLine (heFiveRecordOf j) * (heFiveTransporter j)⁻¹ =
        heFiveLine j) ∧
    (∀ j : Fin 6, heFiveRecordOf j = 0) ∧
    (heFiveC0 = centralizer {heFiveLine 0} ⊓ heAutGroup ∧ Nat.card heFiveC0 = 600) ∧
    (IsSimpleGroup heFiveD0 ∧ (∃ g ∈ heFiveD0, ∃ h ∈ heFiveD0, g * h ≠ h * g) ∧
      Nat.card heFiveD0 = 60 ∧ heFiveD0 ≤ heP ∧
      centralizer (heFiveD0 : Set (Equiv.Perm (Fin 8330))) ⊓ heFiveC0 =
        zpowers (heFiveLine 0) ∧
      Nat.card (centralizer (heFiveD0 : Set (Equiv.Perm (Fin 8330))) ⊓ heFiveC0 :
        Subgroup (Equiv.Perm (Fin 8330))) = 5) :=
  ⟨⟨heFiveQ_le_P, heFiveQ_sylow, card_heFiveQ,
      linesOKG_exponent (by norm_num) (by norm_num) heFiveKeys_lt heFive_lines_ok⟩,
    linesOKG_lines (by norm_num) heFiveKeys_lt heFive_lines_ok, heFiveTransporter_spec,
    heFiveRecordOf_eq, heFiveC0_spec, heFiveD0_spec⟩

end CFSG.RankThree.PartOne

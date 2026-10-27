module

public import Certificates.Certificate8057
public import CFSG.RankThree.PartTwo.KFacts.K426Kit
public import CFSG.RankThree.PartTwo.KFacts.K426A6
public import CFSG.Sporadic.Schreier.PairMcLOrder

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Sporadic.Schreier


theorem mcl3_lines_check :
    linesOK3 3 729 148 275 mcl3QGens mcl3Keys mcl3QCert mcl3Lines = true ∧
      allLt mcl3QGens.size (fun l => siftA 275 PairMcL.levels PairMcL.baseArr 0 mcl3QGens[l]!) =
        true ∧
      transOK2 148 275 mcl3Trans mcl3Lines mcl3Lines mcl3Rec PairMcL.levels PairMcL.baseArr =
        true ∧
      allLt 148 (fun j => decide (mcl3Rec.getD j 0 < 2)) = true :=
  Certificates.certificate8057.1

theorem mcl3_caseA_check :
    caseChainOK2P 275 mcl3ChainAArrs mcl3ChainABaseArr mcl3ChainAWords mclStrongArrs[0]!
        mclStrongArrs[1]! = true ∧
      centOKP 3 275 mcl3ChainAArrs mcl3ChainABaseArr mcl3Lines[0]! mcl3RelsA mcl3CAGens
        mcl3Keys mcl3CACert 29160 = true ∧
      normalOKP 3 275 mcl3CAGens mcl3OGens mcl3Keys mcl3CACert mcl3OCert 243 PairMcL.levels
        PairMcL.baseArr = true :=
  Certificates.certificate8057.2.1

theorem mcl3_caseB_check :
    caseChainOK2P 275 mcl3ChainBArrs mcl3ChainBBaseArr mcl3ChainBWords mclStrongArrs[0]!
        mclStrongArrs[1]! = true ∧
      centOKP 3 275 mcl3ChainBArrs mcl3ChainBBaseArr mcl3Lines[1]! mcl3RelsB mcl3CBGens
        mcl3Keys mcl3CBCert 972 = true :=
  Certificates.certificate8057.2.2

theorem mcl3Keys_lt : ∀ q ∈ mcl3Keys, q < 275 := by decide

theorem mem_mclP_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 275)} (hG : Rep 275 g G)
    (h : siftA 275 PairMcL.levels PairMcL.baseArr 0 g = true) : G ∈ mclP := by
  rw [mclP_eq_original]
  exact (siftA_iff_mem_originalSubgroup mclChainArrays (by norm_num) PairMcL.chain_check.1
    hG).1 h

theorem factorization_card_mclP_three : (Nat.card mclP).factorization 3 = 6 := by
  rw [card_mclP, show (898128000 : ℕ) = 3 ^ 6 * 1232000 by norm_num]
  exact factorization_pow_mulG Nat.prime_three (by norm_num)

@[expose] noncomputable def mcl3Q : Subgroup (Equiv.Perm (Fin 275)) :=
  closure (permsA 275 mcl3QGens)

theorem mcl3Q_le : mcl3Q ≤ mclP := by
  rw [mcl3Q, closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact mem_mclP_of_sift (rep_of_validA (enumOK_gens_valid (linesOK3_parts
    mcl3_lines_check.1).1 hl)) (allLt_spec mcl3_lines_check.2.1 hl)

theorem card_mcl3Q : Nat.card mcl3Q = 3 ^ (Nat.card mclP).factorization 3 := by
  rw [factorization_card_mclP_three, mcl3Q, linesOK3_card mcl3Keys_lt mcl3_lines_check.1]
  norm_num

theorem mcl3Lines_valid {j : ℕ} (hj : j < 148) : validA 275 mcl3Lines[j]! = true :=
  (linesOK3_line mcl3_lines_check.1 hj).1

theorem mcl3_lines {g : Equiv.Perm (Fin 275)} (hg : g ∈ mcl3Q) (hg3 : g ^ 3 = 1) :
    g = 1 ∨ ∃ j < 148, ∃ e < 3, g = permOfArr 275 mcl3Lines[j]! ^ e :=
  linesOK3_spec mcl3Keys_lt mcl3_lines_check.1 hg hg3

theorem mcl3_trans {j : ℕ} (hj : j < 148) :
    permOfArr 275 mcl3Trans[j]! ∈ mclP ∧
      permOfArr 275 mcl3Trans[j]! * permOfArr 275 mcl3Lines[mcl3Rec.getD j 0]! *
        (permOfArr 275 mcl3Trans[j]!)⁻¹ = permOfArr 275 mcl3Lines[j]! :=
  transOK2_spec mem_mclP_of_sift
    (fun j hj => mcl3Lines_valid (lt_trans (of_decide_eq_true
      (allLt_spec mcl3_lines_check.2.2.2 hj)) (by norm_num)))
    (fun j hj => mcl3Lines_valid hj) mcl3_lines_check.2.2.1 hj

theorem mcl3_caseA :
    closure (permsA 275 mcl3CAGens) = centralizer {permOfArr 275 mcl3Lines[0]!} ⊓ mclP ∧
      Nat.card (closure (permsA 275 mcl3CAGens)) = 29160 :=
  case_centralizer2P (by norm_num) (by simp [mcl3ChainAArrs]) (by decide) (rep_mclGen (by norm_num))
    (rep_mclGen (by norm_num)) mcl3_caseA_check.1 (rep_of_validA (mcl3Lines_valid (by norm_num)))
    mcl3Keys_lt mcl3_caseA_check.2.1

theorem mcl3_caseB :
    closure (permsA 275 mcl3CBGens) = centralizer {permOfArr 275 mcl3Lines[1]!} ⊓ mclP ∧
      Nat.card (closure (permsA 275 mcl3CBGens)) = 972 :=
  case_centralizer2P (by norm_num) (by simp [mcl3ChainBArrs]) (by decide) (rep_mclGen (by norm_num))
    (rep_mclGen (by norm_num)) mcl3_caseB_check.1 (rep_of_validA (mcl3Lines_valid (by norm_num)))
    mcl3Keys_lt mcl3_caseB_check.2

theorem mcl3_O :
    closure (permsA 275 mcl3OGens) ≤ closure (permsA 275 mcl3CAGens) ∧
      ((closure (permsA 275 mcl3OGens)).subgroupOf (closure (permsA 275 mcl3CAGens))).Normal ∧
      Nat.card (closure (permsA 275 mcl3OGens)) = 243 := by
  obtain ⟨-, -, hle, hnorm, -, hcard, -⟩ := normal_p Nat.prime_three mcl3Keys_lt
    (centOKP_enum mcl3_caseA_check.2.1) mcl3_caseA_check.2.2 mem_mclP_of_sift (by norm_num)
  exact ⟨hle, hnorm, hcard⟩

theorem noA6_mcl3_caseA : NoA6 (centralizer {permOfArr 275 mcl3Lines[0]!} ⊓ mclP) := by
  rw [← mcl3_caseA.1]
  obtain ⟨hle, hnorm, hcard⟩ := mcl3_O
  exact noA6_of_normal_pGroup hle hnorm (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num))
    (m := 120) (by rw [mcl3_caseA.2, hcard]) (by norm_num)

theorem noA6_mcl3_caseB : NoA6 (centralizer {permOfArr 275 mcl3Lines[1]!} ⊓ mclP) := by
  rw [← mcl3_caseB.1]
  have hbot : ((⊥ : Subgroup (Equiv.Perm (Fin 275))).subgroupOf
      (closure (permsA 275 mcl3CBGens))).Normal := by
    rw [bot_subgroupOf]
    infer_instance
  exact noA6_of_normal_pGroup bot_le hbot (IsPGroup.of_card (n := 0) (by simp)) (m := 972)
    (by rw [mcl3_caseB.2, card_bot, one_mul]) (by norm_num)

theorem noA6_mclP {x : Equiv.Perm (Fin 275)} (hx : x ∈ mclP) (hxo : orderOf x = 3) :
    NoA6 (centralizer {x} ⊓ mclP) := by
  obtain ⟨k, hk, j, hj, e, he, rfl⟩ := exists_conj_rep mcl3Q_le card_mcl3Q
    (fun j => permOfArr 275 mcl3Lines[j]!) (fun c => permOfArr 275 mcl3Lines[c]!)
    (fun j => permOfArr 275 mcl3Trans[j]!) (fun j => mcl3Rec.getD j 0) (r := 148)
    (fun g hg hg3 => mcl3_lines hg hg3) (fun j hj => mcl3_trans hj) hx hxo
  have hrec : mcl3Rec.getD j 0 < 2 := of_decide_eq_true (allLt_spec mcl3_lines_check.2.2.2 hj)
  have hcube := (linesOK3_line mcl3_lines_check.1 (lt_trans hrec (by norm_num : 2 < 148))).2
  have hcase : NoA6 (centralizer {permOfArr 275 mcl3Lines[mcl3Rec.getD j 0]!} ⊓ mclP) := by
    rcases (by omega : mcl3Rec.getD j 0 = 0 ∨ mcl3Rec.getD j 0 = 1) with h | h
    · rw [h]; exact noA6_mcl3_caseA
    · rw [h]; exact noA6_mcl3_caseB
  exact noA6_conj hk hcube hcase he

theorem mclThreeCentralizer : McLThreeCentralizer :=
  noA6_all_of_mulEquiv mclPermEquiv fun _ hx hxo => noA6_mclP hx hxo

end CFSG.RankThree.PartTwo.KFacts.K426

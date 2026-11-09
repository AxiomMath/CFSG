module

public import Certificates.Kernel.Census.Pg.FactsBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAutCard

public section

namespace CertificateChecks.KernelPg

open CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
  CFSG.KC.W16Pg CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2

theorem chain_ok : chainCheck = true := by
  have hA : ChainArrays (RawSchreierDatum.ofArrays 128 (by norm_num) sgsArr 36 (by decide)
      [32, 64, 1, 2, 15, 22] (by decide) wordsArr) (sgsArr.extract 0 36) sgsArr baseArr wordsArr :=
    chainArrays_ofArrays (chainCheckFacts chain_zero).strong_inv
  have hord : (rawOrbitSizes 128 sgsArr baseArr).prod = 3317760 := by
    rw [rawOrbitSizesK_sound binds perm C.hl, orbProd]
  have hle : (RawSchreierDatum.ofArrays 128 (by norm_num) sgsArr 36 (by decide)
      [32, 64, 1, 2, 15, 22] (by decide) wordsArr).levelSubgroup 0 ≤ AutC := by
    rw [RawSchreierDatum.levelSubgroup, RawSchreierDatum.levelGenerators_zero, Subgroup.closure_le]
    intro g hg
    change g ∈ (Vector.ofFn fun j : Fin sgsArr.size => permOfArr 128 sgsArr[(j : ℕ)]!).toList at hg
    rw [Vector.toList_ofFn, List.mem_ofFn] at hg
    obtain ⟨j, rfl⟩ := hg
    exact permOfArr_mem_autC j.2
  have hc := (Subgroup.card_le_of_le hle).trans card_autC_le
  rw [← hord, ← hA.orderCertificate_eq (chainCheckFacts chain_zero)] at hc
  unfold chainCheck
  rw [Bool.and_eq_true, hord]
  exact ⟨rawChainOK_of_card hA chain_zero hc 4, rfl⟩

theorem cert27820 : tableCheck = true ∧ autCheck = true ∧ chainCheck = true ∧ genCheck = true ∧
    candCheck = true :=
  ⟨table_ok', aut_ok', chain_ok, gen_ok', cand_ok'⟩

end CertificateChecks.KernelPg

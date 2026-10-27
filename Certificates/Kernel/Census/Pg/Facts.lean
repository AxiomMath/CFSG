module

public import Certificates.Kernel.Census.Pg.Chain
public import CFSG.Certificates.Kernel.W16PgSound
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Misc.ArrBind

public section

namespace CertificateChecks.KernelPg

open CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
  CFSG.KC.W16Pg

theorem binds : Binds 128 8 C.S 36 6 C.BP sgsArr baseArr :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, fun j hj => arrBind_sound (bS j hj),
    by decide +kernel, bget⟩

theorem bindE : BindE ET := fun a ha => arrBind_sound (bE a ha)

theorem words_eq : wordsArr = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 36 36 dNil := by
  apply Array.ext
  · simp [wordsArr, CFSG.Sporadic.Schreier.Co3.Native.wordsArr]
  · intro i h1 h2
    simp [wordsArr, CFSG.Sporadic.Schreier.Co3.Native.wordsArr, dNil]

theorem chain_ok : chainCheck = true := by
  unfold chainCheck
  rw [Bool.and_eq_true, words_eq, rawOrbitSizesK_sound binds perm C.hl, orbProd]
  exact ⟨rawChainK_sound binds C.head C.hl hNS C.hs, rfl⟩

theorem table_ok' : tableCheck = true := by
  rw [tableCheck_eq bindE]
  exact table_ok

theorem mulC_lt' : ∀ a < 128, ∀ b < 128, mulC a b < 128 := by
  have h := table_ok'
  unfold tableCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1

theorem cert27820 : tableCheck = true ∧ autCheck = true ∧ chainCheck = true ∧ genCheck = true ∧
    candCheck = true :=
  ⟨table_ok', autCheck_of bindE (by decide +kernel) (fun j hj => arrBind_sound (bS j hj))
      mulC_lt' aut_ok, chain_ok, by rw [genCheck_eq bindE]; exact gen_ok,
    by rw [candCheck_eq bindE]; exact cand_ok⟩

end CertificateChecks.KernelPg

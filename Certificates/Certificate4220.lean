module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresWords
import Certificates.Kernel.CosetCC.C4220
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Misc.Coset.PGFilter

public section

open CFSG.CosetTable CFSG.Quasithin.Fan86 CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate4220_rels_a :
    (p1Words.filter (· ≠ [])).map encW = CFSG.KBRoute.F4220a.rels := by
  decide +kernel

private theorem certificate4220_rels_b :
    (restrictWords (subsetOf 13 [0, 1]) (p1Words.filter (· ≠ []))).map encW =
      CFSG.KBRoute.F4220b.rels := by
  decide +kernel

open CFSG.CosetTable CFSG.Quasithin.Fan86 in
theorem certificate4220 : Finite (PG 13 p1Words) ∧ Nat.card (PG 13 p1Words) ≤ 5 * 2 ^ 11 := by
  have ha := CFSG.KBFact.F4220a
  have hb := CFSG.KBFact.F4220b
  rw [← certificate4220_rels_a] at ha
  rw [← certificate4220_rels_b] at hb
  have h := TableFact.card_restrict (p1Words.filter (· ≠ [])) (by norm_num) (subsetOf 13 [0, 1])
    (by decide) ha hb
  rw [PG_filter_ne_nil] at h
  exact ⟨h.1, h.2.trans (by norm_num)⟩

end Certificates

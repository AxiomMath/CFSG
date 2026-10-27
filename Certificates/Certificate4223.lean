module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresWords
import Certificates.Kernel.CosetCC.C4220
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Misc.Coset.PGFilter

public section

open CFSG.CosetTable CFSG.Quasithin.Fan86 CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate4223_rels_a :
    (p2cWords.filter (· ≠ [])).map encW = CFSG.KBRoute.F4223a.rels := by
  decide +kernel

private theorem certificate4223_rels_b :
    (restrictWords (subsetOf 15 [0, 1]) (p2cWords.filter (· ≠ []))).map encW =
      CFSG.KBRoute.F4223b.rels := by
  decide +kernel

open CFSG.CosetTable CFSG.Quasithin.Fan86 in
theorem certificate4223 : Finite (PG 15 p2cWords) ∧ Nat.card (PG 15 p2cWords) ≤ 3 * 2 ^ 12 := by
  have ha := CFSG.KBFact.F4223a
  have hb := CFSG.KBFact.F4223b
  rw [← certificate4223_rels_a] at ha
  rw [← certificate4223_rels_b] at hb
  have h := TableFact.card_restrict (p2cWords.filter (· ≠ [])) (by norm_num) (subsetOf 15 [0, 1])
    (by decide) ha hb
  rw [PG_filter_ne_nil] at h
  exact ⟨h.1, h.2.trans (by norm_num)⟩

end Certificates

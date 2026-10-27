module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresWords
import Certificates.Kernel.CosetCC.C4220
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Misc.Coset.PGFilter

public section

open CFSG.CosetTable CFSG.Quasithin.Fan86 CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate4221_rels_a :
    (p1cWords.filter (· ≠ [])).map encW = CFSG.KBRoute.F4221a.rels := by
  decide +kernel

private theorem certificate4221_rels_b :
    (restrictWords (subsetOf 14 [0, 1]) (p1cWords.filter (· ≠ []))).map encW =
      CFSG.KBRoute.F4221b.rels := by
  decide +kernel

open CFSG.CosetTable CFSG.Quasithin.Fan86 in
theorem certificate4221 : Finite (PG 14 p1cWords) ∧ Nat.card (PG 14 p1cWords) ≤ 5 * 2 ^ 12 := by
  have ha := CFSG.KBFact.F4221a
  have hb := CFSG.KBFact.F4221b
  rw [← certificate4221_rels_a] at ha
  rw [← certificate4221_rels_b] at hb
  have h := TableFact.card_restrict (p1cWords.filter (· ≠ [])) (by norm_num) (subsetOf 14 [0, 1])
    (by decide) ha hb
  rw [PG_filter_ne_nil] at h
  exact ⟨h.1, h.2.trans (by norm_num)⟩

end Certificates

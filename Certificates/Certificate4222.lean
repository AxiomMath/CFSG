module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresWords
import Certificates.Kernel.CosetCC.C4220
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Misc.Coset.PGFilter

public section

open CFSG.CosetTable CFSG.Quasithin.Fan86 CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate4222_rels_a :
    (p2Words.filter (· ≠ [])).map encW = CFSG.KBRoute.F4222a.rels := by
  decide +kernel

private theorem certificate4222_rels_b :
    (restrictWords (subsetOf 14 [0, 1]) (p2Words.filter (· ≠ []))).map encW =
      CFSG.KBRoute.F4222b.rels := by
  decide +kernel

open CFSG.CosetTable CFSG.Quasithin.Fan86 in
theorem certificate4222 : Finite (PG 14 p2Words) ∧ Nat.card (PG 14 p2Words) ≤ 3 * 2 ^ 11 := by
  have ha := CFSG.KBFact.F4222a
  have hb := CFSG.KBFact.F4222b
  rw [← certificate4222_rels_a] at ha
  rw [← certificate4222_rels_b] at hb
  have h := TableFact.card_restrict (p2Words.filter (· ≠ [])) (by norm_num) (subsetOf 14 [0, 1])
    (by decide) ha hb
  rw [PG_filter_ne_nil] at h
  exact ⟨h.1, h.2.trans (by norm_num)⟩

end Certificates

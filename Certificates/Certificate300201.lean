module

public import CFSG.Quasithin.Background.Harris.R1.J2VertWords
import Certificates.Kernel.CosetCC.C300201
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.CosetTablePresented
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.CosetTable CFSG.Quasithin.Background.Harris.R1.J2Vert CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate300201_rels_a :
    (vRels true).map encW = CFSG.KBRoute.F300201a.rels := by decide +kernel

private theorem certificate300201_rels_b :
    (restrictWords (subsetOf 8 [5, 6]) (vRels true)).map encW = CFSG.KBRoute.F300201b.rels := by
  decide +kernel

private theorem certificate300201_rels_c :
    (vRels false).map encW = CFSG.KBRoute.F300201c.rels := by decide +kernel

private theorem certificate300201_rels_d :
    (restrictWords (subsetOf 8 [5, 6]) (vRels false)).map encW = CFSG.KBRoute.F300201d.rels := by
  decide +kernel

open CFSG.CosetTable CFSG.Quasithin.Background.Harris.R1.J2Vert in
theorem certificate300201 : ∀ ε : Bool, Finite (PG 8 (vRels ε)) ∧ Nat.card (PG 8 (vRels ε)) ≤ 3840 := by
  have ha := CFSG.KBFact.F300201a
  have hb := CFSG.KBFact.F300201b
  have hc := CFSG.KBFact.F300201c
  have hd := CFSG.KBFact.F300201d
  rw [← certificate300201_rels_a] at ha
  rw [← certificate300201_rels_b] at hb
  rw [← certificate300201_rels_c] at hc
  rw [← certificate300201_rels_d] at hd
  intro ε
  cases ε
  · exact TableFact.card_restrict (vRels false) (by norm_num) (subsetOf 8 [5, 6]) (by decide) hc hd
  · exact TableFact.card_restrict (vRels true) (by norm_num) (subsetOf 8 [5, 6]) (by decide) ha hb

end Certificates

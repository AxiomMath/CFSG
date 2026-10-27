module

public import CFSG.Quasithin.Background.Harris.R1.D4VertWords
import Certificates.Kernel.CosetCC.C300204
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.CosetTablePresented
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.CosetTable CFSG.Quasithin.Background.Harris.R1.D4Vert CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate300204_rels_a : l28Rels.map encW = CFSG.KBRoute.F300204a.rels := by
  decide +kernel

private theorem certificate300204_rels_b :
    (l28Tw true false).map encW = CFSG.KBRoute.F300204b.rels := by decide +kernel

private theorem certificate300204_rels_c :
    (l28Tw false true).map encW = CFSG.KBRoute.F300204c.rels := by decide +kernel

private theorem certificate300204_rels_d :
    (l28Tw true true).map encW = CFSG.KBRoute.F300204d.rels := by decide +kernel

private theorem certificate300204_rels_e : hRels.map encW = CFSG.KBRoute.F300204e.rels := by
  decide +kernel

private theorem certificate300204_rels_f :
    (restrictWords (subsetOf 4 [2, 3]) hRels).map encW = CFSG.KBRoute.F300204f.rels := by
  decide +kernel

private theorem certificate300204_rels_g : nRels.map encW = CFSG.KBRoute.F300204g.rels := by
  decide +kernel

private theorem certificate300204_rels_h :
    (restrictWords (subsetOf 5 [2, 3, 4]) nRels).map encW = CFSG.KBRoute.F300204h.rels := by
  decide +kernel

open CFSG.CosetTable CFSG.Quasithin.Background.Harris.R1.D4Vert in
theorem certificate300204 :
    (Finite (PG 2 l28Rels) ∧ Nat.card (PG 2 l28Rels) ≤ 504)
    ∧ (∀ e₁ e₄ : Bool, (e₁ = true ∨ e₄ = true) →
        Finite (PG 3 (l28Tw e₁ e₄)) ∧ Nat.card (PG 3 (l28Tw e₁ e₄)) ≤ 504)
    ∧ (Finite (PG 4 hRels) ∧ Nat.card (PG 4 hRels) ≤ 258048)
    ∧ (Finite (PG 5 nRels) ∧ Nat.card (PG 5 nRels) ≤ 86016) := by
  have ha := CFSG.KBFact.F300204a
  have hb := CFSG.KBFact.F300204b
  have hc := CFSG.KBFact.F300204c
  have hd := CFSG.KBFact.F300204d
  have he := CFSG.KBFact.F300204e
  have hf := CFSG.KBFact.F300204f
  have hg := CFSG.KBFact.F300204g
  have hh := CFSG.KBFact.F300204h
  rw [← certificate300204_rels_a] at ha
  rw [← certificate300204_rels_b] at hb
  rw [← certificate300204_rels_c] at hc
  rw [← certificate300204_rels_d] at hd
  rw [← certificate300204_rels_e] at he
  rw [← certificate300204_rels_f] at hf
  rw [← certificate300204_rels_g] at hg
  rw [← certificate300204_rels_h] at hh
  refine ⟨TableFact.card l28Rels (by norm_num) ha, ?_,
    TableFact.card_restrict hRels (by norm_num) (subsetOf 4 [2, 3]) (by decide) he hf,
    TableFact.card_restrict nRels (by norm_num) (subsetOf 5 [2, 3, 4]) (by decide) hg hh⟩
  intro e₁ e₄ h
  cases e₁ <;> cases e₄
  · simp at h
  · exact TableFact.card (l28Tw false true) (by norm_num) hc
  · exact TableFact.card (l28Tw true false) (by norm_num) hb
  · exact TableFact.card (l28Tw true true) (by norm_num) hd

end Certificates

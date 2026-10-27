module

public import Certificates.Kernel.CosetCC.C26963A
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.Kernel.Misc.Coset.PGFilter
public import CFSG.Sporadic.Recognition.HNMult3Words

public section

namespace CertificateChecks.KernelC26963

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.HNMult3
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers

@[expose] def decW3 (w : List (ℕ × Bool)) : List (Fin 3 × Bool) :=
  w.filterMap fun l => if h : l.1 < 3 then some (⟨l.1, h⟩, l.2) else none

@[expose] def wsA : List (List (Fin 3 × Bool)) := CFSG.KBRoute.F26963a.rels.map decW3

theorem wsA_enc : wsA.map encW = CFSG.KBRoute.F26963a.rels := by decide +kernel

theorem wsA_restrict : (restrictWords [(2 : Fin 3)] wsA).map encW = CFSG.KBRoute.F26963b.rels := by
  decide +kernel

theorem wsA_perm :
    wsA.Perm (coverWords hn3Rels hn3Cw ++ cubeWords hn3Rels ++ powWords hn3Ord) := by
  decide +kernel

theorem wsA_mem (w : List (Fin 3 × Bool)) : w ∈ wsA ↔ w ∈ hn3Cover := by
  rw [wsA_perm.mem_iff, hn3Cover, cover₃Words, (List.mergeSort_perm _ _).mem_iff]

theorem card_hn3Cover_le : Finite (PG 3 hn3Cover) ∧ Nat.card (PG 3 hn3Cover) ≤ 58320 := by
  have ha := CFSG.KBFact.F26963a
  rw [← wsA_enc] at ha
  have hb := CFSG.KBFact.F26963b
  rw [← wsA_restrict] at hb
  obtain ⟨f, c⟩ := TableFact.card_restrict wsA (by norm_num) [(2 : Fin 3)] (by decide) ha hb
  rw [← PG_congr_mem wsA_mem]
  exact ⟨f, c.trans (by norm_num)⟩

end CertificateChecks.KernelC26963

end

module

public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplierInputs
import Certificates.Kernel.CosetCC.C24052A
import Certificates.Kernel.Fi24PG10.Rels
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
  CFSG.Sporadic.Presentation.Fi24Prime CertificateChecks.KernelPG10 CFSG.KC.MiscCoset

namespace CertificateChecks.Batch24052

open CFSG.CosetTable CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
  CFSG.Sporadic.Presentation.Fi24Prime CertificateChecks.KernelPG10 CFSG.KC.MiscCoset

private def wsNat (L : List (List (ℕ × Bool))) : List (List (ℕ × Bool)) :=
  (L.filter fun w => !(w.any fun l => l.1 == 8)).map (·.map fun l => (l.1 % 22, l.2)) ++
    [(L.getD r0Idx []).map fun l => (l.1 % 22, l.2)] ++
    (List.range 11).flatMap fun k =>
      [(L.getD (repIdx.getD k 0) []).map (fun l => (l.1 % 22, l.2)) ++ [((11 + k) % 22, false)],
        [((11 + k) % 22, true), ((11 + k) % 22, true)]] ++
      (List.range 11).map fun i =>
        [((11 + k) % 22, true), (i % 22, true), ((11 + k) % 22, false), (i % 22, false)]

private theorem wsN_map : wsN.map encW = wsNat (X0.map toNw) := by
  have hget : ∀ i, (X0.map toNw).getD i [] = toNw (X0.getD i []) := fun i => by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases X0[i]? <;> rfl
  simp only [wsNat, hget]
  simp only [wsN, centralWords, encW, toNw, liftL, zeta, List.map_append, List.map_cons,
    List.map_nil, List.map_flatMap, List.map_map, Function.comp_def, List.filter_map,
    List.any_map, Fin.val_ofNat]

private theorem rels_eq : wsN.map encW = CFSG.KBRoute.F24052.rels := by
  rw [wsN_map, x0_letters]
  decide +kernel

end CertificateChecks.Batch24052

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.Sporadic.Recognition.Fi24PrimeMultiplier in
theorem certificate24052 : (genSub {r : FreeGroup (Fin nG) | r ∈ wsN.map FreeGroup.mk}
      (subsetOf nG [0, 1, 2, 3, 4, 5, 6, 7, 9, 10])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin nG) | r ∈ wsN.map FreeGroup.mk}
      (subsetOf nG [0, 1, 2, 3, 4, 5, 6, 7, 9, 10])).index ≤ 306936 := by
  have h := CFSG.KBFact.F24052
  rw [← CertificateChecks.Batch24052.rels_eq] at h
  exact TableFact.genSub_index wsN (by norm_num) (subsetOf nG [0, 1, 2, 3, 4, 5, 6, 7, 9, 10]) h

end Certificates

module

public import Certificates.Data.J4Loc.I5Native
public import Certificates.Kernel.J4Loc.I5Asm
public import Certificates.Certificate4008Base
public import Certificates.Kernel.J4Loc.TrioAsm

public section

namespace Certificates

open CFSG.Quasithin.J4Loc CertificateChecks.KernelJ4Loc

open CFSG.Quasithin.J4Loc CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 in
theorem certificate4177 :
    (∀ p ∈ ([(965, 1243), (1979, 1979), (165, 165)] : List (ℕ × ℕ)),
      mulRows (mulRows (pathRows (repPaths.getD 5 []))
        (etaRows (uTab (locMats ()) (locInvs ())) 11 p.1))
        (CFSG.Sporadic.J4.Native.invRows (pathRows (repPaths.getD 5 []))) =
        etaRows (uTab (locMats ()) (locInvs ())) 11 p.2) ∧
    i5Masks.toFinset ∈ TrioOct := by
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact CFSG.Sporadic.J4.eqRows_iff.1 (k4177_rows (k := 0) (by norm_num))
    · exact CFSG.Sporadic.J4.eqRows_iff.1 (k4177_rows (k := 1) (by norm_num))
    · exact CFSG.Sporadic.J4.eqRows_iff.1 (k4177_rows (k := 2) (by norm_num))
  · have h : i5Masks.toFinset = ({0, 965, 1979, 1243, 165, 864, 1822, 1150} : Finset ℕ) := by
      ext x
      simp only [i5Masks, srt, i5Pairs, List.mem_toFinset, List.mem_mergeSort, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert,
        Finset.mem_singleton]
    rw [h]
    exact k4177_oct_mem

end Certificates

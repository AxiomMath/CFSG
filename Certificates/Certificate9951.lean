module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23OrbitInputs

public section

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.G3
  CFSG.QuasithinUnique.A5.G3.M23
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

namespace CertificateChecks.Batch9951

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.G3
  CFSG.QuasithinUnique.A5.G3.M23
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

private theorem tGens_fix_zero : ∀ g ∈ tGens, g 0 = 0 := by
  intro g hg'
  simp only [tGens, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl | rfl <;>
    decide +kernel

private theorem pat_zero :
    ∀ y : Fin 23, ![true, false, false, false] (tau y) = true ↔ tau y = 0 := by
  decide +kernel

private theorem pat_zero_one_card :
    (Finset.univ.filter (fun y => ![true, true, false, false] (tau y) = true)).card = 3 := by
  decide +kernel

private theorem pat_zero_two :
    ∀ y : Fin 23, ![true, false, true, false] (tau y) = true ↔ (tau y = 0 ∨ tau y = 2) := by
  decide +kernel

private theorem tau_nineteen : (tau 19 = 0 ∨ tau 19 = 2) → False := by
  decide +kernel

private theorem pat_one :
    ∀ y : Fin 23, ![false, true, false, false] (tau y) = true ↔ tau y = 1 := by
  decide +kernel

end CertificateChecks.Batch9951

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.G3
  CFSG.QuasithinUnique.A5.G3.M23 in
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
theorem certificate9951 : (∀ g ∈ tGens, g 0 = 0)
    ∧ (∀ y : Fin 23, ![true, false, false, false] (tau y) = true ↔ tau y = 0)
    ∧ ((Finset.univ.filter (fun y => ![true, true, false, false] (tau y) = true)).card = 3)
    ∧ (∀ y : Fin 23, ![true, false, true, false] (tau y) = true ↔ (tau y = 0 ∨ tau y = 2))
    ∧ ((tau 19 = 0 ∨ tau 19 = 2) → False)
    ∧ (∀ y : Fin 23, ![false, true, false, false] (tau y) = true ↔ tau y = 1) := by
  exact ⟨CertificateChecks.Batch9951.tGens_fix_zero, CertificateChecks.Batch9951.pat_zero, CertificateChecks.Batch9951.pat_zero_one_card,
    CertificateChecks.Batch9951.pat_zero_two, CertificateChecks.Batch9951.tau_nineteen, CertificateChecks.Batch9951.pat_one⟩

end Certificates

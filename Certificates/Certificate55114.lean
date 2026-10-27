module

public import Certificates.Data.GH74.AE117
import Certificates.Kernel.Census.AE117.Adj7
import Certificates.Kernel.Census.AE117.Adj56
import Certificates.Kernel.Census.AE117.Rest
import CFSG.Certificates.Kernel.AE117AdjSound

public section

namespace Certificates

open Certificates.Kernel.AE117Adj CertificateChecks.KernelCensus

theorem certificate55114 : (AE117.adjCheck 5 () = true ∧ AE117.adjCheck 6 () = true ∧
      AE117.adjCheck 7 () = true) ∧
    (AE117.cocCheck₅ () = true ∧ AE117.cocCheck₆ () = true ∧ AE117.cocCheck₇ () = true) ∧
    (AE117.genCheck₅ () = true ∧ AE117.genCheck₆ () = true ∧ AE117.genCheck₇ () = true) ∧
    (AE117.spanCheck 5 () = true ∧ AE117.spanCheck 6 () = true ∧ AE117.spanCheck 7 () = true) :=
  ⟨⟨adjCheck_of adjCheckL_five, adjCheck_of adjCheckL_six, adjCheck_of adjCheckL_seven⟩,
    ⟨cocCheck₅_eq, cocCheck₆_eq, cocCheck₇_eq⟩, ⟨genCheck₅_eq, genCheck₆_eq, genCheck₇_eq⟩,
    ⟨spanCheck_five, spanCheck_six, spanCheck_seven⟩⟩

end Certificates

module

public import CFSG.Sporadic.Co1I301.Inputs

public section

namespace CertificateChecks.KernelCo1I301

open CFSG.Sporadic.Co1I301.Native CFSG.Sporadic.Co1Patterson.Native

def r0Arr : Array (Array Nat) := r0Gens ()

def dGs : List (Array (Array Nat)) := [brayArr]

def dGis : List (Array (Array Nat)) := [brayInvArr]

def dRs : List (Array Nat) := [dRw ()]

def dCs : List Nat := [8961]

end CertificateChecks.KernelCo1I301

end

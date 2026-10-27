module

public import Certificates.Data.P43Twin
public import CFSG.Monster.B.Mathieu.Order

public section

namespace CertificateChecks.KernelA45

open CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] def img (g : Equiv.Perm (Fin 45)) : Array ℕ := (CFSG.Monster.B.Mathieu.imageList g).toArray

@[expose] def wv (w : List ℕ) : Equiv.Perm (Fin 45) :=
  w.foldl (fun g k => g * [x45, y45, f45].getD k 1) 1

@[expose] def gA : Array (Array ℕ) := #[img x45, img y45, img f45]

@[expose] def ps : List ℕ := [0, 1, 3, 9]

@[expose] def rA : Array ℕ := img (Certificates.P43Twin.tA ())

@[expose] def rB : Array ℕ := img (Certificates.P43Twin.tB ())

@[expose] def r36 : Array ℕ := img (Certificates.P43Twin.t36 ())

@[expose] def r540 : Array ℕ := img (Certificates.P43Twin.t540 ())

@[expose] def sW : List (List ℕ) :=
  [[1, 1, 1, 2, 1, 2, 1, 2, 1, 0, 1, 0, 1, 1, 2], [1, 2, 1, 1, 2, 1, 2, 0, 1, 2, 0, 1, 1],
    [1, 1, 0, 1, 2, 1, 1, 0, 1, 1, 0, 1, 2], [2]]

@[expose] def cW : List (List ℕ) := [[0], [2], [1, 0, 1, 1]]

@[expose] def sGen : Array (Array ℕ) := (sW.map fun w => img (wv w)).toArray

@[expose] def cGen : Array (Array ℕ) := (cW.map fun w => img (wv w)).toArray

end CertificateChecks.KernelA45

end

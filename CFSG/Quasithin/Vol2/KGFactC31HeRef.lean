
module


public import Certificates.Certificate7223

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Sporadic.HeldB _root_.Certificates

theorem c_letters :
    (eW ++ qW ++ lsGenW ++ njW).all (lettersOK 2) = true := by
  refine List.all_eq_true.2 fun w hw => List.all_eq_true.2 fun l hl => ?_
  obtain ⟨h0, h2⟩ := Certificates.certificate7223.1.1 w hw l hl
  simpa [h0] using h2

theorem c_w5 : w5W = eW.take 4 := Certificates.certificate7223.1.2.1

theorem c_w7 : w7W = qW.take 3 := Certificates.certificate7223.1.2.2.1

theorem c_eLen : eW.length = 6 := Certificates.certificate7223.1.2.2.2.1

theorem c_qLen : qW.length = 4 := Certificates.certificate7223.1.2.2.2.2

theorem c_basisE : EBasis (fun i : Fin 6 => elt (eW.getD i [])) :=
  Certificates.certificate7223.2.1.1

theorem c_basisQ : EBasis (fun i : Fin 4 => elt (qW.getD i [])) :=
  Certificates.certificate7223.2.1.2

theorem c_centE {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (hc : ∀ i : Fin 4, x * elt (eW.getD i []) = elt (eW.getD i []) * x) : x ∈ heE :=
  Certificates.certificate7223.2.2.1.1 x hx hc

theorem c_centQ {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (hc : ∀ i : Fin 3, x * elt (qW.getD i []) = elt (qW.getD i []) * x) : x ∈ heQ :=
  Certificates.certificate7223.2.2.1.2 x hx hc

theorem c_cardNs : Nat.card nsGrp = 138240 :=
  Certificates.certificate7223.2.2.2.1.1

theorem c_cardLs : Nat.card lGrp = 69120 :=
  Certificates.certificate7223.2.2.2.1.2.1

theorem c_cardN7 : Nat.card n7Grp = 21504 :=
  Certificates.certificate7223.2.2.2.1.2.2.1

theorem c_normNs :
    nsGrp ≤ heP ⊓ Subgroup.normalizer (heE : Set (Equiv.Perm (Fin 8330))) :=
  Certificates.certificate7223.2.2.2.1.2.2.2.1

theorem c_normN7 :
    n7Grp ≤ heP ⊓ Subgroup.normalizer (heQ : Set (Equiv.Perm (Fin 8330))) :=
  Certificates.certificate7223.2.2.2.1.2.2.2.2.1

theorem c_normL :
    lGrp ≤ Subgroup.normalizer (heE : Set (Equiv.Perm (Fin 8330))) :=
  Certificates.certificate7223.2.2.2.1.2.2.2.2.2.1

theorem c_normNj :
    ∀ n ∈ njW, elt n ∈ Subgroup.normalizer (heE : Set (Equiv.Perm (Fin 8330))) :=
  Certificates.certificate7223.2.2.2.1.2.2.2.2.2.2.1

theorem c_y5 : orderOf (elt y5W) = 5 :=
  Certificates.certificate7223.2.2.2.1.2.2.2.2.2.2.2.1

theorem c_EL : heE ≤ lGrp :=
  Certificates.certificate7223.2.2.2.1.2.2.2.2.2.2.2.2

theorem c_LB :
    ∀ w ∈ lsGenW, ∀ p : Fin 8330, (p : ℕ) ∈ bB → ((elt w p : Fin 8330) : ℕ) ∈ bB :=
  Certificates.certificate7223.2.2.2.2.1

theorem c_EB :
    ∀ i : Fin 6, ∀ p : Fin 8330, (p : ℕ) ∈ bB → elt (eW.getD i []) p = p :=
  Certificates.certificate7223.2.2.2.2.2.1

theorem c_ker :
    Nat.card {x : lGrp // ∀ p : Fin 8330, (p : ℕ) ∈ bB → (x : Equiv.Perm (Fin 8330)) p = p} =
      192 :=
  Certificates.certificate7223.2.2.2.2.2.2

end CFSG.Quasithin.KGC31.He

end

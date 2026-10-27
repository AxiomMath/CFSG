module

public import CFSG.Sporadic.Recognition.McLCentralizer
public import Certificates.Certificate21000

public section

namespace CFSG.Sporadic.Recognition.McLCentralizer

open Subgroup

theorem mooreCheck_eq_true : mooreCheck = true :=
  Certificates.certificate21000.1

theorem liftCheck_eq_true : liftCheck = true :=
  Certificates.certificate21000.2

theorem mcl_involution_centralizer_alt8_of_certificate
    {T : Type*} [Group T] (hT : Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.McL)) {t : T}
    (ht : orderOf t = 2) :
    Group.IsPerfect (centralizer ({t} : Set T)) ∧
    center (centralizer ({t} : Set T)) =
      zpowers (⟨t, self_mem_centralizer t⟩ : centralizer ({t} : Set T)) ∧
    Nonempty (centralizer ({t} : Set T) ⧸
      zpowers (⟨t, self_mem_centralizer t⟩ : centralizer ({t} : Set T)) ≃*
        alternatingGroup (Fin 8)) :=
  mcl_involution_centralizer_alt8 mooreCheck_eq_true liftCheck_eq_true hT ht

end CFSG.Sporadic.Recognition.McLCentralizer

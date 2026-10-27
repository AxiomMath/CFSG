module

public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.Schreier.PairHSCheck
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public import CFSG.Sporadic.SmallOddCore.HSCheckInputs
public import Certificates.Certificate2272

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native Subgroup
open CFSG.Monster.B.Co2.Native

theorem hs_stab_facts :
    ∀ x : Fin 3850, x ≠ 0 → ∃ s ∈ hsP, s 0 = 0 ∧ s x ≠ x :=
  Certificates.certificate2272.1

theorem hs_rep_a :
    (permOK 3850 (hsCentTbl 5) && tblEq 3850 (hsCentTbl 5) hsPGTbls[0]!) = true :=
  Certificates.certificate2272.2.1

theorem hs_u_facts :
    hsU ^ 2 = 1 ∧ hsU ≠ 1 ∧ hsU ∉ hsP ∧ ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP :=
  Certificates.certificate2272.2.2.1

theorem hs_rows_facts :
    ∀ r ∈ hsRows, permOK 3850 r.rep = true ∧ tp 3850 r.rep ∈ hsR ∧
      orderOf (tp 3850 r.rep) = 2 ∧ (r.outer = true ↔ tp 3850 r.rep ∉ hsP) ∧
      CFSG.Sporadic.SmallOddCore.hsC r =
        hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) ∧
      Nat.card ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) =
        r.centOrder ∧
      (conjClass hsP (tp 3850 r.rep)).ncard = r.classSize ∧
      CFSG.oddCore ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) = ⊥ :=
  Certificates.certificate2272.2.2.2.1

theorem hs_sylow_facts : hsS ≤ hsR ∧ Nat.card hsS = 1024 :=
  Certificates.certificate2272.2.2.2.2.1

theorem hs_cover :
    ∀ t ∈ hsR, orderOf t = 2 → ∃ r ∈ hsRows, ∃ g ∈ hsP, t = g * tp 3850 r.rep * g⁻¹ :=
  Certificates.certificate2272.2.2.2.2.2.1

theorem hs_witness34 :
    ∃ x ∈ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set (Equiv.Perm (Fin 3850))),
      orderOf x = 5 ∧
      ∃ y ∈ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set (Equiv.Perm (Fin 3850))),
        orderOf (x * (y * x * y⁻¹)) = 6 :=
  Certificates.certificate2272.2.2.2.2.2.2.1

theorem hs_sylowGens_permOK :
    ∀ T ∈ hsSylowGenTbls, permOK 3850 T = true :=
  Certificates.certificate2272.2.2.2.2.2.2.2

end CFSG.Sporadic.SmallOddCore

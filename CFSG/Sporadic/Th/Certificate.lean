
module


public import Certificates.Certificate1021
public import CFSG.Assembly.Defs

public section

namespace CFSG.Sporadic.Th

theorem th_kernel_facts :
    Kernel.KernelFacts :=
  Certificates.certificate1021.facts

theorem card_nativeTh_kernel :
    Nat.card Blueprint.NativeSporadic.Th = 90745943887872000 := by
  rw [Nat.card_congr thEquivJ.toEquiv]
  exact Kernel.card_J_eq th_kernel_facts

theorem y_cube_kernel :
    yJ ^ 3 = 1 :=
  Certificates.certificate1021.y_cube

theorem centralizer_a_eq_M_kernel :
    Subgroup.centralizer ({a} : Set J) = Max3.M :=
  Certificates.certificate1021.cent_a

theorem exists_cent7_kernel :
    ∃ z : J, orderOf z = 7 ∧ Nat.card (Subgroup.centralizer ({z} : Set J)) ≤ 1176 :=
  Certificates.certificate1021.cent7

theorem exists_cent5_kernel :
    ∃ x : J, orderOf x = 5 ∧ Nat.card (Subgroup.centralizer ({x} : Set J)) ≤ 3000 :=
  Certificates.certificate1021.cent5

end CFSG.Sporadic.Th

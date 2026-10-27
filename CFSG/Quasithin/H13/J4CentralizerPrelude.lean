module

public import CFSG.Quasithin.H13.J4CentralizerBase4

public import CFSG.Quasithin.H13.J4FixCheck
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4WordsInputs
public import CFSG.Quasithin.H13.J4ChainSpec
public import Certificates.Data.CFSGNative.H13.J4Elems
public import CFSG.Quasithin.H13.J4FixSpec
public import CFSG.Sporadic.Schreier.J4SLocal
public import CFSG.Sporadic.J4.Local
public import CFSG.Quasithin.H13.J4ClassCheckInputs
public import Certificates.Data.CFSGNative.H13.J4Class
public import CFSG.Sporadic.Schreier.J4SKCent

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4

theorem isConj_tJ_e2
    : IsConj tJ J4Classes.e2 := tS_eq_tJ ▸ J4Classes.isConj_tS_e2

theorem isConj_tJ_e3
    : IsConj tJ J4Classes.e3 := tS_eq_tJ ▸ J4Classes.isConj_tS_e3

theorem hClass_disjoint {e e' : J} (h : (hClass e).ncard ≠ (hClass e').ncard) :
    Disjoint (hClass e) (hClass e') := by
  rw [Set.disjoint_left]
  intro m h1 h2
  apply h
  exact congrArg Set.ncard
    ((J4Classes.conjOrbit_eq_of_mem' h1).symm.trans (J4Classes.conjOrbit_eq_of_mem' h2))

theorem le_card_conj_inter_H :
    1204027 ≤ Nat.card {s : J // s ∈ CFSG.Sporadic.J4Schreier.H ∧ IsConj tJ s} := by
  have hfinJ : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J j4Facts]; norm_num)
  have h1 := J4Classes.ncard_class_e1
  have h2 := J4Classes.ncard_class_e2
  have h3 := J4Classes.ncard_class_e3
  have hsub : hClass CFSG.Sporadic.J4Schreier.z ∪ hClass J4Classes.e2 ∪ hClass J4Classes.e3 ⊆
      {s : J | s ∈ CFSG.Sporadic.J4Schreier.H ∧ IsConj tJ s} := by
    rintro s ((hs | hs) | hs)
    · exact ⟨J4Classes.conjOrbit_subset J4Classes.z_mem_H' hs, isConj_of_mem_hClass isConj_tJ_e1 hs⟩
    · exact ⟨J4Classes.conjOrbit_subset J4Classes.e2_mem_H hs,
        isConj_of_mem_hClass isConj_tJ_e2 hs⟩
    · exact ⟨J4Classes.conjOrbit_subset J4Classes.e3_mem_H hs,
        isConj_of_mem_hClass isConj_tJ_e3 hs⟩
  have hd12 := hClass_disjoint (e := CFSG.Sporadic.J4Schreier.z) (e' := J4Classes.e2)
    (by rw [h1, h2]; norm_num)
  have hd13 := hClass_disjoint (e := CFSG.Sporadic.J4Schreier.z) (e' := J4Classes.e3)
    (by rw [h1, h3]; norm_num)
  have hd23 := hClass_disjoint (e := J4Classes.e2) (e' := J4Classes.e3) (by rw [h2, h3]; norm_num)
  have hu : (hClass CFSG.Sporadic.J4Schreier.z ∪ hClass J4Classes.e2 ∪
      hClass J4Classes.e3).ncard = 1204027 := by
    rw [Set.ncard_union_eq (Disjoint.union_left hd13 hd23) (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hd12 (Set.toFinite _) (Set.toFinite _), h1, h2, h3]
  rw [← hu, ← Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem card_centralizer_tJ_le
    : Nat.card (Subgroup.centralizer ({tJ} : Set J)) ≤ 21799895040 := by
  have hfinJ : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J j4Facts]; norm_num)
  have hdc := card_fix_mul_card_stabilizer (G := J) (X := Om) vOm tJ
  rw [card_fix_Om, stabilizer_root_eq_H, CFSG.Sporadic.J4Schreier.card_H] at hdc
  have hR := le_card_conj_inter_H
  refine Nat.le_of_mul_le_mul_right (c := 1204027) ?_ (by norm_num)
  calc Nat.card (Subgroup.centralizer ({tJ} : Set J)) * 1204027
      ≤ Nat.card (Subgroup.centralizer ({tJ} : Set J)) *
          Nat.card {s : J // s ∈ CFSG.Sporadic.J4Schreier.H ∧ IsConj tJ s} :=
        Nat.mul_le_mul_left _ hR
    _ = 21799895040 * 1204027 := by rw [← hdc]

end CFSG.Quasithin.H13.J4

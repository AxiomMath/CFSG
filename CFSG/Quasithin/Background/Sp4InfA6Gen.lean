module

public import CFSG.Quasithin.Background.Sp4InfA6Basic
public meta import CFSG.Quasithin.Background.Sp4InfA6Basic
public import CFSG.Quasithin.Background.Sp4InfA6GenInputs
public import Certificates.Certificate8067
public meta import CFSG.Quasithin.Background.Sp4InfA6BasicBase
public import CFSG.Quasithin.Background.Sp4InfA6BasicBase
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open Equiv Pointwise

theorem reach_subset {u v : Perm (Fin 6)} {H : Subgroup (Perm (Fin 6))} (hu : u ∈ H) (hv : v ∈ H) :
    ∀ k, ∀ x ∈ reach u v k, x ∈ H := by
  intro k
  induction k with
  | zero =>
    intro x hx
    simp only [reach, Function.iterate_zero, id_eq, Finset.mem_singleton] at hx
    rw [hx]
    exact H.one_mem
  | succ k ih =>
    intro x hx
    simp only [reach, Function.iterate_succ_apply', reachStep, Finset.mem_union,
      Finset.mem_image] at hx
    rcases hx with (hx | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩
    · exact ih x hx
    · exact H.mul_mem (ih y hy) hu
    · exact H.mul_mem (ih y hy) hv

theorem gu_mem : gu ∈ q1 :=
  Certificates.certificate8067.1

theorem gv_mem : gv ∈ q2 :=
  Certificates.certificate8067.2.1

theorem alt_subset_reach :
    (Finset.univ.filter (fun x : Perm (Fin 6) => Perm.sign x = 1)) ⊆ reach gu gv 14 :=
  Certificates.certificate8067.2.2

theorem alt_le_reach
    (x : Perm (Fin 6)) (hx : Perm.sign x = 1) : x ∈ reach gu gv 14 :=
  alt_subset_reach (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)

theorem alt_le_sup : alternatingGroup (Fin 6) ≤ q1 ⊔ q2 := by
  intro x hx
  exact reach_subset (H := q1 ⊔ q2) (Subgroup.mem_sup_left gu_mem) (Subgroup.mem_sup_right gv_mem) 14 x
    (alt_le_reach x (Perm.mem_alternatingGroup.mp hx))

theorem sup_eq_alt : q1 ⊔ q2 = alternatingGroup (Fin 6) :=
  le_antisymm (sup_le q1_le_alt q2_le_alt) alt_le_sup

end Sp4Inf

end CFSG.Quasithin

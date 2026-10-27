module

public import CFSG.RankThree.Asc83Table.Reduction
public import Certificates.Certificate13950

public section

namespace CFSG.RankThree.Asc83Table.M24

open CFSG.Blueprint CFSG.Sporadic.Mathieu Subgroup
open scoped commutatorElement

theorem gens_mem : ∀ g ∈ gens, g ∈ NativeSporadic.M24 := by
  intro g hg
  rw [m24_eq]
  simp only [gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem x_c0_eq : x_c0 = permWord gens [(0, -2), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1),
    (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1),
    (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1),
    (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1),
    (0, -1), (1, 2), (0, 1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1),
    (0, -1), (1, -1)] :=
  Certificates.certificate13950.1

theorem x_c0_mem : x_c0 ∈ NativeSporadic.M24 := x_c0_eq ▸ permWord_mem gens_mem _

theorem x_c1_eq : x_c1 = permWord gens [(0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1),
    (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1),
    (0, -1), (1, 1), (0, -1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1),
    (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1),
    (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1),
    (0, 1), (1, 1), (0, 1), (1, -1)] :=
  Certificates.certificate13950.2.1

theorem x_c1_mem : x_c1 ∈ NativeSporadic.M24 := x_c1_eq ▸ permWord_mem gens_mem _

theorem x_c2_eq : x_c2 = permWord gens [(0, 1), (1, 1), (0, 2), (1, 1), (0, 1), (1, 1),
    (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1),
    (0, 1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1),
    (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1),
    (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1),
    (0, -1), (1, -1), (0, -1)] :=
  Certificates.certificate13950.2.2.1

theorem x_c2_mem : x_c2 ∈ NativeSporadic.M24 := x_c2_eq ▸ permWord_mem gens_mem _

theorem x_c3_eq : x_c3 = permWord gens [(1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, -1), (0, -1), (1, 2), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.1

theorem x_c3_mem : x_c3 ∈ NativeSporadic.M24 := x_c3_eq ▸ permWord_mem gens_mem _

theorem x_eq : x = x_c0 * x_c1 * x_c2 * x_c3 :=
  Certificates.certificate13950.2.2.2.2.1

theorem x_mem : x ∈ NativeSporadic.M24 := by
  rw [x_eq]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · exact x_c0_mem
  · exact x_c1_mem
  · exact x_c2_mem
  · exact x_c3_mem

theorem y_c0_eq : y_c0 = permWord gens [(1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1),
    (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 2), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -2), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1),
    (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, -1), (0, 1)] :=
  Certificates.certificate13950.2.2.2.2.2.1

theorem y_c0_mem : y_c0 ∈ NativeSporadic.M24 := y_c0_eq ▸ permWord_mem gens_mem _

theorem y_c1_eq : y_c1 = permWord gens [(1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.1

theorem y_c1_mem : y_c1 ∈ NativeSporadic.M24 := y_c1_eq ▸ permWord_mem gens_mem _

theorem y_c2_eq : y_c2 = permWord gens [(1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.1

theorem y_c2_mem : y_c2 ∈ NativeSporadic.M24 := y_c2_eq ▸ permWord_mem gens_mem _

theorem y_c3_eq : y_c3 = permWord gens [(1, -1), (0, -1), (1, 2), (0, 1), (1, 1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.1

theorem y_c3_mem : y_c3 ∈ NativeSporadic.M24 := y_c3_eq ▸ permWord_mem gens_mem _

theorem y_eq : y = y_c0 * y_c1 * y_c2 * y_c3 :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.1

theorem y_mem : y ∈ NativeSporadic.M24 := by
  rw [y_eq]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · exact y_c0_mem
  · exact y_c1_mem
  · exact y_c2_mem
  · exact y_c3_mem

theorem g1R_c0_eq : g1R_c0 = permWord gens [(0, -1), (1, -1), (0, -1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1),
    (0, 1), (1, -1), (0, 1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.1

theorem g1R_c0_mem : g1R_c0 ∈ NativeSporadic.M24 := g1R_c0_eq ▸ permWord_mem gens_mem _

theorem g1R_c1_eq : g1R_c1 = permWord gens [(0, 1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, -1), (0, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.1

theorem g1R_c1_mem : g1R_c1 ∈ NativeSporadic.M24 := g1R_c1_eq ▸ permWord_mem gens_mem _

theorem g1R_c2_eq : g1R_c2 = permWord gens [(1, -2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1),
    (0, 1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g1R_c2_mem : g1R_c2 ∈ NativeSporadic.M24 := g1R_c2_eq ▸ permWord_mem gens_mem _

theorem g1R_eq : g1R = g1R_c0 * g1R_c1 * g1R_c2 :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g1R_mem : g1R ∈ NativeSporadic.M24 := by
  rw [g1R_eq]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact g1R_c0_mem
  · exact g1R_c1_mem
  · exact g1R_c2_mem

theorem g1S_c0_eq : g1S_c0 = permWord gens [(0, -1), (1, -1), (0, -1), (1, 1), (0, -1),
    (1, -2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1),
    (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1),
    (1, -1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 2), (0, -1),
    (1, 1), (0, 1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g1S_c0_mem : g1S_c0 ∈ NativeSporadic.M24 := g1S_c0_eq ▸ permWord_mem gens_mem _

theorem g1S_c1_eq : g1S_c1 = permWord gens [(1, 1), (0, 1), (1, -1), (0, 1), (1, -1),
    (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1),
    (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1),
    (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -2), (0, -1), (1, 1),
    (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1),
    (0, -1), (1, 1), (0, -1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g1S_c1_mem : g1S_c1 ∈ NativeSporadic.M24 := g1S_c1_eq ▸ permWord_mem gens_mem _

theorem g1S_c2_eq : g1S_c2 = permWord gens [(0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, -2), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1),
    (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g1S_c2_mem : g1S_c2 ∈ NativeSporadic.M24 := g1S_c2_eq ▸ permWord_mem gens_mem _

theorem g1S_eq : g1S = g1S_c0 * g1S_c1 * g1S_c2 :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g1S_mem : g1S ∈ NativeSporadic.M24 := by
  rw [g1S_eq]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact g1S_c0_mem
  · exact g1S_c1_mem
  · exact g1S_c2_mem

theorem g2R_c0_eq : g2R_c0 = permWord gens [(1, -1), (0, -1), (1, 1), (0, -1), (1, 1),
    (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1),
    (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1),
    (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -2), (0, 1), (1, 1),
    (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1),
    (0, -1), (1, -1), (0, -1), (1, 1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g2R_c0_mem : g2R_c0 ∈ NativeSporadic.M24 := g2R_c0_eq ▸ permWord_mem gens_mem _

theorem g2R_c1_eq : g2R_c1 = permWord gens [(0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 2), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g2R_c1_mem : g2R_c1 ∈ NativeSporadic.M24 := g2R_c1_eq ▸ permWord_mem gens_mem _

theorem g2R_c2_eq : g2R_c2 = permWord gens [(1, -1), (0, -1), (1, -1), (0, -1), (1, 1),
    (0, -1), (1, -1), (0, -1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1),
    (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1),
    (0, -1), (1, -2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1),
    (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g2R_c2_mem : g2R_c2 ∈ NativeSporadic.M24 := g2R_c2_eq ▸ permWord_mem gens_mem _

theorem g2R_eq : g2R = g2R_c0 * g2R_c1 * g2R_c2 :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g2R_mem : g2R ∈ NativeSporadic.M24 := by
  rw [g2R_eq]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact g2R_c0_mem
  · exact g2R_c1_mem
  · exact g2R_c2_mem

theorem g2S_c0_eq : g2S_c0 = permWord gens [(0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g2S_c0_mem : g2S_c0 ∈ NativeSporadic.M24 := g2S_c0_eq ▸ permWord_mem gens_mem _

theorem g2S_c1_eq : g2S_c1 = permWord gens [(0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -2), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, 2)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g2S_c1_mem : g2S_c1 ∈ NativeSporadic.M24 := g2S_c1_eq ▸ permWord_mem gens_mem _

theorem g2S_c2_eq : g2S_c2 = permWord gens [(0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -2), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g2S_c2_mem : g2S_c2 ∈ NativeSporadic.M24 := g2S_c2_eq ▸ permWord_mem gens_mem _

theorem g2S_c3_eq : g2S_c3 = permWord gens [(1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1),
    (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g2S_c3_mem : g2S_c3 ∈ NativeSporadic.M24 := g2S_c3_eq ▸ permWord_mem gens_mem _

theorem g2S_eq : g2S = g2S_c0 * g2S_c1 * g2S_c2 * g2S_c3 :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g2S_mem : g2S ∈ NativeSporadic.M24 := by
  rw [g2S_eq]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · exact g2S_c0_mem
  · exact g2S_c1_mem
  · exact g2S_c2_mem
  · exact g2S_c3_mem

theorem g3R_c0_eq : g3R_c0 = permWord gens [(1, 1), (0, 1), (1, -1), (0, 1), (1, -1),
    (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1),
    (0, 1), (1, 2), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -2),
    (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1),
    (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, -1), (0, 1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g3R_c0_mem : g3R_c0 ∈ NativeSporadic.M24 := g3R_c0_eq ▸ permWord_mem gens_mem _

theorem g3R_c1_eq : g3R_c1 = permWord gens [(1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g3R_c1_mem : g3R_c1 ∈ NativeSporadic.M24 := g3R_c1_eq ▸ permWord_mem gens_mem _

theorem g3R_c2_eq : g3R_c2 = permWord gens [(1, -1), (0, -1), (1, 1), (0, -1), (1, 1),
    (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 2)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g3R_c2_mem : g3R_c2 ∈ NativeSporadic.M24 := g3R_c2_eq ▸ permWord_mem gens_mem _

theorem g3R_eq : g3R = g3R_c0 * g3R_c1 * g3R_c2 :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g3R_mem : g3R ∈ NativeSporadic.M24 := by
  rw [g3R_eq]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact g3R_c0_mem
  · exact g3R_c1_mem
  · exact g3R_c2_mem

theorem g3S_c0_eq : g3S_c0 = permWord gens [(1, -1), (0, -1), (1, -1), (0, -1), (1, 1),
    (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 2), (0, -1), (1, 1),
    (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1),
    (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1),
    (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1),
    (0, 1), (1, 1), (0, 1), (1, 1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g3S_c0_mem : g3S_c0 ∈ NativeSporadic.M24 := g3S_c0_eq ▸ permWord_mem gens_mem _

theorem g3S_c1_eq : g3S_c1 = permWord gens [(0, 1), (1, 1), (0, 1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -2), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g3S_c1_mem : g3S_c1 ∈ NativeSporadic.M24 := g3S_c1_eq ▸ permWord_mem gens_mem _

theorem g3S_c2_eq : g3S_c2 = permWord gens [(1, 2), (0, 1), (1, -1), (0, 1), (1, -1),
    (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g3S_c2_mem : g3S_c2 ∈ NativeSporadic.M24 := g3S_c2_eq ▸ permWord_mem gens_mem _

theorem g3S_eq : g3S = g3S_c0 * g3S_c1 * g3S_c2 :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g3S_mem : g3S ∈ NativeSporadic.M24 := by
  rw [g3S_eq]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact g3S_c0_mem
  · exact g3S_c1_mem
  · exact g3S_c2_mem

theorem g4R_c0_eq : g4R_c0 = permWord gens [(0, -1), (1, -1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 2), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, 2),
    (1, 1), (0, 1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g4R_c0_mem : g4R_c0 ∈ NativeSporadic.M24 := g4R_c0_eq ▸ permWord_mem gens_mem _

theorem g4R_c1_eq : g4R_c1 = permWord gens [(0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, 1),
    (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, -1),
    (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, -2),
    (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, -1),
    (0, 1), (1, 1), (0, 2), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1),
    (0, -1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g4R_c1_mem : g4R_c1 ∈ NativeSporadic.M24 := g4R_c1_eq ▸ permWord_mem gens_mem _

theorem g4R_c2_eq : g4R_c2 = permWord gens [(0, -1), (1, -1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1), (1, -2), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g4R_c2_mem : g4R_c2 ∈ NativeSporadic.M24 := g4R_c2_eq ▸ permWord_mem gens_mem _

theorem g4R_eq : g4R = g4R_c0 * g4R_c1 * g4R_c2 :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g4R_mem : g4R ∈ NativeSporadic.M24 := by
  rw [g4R_eq]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact g4R_c0_mem
  · exact g4R_c1_mem
  · exact g4R_c2_mem

theorem g4S_c0_eq : g4S_c0 = permWord gens [(0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -2), (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g4S_c0_mem : g4S_c0 ∈ NativeSporadic.M24 := g4S_c0_eq ▸ permWord_mem gens_mem _

theorem g4S_c1_eq : g4S_c1 = permWord gens [(0, -2), (1, -1), (0, -1), (1, 1), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, 1), (1, -1), (0, 1),
    (1, 1), (0, 2), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1),
    (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1),
    (0, -1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g4S_c1_mem : g4S_c1 ∈ NativeSporadic.M24 := g4S_c1_eq ▸ permWord_mem gens_mem _

theorem g4S_c2_eq : g4S_c2 = permWord gens [(0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, 2), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g4S_c2_mem : g4S_c2 ∈ NativeSporadic.M24 := g4S_c2_eq ▸ permWord_mem gens_mem _

theorem g4S_c3_eq : g4S_c3 = permWord gens [(1, 1), (0, -1), (1, 1), (0, -1), (1, 1),
    (0, -1), (1, -1)] :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g4S_c3_mem : g4S_c3 ∈ NativeSporadic.M24 := g4S_c3_eq ▸ permWord_mem gens_mem _

theorem g4S_eq : g4S = g4S_c0 * g4S_c1 * g4S_c2 * g4S_c3 :=
  Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g4S_mem : g4S ∈ NativeSporadic.M24 := by
  rw [g4S_eq]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · exact g4S_c0_mem
  · exact g4S_c1_mem
  · exact g4S_c2_mem
  · exact g4S_c3_mem

abbrev X : NativeSporadic.M24 := ⟨x, x_mem⟩

abbrev Y : NativeSporadic.M24 := ⟨y, y_mem⟩

theorem X_cube : X ^ 3 = 1 := Subtype.ext (show x ^ 3 = 1 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem Y_cube : Y ^ 3 = 1 := Subtype.ext (show y ^ 3 = 1 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem Z_X : Commute ⁅X, Y⁆ X :=
  Subtype.ext (show x * y * x⁻¹ * y⁻¹ * x = x * (x * y * x⁻¹ * y⁻¹) from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem Z_Y : Commute ⁅X, Y⁆ Y :=
  Subtype.ext (show x * y * x⁻¹ * y⁻¹ * y = y * (x * y * x⁻¹ * y⁻¹) from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem Z_ne : ⁅X, Y⁆ ≠ 1 := fun h =>
  absurd (congrArg Subtype.val h) (show x * y * x⁻¹ * y⁻¹ ≠ 1 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

noncomputable abbrev E (i : Fin 4) : E9Basis NativeSporadic.M24 :=
  ex27Basis X_cube Y_cube Z_X Z_Y Z_ne i

abbrev G1R : NativeSporadic.M24 := ⟨g1R, g1R_mem⟩

abbrev G1S : NativeSporadic.M24 := ⟨g1S, g1S_mem⟩

theorem G1R_z : G1R * ⁅X, Y⁆ * G1R⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 0 ^ 0 :=
  Subtype.ext (show g1R * (x * y * x⁻¹ * y⁻¹) * g1R⁻¹ =
    (x * y * x⁻¹ * y⁻¹) ^ 2 * (x) ^ 0 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G1R_w : G1R * ex27Rep X Y 0 * G1R⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 0 ^ 2 :=
  Subtype.ext (show g1R * (x) * g1R⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 2 * (x) ^ 2 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G1S_z : G1S * ⁅X, Y⁆ * G1S⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 0 ^ 0 :=
  Subtype.ext (show g1S * (x * y * x⁻¹ * y⁻¹) * g1S⁻¹ =
    (x * y * x⁻¹ * y⁻¹) ^ 2 * (x) ^ 0 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G1S_w : G1S * ex27Rep X Y 0 * G1S⁻¹ = ⁅X, Y⁆ ^ 0 * ex27Rep X Y 0 ^ 1 :=
  Subtype.ext (show g1S * (x) * g1S⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 0 * (x) ^ 1 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

abbrev G2R : NativeSporadic.M24 := ⟨g2R, g2R_mem⟩

abbrev G2S : NativeSporadic.M24 := ⟨g2S, g2S_mem⟩

theorem G2R_z : G2R * ⁅X, Y⁆ * G2R⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 1 ^ 0 :=
  Subtype.ext (show g2R * (x * y * x⁻¹ * y⁻¹) * g2R⁻¹ =
    (x * y * x⁻¹ * y⁻¹) ^ 2 * (y) ^ 0 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G2R_w : G2R * ex27Rep X Y 1 * G2R⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 1 ^ 2 :=
  Subtype.ext (show g2R * (y) * g2R⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 2 * (y) ^ 2 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G2S_z : G2S * ⁅X, Y⁆ * G2S⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 1 ^ 0 :=
  Subtype.ext (show g2S * (x * y * x⁻¹ * y⁻¹) * g2S⁻¹ =
    (x * y * x⁻¹ * y⁻¹) ^ 2 * (y) ^ 0 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G2S_w : G2S * ex27Rep X Y 1 * G2S⁻¹ = ⁅X, Y⁆ ^ 0 * ex27Rep X Y 1 ^ 1 :=
  Subtype.ext (show g2S * (y) * g2S⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 0 * (y) ^ 1 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

abbrev G3R : NativeSporadic.M24 := ⟨g3R, g3R_mem⟩

abbrev G3S : NativeSporadic.M24 := ⟨g3S, g3S_mem⟩

theorem G3R_z : G3R * ⁅X, Y⁆ * G3R⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 2 ^ 0 :=
  Subtype.ext (show g3R * (x * y * x⁻¹ * y⁻¹) * g3R⁻¹ =
    (x * y * x⁻¹ * y⁻¹) ^ 2 * (x * y) ^ 0 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G3R_w : G3R * ex27Rep X Y 2 * G3R⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 2 ^ 2 :=
  Subtype.ext (show g3R * (x * y) * g3R⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 2 * (x * y) ^ 2 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G3S_z : G3S * ⁅X, Y⁆ * G3S⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 2 ^ 0 :=
  Subtype.ext (show g3S * (x * y * x⁻¹ * y⁻¹) * g3S⁻¹ =
    (x * y * x⁻¹ * y⁻¹) ^ 2 * (x * y) ^ 0 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G3S_w : G3S * ex27Rep X Y 2 * G3S⁻¹ = ⁅X, Y⁆ ^ 0 * ex27Rep X Y 2 ^ 1 :=
  Subtype.ext (show g3S * (x * y) * g3S⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 0 * (x * y) ^ 1 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

abbrev G4R : NativeSporadic.M24 := ⟨g4R, g4R_mem⟩

abbrev G4S : NativeSporadic.M24 := ⟨g4S, g4S_mem⟩

theorem G4R_z : G4R * ⁅X, Y⁆ * G4R⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 3 ^ 0 :=
  Subtype.ext (show g4R * (x * y * x⁻¹ * y⁻¹) * g4R⁻¹ =
    (x * y * x⁻¹ * y⁻¹) ^ 2 * (x * y ^ 2) ^ 0 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G4R_w : G4R * ex27Rep X Y 3 * G4R⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 3 ^ 2 :=
  Subtype.ext (show g4R * (x * y ^ 2) * g4R⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 2 * (x * y ^ 2) ^ 2 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G4S_z : G4S * ⁅X, Y⁆ * G4S⁻¹ = ⁅X, Y⁆ ^ 2 * ex27Rep X Y 3 ^ 0 :=
  Subtype.ext (show g4S * (x * y * x⁻¹ * y⁻¹) * g4S⁻¹ =
    (x * y * x⁻¹ * y⁻¹) ^ 2 * (x * y ^ 2) ^ 0 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem G4S_w : G4S * ex27Rep X Y 3 * G4S⁻¹ = ⁅X, Y⁆ ^ 0 * ex27Rep X Y 3 ^ 1 :=
  Subtype.ext (show g4S * (x * y ^ 2) * g4S⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 0 * (x * y ^ 2) ^ 1 from Certificates.certificate13950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)

theorem automizer_B (i : Fin 4) :
    Nonempty (Automizer (E i).sub ≃* DihedralGroup 6) ∨ Nonempty (Automizer (E i).sub ≃* GL23) := by
  fin_cases i
  · exact (E 0).dihedral_or_gl ((E 0).mem_range_of_conj 2 2 0 2 G1R_z G1R_w (by decide))
      ((E 0).mem_range_of_conj 2 0 0 1 G1S_z G1S_w (by decide))
  · exact (E 1).dihedral_or_gl ((E 1).mem_range_of_conj 2 2 0 2 G2R_z G2R_w (by decide))
      ((E 1).mem_range_of_conj 2 0 0 1 G2S_z G2S_w (by decide))
  · exact (E 2).dihedral_or_gl ((E 2).mem_range_of_conj 2 2 0 2 G3R_z G3R_w (by decide))
      ((E 2).mem_range_of_conj 2 0 0 1 G3S_z G3S_w (by decide))
  · exact (E 3).dihedral_or_gl ((E 3).mem_range_of_conj 2 2 0 2 G4R_z G4R_w (by decide))
      ((E 3).mem_range_of_conj 2 0 0 1 G4S_z G4S_w (by decide))

theorem factorization_card : (Nat.card NativeSporadic.M24).factorization 3 = 3 := by
  rw [card_M24]
  exact factorization_eq_of_eq Nat.prime_three (show 244823040 = 3 ^ 3 * 9067520 by norm_num)
    (by norm_num)

theorem table {L : Type} [Group L] (hL : NativeSporadic.IsSporadic L .M24) :
    (∀ P : Sylow 3 L, Nat.card P = 27) ∧ CFSG.pRank 3 L = 2 ∧
      ∀ B : Subgroup L, IsElementaryAbelian 3 B → Nat.card B = 9 →
        ActsNontriviallyOnTwoSubgroup B →
          Nonempty (Automizer B ≃* DihedralGroup 6) ∨ Nonempty (Automizer B ≃* GL23) := by
  obtain ⟨e⟩ := hL
  obtain ⟨h₁, h₂, h₃⟩ := ex27_transport X_cube Y_cube Z_X Z_Y Z_ne factorization_card
    (e : L ≃* NativeSporadic.M24)
  refine ⟨h₁, h₂, fun B _ hB _ => ?_⟩
  obtain ⟨i, ⟨f⟩⟩ := h₃ B hB
  rcases automizer_B i with h | h
  · obtain ⟨q⟩ := h
    exact Or.inl ⟨f.trans q⟩
  · obtain ⟨q⟩ := h
    exact Or.inr ⟨f.trans q⟩

end CFSG.RankThree.Asc83Table.M24

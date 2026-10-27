module

public import CFSG.Sporadic.FischerOddCore.Fi22Search
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCover

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer

theorem index_fi22P_subgroupOf_R :
    (fi22P.subgroupOf fi22R).index = 2 := by
  have h := (fi22P.subgroupOf fi22R).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22P_le_R).toEquiv, card_fi22P,
    card_fi22R] at h
  omega

theorem fi22R_mul_mem_P_iff
    {b c : Equiv.Perm (Fin 3510)} (hb : b ∈ fi22R) (hc : c ∈ fi22R) :
    b * c ∈ fi22P ↔ (b ∈ fi22P ↔ c ∈ fi22P) :=
  Subgroup.mul_mem_iff_of_index_two (a := ⟨b, hb⟩) (b := ⟨c, hc⟩) index_fi22P_subgroupOf_R

theorem card_inf_centralizer_R
    {t c : Equiv.Perm (Fin 3510)} (hc : c ∈ fi22R) (hcP : c ∉ fi22P)
    (hct : c * t = t * c) :
    Nat.card (fi22R ⊓ Subgroup.centralizer {t} : Subgroup (Equiv.Perm (Fin 3510))) =
      2 * Nat.card (fi22P ⊓ Subgroup.centralizer {t} : Subgroup (Equiv.Perm (Fin 3510))) := by
  set C := fi22R ⊓ Subgroup.centralizer {t}
  set D := fi22P ⊓ Subgroup.centralizer {t}
  have hDC : D ≤ C := inf_le_inf_right _ fi22P_le_R
  have hcC : c ∈ C := ⟨hc, Subgroup.mem_centralizer_singleton_iff.2 hct⟩
  have hidx : (D.subgroupOf C).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨c, hcC⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    have hbR : (b : Equiv.Perm (Fin 3510)) ∈ fi22R := b.2.1
    have hbt : (b : Equiv.Perm (Fin 3510)) ∈ Subgroup.centralizer {t} := b.2.2
    have hbct : (b : Equiv.Perm (Fin 3510)) * c ∈ Subgroup.centralizer {t} :=
      Subgroup.mul_mem _ hbt hcC.2
    have key := fi22R_mul_mem_P_iff hbR hc
    by_cases hbP : (b : Equiv.Perm (Fin 3510)) ∈ fi22P
    · exact Or.inr ⟨⟨hbP, hbt⟩, fun h => hcP ((key.1 h.1).1 hbP)⟩
    · exact Or.inl ⟨⟨key.2 ⟨fun h => absurd h hbP, fun h => absurd h hcP⟩, hbct⟩,
        fun h => hbP h.1⟩
  have h := (D.subgroupOf C).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv] at h
  omega

theorem fi22R_inf_le_K
    (k : ℕ) : fi22R ⊓ Subgroup.centralizer {fi22ExtRep k} ≤ fi22K k :=
  inf_le_inf_right _ fi22R_le_AutG

theorem fi22CP_eq_H
    {c : ℕ} (hc5 : c < 5) {o : Equiv.Perm (Fin 3510)} (ho : o ∈ fi22R)
    (hoP : o ∉ fi22P) (hot : o * fi22CentT c = fi22CentT c * o)
    (hK : Nat.card (fi22K (fi22CentCase c)) ≤ 2 * Nat.card (fi22H c)) :
    fi22P ⊓ Subgroup.centralizer {fi22CentT c} = fi22H c := by
  have h2 := card_inf_centralizer_R ho hoP hot
  have hle : Nat.card (fi22R ⊓ Subgroup.centralizer {fi22CentT c} :
      Subgroup (Equiv.Perm (Fin 3510))) ≤ Nat.card (fi22K (fi22CentCase c)) :=
    Subgroup.card_le_of_le (fi22R_inf_le_K _)
  symm
  exact Subgroup.eq_of_le_of_card_ge (fi22H_le hc5) (by omega)

theorem CTUC_Fi22_five_exact_involution_fixed_subgroups :
    fi22P ⊓ Subgroup.centralizer {fi22ExtRep 0} = fi22H 0 ∧
    fi22P ⊓ Subgroup.centralizer {fi22ExtRep 1} = fi22H 1 ∧
    fi22P ⊓ Subgroup.centralizer {fi22ExtRep 3} = fi22H 2 ∧
    fi22P ⊓ Subgroup.centralizer {fi22ExtRep 4} = fi22H 3 ∧
    fi22P ⊓ Subgroup.centralizer {fi22ExtRep 5} = fi22H 4 ∧
    ((List.range 5).map fun c => Nat.card (fi22H c)) =
      [1769472, 53084160, 3317760, 1045094400, 2903040] := by
  obtain ⟨-, hK1, hK3, hK4, hK5, hcR, hcP, hct⟩ := CTUC_Fi22_involution_relational_graph_bounds
  obtain ⟨-, -, hK0, hacc, -, ha1R, ha1P⟩ := CTUC_Fi22_54_fixed_point_involution_pruned_graph_bound
  have hord := CTUC_Fi22_literal_centralizer_subgroup_orders.2.2.1
  obtain ⟨-, hout, -⟩ := CTUC_Fi22_all_extension_involutions_covered
  have hH : ∀ c < 5,
      Nat.card (fi22H c) = [1769472, 53084160, 3317760, 1045094400, 2903040].getD c 0 :=
    fun c hc => by rw [← hord]; simp [List.getD_eq_getElem?_getD, hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, hord⟩
  · exact fi22CP_eq_H (c := 0) (by norm_num) ha1R ha1P (hacc 1 (by norm_num)).2
      (by rw [hH 0 (by norm_num)]; exact hK0)
  · exact fi22CP_eq_H (c := 1) (by norm_num) hcR hcP hct (by rw [hH 1 (by norm_num)]; exact hK1)
  · exact fi22CP_eq_H (c := 2) (by norm_num) (hout 0 (by norm_num)).1 (hout 0 (by norm_num)).2 rfl
      (by rw [hH 2 (by norm_num)]; exact hK3)
  · exact fi22CP_eq_H (c := 3) (by norm_num) (hout 1 (by norm_num)).1 (hout 1 (by norm_num)).2 rfl
      (by rw [hH 3 (by norm_num)]; exact hK4)
  · exact fi22CP_eq_H (c := 4) (by norm_num) (hout 2 (by norm_num)).1 (hout 2 (by norm_num)).2 rfl
      (by rw [hH 4 (by norm_num)]; exact hK5)

end CFSG.Sporadic.FischerOddCore

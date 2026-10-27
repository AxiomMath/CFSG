module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2FLab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P2F

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem FiveRel.prod_rel {a z : Fin 5 → G} {w : G} (hR : FiveRel a z w)
    (h : z 0 * z 1 * z 2 * z 3 * z 4 = 1) : z 0 * z 1 * z 4 = z 3 * z 2 := by
  have h42 : Commute (z 4) (z 2) := hR.comm_zz 4 2
  have h43 : Commute (z 4) (z 3) := hR.comm_zz 4 3
  have hc : Commute (z 4) (z 2 * z 3) := h42.mul_right h43
  have e1 : z 0 * z 1 * z 4 * (z 2 * z 3) = 1 := by
    calc z 0 * z 1 * z 4 * (z 2 * z 3) = z 0 * z 1 * (z 4 * (z 2 * z 3)) := by
          simp only [mul_assoc]
      _ = z 0 * z 1 * (z 2 * z 3 * z 4) := by rw [hc.eq]
      _ = z 0 * z 1 * z 2 * z 3 * z 4 := by simp only [mul_assoc]
      _ = 1 := h
  have e2 : z 0 * z 1 * z 4 = (z 2 * z 3)⁻¹ := eq_inv_of_mul_eq_one_left e1
  rw [e2, mul_inv_rev, inv_eq_of_mul_eq_one_right (hR.sq_z 3),
    inv_eq_of_mul_eq_one_right (hR.sq_z 2)]

theorem z_mul_sibling (F : FanTree Γ G) (h512 : Fan512 F L) {ν a p q : V}
    (hν : valence Γ ν = 3) (ha : Γ.Adj ν a) (hp : Γ.Adj ν p) (hq : Γ.Adj ν q) (hap : a ≠ p)
    (haq : a ≠ q) : L.z p * L.z q = 1 ∨ L.z p * L.z q = L.z a := by
  by_cases hpq : p = q
  · subst hpq
    exact Or.inl (L.z_mul_self (valence_adj_five F hν hp))
  · right
    obtain ⟨c, hc, -, -⟩ := exists_third_neighbor hν ha hp hap
    have hqmem : q ∈ Γ.neighborSet ν := hq
    rw [hc] at hqmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hqmem
    have hqc : q = c := by
      rcases hqmem with h | h | h
      · exact absurd h.symm haq
      · exact absurd h.symm hpq
      · exact h
    subst hqc
    have h3 := h512.2.2.1 ν a p q hν hc hap haq hpq
    have h4 : L.z p * L.z q = (L.z a)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by rw [← mul_assoc]; exact h3)
    rw [h4, L.z_inv (valence_adj_five F hν ha)]

variable {D}

theorem prodFive_mem_calpha (F : FanTree Γ G) (h71c : Fan71c F L) (h83a : Fan83a F L)
    (h83b : Fan83b F L) (h83d : Fan83d F L) {δ' : V} (hY : D.IsYPair δ') :
    prodFive (D.y δ') ∈ D.calpha := by
  obtain ⟨-, -, hxy⟩ := y_labels F h71c h83a h83b h83d hY
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · unfold prodFive
    exact mul_mem (mul_mem (mul_mem (mul_mem (Sec8P3.y_mem_nbrStab D h83a hY 0)
      (Sec8P3.y_mem_nbrStab D h83a hY 1)) (Sec8P3.y_mem_nbrStab D h83a hY 2))
      (Sec8P3.y_mem_nbrStab D h83a hY 3)) (Sec8P3.y_mem_nbrStab D h83a hY 4)
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := congrArg (fun t => D.x * t) hxy
    exact (by simpa [mul_assoc] using this : prodFive (D.y δ') * D.x = D.x * prodFive (D.y δ')).symm

theorem z_alpha_not_mem_calpha (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) :
    L.z (D.alpha 0) ∉ D.calpha := by
  intro h
  have h1 : L.z (D.alpha 0) • D.delta 1 = D.delta 1 :=
    D.fix_of_mem_calpha F h71a h71c h 1 (m := 4) (by norm_num)
  have hd : Γ.dist (D.alpha 0) (D.delta 1) = 2 + 4 :=
    D.dist_vert_ne F h71c (i := 0) (j := 1) (by decide) (m := 2) (m' := 4) (by norm_num)
      (by norm_num)
  have := (h71c.z_smul_eq_iff (D.valence_alpha F 0) _).1 h1
  omega

end Sec8P2F

end CFSG.Quasithin.Fan86

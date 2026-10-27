module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Val

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def xe (L : ZLab Γ G) (P : Arc Γ 8) : G := L.z (P.vert 0) * L.z (P.vert 8)

theorem valence_vert (F : FanTree Γ G) (P : Arc Γ 8) (h5 : valence Γ (P.vert 4) = 5) {i : ℕ}
    (hi : i ≤ 8) (he : i % 2 = 0) : valence Γ (P.vert i) = 5 :=
  (P71.valence_arc F P (by norm_num) h5 i hi).1 he

theorem dist_vert (F : FanTree Γ G) (P : Arc Γ 8) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 8) :
    Γ.dist (P.vert i) (P.vert j) = j - i :=
  Arc.dist_vert F.isTree P hij hj

variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem z_end_mem (h71c : Fan71c F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5)
    {i : ℕ} (hi : i = 0 ∨ i = 8) :
    L.z (P.vert i) ∈ MulAction.stabilizer G (P.vert 4) := by
  have hv : valence Γ (P.vert i) = 5 := by
    rcases hi with rfl | rfl
    · exact valence_vert F P h5 (by norm_num) (by norm_num)
    · exact valence_vert F P h5 (by norm_num) (by norm_num)
  rw [h71c.z_mem_stabilizer_iff hv]
  rcases hi with rfl | rfl
  · have := dist_vert F P (i := 0) (j := 4) (by norm_num) (by norm_num)
    omega
  · have := dist_vert F P (i := 4) (j := 8) (by norm_num) (by norm_num)
    rw [dist_comm]
    omega

theorem xe_mem_stabilizer (h71c : Fan71c F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) :
    xe L P ∈ MulAction.stabilizer G (P.vert 4) :=
  mul_mem (z_end_mem h71c h5 (Or.inl rfl)) (z_end_mem h71c h5 (Or.inr rfl))

theorem dihedral_five : ∀ g h : DihedralGroup 5, g * g = 1 → h * h = 1 → g ≠ 1 → h ≠ 1 →
    (g * h) ^ 5 = 1 := by
  decide

theorem xe_pow_five (h71a : Fan71a F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) :
    xe L P ^ 5 = 1 := by
  have h0 : valence Γ (P.vert 0) = 5 := valence_vert F P h5 (by norm_num) (by norm_num)
  have h8 : valence Γ (P.vert 8) = 5 := valence_vert F P h5 (by norm_num) (by norm_num)
  obtain ⟨⟨e⟩, -⟩ := h71a P h0
  let a : Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G) :=
    ⟨L.z (P.vert 0), Subgroup.subset_closure (by simp)⟩
  let b : Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G) :=
    ⟨L.z (P.vert 8), Subgroup.subset_closure (by simp)⟩
  have ha2 : a * a = 1 := Subtype.ext (L.z_mul_self h0)
  have hb2 : b * b = 1 := Subtype.ext (L.z_mul_self h8)
  have ha1 : a ≠ 1 := fun h => L.z_ne_one h0 (congrArg Subtype.val h)
  have hb1 : b ≠ 1 := fun h => L.z_ne_one h8 (congrArg Subtype.val h)
  have key : e ((a * b) ^ 5) = 1 := by
    rw [map_pow, map_mul]
    refine dihedral_five _ _ ?_ ?_ ?_ ?_
    · rw [← map_mul, ha2, map_one]
    · rw [← map_mul, hb2, map_one]
    · exact fun h => ha1 (e.injective (by rw [h, map_one]))
    · exact fun h => hb1 (e.injective (by rw [h, map_one]))
  have h2 : (a * b) ^ 5 = 1 := e.injective (by rw [key, map_one])
  have := congrArg Subtype.val h2
  simpa [xe] using this

theorem xe_ne_one (h71c : Fan71c F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) :
    xe L P ≠ 1 := by
  intro h
  have h0 : valence Γ (P.vert 0) = 5 := valence_vert F P h5 (by norm_num) (by norm_num)
  have h8 : valence Γ (P.vert 8) = 5 := valence_vert F P h5 (by norm_num) (by norm_num)
  have h1 : L.z (P.vert 0) = L.z (P.vert 8) := by
    rw [eq_inv_of_mul_eq_one_left h, L.z_inv h8]
  have hne : P.vert 0 ≠ P.vert 8 := by
    intro e
    have := dist_vert F P (i := 0) (j := 8) (by norm_num) (by norm_num)
    rw [e, SimpleGraph.dist_self] at this
    omega
  exact hne (h71c.z_injective h0 h8 h1)

theorem orderOf_xe (h71a : Fan71a F L) (h71c : Fan71c F L) {P : Arc Γ 8}
    (h5 : valence Γ (P.vert 4) = 5) : orderOf (xe L P) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime (xe_pow_five h71a h5) (xe_ne_one h71c h5)

theorem calpha_eq_stab (h71a : Fan71a F L) (h71c : Fan71c F L) {P : Arc Γ 8}
    (h5 : valence Γ (P.vert 4) = 5) : L.calpha P = P.stab G := by
  have h0 : valence Γ (P.vert 0) = 5 := valence_vert F P h5 (by norm_num) (by norm_num)
  obtain ⟨-, hc⟩ := h71a P h0
  exact hc (xe L P) (mul_mem (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))) (orderOf_xe h71a h71c h5)

end P74

end CFSG.Quasithin.Fan86

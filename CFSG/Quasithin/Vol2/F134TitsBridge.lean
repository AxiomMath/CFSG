module

public import CFSG.Quasithin.Vol2.F134TitsCheck
public import CFSG.Literature.ParrottTits

public section

namespace CFSG.Quasithin.F134

open CFSG.Blueprint CFSG.Literature.ParrottTits

theorem glCode26_one : glCode26 (1 : GL (Fin 26) (ZMod 2)) = titsOneC := tits_one_check.2

theorem eq_of_glCode26 {u v : GL (Fin 26) (ZMod 2)} (h : glCode26 u = glCode26 v) : u = v :=
  glCode26_injective h

theorem toM26_mul_eq_one {x y : ℕ} (hx : x < 2 ^ (26 * 26)) (hy : y < 2 ^ (26 * 26))
    (h : mulF26 x y = titsOneC) : toM26 x * toM26 y = 1 :=
  matCode26_injective (by rw [matCode26_mul, matCode26_toM26 hx, matCode26_toM26 hy, h,
    tits_one_check.2])

@[expose] noncomputable def glOfCode26 (x y : ℕ) (hx : x < 2 ^ (26 * 26))
    (hy : y < 2 ^ (26 * 26)) (hxy : mulF26 x y = titsOneC) (hyx : mulF26 y x = titsOneC) :
    GL (Fin 26) (ZMod 2) :=
  ⟨toM26 x, toM26 y, toM26_mul_eq_one hx hy hxy, toM26_mul_eq_one hy hx hyx⟩

@[expose] noncomputable def titsRhoN (i : ℕ) : GL (Fin 26) (ZMod 2) :=
  if h : i < 10 then
    glOfCode26 (titsRC i) (titsRInvC i) (tits_rho_check i h).1 (tits_rinv_check i h).1
      (tits_rinv_check i h).2.1 (tits_rinv_check i h).2.2
  else 1

@[expose] noncomputable def titsRho (i : Fin 10) : GL (Fin 26) (ZMod 2) := titsRhoN i

theorem glCode26_titsRhoN {i : ℕ} (hi : i < 10) : glCode26 (titsRhoN i) = titsRC i := by
  rw [glCode26, titsRhoN, dite_eq_left hi]
  exact matCode26_toM26 (tits_rho_check i hi).1

theorem glCode26_titsRhoN_inv {i : ℕ} (hi : i < 10) : glCode26 (titsRhoN i)⁻¹ = titsRInvC i := by
  rw [glCode26, titsRhoN, dite_eq_left hi]
  exact matCode26_toM26 (tits_rinv_check i hi).1

@[expose] def titsLetC (x : Fin 10 × Bool) : ℕ := bif x.2 then titsRC x.1 else titsRInvC x.1

@[expose] def titsSWordC : List (Fin 10 × Bool) → ℕ
  | [] => titsOneC
  | x :: w => mulF26 (titsLetC x) (titsSWordC w)

theorem glCode26_letter (x : Fin 10 × Bool) :
    glCode26 (bif x.2 then titsRho x.1 else (titsRho x.1)⁻¹) = titsLetC x := by
  obtain ⟨i, b⟩ := x
  cases b
  · simp only [titsLetC, Bool.cond_false]
    exact glCode26_titsRhoN_inv i.2
  · simp only [titsLetC, Bool.cond_true]
    exact glCode26_titsRhoN i.2

theorem glCode26_prod_map : ∀ w : List (Fin 10 × Bool),
    glCode26 (w.map fun x => bif x.2 then titsRho x.1 else (titsRho x.1)⁻¹).prod = titsSWordC w
  | [] => glCode26_one
  | x :: w => by
    rw [List.map_cons, List.prod_cons, glCode26_mul, glCode26_prod_map w, glCode26_letter,
      titsSWordC]

theorem tits_parrott_check : ∀ w ∈ parrottWords, titsSWordC w = titsOneC := by
  decide +kernel

theorem titsRho_relations :
    ∀ p ∈ parrottRelations, FreeGroup.lift titsRho p.1 = FreeGroup.lift titsRho p.2 := by
  rw [lift_relators_iff, parrottRelators_eq]
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  rw [FreeGroup.lift_mk]
  apply eq_of_glCode26
  rw [glCode26_prod_map, tits_parrott_check w hw, glCode26_one]

@[expose] noncomputable def titsGroup : Subgroup (GL (Fin 26) (ZMod 2)) :=
  Subgroup.closure (Set.range titsRho)

theorem titsRhoN_mem (i : ℕ) : titsRhoN i ∈ titsGroup := by
  by_cases hi : i < 10
  · exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
  · rw [titsRhoN, dite_eq_right hi]
    exact one_mem _

theorem titsGroup_ne_bot : titsGroup ≠ ⊥ := by
  intro h
  have h0 := titsRhoN_mem 0
  rw [h, Subgroup.mem_bot] at h0
  have := congrArg glCode26 h0
  rw [glCode26_titsRhoN (by norm_num), glCode26_one] at this
  exact tits_rho_ne_one this

theorem titsEquiv
    {X : Type} [Group X] (h : ReeTitsModel X .Tits 2 1) :
    Nonempty (X ≃* titsGroup) := by
  have hL : LieModel X .Tits 0 2 1 := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))
  obtain ⟨-, -, -, hall⟩ := CL_LIT_Parrott_Tits_group_presentation X hL
  obtain ⟨-, -, hor⟩ := hall (GL (Fin 26) (ZMod 2)) titsRho titsRho_relations
  rcases hor with hbot | he
  · exact absurd hbot titsGroup_ne_bot
  · obtain ⟨e⟩ := he
    exact ⟨e.symm⟩

end CFSG.Quasithin.F134

module

public import CFSG.Quasithin.EmptyFaithful.S153PE1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace S153P

namespace PE

section Perm3

theorem eq_one_or_eq_or_eq_sq_of_perm {N : Type*} [Group N] (e : N ≃* Equiv.Perm (Fin 3)) {a b : N}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hb1 : b ≠ 1) : a = 1 ∨ a = b ∨ a = b ^ 2 := by
  have key : ∀ a' b' : Equiv.Perm (Fin 3), a' ^ 3 = 1 → b' ^ 3 = 1 → b' ≠ 1 →
      a' = 1 ∨ a' = b' ∨ a' = b' ^ 2 := by
    decide +kernel
  have h := key (e a) (e b) (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
    (fun h => hb1 (e.injective (by rw [h, map_one])))
  rcases h with h | h | h
  · exact Or.inl (e.injective (by rw [h, map_one]))
  · exact Or.inr (Or.inl (e.injective h))
  · exact Or.inr (Or.inr (e.injective (by rw [h, map_pow])))

end Perm3

section V0

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

theorem bar_cases (H : HypsA cx N₁ N₂ g s y) {h : G} (hh : h ∈ Yi153 T Mc M V₁ N₁) :
    S153E55.bar cx (Yi_mem_YU N₁ hh) = 1 ∨ S153E55.bar cx (Yi_mem_YU N₁ hh) = ybar H ∨
      S153E55.bar cx (Yi_mem_YU N₁ hh) = ybar H ^ 2 := by
  obtain ⟨e⟩ := H.c.h53one.iso₁
  have hb : S153E55.bar cx (Yi_mem_YU N₁ hh) ∈ N₁ :=
    S153E55.bar_mem_of_mem_Ni cx (Yi_mem_Ni hh) (Yi_mem_YU N₁ hh)
  have key := eq_one_or_eq_or_eq_sq_of_perm e (a := (⟨_, hb⟩ : ↥N₁))
    (b := (⟨ybar H, ybar_mem_N₁ H⟩ : ↥N₁)) (Subtype.ext (bar_pow_three H hh))
    (Subtype.ext (ybar_pow_three H)) (fun h => ybar_ne_one H (congrArg Subtype.val h))
  rcases key with h1 | h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (Or.inl (congrArg Subtype.val h1))
  · exact Or.inr (Or.inr (congrArg Subtype.val h1))

theorem conj_mem_V0 (H : HypsA cx N₁ N₂ g s y) {z : G} (hz : S153E56e.ZGen T z) {h : G}
    (hh : h ∈ Yi153 T Mc M V₁ N₁) :
    h * z * h⁻¹ ∈ quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y := by
  have hV := cx.c.hyp.elemAbelian
  let w : IntMod (VZ T M) hV := IntMod.mk hV ⟨z, hz.memV cx⟩
  have hw : (w.val : G) = z := rfl
  have e1 : (S153E55.bar cx (Yi_mem_YU N₁ hh) w).val = h * z * h⁻¹ :=
    S153E55.bar_apply_val cx (Yi_mem_YU N₁ hh) w
  have hZ : y⁻¹ * z * y ∈ conjSubgroup (quasithinOmegaOneCenter T) y :=
    (hz.mem_conj_iff y).2 (Or.inr rfl)
  rcases bar_cases H hh with h1 | h1 | h1
  · rw [h1] at e1
    have e2 : h * z * h⁻¹ = z := e1.symm
    rw [e2]
    exact Subgroup.mem_sup_left hz.mem
  · rw [h1, ybar_apply H w, hw] at e1
    rw [← e1, yz_eq H hz]
    exact Subgroup.mul_mem_sup hz.mem hZ
  · rw [h1] at e1
    have e2 : ((ybar H ^ 2) w) = ybar H (ybar H w) := by rw [pow_two]; rfl
    rw [e2, ybar_apply H, ybar_apply H, hw, y_sq_conj H (hz.memV cx)] at e1
    rw [← e1]
    exact Subgroup.mem_sup_right hZ

theorem V0_eq_of_hypsA (H : HypsA cx N₁ N₂ g s y) {z : G} (hz : S153E56e.ZGen T z) :
    V0gp153 T Mc M V₁ N₁ =
      quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y := by
  refine le_antisymm (conjClosure_le fun h hh z₀ hz₀ => ?_) (sup_le (le_conjClosure _ _) ?_)
  · rcases hz.mem_Z_iff.1 hz₀ with rfl | rfl
    · simp
    · exact conj_mem_V0 H hz hh
  · intro x hx
    rcases (hz.mem_conj_iff y).1 hx with rfl | rfl
    · exact one_mem _
    · simpa using mem_conjClosure (inv_mem H.hy.1) hz.mem

end V0

end PE

end S153P

end CFSG.Quasithin

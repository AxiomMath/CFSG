module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5RootsComm

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits
open scoped commutatorElement

section Relations

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

theorem octComm_one_three_un5 :
    ∀ x ∈ un5Oct hF 1, ∀ y ∈ un5Oct hF 3, ⁅x, y⁆ ∈ un5Oct hF 2 :=
  octComm_aux_un5 hF (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRootB_one, octRootB_three] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords5 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRootB_one, octRootB_three] at h0 h1
      have hε : ε = 2 • octRootB 2 := by
        refine ext_fin_two ?_ ?_ <;> simp [octRootB_two] <;> omega
      rw [hε] at hr ⊢
      exact rootGroup_two_le_un hF (octRootB_mem_roots_un hF (by norm_num) (by norm_num)) hr)

theorem octComm_one_four_un5 :
    ∀ x ∈ un5Oct hF 1, ∀ y ∈ un5Oct hF 4, ⁅x, y⁆ ∈ un5Oct hF 2 ⊔ un5Oct hF 3 :=
  octComm_aux_un5 hF (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRootB_one, octRootB_four] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords5 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRootB_one, octRootB_four] at h0 h1
      rcases (by omega : (ε 0 = 1 ∧ ε 1 = 1) ∨ (ε 0 = 1 ∧ ε 1 = 2) ∨ (ε 0 = 2 ∧ ε 1 = 2)) with
        ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩
      · have hε : ε = octRootB 2 := by
          refine ext_fin_two ?_ ?_ <;> simp [octRootB_two] <;> omega
        subst hε
        exact le_sup_left
      · have hε : ε = octRootB 3 := by
          refine ext_fin_two ?_ ?_ <;> simp [octRootB_three] <;> omega
        subst hε
        exact le_sup_right
      · have hε : ε = 2 • octRootB 2 := by
          refine ext_fin_two ?_ ?_ <;> simp [octRootB_two] <;> omega
        rw [hε] at hr ⊢
        exact (rootGroup_two_le_un hF (octRootB_mem_roots_un hF (by norm_num) (by norm_num))
          hr).trans le_sup_left)

theorem octComm_one_two_un5 :
    ∀ x ∈ un5Oct hF 1, ∀ y ∈ un5Oct hF 2, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux_un5 hF (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRootB_one, octRootB_two] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords5 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRootB_one, octRootB_two] at h0 h1
      omega) x hx y hy)

theorem octComm_two_three_un5 :
    ∀ x ∈ un5Oct hF 2, ∀ y ∈ un5Oct hF 3, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux_un5 hF (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRootB_two, octRootB_three] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords5 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRootB_two, octRootB_three] at h0 h1
      omega) x hx y hy)

theorem octComm_two_four_un5 :
    ∀ x ∈ un5Oct hF 2, ∀ y ∈ un5Oct hF 4, ⁅x, y⁆ ∈ un5Oct hF 3 :=
  octComm_aux_un5 hF (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRootB_two, octRootB_four] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords5 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRootB_two, octRootB_four] at h0 h1
      have hε : ε = octRootB 3 := by
        refine ext_fin_two ?_ ?_ <;> simp [octRootB_three] <;> omega
      subst hε
      exact le_rfl)

theorem octComm_three_four_un5 :
    ∀ x ∈ un5Oct hF 3, ∀ y ∈ un5Oct hF 4, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux_un5 hF (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRootB_three, octRootB_four] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords5 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRootB_three, octRootB_four] at h0 h1
      omega) x hx y hy)

theorem octComm_un5 : OctComm (un5Oct hF) ((4 : ℕ) : ℤ) := by
  intro a b ha hab hb x hx y hy
  have hcases : (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 3) ∨
      (a = 2 ∧ b = 4) ∨ (a = 3 ∧ b = 4) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [octComm_one_two_un5 hF x hx y hy]
    exact one_mem _
  · exact le_iSup₂_of_le (f := fun c (_ : c ∈ Set.Ioo (1 : ℤ) 3) => un5Oct hF c) 2
      (by simp [Set.mem_Ioo]) le_rfl (octComm_one_three_un5 hF x hx y hy)
  · refine (sup_le (le_iSup₂_of_le (f := fun c (_ : c ∈ Set.Ioo (1 : ℤ) 4) => un5Oct hF c) 2
      (by simp [Set.mem_Ioo]) le_rfl) (le_iSup₂_of_le
        (f := fun c (_ : c ∈ Set.Ioo (1 : ℤ) 4) => un5Oct hF c) 3 (by simp [Set.mem_Ioo])
        le_rfl) : un5Oct hF 2 ⊔ un5Oct hF 3 ≤ _) (octComm_one_four_un5 hF x hx y hy)
  · rw [octComm_two_three_un5 hF x hx y hy]
    exact one_mem _
  · exact le_iSup₂_of_le (f := fun c (_ : c ∈ Set.Ioo (2 : ℤ) 4) => un5Oct hF c) 3
      (by simp [Set.mem_Ioo]) le_rfl (octComm_two_four_un5 hF x hx y hy)
  · rw [octComm_three_four_un5 hF x hx y hy]
    exact one_mem _

end Relations

end CFSG.Quasithin.H13.F431.Un

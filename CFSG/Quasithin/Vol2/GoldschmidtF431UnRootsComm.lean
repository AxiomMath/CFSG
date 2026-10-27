module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits
open scoped commutatorElement

section Commutators

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

theorem octRoot_mem_roots_un {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) :
    octRoot k ∈ (rootDatum hF 4).roots :=
  octRoot_mem_roots' (isRoot_four_of h1 h4)

theorem octComm_aux_un {a b : ℤ} (ha : 1 ≤ a) (ha4 : a ≤ 4) (hb : 1 ≤ b) (hb4 : b ≤ 4)
    (hind : LinIndepPair (octRoot a) (octRoot b)) {S : Subgroup (SU (unitaryInvolution F p f) 4)}
    (hS : ∀ ε : Fin 2 → ℤ, ε ∈ openCone (rootDatum hF 4).roots (octRoot a) (octRoot b) →
      (rootDatum hF 4).rootGroup ε ≤ S) :
    ∀ x ∈ unOct hF a, ∀ y ∈ unOct hF b, ⁅x, y⁆ ∈ S := fun x hx y hy => by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hext := steinbergExtras hF 4 (by norm_num) ζ hζ
  exact (iSup₂_le hS : (⨆ ε ∈ openCone (rootDatum hF 4).roots (octRoot a) (octRoot b),
      (rootDatum hF 4).rootGroup ε) ≤ S)
    (hext.commutator_mem (octRoot a) (octRoot_mem_roots_un hF ha ha4)
      (octRoot b) (octRoot_mem_roots_un hF hb hb4) hind x hx y hy)

theorem octComm_one_three_un :
    ∀ x ∈ unOct hF 1, ∀ y ∈ unOct hF 3, ⁅x, y⁆ ∈ unOct hF 2 :=
  octComm_aux_un hF (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_one, octRoot_three] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_one, octRoot_three] at h0 h1
      have hε : ε = octRoot 2 := by
        refine ext_fin_two ?_ ?_ <;> simp [octRoot_two] <;> omega
      subst hε
      exact le_rfl)

theorem octComm_one_four_un :
    ∀ x ∈ unOct hF 1, ∀ y ∈ unOct hF 4, ⁅x, y⁆ ∈ unOct hF 2 ⊔ unOct hF 3 :=
  octComm_aux_un hF (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_one, octRoot_four] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_one, octRoot_four] at h0 h1
      rcases (by omega : (ε 0 = 2 ∧ ε 1 = 1) ∨ (ε 0 = 1 ∧ ε 1 = 1)) with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · have hε : ε = octRoot 2 := by
          refine ext_fin_two ?_ ?_ <;> simp [octRoot_two] <;> omega
        subst hε
        exact le_sup_left
      · have hε : ε = octRoot 3 := by
          refine ext_fin_two ?_ ?_ <;> simp [octRoot_three] <;> omega
        subst hε
        exact le_sup_right)

theorem octComm_one_two_un :
    ∀ x ∈ unOct hF 1, ∀ y ∈ unOct hF 2, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux_un hF (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_one, octRoot_two] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_one, octRoot_two] at h0 h1
      omega) x hx y hy)

theorem octComm_two_three_un :
    ∀ x ∈ unOct hF 2, ∀ y ∈ unOct hF 3, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux_un hF (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_two, octRoot_three] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_two, octRoot_three] at h0 h1
      omega) x hx y hy)

theorem octComm_two_four_un :
    ∀ x ∈ unOct hF 2, ∀ y ∈ unOct hF 4, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux_un hF (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_two, octRoot_four] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_two, octRoot_four] at h0 h1
      omega) x hx y hy)

theorem octComm_three_four_un :
    ∀ x ∈ unOct hF 3, ∀ y ∈ unOct hF 4, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux_un hF (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_three, octRoot_four] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_three, octRoot_four] at h0 h1
      omega) x hx y hy)

theorem octComm_un : OctComm (unOct hF) ((4 : ℕ) : ℤ) := by
  intro a b ha hab hb x hx y hy
  have hcases : (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 3) ∨
      (a = 2 ∧ b = 4) ∨ (a = 3 ∧ b = 4) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [octComm_one_two_un hF x hx y hy]
    exact one_mem _
  · exact le_iSup₂_of_le (f := fun c (_ : c ∈ Set.Ioo (1 : ℤ) 3) => unOct hF c) 2
      (by simp [Set.mem_Ioo]) le_rfl (octComm_one_three_un hF x hx y hy)
  · refine (sup_le (le_iSup₂_of_le (f := fun c (_ : c ∈ Set.Ioo (1 : ℤ) 4) => unOct hF c) 2
      (by simp [Set.mem_Ioo]) le_rfl) (le_iSup₂_of_le
        (f := fun c (_ : c ∈ Set.Ioo (1 : ℤ) 4) => unOct hF c) 3 (by simp [Set.mem_Ioo])
        le_rfl) : unOct hF 2 ⊔ unOct hF 3 ≤ _) (octComm_one_four_un hF x hx y hy)
  · rw [octComm_two_three_un hF x hx y hy]
    exact one_mem _
  · rw [octComm_two_four_un hF x hx y hy]
    exact one_mem _
  · rw [octComm_three_four_un hF x hx y hy]
    exact one_mem _

end Commutators

end CFSG.Quasithin.H13.F431.Un

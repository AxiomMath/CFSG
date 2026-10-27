module

public import CFSG.Quasithin.EmptyFaithful.S1417System
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow

public section

namespace CFSG.Quasithin

namespace S1417

open scoped Classical

open CFSG.QuasithinUnique

section Factor

variable {W : Type*} [CommGroup W] {X Y : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))}

theorem conjAut_inv_eq {g : MulAut W} {A B : Subgroup (MulAut W)} (h : B1.conjAut g B = A) :
    B1.conjAut g⁻¹ A = B := by
  rw [← h]
  ext x
  simp [B1.mem_conjAut, mul_assoc]

theorem conjAut_injective {g : MulAut W} {A B : Subgroup (MulAut W)}
    (h : B1.conjAut g A = B1.conjAut g B) : A = B :=
  le_antisymm (B1.conjAut_le_iff.mp h.le) (B1.conjAut_le_iff.mp h.ge)

theorem iSup_pair {α : Type*} [CompleteLattice α] (f : Subgroup (MulAut W) → α)
    (L₁ L₂ : Subgroup (MulAut W)) :
    (⨆ L ∈ ({L₁, L₂} : Finset (Subgroup (MulAut W))), f L) = f L₁ ⊔ f L₂ := by
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact le_sup_left
    · rw [Finset.mem_singleton.mp hL]
      exact le_sup_right
  · exact sup_le
      (le_iSup₂ (f := fun (L : Subgroup (MulAut W)) (_ : L ∈ ({L₁, L₂} : Finset _)) => f L) L₁
        (by simp))
      (le_iSup₂ (f := fun (L : Subgroup (MulAut W)) (_ : L ∈ ({L₁, L₂} : Finset _)) => f L) L₂
        (by simp))

theorem iSup_pair_ne {α : Type*} [CompleteLattice α] (f : Subgroup (MulAut W) → α)
    {L₁ L₂ : Subgroup (MulAut W)} (h : L₂ ≠ L₁) :
    (⨆ L' ∈ ({L₁, L₂} : Finset (Subgroup (MulAut W))), ⨆ (_ : L' ≠ L₁), f L') = f L₂ := by
  apply le_antisymm
  · refine iSup₂_le fun L' hL' => iSup_le fun hne => ?_
    rcases Finset.mem_insert.mp hL' with rfl | hL'
    · exact absurd rfl hne
    · rw [Finset.mem_singleton.mp hL']
  · exact le_iSup₂_of_le L₂ (by simp) (le_iSup_of_le h le_rfl)

theorem iSup_single {α : Type*} [CompleteLattice α] (f : Subgroup (MulAut W) → α)
    (L₁ : Subgroup (MulAut W)) :
    (⨆ L ∈ ({L₁} : Finset (Subgroup (MulAut W))), f L) = f L₁ := by
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    rw [Finset.mem_singleton.mp hL]
  · exact le_iSup₂ (f := fun (L : Subgroup (MulAut W)) (_ : L ∈ ({L₁} : Finset _)) => f L) L₁
      (by simp)

theorem BlockSystem.perm_pair {L₁ L₂ : Subgroup (MulAut W)} (hS : BlockSystem X Y {L₁, L₂})
    (hne : L₁ ≠ L₂) {g : MulAut W} (hg : g ∈ X) :
    (B1.conjAut g L₁ = L₁ ∧ B1.conjAut g L₂ = L₂) ∨
      (B1.conjAut g L₁ = L₂ ∧ B1.conjAut g L₂ = L₁) := by
  have h1 := (hS.perm g hg L₁ (by simp)).1
  have h2 := (hS.perm g hg L₂ (by simp)).1
  have hne' : B1.conjAut g L₁ ≠ B1.conjAut g L₂ := fun h => hne (conjAut_injective h)
  rcases Finset.mem_insert.mp h1 with h1 | h1 <;> rcases Finset.mem_insert.mp h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne'
  · exact Or.inl ⟨h1, Finset.mem_singleton.mp h2⟩
  · exact Or.inr ⟨Finset.mem_singleton.mp h1, h2⟩
  · exact absurd ((Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm) hne'

theorem BlockSystem.exists_mem_apply_eq (hS : BlockSystem X Y I) (hcard : I.card = 1 ∨ I.card = 2)
    {g : MulAut W} (hg : g ∈ X) (hfix : ∀ L ∈ I, B1.conjAut g L = L) :
    ∃ y ∈ Y, ∀ u ∈ ⨆ L ∈ I, commV L, g u = y u := by
  rcases hcard with h1 | h2
  · obtain ⟨L₁, rfl⟩ := Finset.card_eq_one.mp h1
    have hL₁ : L₁ ∈ ({L₁} : Finset (Subgroup (MulAut W))) := Finset.mem_singleton_self L₁
    have hmap := (hS.perm g hg L₁ hL₁).2
    rw [hfix L₁ hL₁] at hmap
    obtain ⟨l, hl, hlg⟩ := exists_apply_eq_of_stab (hS.nat L₁ hL₁)
      (fun l hl u hu => commV_stable L₁ hl hu) (mem_stabSub_of_map_eq hmap)
    refine ⟨l, hS.le_Y hL₁ hl, fun u hu => ?_⟩
    rw [iSup_single] at hu
    exact (hlg u hu).symm
  · obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.mp h2
    have hL₁ : L₁ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut W))) := by simp
    have hL₂ : L₂ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut W))) := by simp
    have hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := hS.comm L₁ hL₁ L₂ hL₂ hne
    have hinf : commV L₁ ⊓ commV L₂ = ⊥ := by
      have := hS.indepV L₁ hL₁
      rwa [iSup_pair_ne commV (Ne.symm hne)] at this
    have hmap₁ := (hS.perm g hg L₁ hL₁).2
    have hmap₂ := (hS.perm g hg L₂ hL₂).2
    rw [hfix L₁ hL₁] at hmap₁
    rw [hfix L₂ hL₂] at hmap₂
    obtain ⟨y, hy, hgy⟩ := exists_mem_sup_apply_eq (hS.nat L₁ hL₁) (hS.nat L₂ hL₂) hc hinf
      (mem_stabSub_of_map_eq hmap₁) (mem_stabSub_of_map_eq hmap₂)
    refine ⟨y, ?_, fun u hu => ?_⟩
    · rw [hS.Y_eq, iSup_pair]
      exact hy
    · rw [iSup_pair] at hu
      exact hgy u hu

theorem BlockSystem.exists_factor [Finite W] (hS : BlockSystem X Y I) (hYX : Y ≤ X)
    (hXY : ∀ g ∈ X, B1.conjAut g Y = Y) (hcard : I.card = 1 ∨ I.card = 2)
    {T' : Subgroup (MulAut W)} (hT : IsSylowTwoOf T' X) {g : MulAut W} (hg : g ∈ X) :
    ∃ y ∈ Y, ∃ τ ∈ T', ∀ y' ∈ Y, (y⁻¹ * g * τ⁻¹) * y' = y' * (y⁻¹ * g * τ⁻¹) := by
  obtain ⟨τ, hτ, hfix⟩ : ∃ τ ∈ T', ∀ L ∈ I, B1.conjAut (g * τ⁻¹) L = L := by
    rcases hcard with h1 | h2
    · obtain ⟨L₁, rfl⟩ := Finset.card_eq_one.mp h1
      refine ⟨1, T'.one_mem, fun L hL => ?_⟩
      have := (hS.perm g hg L hL).1
      rw [Finset.mem_singleton.mp hL, inv_one, mul_one]
      rw [Finset.mem_singleton.mp hL] at this
      exact Finset.mem_singleton.mp this
    · obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.mp h2
      have hperm : ∀ h ∈ X, (B1.conjAut h L₁ = L₁ ∧ B1.conjAut h L₂ = L₂) ∨
          (B1.conjAut h L₁ = L₂ ∧ B1.conjAut h L₂ = L₁) := fun h hh => hS.perm_pair hne hh
      by_cases hgf : B1.conjAut g L₁ = L₁
      · refine ⟨1, T'.one_mem, fun L hL => ?_⟩
        have hg2 : B1.conjAut g L₂ = L₂ := by
          rcases hperm g hg with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · exact absurd (hgf.symm.trans h) hne
        rw [inv_one, mul_one]
        rcases Finset.mem_insert.mp hL with rfl | hL
        · exact hgf
        · rw [Finset.mem_singleton.mp hL]
          exact hg2
      · obtain ⟨τ, hτ, hτ1⟩ := exists_swap_mem_of_isSylowTwoOf hT hg hgf hperm
        have hτX : τ ∈ X := hT.1 hτ
        have hτs : B1.conjAut τ L₁ = L₂ ∧ B1.conjAut τ L₂ = L₁ := by
          rcases hperm τ hτX with ⟨h, -⟩ | h
          · exact absurd h hτ1
          · exact h
        have hgs : B1.conjAut g L₁ = L₂ ∧ B1.conjAut g L₂ = L₁ := by
          rcases hperm g hg with ⟨h, -⟩ | h
          · exact absurd h hgf
          · exact h
        refine ⟨τ, hτ, fun L hL => ?_⟩
        rw [conjAut_mul]
        rcases Finset.mem_insert.mp hL with rfl | hL
        · rw [conjAut_inv_eq hτs.2, hgs.2]
        · rw [Finset.mem_singleton.mp hL, conjAut_inv_eq hτs.1, hgs.1]
  have hτX : τ ∈ X := hT.1 hτ
  have hg' : g * τ⁻¹ ∈ X := X.mul_mem hg (X.inv_mem hτX)
  obtain ⟨y, hy, hgy⟩ := hS.exists_mem_apply_eq hcard hg' hfix
  refine ⟨y, hy, τ, hτ, ?_⟩
  have hc : (y⁻¹ * g * τ⁻¹) ∈ X := by
    rw [mul_assoc]
    exact X.mul_mem (X.inv_mem (hYX hy)) hg'
  refine hS.commute_of_trivial hYX hXY hc fun u hu => ?_
  rw [mul_assoc]
  show y⁻¹ ((g * τ⁻¹) u) = u
  rw [show (g * τ⁻¹) u = y u from hgy u hu]
  simp

end Factor

end S1417

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.C124YZSwap
public import CFSG.Quasithin.Background.B4ModelsAction

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Quasithin Equiv Equiv.Perm

section Fix

variable {Γ Q : Type*} [Group Γ] [Group Q]

@[expose] def fixAct (act : Γ →* MulAut Q) (B : Subgroup Γ) : Subgroup Q where
  carrier := {q | ∀ b ∈ B, act b q = q}
  one_mem' := fun b _ => map_one _
  mul_mem' := fun {x y} hx hy b hb => by rw [map_mul, hx b hb, hy b hb]
  inv_mem' := fun {x} hx b hb => by rw [map_inv, hx b hb]

theorem fixAct_anti {act : Γ →* MulAut Q} {B B' : Subgroup Γ} (h : B ≤ B') :
    fixAct act B' ≤ fixAct act B := fun _ hq b hb => hq b (h hb)

end Fix

structure PairModel (m : ℕ) (Q : Type*) [Group Q] (act : Perm (Fin m) →* MulAut Q) where
  pq : Fin m → Fin m → Q
  act_pq : ∀ σ i j, act σ (pq i j) = pq (σ i) (σ j)
  pq_comm : ∀ i j, pq i j = pq j i
  mem_of_eq : ∀ i j p q', i ≠ j → p ≠ q' → pq p q' = pq i j → p = i ∨ p = j

section Stab

variable {m : ℕ} {Q : Type*} [Group Q] {act : Perm (Fin m) →* MulAut Q}
  (M : PairModel m Q act)

include M

theorem PairModel.apply_mem_of_fix {a b : Fin m} (hab : a ≠ b) {σ : Perm (Fin m)}
    (h : act σ (M.pq a b) = M.pq a b) : (σ a = a ∨ σ a = b) ∧ (σ b = a ∨ σ b = b) := by
  rw [M.act_pq] at h
  refine ⟨M.mem_of_eq a b _ _ hab (fun e => hab (σ.injective e)) h, ?_⟩
  rw [M.pq_comm] at h
  rcases M.mem_of_eq a b _ _ hab (fun e => hab (σ.injective e).symm) h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

theorem PairModel.pq_mem_fixAct {H : Subgroup (Perm (Fin m))} (hH : IsSwapGroup H)
    (hp : IsPGroup 2 H) {a b : Fin m} (hab : a ≠ b) (h : swap a b ∈ H) :
    M.pq a b ∈ fixAct act H := by
  intro d hd
  rw [M.act_pq]
  have h1 := hH.apply_mem_pair hp hab h hd
  have h2 := hH.apply_mem_pair hp (Ne.symm hab) (by rwa [swap_comm]) hd
  rcases h1 with h1 | h1
  · have : d b = b := by
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd (d.injective (h2.trans h1.symm)) (Ne.symm hab)
    rw [h1, this]
  · have : d b = a := by
      rcases h2 with h2 | h2
      · exact absurd (d.injective (h2.trans h1.symm)) (Ne.symm hab)
      · exact h2
    rw [h1, this, M.pq_comm]

theorem PairModel.pq_mem_fixAct_of_fixed {H : Subgroup (Perm (Fin m))} {x y : Fin m}
    (hx : ∀ d ∈ H, d x = x) (hy : ∀ d ∈ H, d y = y) : M.pq x y ∈ fixAct act H := by
  intro d hd
  rw [M.act_pq, hx d hd, hy d hd]

theorem PairModel.mem_of_fix {H : Subgroup (Perm (Fin m))} (hH : IsSwapGroup H)
    (hp : IsPGroup 2 H)
    (hF : ∀ x, (∀ d ∈ H, d x = x) →
      (∃ f₁ f₂, f₁ ≠ x ∧ f₂ ≠ x ∧ f₁ ≠ f₂ ∧ (∀ d ∈ H, d f₁ = f₁) ∧ (∀ d ∈ H, d f₂ = f₂)) ∨
        ∀ y, (∀ d ∈ H, d y = y) → y = x)
    (σ : Perm (Fin m)) (hσ : ∀ q ∈ fixAct act H, act σ q = q) : σ ∈ H := by
  have hA : ∀ τ : Perm (Fin m), (∀ q ∈ fixAct act H, act τ q = q) → ∀ y, (∃ d ∈ H, d y ≠ y) →
      (∃ d ∈ H, d (τ y) ≠ τ y) ∧ (τ y = y ∨ swap y (τ y) ∈ H) := by
    intro τ hτ y ⟨d, hd, hdy⟩
    have hyy : swap y (d y) ∈ H := (hH d hd y).resolve_left hdy
    have h := M.apply_mem_of_fix hdy.symm (hτ _ (M.pq_mem_fixAct hH hp hdy.symm hyy))
    rcases h.1 with h1 | h1
    · exact ⟨⟨d, hd, by rw [h1]; exact hdy⟩, Or.inl h1⟩
    · refine ⟨⟨swap y (d y), hyy, ?_⟩, Or.inr (by rw [h1]; exact hyy)⟩
      rw [h1, swap_apply_right]
      exact hdy.symm
  have hσinv : ∀ q ∈ fixAct act H, act σ⁻¹ q = q := by
    intro q hq
    have := hσ q hq
    calc act σ⁻¹ q = act σ⁻¹ (act σ q) := by rw [this]
      _ = q := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  refine hH.mem_of σ fun x => ?_
  by_cases hx : ∃ d ∈ H, d x ≠ x
  · exact (hA σ hσ x hx).2
  · push Not at hx
    left
    rcases hF x hx with ⟨f₁, f₂, h1, h2, h12, hf1, hf2⟩ | hall
    · have e1 := M.apply_mem_of_fix h1.symm (hσ _ (M.pq_mem_fixAct_of_fixed hx hf1))
      have e2 := M.apply_mem_of_fix h2.symm (hσ _ (M.pq_mem_fixAct_of_fixed hx hf2))
      rcases e1.1 with e1 | e1
      · exact e1
      · rcases e2.1 with e2 | e2
        · exact e2
        · exact absurd (e1.symm.trans e2) h12
    · by_contra hne
      have hy : ∃ d ∈ H, d (σ x) ≠ σ x := by
        by_contra hy
        push Not at hy
        exact hne (hall _ hy)
      have := (hA σ⁻¹ hσinv (σ x) hy).1
      obtain ⟨d, hd, hdne⟩ := this
      apply hdne
      rw [show σ⁻¹ (σ x) = x from σ.symm_apply_apply x]
      exact hx d hd

end Stab

section Instances

theorem zpow_eq_one_or_self' {G : Type*} [Group G] {g : G} (hg : g * g = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g := by
  have hg2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← Int.mul_ediv_add_emod k 2, h0, add_zero, zpow_mul, hg2, one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, h1, zpow_add, zpow_mul, hg2, one_zpow, one_mul, zpow_one]

theorem mem_zpowers_allOnes {n : ℕ} {x : G6.PermMod n}
    (hx : x ∈ Subgroup.zpowers (G6.allOnes n)) : x = 1 ∨ x = G6.allOnes n := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact zpow_eq_one_or_self' (G6.permMod_mul_self _) z

theorem pairVec_comm {m : ℕ} (i j : Fin m) : G64.pairVec i j = G64.pairVec j i := by
  simp [G64.pairVec, add_comm]

theorem pairVec_eq_apply {m : ℕ} {i j p q' : Fin m} (hpq : p ≠ q')
    (h : G64.pairVec p q' = G64.pairVec i j) : p = i ∨ p = j := by
  have := congrArg (fun x : G6.PermMod m => Multiplicative.toAdd x p) h
  simp only [G64.toAdd_pairVec_apply] at this
  by_contra hne
  push Not at hne
  simp [hne.1, hne.2, hpq] at this

@[expose] def pairModelCore (m : ℕ) : PairModel m ↥(G6.coreMod m) (G6.coreAct m) where
  pq i j := ⟨G64.pairVec i j, G64.pairVec_mem_coreMod i j⟩
  act_pq σ i j := Subtype.ext (by rw [G6.coreAct_coe]; exact G64.permAct_pairVec σ i j)
  pq_comm i j := Subtype.ext (pairVec_comm i j)
  mem_of_eq i j p q' _ hpq h := pairVec_eq_apply hpq (congrArg Subtype.val h)

theorem exists_not_mem_four {m : ℕ} (hm : 5 ≤ m) (i j k l : Fin m) :
    ∃ t : Fin m, t ≠ i ∧ t ≠ j ∧ t ≠ k ∧ t ≠ l := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i, j, k, l} := by
    intro t _
    by_cases h1 : t = i
    · simp [h1]
    by_cases h2 : t = j
    · simp [h2]
    by_cases h3 : t = k
    · simp [h3]
    simp [hcon t h1 h2 h3]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  have h4 : ({i, j, k, l} : Finset (Fin m)).card ≤ 4 := by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    exact Nat.succ_le_succ (by simp)
  omega

theorem pairVec_eq_of_mem_zpowers {m : ℕ} (hm : 5 ≤ m) {i j p q' : Fin m}
    (h : (G64.pairVec p q')⁻¹ * G64.pairVec i j ∈ Subgroup.zpowers (G6.allOnes m)) :
    G64.pairVec p q' = G64.pairVec i j := by
  rcases mem_zpowers_allOnes h with h1 | h1
  · rw [G6.permMod_inv_eq] at h1
    have := mul_eq_one_iff_eq_inv.1 h1
    exact this.trans (G6.permMod_inv_eq _)
  · exfalso
    obtain ⟨t, h1', h2', h3', h4'⟩ := exists_not_mem_four hm i j p q'
    have := congrArg (fun x : G6.PermMod m => Multiplicative.toAdd x t) h1
    simp [G6.allOnes, G64.toAdd_pairVec_apply, h1', h2', h3', h4'] at this
    exact absurd this (by decide)

end Instances

section DM

abbrev DM (m : ℕ) : Type := (FFModel.symDn m).Mod

noncomputable abbrev dAct (m : ℕ) : Perm (Fin m) →* MulAut (DM m) :=
  (FFModel.symDn_isActionModel m).modAct

@[expose] def pairQ {m : ℕ} (i j : Fin m) : DM m :=
  QuotientGroup.mk ⟨G64.pairVec i j, G64.pairVec_mem_coreMod i j⟩

theorem dAct_pairQ {m : ℕ} (σ : Perm (Fin m)) (i j : Fin m) :
    dAct m σ (pairQ i j) = pairQ (σ i) (σ j) := by
  show QuotientGroup.mk _ = QuotientGroup.mk _
  congr 1
  exact Subtype.ext (G64.permAct_pairVec σ i j)

@[expose] noncomputable def pairModelDM {m : ℕ} (hm : 5 ≤ m) : PairModel m (DM m) (dAct m) where
  pq i j := pairQ i j
  act_pq σ i j := dAct_pairQ σ i j
  pq_comm i j := by
    show QuotientGroup.mk _ = QuotientGroup.mk _
    congr 1
    exact Subtype.ext (pairVec_comm i j)
  mem_of_eq i j p q' _ hpq h := by
    have h1 := (QuotientGroup.eq.1 h)
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (G64.pairVec p q')⁻¹ * G64.pairVec i j ∈
        Subgroup.zpowers (G6.allOnes m) := h1.1
    exact pairVec_eq_apply hpq (pairVec_eq_of_mem_zpowers hm h2)

end DM

end CFSG.Quasithin.C124.YZ

module

public import CFSG.Quasithin.Recognition.M12AscPinData

public section

namespace CFSG.Quasithin.M12Pin

open Equiv CFSG.Sporadic.Bridge

private theorem le_val_apply {h : Perm (Fin 12)} (n : ℕ) (hh : ∀ i : Fin 12, i.val < n → h i = i)
    {i : Fin 12} (hi : n ≤ i.val) : n ≤ (h i).val := by
  by_contra hlt
  push Not at hlt
  have h2 : h i = i := h.injective (hh _ hlt)
  rw [h2] at hlt
  omega

private theorem sift_step {h t : Perm (Fin 12)} (n : ℕ) (p : Fin 12) (hp : p.val = n)
    (hh : ∀ i : Fin 12, i.val < n → h i = i) (ht : ∀ i : Fin 12, i.val < n → t i = i)
    (htn : t p = h p) : ∀ i : Fin 12, i.val < n + 1 → (t⁻¹ * h) i = i := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
  · rw [Perm.mul_apply, hh i hlt, Perm.inv_def, Equiv.symm_apply_eq]
    exact (ht i hlt).symm
  · have : i = p := Fin.ext (heq.trans hp.symm)
    subst this
    rw [Perm.mul_apply, ← htn]
    simp

theorem sift {P : Subgroup (Perm (Fin 12))}
    (hA : ∀ g ∈ P, (∀ i : Fin 12, i.val < 5 → g i = i) → g = 1) (hS : S0 ≤ P)
    {h : Perm (Fin 12)} (hh : h ∈ P) (h0 : ∀ i : Fin 12, i.val < 2 → h i = i) :
    ∃ a ∈ transT2, ∃ b ∈ transT3, ∃ c ∈ transT4, h = a * b * c := by
  obtain ⟨a, ha, haf, ha2⟩ := T2_spec (h 2) (le_val_apply 2 h0 (by decide))
  have h1 : ∀ i : Fin 12, i.val < 3 → (a⁻¹ * h) i = i := sift_step 2 2 rfl h0 haf ha2
  have hP1 : a⁻¹ * h ∈ P := P.mul_mem (P.inv_mem (hS (transT2_mem a ha))) hh
  obtain ⟨b, hb, hbf, hb3⟩ := T3_spec ((a⁻¹ * h) 3) (le_val_apply 3 h1 (by decide))
  have h2 : ∀ i : Fin 12, i.val < 4 → (b⁻¹ * (a⁻¹ * h)) i = i := sift_step 3 3 rfl h1 hbf hb3
  have hP2 : b⁻¹ * (a⁻¹ * h) ∈ P := P.mul_mem (P.inv_mem (hS (transT3_mem b hb))) hP1
  obtain ⟨c, hc, hcf, hc4⟩ := T4_spec ((b⁻¹ * (a⁻¹ * h)) 4) (le_val_apply 4 h2 (by decide))
  have h3 : ∀ i : Fin 12, i.val < 5 → (c⁻¹ * (b⁻¹ * (a⁻¹ * h))) i = i :=
    sift_step 4 4 rfl h2 hcf hc4
  have hP3 : c⁻¹ * (b⁻¹ * (a⁻¹ * h)) ∈ P := P.mul_mem (P.inv_mem (hS (transT4_mem c hc))) hP2
  have h4 : c⁻¹ * (b⁻¹ * (a⁻¹ * h)) = 1 := hA _ hP3 h3
  refine ⟨a, ha, b, hb, c, hc, ?_⟩
  have e : a * (b * (c * (c⁻¹ * (b⁻¹ * (a⁻¹ * h))))) = a * (b * (c * 1)) := by rw [h4]
  simpa [mul_assoc] using e

private theorem fix_lt_five {g : Perm (Fin 12)} (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h4 : g 4 = 4) : ∀ i : Fin 12, i.val < 5 → g i = i := by
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert hi; revert i; decide
  rcases this with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem eq_M12_of_sharply_five_transitive (P : Subgroup (Perm (Fin 12)))
    (hA : ∀ g ∈ P, ∀ a : Fin 5 → Fin 12, Function.Injective a → (∀ i, g (a i) = a i) → g = 1)
    (hτ : ∃ τ ∈ P, τ 0 = 1 ∧ τ 1 = 0 ∧ τ 2 = 2 ∧ τ 3 = 3 ∧ τ 4 = 4)
    (hS : ∀ g : Perm (Fin 12), (g ∈ P ∧ g 0 = 0) ↔ g ∈ S0) :
    P = CFSG.Blueprint.NativeSporadic.M12 := by
  have hSP : S0 ≤ P := fun g hg => ((hS g).2 hg).1
  have hA5 : ∀ g ∈ P, (∀ i : Fin 12, i.val < 5 → g i = i) → g = 1 := by
    intro g hg hfix
    refine hA g hg (fun i => ⟨i.val, by have := i.isLt; omega⟩) ?_ fun i => hfix _ i.isLt
    intro i j hij
    exact Fin.ext (Fin.mk.inj hij)
  obtain ⟨τ, hτP, t0, t1, t2, t3, t4⟩ := hτ
  have hττ : τ * τ = 1 :=
    hA5 _ (P.mul_mem hτP hτP) (fix_lt_five (by simp [t0, t1]) (by simp [t0, t1])
      (by simp [t2]) (by simp [t3]) (by simp [t4]))
  have hinv : ∀ j, τ (τ j) = j := fun j => by
    simpa using congrArg (fun g : Perm (Fin 12) => g j) hττ
  have hge : ∀ i : Fin 12, 5 ≤ i.val → 5 ≤ (τ i).val := by
    intro i hi
    by_contra hlt
    push Not at hlt
    have hx : ∀ x : Fin 12, x.val < 5 → (τ x).val < 5 := by
      intro x hx
      have : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by revert hx; revert x; decide
      rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [t0, t1, t2, t3, t4]
    have := hx _ hlt
    rw [hinv] at this
    omega
  have hkP : τ * kElt * τ ∈ P := P.mul_mem (P.mul_mem hτP (hSP kElt_mem)) hτP
  have hkfix : ∀ i : Fin 12, i.val < 2 → (τ * kElt * τ) i = i := by
    intro i hi
    have : i = 0 ∨ i = 1 := by revert hi; revert i; decide
    rcases this with rfl | rfl <;> simp [Perm.mul_apply, t0, t1, kElt_apply, kvec]
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := sift hA5 hSP hkP hkfix
  have hmemL : τ * kElt * τ ∈ Llist := by rw [habc]; exact mem_Llist ha hb hc
  have hkey : keyF (fun j => τ (kvec (τ j))) ∈ Lkeys := by
    have h1 : keyF ⇑(τ * kElt * τ) ∈ Llist.map (fun ℓ : Perm (Fin 12) => keyF ℓ) :=
      List.mem_map.2 ⟨_, hmemL, rfl⟩
    rw [Llist_keys] at h1
    have h2 : ⇑(τ * kElt * τ) = fun j => τ (kvec (τ j)) := by
      funext j
      simp [Perm.mul_apply, kElt_apply]
    rwa [h2] at h1
  have hcand : candFun (τ 5) (τ 6) (τ 7) (τ 8) (τ 9) (τ 10) (τ 11) = ⇑τ := by
    funext j
    fin_cases j <;> simp [candFun, t0, t1, t2, t3, t4]
  have hne : ∀ x y : Fin 12, x ≠ y → τ x ≠ τ y := fun x y h h' => h (τ.injective h')
  have hiff : ∀ x y : Fin 12, τ x = y ↔ τ y = x := fun x y =>
    ⟨fun h => by rw [← h, hinv], fun h => by rw [← h, hinv]⟩
  have hfl := finite_lemma (τ 5) (hge 5 (by decide))
    (τ 6) (hge 6 (by decide)) (hne _ _ (by decide)) (hiff _ _)
    (τ 7) (hge 7 (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hiff _ _) (hiff _ _)
    (τ 8) (hge 8 (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
    (hiff _ _) (hiff _ _) (hiff _ _)
    (τ 9) (hge 9 (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
    (hne _ _ (by decide)) (hiff _ _) (hiff _ _) (hiff _ _) (hiff _ _)
    (τ 10) (hge 10 (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
    (hne _ _ (by decide)) (hne _ _ (by decide)) (hiff _ _) (hiff _ _) (hiff _ _) (hiff _ _)
    (hiff _ _)
    (τ 11) (hge 11 (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
    (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hiff _ _) (hiff _ _)
    (hiff _ _) (hiff _ _) (hiff _ _) (hiff _ _)
    (by rw [hcand]; exact hkey)
  rw [hcand] at hfl
  have hswap : τ ≠ Equiv.swap (0 : Fin 12) 1 := by
    intro h
    have hmem : Equiv.swap (0 : Fin 12) 1 ∈ P := h ▸ hτP
    have h1 := hA _ hmem (fun i : Fin 5 => (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin 12))
      (by
        intro i j hij
        exact Fin.ext (by simpa using congrArg Fin.val hij))
      (by
        intro i
        refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;>
          (intro h; have := congrArg Fin.val h; simp at this))
    have h2 := congrArg (fun g : Perm (Fin 12) => g 0) h1
    simp at h2
  have hτ0 : τ = tau0 := by
    rcases hfl with h | h
    · exact absurd (DFunLike.coe_injective h) hswap
    · exact DFunLike.coe_injective h
  have hτ0P : tau0 ∈ P := hτ0 ▸ hτP
  have hM12P : CFSG.Blueprint.NativeSporadic.M12 ≤ P :=
    M12_le (hSP s1_mem_S0) (hSP s2_mem_S0) hτ0P
  refine le_antisymm ?_ hM12P
  intro g hg
  obtain ⟨r, hrM, hr0⟩ := exists_mem_M12_apply_zero (g 0)
  have hrP : r ∈ P := hM12P hrM
  have hgr : r⁻¹ * g ∈ P ∧ (r⁻¹ * g) 0 = 0 := by
    refine ⟨P.mul_mem (P.inv_mem hrP) hg, ?_⟩
    rw [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_eq, hr0]
  have hgS : r⁻¹ * g ∈ S0 := (hS _).1 hgr
  have hgM := Subgroup.mul_mem _ hrM (S0_le_M12 hgS)
  rwa [mul_inv_cancel_left] at hgM

end CFSG.Quasithin.M12Pin

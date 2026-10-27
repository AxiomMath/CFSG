module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix symmDiff

private theorem nmh_even_card_symmDiff_singleton_of_odd {k : ℕ} {A : Finset (Fin k)} {i : Fin k}
    (hA : Odd A.card) : Even (A ∆ {i}).card := by
  have hcard : (A ∆ {i}).card = if i ∈ A then A.card - 1 else A.card + 1 := by
    by_cases hi : i ∈ A
    · rw [if_pos hi]
      have h : A ∆ {i} = A.erase i := by
        ext j
        simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_singleton]
        constructor
        · rintro (⟨hjA, hji⟩ | ⟨hji, hjnA⟩)
          · exact ⟨hji, hjA⟩
          · exact absurd (hji.symm ▸ hi) hjnA
        · rintro ⟨hji, hjA⟩
          exact Or.inl ⟨hjA, hji⟩
      rw [h, Finset.card_erase_of_mem hi]
    · rw [if_neg hi]
      have h : A ∆ {i} = insert i A := by
        ext j
        simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (⟨hjA, hji⟩ | ⟨rfl, _⟩)
          · exact Or.inr hjA
          · exact Or.inl rfl
        · rintro (rfl | hjA)
          · exact Or.inr ⟨rfl, hi⟩
          · exact Or.inl ⟨hjA, fun hji => hi (hji ▸ hjA)⟩
      rw [h, Finset.card_insert_of_notMem hi]
  rw [hcard]
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    obtain ⟨t, ht⟩ := hA
    rw [ht, Nat.add_sub_cancel]
    exact even_two_mul t
  · rw [if_neg hi]
    exact hA.add_one

private theorem nmh_exists_notMem_pair {k l : Fin 8} (hkl : k ≠ l) :
    ∃ m : Fin 8, m ∉ ({k, l} : Finset (Fin 8)) := by
  have hlt : ({k, l} : Finset (Fin 8)).card < (Finset.univ : Finset (Fin 8)).card := by
    rw [Finset.card_pair hkl, Finset.card_univ, Fintype.card_fin]
    decide
  obtain ⟨m, _, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨m, hm⟩

private theorem nmh_nmSgn_singleton_mulVec :
    nmSgn ({0} : Finset (Fin 8)) *ᵥ nmE0 = (-1 : ZMod 3) • nmE0 := by
  decide

theorem nmF_subset_evenAll0 : nmF ⊆ evenAll0 7 := by
  rintro A ⟨σ, s, hs, ⟨hσ, hps⟩, rfl⟩
  exact ⟨σ, s, hs, ⟨by rw [hσ]; rfl, hps⟩, rfl⟩

theorem N7MSetup.exists_of_mem_nmF {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {a : Matrix (Fin 8) (Fin 8) (ZMod 3)} (ha : a ∈ nmF) : ∃ x, S.ρ x = a :=
  S.surj_H1 a (nmF_subset_evenAll0 ha)

theorem N7MSetup.ne_nmSgn_of_odd {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A : Finset (Fin 8)} (hA : Odd A.card) (x : X) : S.ρ x ≠ nmSgn A := by
  intro hx
  obtain ⟨y, hy⟩ := S.exists_of_mem_nmF
    (nmSgn_mem_nmF (nmh_even_card_symmDiff_singleton_of_odd (i := 0) hA))
  have hxy : S.ρ (x * y) = nmSgn ({0} : Finset (Fin 8)) := by
    rw [map_mul, hx, hy, nmSgn_mul]
    congr 1
    exact symmDiff_symmDiff_cancel_left A ({0} : Finset (Fin 8))
  have hmem : S.ρ (x * y) ∈ evenAll0 7 := by
    rw [← S.norm_iff]
    exact ⟨-1, by rw [hxy, nmh_nmSgn_singleton_mulVec]⟩
  obtain ⟨σ, s, hs, ⟨-, hps⟩, hsp⟩ := hmem
  have h_eq : spMat (1 : Equiv.Perm (Fin 8))
      (fun i : Fin 8 => if i ∈ ({0} : Finset (Fin 8)) then (-1 : ZMod 3) else 1) =
      spMat σ s := by
    have hd : nmSgn ({0} : Finset (Fin 8)) =
        spMat (1 : Equiv.Perm (Fin 8))
          (fun i : Fin 8 => if i ∈ ({0} : Finset (Fin 8)) then (-1 : ZMod 3) else 1) := by
      show Matrix.diagonal (fun i : Fin 8 =>
          if i ∈ ({0} : Finset (Fin 8)) then (-1 : ZMod 3) else 1) =
        spMat (1 : Equiv.Perm (Fin 8))
          (fun i : Fin 8 => if i ∈ ({0} : Finset (Fin 8)) then (-1 : ZMod 3) else 1)
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [spMat_apply, Matrix.diagonal]
      · simp [spMat_apply, Matrix.diagonal, hij]
    exact hd.symm.trans (hxy.symm.trans hsp)
  have hds : (fun i : Fin 8 =>
      if i ∈ ({0} : Finset (Fin 8)) then (-1 : ZMod 3) else 1) = s :=
    (nm_spMat_inj (fun i => by split_ifs <;> simp) hs h_eq).2
  have hprod1 : (∏ i : Fin 8,
      (if i ∈ ({0} : Finset (Fin 8)) then (-1 : ZMod 3) else 1)) = 1 := by
    rw [hds]
    exact hps
  have hprod2 : (∏ i : Fin 8,
      (if i ∈ ({0} : Finset (Fin 8)) then (-1 : ZMod 3) else 1)) = -1 := by
    rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const,
      Finset.prod_const_one, mul_one, Finset.card_singleton, pow_one]
  exact absurd (hprod1.symm.trans hprod2) (by decide)

theorem nm_normalizer_mono {X : Type} [Group X] [Finite X] (S : N7MSetup X) {x : X}
    (hx : ∀ a, a ∈ S.Fgrp ↔ x * a * x⁻¹ ∈ S.Fgrp) :
    ∃ (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3), IsSign s ∧ S.ρ x = spMat σ s := by
  have hz_cancel : ∀ a b c : ZMod 3, a ≠ 0 → a * b = a * c → b = c := by decide
  have hz_ne_mul : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by decide
  have hz_mul_one : ∀ a b : ZMod 3, a * b = 1 → a ≠ 0 := by decide
  have hcol_ne : ∀ l, S.ρ x *ᵥ Pi.single l (1 : ZMod 3) ≠ 0 := by
    intro l hv
    have h1 : (S.ρ x⁻¹) *ᵥ (S.ρ x *ᵥ Pi.single l (1 : ZMod 3)) =
        Pi.single l (1 : ZMod 3) := by
      rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    rw [hv, Matrix.mulVec_zero] at h1
    have h01 : (0 : ZMod 3) = 1 := by
      have := congrFun h1 l
      simpa using this
    exact one_ne_zero h01.symm
  have hex : ∀ l, ∃ r, S.ρ x r l ≠ 0 := by
    intro l
    have hcol : (S.ρ x).col l ≠ 0 := by
      rw [← Matrix.mulVec_single_one]
      exact hcol_ne l
    exact Function.ne_iff.mp hcol
  have huniq : ∀ l r r', S.ρ x r l ≠ 0 → S.ρ x r' l ≠ 0 → r = r' := by
    intro l r r' hr hr'
    by_contra hne
    obtain ⟨m, hm⟩ := nmh_exists_notMem_pair hne
    have hmr : m ≠ r := fun h => hm (by simp [h])
    have hmr' : m ≠ r' := fun h => hm (by simp [h])
    have hbmem : nmSgn ({r, m} : Finset (Fin 8)) ∈ nmF :=
      nmSgn_mem_nmF (by rw [Finset.card_pair hmr.symm]; decide)
    obtain ⟨y, hy⟩ := S.exists_of_mem_nmF hbmem
    have hyF : y ∈ S.Fgrp := by rw [S.mem_Fgrp, hy]; exact hbmem
    have haF : x⁻¹ * y * x ∈ S.Fgrp := by
      rw [hx]
      have h : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rw [h]
      exact hyF
    obtain ⟨B, _, hSa⟩ :=
      exists_nmSgn_of_mem_nmF ((S.mem_Fgrp (x⁻¹ * y * x)).mp haF)
    have hEq : S.ρ y * S.ρ x = S.ρ x * S.ρ (x⁻¹ * y * x) := by
      have h : y * x = x * (x⁻¹ * y * x) := by group
      have hh := congrArg S.ρ h
      rw [map_mul, map_mul] at hh
      exact hh
    have hr'_notmem : r' ∉ ({r, m} : Finset (Fin 8)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hne h.symm
      · exact hmr' h.symm
    have h_r : S.ρ x r l * (if l ∈ B then (-1 : ZMod 3) else 1) = S.ρ x r l * (-1) := by
      have h := congrFun (congrFun hEq r) l
      rw [hy, hSa] at h
      simp only [nmSgn, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
      rw [if_pos (show r ∈ ({r, m} : Finset (Fin 8)) by simp)] at h
      have hcomm : ∀ z w : ZMod 3, -1 * z = w → w = z * (-1) := by decide
      exact hcomm _ _ h
    have h_r' : S.ρ x r' l * (if l ∈ B then (-1 : ZMod 3) else 1) = S.ρ x r' l * 1 := by
      have h := congrFun (congrFun hEq r') l
      rw [hy, hSa] at h
      simp only [nmSgn, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
      rw [if_neg hr'_notmem, one_mul] at h
      rw [mul_one]
      exact h.symm
    have hdl : (if l ∈ B then (-1 : ZMod 3) else 1) = -1 :=
      hz_cancel (S.ρ x r l) (if l ∈ B then -1 else 1) (-1) hr h_r
    have hdl' : (if l ∈ B then (-1 : ZMod 3) else 1) = 1 :=
      hz_cancel (S.ρ x r' l) (if l ∈ B then -1 else 1) 1 hr' h_r'
    exact absurd (hdl.symm.trans hdl') (by decide)
  let π : Fin 8 → Fin 8 := fun l => Classical.choose (hex l)
  have hπ_spec : ∀ l, S.ρ x (π l) l ≠ 0 := fun l => Classical.choose_spec (hex l)
  have hM_zero : ∀ l r, r ≠ π l → S.ρ x r l = 0 := by
    intro l r hr
    by_contra hc
    exact hr (huniq l r (π l) hc (hπ_spec l))
  have hπ_inj : Function.Injective π := by
    intro l l' hl
    by_contra hne
    have hNM : S.ρ x⁻¹ * S.ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have hNM_entry : ∀ s l, (S.ρ x⁻¹ * S.ρ x) s l =
        (S.ρ x⁻¹) s (π l) * S.ρ x (π l) l := by
      intro s l
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_single (π l)
        (fun j _ hj => by rw [hM_zero l j hj, mul_zero])
        (fun h => absurd (Finset.mem_univ _) h)
    have h1 : (S.ρ x⁻¹) l (π l) * S.ρ x (π l) l = 1 := by
      have h := congrFun (congrFun hNM l) l
      rwa [hNM_entry l l, Matrix.one_apply_eq] at h
    have h2 : (S.ρ x⁻¹) l (π l) * S.ρ x (π l) l' = 0 := by
      have h := congrFun (congrFun hNM l) l'
      rw [hNM_entry l l', ← hl, Matrix.one_apply_ne hne] at h
      exact h
    have hNne : (S.ρ x⁻¹) l (π l) ≠ 0 := hz_mul_one _ _ h1
    have hMne : S.ρ x (π l) l' ≠ 0 := by rw [hl]; exact hπ_spec l'
    exact hz_ne_mul _ _ hNne hMne h2
  have hπ_bij : Function.Bijective π := Finite.injective_iff_bijective.mp hπ_inj
  let σ : Equiv.Perm (Fin 8) := Equiv.ofBijective π hπ_bij
  let s : Fin 8 → ZMod 3 := fun l => S.ρ x (π l) l
  refine ⟨σ, s, ?_, ?_⟩
  · intro l
    exact (by decide : ∀ z : ZMod 3, z ≠ 0 → z = 1 ∨ z = -1) (S.ρ x (π l) l) (hπ_spec l)
  · ext i j
    have hσj : σ j = π j := rfl
    rw [spMat_apply, hσj]
    by_cases hij : i = π j
    · subst hij
      simp [s]
    · rw [if_neg hij]
      exact hM_zero j i hij

end CFSG.StandardType.FrameRoute.FS81

end

module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeter

public section

namespace CFSG.StandardType.SpFrame

open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem CoxeterSystem
  CFSG.LieType.Universal.Symplectic

theorem card_coxeterB_ge (n : ℕ) (hn : 2 ≤ n) :
    2 ^ n * n.factorial ≤ Nat.card (CoxeterMatrix.B n).Group := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have hr : 1 ≤ r := by omega
  rw [← coxeterMatrix_cartanC_eq_B (r + 1)]
  let W := (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group
  haveI hfinite : Finite W := by
    classical
    let sgn : (Fin (r + 1) → ℤ) → (Fin (r + 1) → Bool) := fun s a => decide (s a = 1)
    have key : ∀ w : W, ∃ q : Equiv.Perm (Fin (r + 1)) × (Fin (r + 1) → ℤ),
        SpIsSign q.2 ∧ SpRealizes (r + 1) w q.1 q.2 := by
      intro w
      obtain ⟨π, s, hs, h⟩ := exists_spRealizes w
      exact ⟨(π, s), hs, h⟩
    choose q hq using key
    let f : W → Equiv.Perm (Fin (r + 1)) × (Fin (r + 1) → Bool) :=
      fun w => ((q w).1, sgn (q w).2)
    have hsgn : ∀ {s s' : Fin (r + 1) → ℤ}, SpIsSign s → SpIsSign s' → sgn s = sgn s' → s = s' := by
      intro s s' hs hs' h
      funext a
      have ha := congrFun h a
      simp only [sgn, decide_eq_decide] at ha
      rcases hs a with h1 | h1 <;> rcases hs' a with h2 | h2
      · rw [h1, h2]
      · exfalso
        have := ha.mp h1
        rw [h2] at this
        norm_num at this
      · exfalso
        have := ha.mpr h2
        rw [h1] at this
        norm_num at this
      · rw [h1, h2]
    have hf : Function.Injective f := by
      intro w w' hww'
      have h1 : (q w).1 = (q w').1 := (Prod.ext_iff.mp hww').1
      have h2 : sgn (q w).2 = sgn (q w').2 := (Prod.ext_iff.mp hww').2
      have h3 : (q w).2 = (q w').2 := hsgn (hq w).1 (hq w').1 h2
      exact SpRealizes.inj (hq w).2 ((hq w').2.congr h1.symm h3.symm)
    exact Finite.of_injective f hf
  have hmem_gen : ∀ σ : Equiv.Perm (Fin (r + 1)),
      σ ∈ Submonoid.closure (Set.range fun i : Fin r => Equiv.swap i.castSucc i.succ) := by
    intro σ
    rw [Equiv.Perm.mclosure_swap_castSucc_succ r]
    exact Submonoid.mem_top σ
  have hperm : ∀ σ : Equiv.Perm (Fin (r + 1)), ∃ w : W, SpRealizes (r + 1) w σ 1 := by
    intro σ
    refine Submonoid.closure_induction (motive := fun σ _ => ∃ w : W, SpRealizes (r + 1) w σ 1)
      ?_ ?_ ?_ (hmem_gen σ)
    · rintro x ⟨i, rfl⟩
      have hlt : i.castSucc.val + 1 < r + 1 := by
        simp only [Fin.val_castSucc]; omega
      have he : (⟨i.castSucc.val + 1, hlt⟩ : Fin (r + 1)) = i.succ := Fin.ext (by simp)
      exact ⟨(coxeterMatrix (isFiniteType_cartanC (r + 1))).toCoxeterSystem.simple i.castSucc,
        (spRealizes_simple_of_lt (m := r + 1) hlt).congr (by rw [he]) rfl⟩
    · exact ⟨1, spRealizes_one⟩
    · rintro x y hx hy ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
      exact ⟨w₁ * w₂, h₁.mul_one h₂⟩
  obtain ⟨ε, hε, -⟩ := exists_sign_family r hr
  have hsign : ∀ T : Finset (Fin (r + 1)), ∃ w : W, SpRealizes (r + 1) w 1 (spSgnOn T) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, spRealizes_one.congr rfl (by funext c; simp [spSgnOn])⟩
    | insert a T ha ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨ε a * w, ((hε a).mul hw).congr (mul_one 1) ?_⟩
      funext c
      simp only [Equiv.Perm.one_apply]
      unfold spSgnOn spSgn
      by_cases hca : c = a
      · subst hca
        simp [ha]
      · by_cases hcT : c ∈ T <;> simp [hca, hcT]
  have hpair : ∀ q : Equiv.Perm (Fin (r + 1)) × Finset (Fin (r + 1)),
      ∃ w : W, SpRealizes (r + 1) w q.1 (spSgnOn q.2) := by
    rintro ⟨σ, T⟩
    obtain ⟨w₁, h₁⟩ := hperm σ
    obtain ⟨w₂, h₂⟩ := hsign T
    exact ⟨w₁ * w₂, (h₁.mul h₂).congr (mul_one σ) (by funext c; simp)⟩
  choose F hF using hpair
  have hF_inj : Function.Injective F := by
    intro q q' hqq
    have h1 : SpRealizes (r + 1) (F q) q'.1 (spSgnOn q'.2) := by
      rw [hqq]
      exact hF q'
    obtain ⟨hπ, hs⟩ := SpRealizes.unique (spIsSign_spSgnOn q.2) (spIsSign_spSgnOn q'.2)
      (hF q) h1
    refine Prod.ext hπ ?_
    apply Finset.ext
    intro a
    have ha := congrFun hs a
    unfold spSgnOn at ha
    by_cases h2 : a ∈ q.2
    · by_cases h2' : a ∈ q'.2
      · simp [h2, h2']
      · exfalso
        rw [if_pos h2, if_neg h2'] at ha
        norm_num at ha
    · by_cases h2' : a ∈ q'.2
      · exfalso
        rw [if_neg h2, if_pos h2'] at ha
        norm_num at ha
      · simp [h2, h2']
  have hcard : Nat.card (Equiv.Perm (Fin (r + 1)) × Finset (Fin (r + 1))) =
      2 ^ (r + 1) * (r + 1).factorial := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin, Fintype.card_finset, Fintype.card_fin]
    ring
  exact hcard ▸ Nat.card_le_card_of_injective F hF_inj

end CFSG.StandardType.SpFrame

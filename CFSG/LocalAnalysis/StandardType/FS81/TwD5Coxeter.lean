module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Mat
public import CFSG.LocalAnalysis.StandardType.FS81.MonoRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

variable {k : ℕ}

@[expose] def glOfInvolutive (M : Matrix (Fin k) (Fin k) (ZMod 3)) (hM : M * M = 1) :
    GL (Fin k) (ZMod 3) :=
  ⟨M, M, hM, hM⟩

def swapUnit (a b : Fin 6) : GL (Fin 6) (ZMod 3) :=
  glOfInvolutive (spMat (Equiv.swap a b) (fun _ => 1))
    (spMat_mul_self _ _ (Equiv.swap_mul_self a b) (by intro j; simp))

def signChangeUnit : GL (Fin 6) (ZMod 3) :=
  glOfInvolutive (swapRefl 4 5 (-1))
    (spMat_mul_self _ _ (Equiv.swap_mul_self 4 5) (by
      intro j
      fin_cases j <;> decide))

theorem rE6_mul_self_of_ne_zero {ε : ZMod 3} (hε : ε ≠ 0) : rE6 ε * rE6 ε = 1 := by
  have hcases : ∀ ε : ZMod 3, ε ≠ 0 → ε = 1 ∨ ε = -1 := by decide
  rcases hcases ε hε with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> decide

@[expose] def rE6Unit (ε : ZMod 3) (hε : ε ≠ 0) : GL (Fin 6) (ZMod 3) :=
  glOfInvolutive (rE6 ε) (rE6_mul_self_of_ne_zero hε)

theorem coe_rE6Unit (ε : ZMod 3) (hε : ε ≠ 0) :
    ((rE6Unit ε hε : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = rE6 ε :=
  rfl

def wE6Gen (ε : ZMod 3) : Fin 6 → GL (Fin 6) (ZMod 3) :=
  if ε = 1 then
    ![
      swapUnit 1 2,
      swapUnit 4 5,
      swapUnit 2 3,
      swapUnit 3 4,
      signChangeUnit,
      rE6Unit 1 (by decide)
    ]
  else if ε = -1 then
    ![
      swapUnit 1 2,
      signChangeUnit,
      swapUnit 2 3,
      swapUnit 3 4,
      swapUnit 4 5,
      rE6Unit (-1) (by decide)
    ]
  else fun _ => 1


theorem signChange_mem_evenFix0 : swapRefl 4 5 (-1) ∈ evenFix0 5 := by
  refine ⟨Equiv.swap 4 5, fun l => if l = 4 ∨ l = 5 then -1 else 1, ?_, ?_, rfl⟩
  · intro l
    fin_cases l <;> decide
  · refine ⟨?_, ?_, ?_⟩
    · exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    · simp
    · decide

theorem wE6Gen_mem (ε : ZMod 3) (i : Fin 6) : wE6Gen ε i ∈ wE6 ε := by
  by_cases h1 : ε = 1
  · subst h1
    simp only [wE6Gen]
    fin_cases i
    · exact Subgroup.subset_closure
        (Or.inl (perm_mem_evenFix0 (n := 5) (Equiv.swap 1 2) (by decide)))
    · exact Subgroup.subset_closure
        (Or.inl (perm_mem_evenFix0 (n := 5) (Equiv.swap 4 5) (by decide)))
    · exact Subgroup.subset_closure
        (Or.inl (perm_mem_evenFix0 (n := 5) (Equiv.swap 2 3) (by decide)))
    · exact Subgroup.subset_closure
        (Or.inl (perm_mem_evenFix0 (n := 5) (Equiv.swap 3 4) (by decide)))
    · exact Subgroup.subset_closure (Or.inl signChange_mem_evenFix0)
    · exact Subgroup.subset_closure (Or.inr rfl)
  · by_cases h2 : ε = -1
    · subst h2
      simp only [wE6Gen]
      fin_cases i
      · exact Subgroup.subset_closure
          (Or.inl (perm_mem_evenFix0 (n := 5) (Equiv.swap 1 2) (by decide)))
      · exact Subgroup.subset_closure (Or.inl signChange_mem_evenFix0)
      · exact Subgroup.subset_closure
          (Or.inl (perm_mem_evenFix0 (n := 5) (Equiv.swap 2 3) (by decide)))
      · exact Subgroup.subset_closure
          (Or.inl (perm_mem_evenFix0 (n := 5) (Equiv.swap 3 4) (by decide)))
      · exact Subgroup.subset_closure
          (Or.inl (perm_mem_evenFix0 (n := 5) (Equiv.swap 4 5) (by decide)))
      · exact Subgroup.subset_closure (Or.inr rfl)
    · simp only [wE6Gen, if_neg h1, if_neg h2]
      exact Subgroup.one_mem _



theorem isLiftable_wE6Gen {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) :
    CoxeterMatrix.E₆.IsLiftable (wE6Gen ε) := by
  rcases hε with rfl | rfl
  · intro i i'
    fin_cases i <;> fin_cases i' <;> decide +kernel
  · intro i i'
    fin_cases i <;> fin_cases i' <;> decide +kernel



def spMatPermUnit (σ : Equiv.Perm (Fin k)) : GL (Fin k) (ZMod 3) :=
  ⟨spMat σ (fun _ => 1), spMat σ⁻¹ (fun _ => 1), by
      rw [spMat_mul, mul_inv_cancel σ]
      simp [spMat_one], by
      rw [spMat_mul, inv_mul_cancel σ]
      simp [spMat_one]⟩

def spMatPermUnitHom : Equiv.Perm (Fin k) →* GL (Fin k) (ZMod 3) where
  toFun := spMatPermUnit
  map_one' := by
    refine Units.ext ?_
    simp [spMatPermUnit, spMat_one]
  map_mul' σ τ := by
    refine Units.ext ?_
    simp [spMatPermUnit, spMat_mul]

def succPerm (e : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k+1)) :=
  Equiv.Perm.decomposeFin.symm (0, e)

theorem succPerm_mul (e₁ e₂ : Equiv.Perm (Fin k)) :
    succPerm (e₁ * e₂) = succPerm e₁ * succPerm e₂ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [succPerm]
  · simp [succPerm, Equiv.Perm.mul_apply]

theorem succPerm_one : succPerm (1 : Equiv.Perm (Fin k)) = 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [succPerm]

def succPermHom : Equiv.Perm (Fin k) →* Equiv.Perm (Fin (k+1)) where
  toFun := succPerm
  map_one' := succPerm_one
  map_mul' := succPerm_mul

theorem eq_succPerm_of_apply_zero {σ : Equiv.Perm (Fin (k+1))} (hσ : σ 0 = 0) :
    ∃ e : Equiv.Perm (Fin k), σ = succPerm e := by
  refine ⟨(Equiv.Perm.decomposeFin σ).2, ?_⟩
  have hfst : (Equiv.Perm.decomposeFin σ).1 = 0 := by
    have h := Equiv.Perm.decomposeFin_symm_apply_zero (Equiv.Perm.decomposeFin σ).1
      (Equiv.Perm.decomposeFin σ).2
    simp only [Prod.mk.eta, Equiv.symm_apply_apply] at h
    exact h.symm.trans hσ
  conv_lhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply σ]
  change Equiv.Perm.decomposeFin.symm ((Equiv.Perm.decomposeFin σ).1,
    (Equiv.Perm.decomposeFin σ).2) = succPerm (Equiv.Perm.decomposeFin σ).2
  rw [hfst]
  rfl

theorem succPerm_swap_castSucc (i : Fin 4) :
    succPerm (Equiv.swap i.castSucc i.succ) =
      Equiv.swap (Fin.succ i.castSucc) (Fin.succ i.succ) := by
  ext j
  fin_cases i <;> fin_cases j <;> decide

theorem spMatPermUnit_swap (a b : Fin 6) :
    spMatPermUnit (Equiv.swap a b) = swapUnit a b :=
  Units.ext rfl

theorem spMatPermUnit_succPerm_swap_castSucc (i : Fin 4) :
    spMatPermUnit (succPerm (Equiv.swap i.castSucc i.succ)) =
      swapUnit (Fin.succ i.castSucc) (Fin.succ i.succ) := by
  rw [succPerm_swap_castSucc i, spMatPermUnit_swap]

theorem mem_closure_wE6Gen {ε : ZMod 3} (i : Fin 6) :
    wE6Gen ε i ∈ Subgroup.closure (Set.range (wE6Gen ε)) :=
  Subgroup.subset_closure (Set.mem_range_self i)

theorem swapUnit_mem_adjacent {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) :
    swapUnit (1 : Fin 6) 2 ∈ Subgroup.closure (Set.range (wE6Gen ε)) ∧
      swapUnit 2 3 ∈ Subgroup.closure (Set.range (wE6Gen ε)) ∧
      swapUnit 3 4 ∈ Subgroup.closure (Set.range (wE6Gen ε)) ∧
      swapUnit 4 5 ∈ Subgroup.closure (Set.range (wE6Gen ε)) := by
  rcases hε with rfl | rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have h : wE6Gen (1 : ZMod 3) 0 = swapUnit 1 2 := by decide
      rw [← h]
      exact mem_closure_wE6Gen 0
    · have h : wE6Gen (1 : ZMod 3) 2 = swapUnit 2 3 := by decide
      rw [← h]
      exact mem_closure_wE6Gen 2
    · have h : wE6Gen (1 : ZMod 3) 3 = swapUnit 3 4 := by decide
      rw [← h]
      exact mem_closure_wE6Gen 3
    · have h : wE6Gen (1 : ZMod 3) 1 = swapUnit 4 5 := by decide
      rw [← h]
      exact mem_closure_wE6Gen 1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have h : wE6Gen (-1 : ZMod 3) 0 = swapUnit 1 2 := by decide
      rw [← h]
      exact mem_closure_wE6Gen 0
    · have h : wE6Gen (-1 : ZMod 3) 2 = swapUnit 2 3 := by decide
      rw [← h]
      exact mem_closure_wE6Gen 2
    · have h : wE6Gen (-1 : ZMod 3) 3 = swapUnit 3 4 := by decide
      rw [← h]
      exact mem_closure_wE6Gen 3
    · have h : wE6Gen (-1 : ZMod 3) 4 = swapUnit 4 5 := by decide
      rw [← h]
      exact mem_closure_wE6Gen 4

theorem swapUnit_succ_mem {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) (i : Fin 4) :
    swapUnit (Fin.succ i.castSucc) (Fin.succ i.succ) ∈
      Subgroup.closure (Set.range (wE6Gen ε)) := by
  have h := swapUnit_mem_adjacent hε
  fin_cases i
  · simpa using h.1
  · simpa using h.2.1
  · simpa using h.2.2.1
  · simpa using h.2.2.2

theorem signChangeUnit_mem {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) :
    signChangeUnit ∈ Subgroup.closure (Set.range (wE6Gen ε)) := by
  rcases hε with rfl | rfl
  · have h : wE6Gen (1 : ZMod 3) 4 = signChangeUnit := by decide
    rw [← h]
    exact mem_closure_wE6Gen 4
  · have h : wE6Gen (-1 : ZMod 3) 1 = signChangeUnit := by decide
    rw [← h]
    exact mem_closure_wE6Gen 1

theorem rE6Unit_mem {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) (hε0 : ε ≠ 0) :
    rE6Unit ε hε0 ∈ Subgroup.closure (Set.range (wE6Gen ε)) := by
  have h5 : rE6Unit ε hε0 = wE6Gen ε 5 := by
    rcases hε with rfl | rfl <;> exact Units.ext (by rw [coe_rE6Unit]; decide)
  rw [h5]
  exact mem_closure_wE6Gen 5

theorem spMatPermUnit_mem_of_apply_zero {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    {σ : Equiv.Perm (Fin 6)} (hσ : σ 0 = 0) :
    spMatPermUnit σ ∈ Subgroup.closure (Set.range (wE6Gen ε)) := by
  obtain ⟨e, rfl⟩ := eq_succPerm_of_apply_zero (k := 5) hσ
  have hgen : Subgroup.closure (Set.range fun i : Fin 4 =>
      Equiv.swap i.castSucc i.succ) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 4)
  have hle : Subgroup.closure (Set.range fun i : Fin 4 =>
      Equiv.swap i.castSucc i.succ) ≤
      Subgroup.comap ((spMatPermUnitHom (k := 6)).comp (succPermHom (k := 5)))
        (Subgroup.closure (Set.range (wE6Gen ε))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    change spMatPermUnit (succPerm (Equiv.swap i.castSucc i.succ)) ∈
      Subgroup.closure (Set.range (wE6Gen ε))
    rw [spMatPermUnit_succPerm_swap_castSucc i]
    exact swapUnit_succ_mem hε i
  have he : e ∈ Subgroup.closure (Set.range fun i : Fin 4 =>
      Equiv.swap i.castSucc i.succ) := by
    rw [hgen]
    exact Subgroup.mem_top e
  exact hle he

def spMatSignUnit (s : Fin k → ZMod 3) (hs : IsSign s) : GL (Fin k) (ZMod 3) :=
  ⟨spMat 1 s, spMat 1 s, spMat_one_mul_self hs, spMat_one_mul_self hs⟩

def diagPairUnit (a b : Fin k) : GL (Fin k) (ZMod 3) :=
  spMatSignUnit (fun i => if i = a ∨ i = b then -1 else 1)
    (by
      intro i
      simp only
      split_ifs with h
      · exact Or.inr rfl
      · exact Or.inl rfl)

def evenSignProd (s : Fin 6 → ZMod 3) : GL (Fin 6) (ZMod 3) :=
  (if s 1 = -1 then diagPairUnit 1 2 else 1) *
    (if s 1 * s 2 = -1 then diagPairUnit 2 3 else 1) *
    (if s 1 * s 2 * s 3 = -1 then diagPairUnit 3 4 else 1) *
    (if s 5 = -1 then diagPairUnit 4 5 else 1)

theorem diagPairUnit_four_five_mem {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) :
    diagPairUnit (4 : Fin 6) 5 ∈ Subgroup.closure (Set.range (wE6Gen ε)) := by
  have h45 : diagPairUnit (4 : Fin 6) 5 = swapUnit 4 5 * signChangeUnit := by decide
  rw [h45]
  exact Subgroup.mul_mem _ (swapUnit_mem_adjacent hε).2.2.2 (signChangeUnit_mem hε)

theorem diagPairUnit_adjacent_mem {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) :
    diagPairUnit (1 : Fin 6) 2 ∈ Subgroup.closure (Set.range (wE6Gen ε)) ∧
      diagPairUnit 2 3 ∈ Subgroup.closure (Set.range (wE6Gen ε)) ∧
      diagPairUnit 3 4 ∈ Subgroup.closure (Set.range (wE6Gen ε)) ∧
      diagPairUnit 4 5 ∈ Subgroup.closure (Set.range (wE6Gen ε)) := by
  have h45 := diagPairUnit_four_five_mem hε
  refine ⟨?_, ?_, ?_, h45⟩
  · have hc : spMatPermUnit (Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5) * diagPairUnit 4 5 *
        (spMatPermUnit (Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5))⁻¹ = diagPairUnit 1 2 := by
      decide
    rw [← hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (spMatPermUnit_mem_of_apply_zero hε (by decide)) h45)
      (Subgroup.inv_mem _ (spMatPermUnit_mem_of_apply_zero hε (by decide)))
  · have hc : spMatPermUnit (Equiv.swap (2 : Fin 6) 4 * Equiv.swap 3 5) * diagPairUnit 4 5 *
        (spMatPermUnit (Equiv.swap (2 : Fin 6) 4 * Equiv.swap 3 5))⁻¹ = diagPairUnit 2 3 := by
      decide
    rw [← hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (spMatPermUnit_mem_of_apply_zero hε (by decide)) h45)
      (Subgroup.inv_mem _ (spMatPermUnit_mem_of_apply_zero hε (by decide)))
  · have hc : spMatPermUnit (Equiv.swap (3 : Fin 6) 5) * diagPairUnit 4 5 *
        (spMatPermUnit (Equiv.swap 3 5))⁻¹ = diagPairUnit 3 4 := by decide
    rw [← hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (spMatPermUnit_mem_of_apply_zero hε (by decide)) h45)
      (Subgroup.inv_mem _ (spMatPermUnit_mem_of_apply_zero hε (by decide)))

theorem spMatSignUnit_eq_evenSignProd {s : Fin 6 → ZMod 3} (hs : IsSign s) (h0 : s 0 = 1)
    (hprod : ∏ i : Fin 5, s i.succ = 1) :
    spMatSignUnit s hs = evenSignProd s := by
  have hp : s 1 * s 2 * s 3 * s 4 * s 5 = 1 := by
    simpa [Fin.prod_univ_five] using hprod
  refine Units.ext ?_
  change spMat (1 : Equiv.Perm (Fin 6)) s = (evenSignProd s).val
  have hvec : s = ![s 0, s 1, s 2, s 3, s 4, s 5] := by
    funext j
    fin_cases j <;> rfl
  rw [hvec]
  rcases hs 1 with h1 | h1 <;> rcases hs 2 with h2 | h2 <;>
    rcases hs 3 with h3 | h3 <;> rcases hs 4 with h4 | h4 <;>
    rcases hs 5 with h5 | h5 <;>
    simp only [h0, h1, h2, h3, h4, h5] at hp ⊢
  all_goals
    first
      | decide
      | exact absurd hp (by decide)

theorem spMatSignUnit_mem {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) {s : Fin 6 → ZMod 3}
    (hs : IsSign s) (h0 : s 0 = 1) (hprod : ∏ i : Fin 5, s i.succ = 1) :
    spMatSignUnit s hs ∈ Subgroup.closure (Set.range (wE6Gen ε)) := by
  have hd := diagPairUnit_adjacent_mem hε
  rw [spMatSignUnit_eq_evenSignProd hs h0 hprod]
  simp only [evenSignProd]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · split_ifs with h1
    · exact hd.1
    · exact Subgroup.one_mem _
  · split_ifs with h1
    · exact hd.2.1
    · exact Subgroup.one_mem _
  · split_ifs with h1
    · exact hd.2.2.1
    · exact Subgroup.one_mem _
  · split_ifs with h1
    · exact hd.2.2.2
    · exact Subgroup.one_mem _

theorem spMat_mem_of_evenFix0 {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    {A : GL (Fin 6) (ZMod 3)}
    (hA : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ evenFix0 5) :
    A ∈ Subgroup.closure (Set.range (wE6Gen ε)) := by
  simp only [evenFix0, spSet] at hA
  obtain ⟨σ, s, hs, ⟨hσ, hs0, hprod⟩, hAeq⟩ := hA
  have hperm : spMatPermUnit σ ∈ Subgroup.closure (Set.range (wE6Gen ε)) :=
    spMatPermUnit_mem_of_apply_zero hε hσ
  have hdiag : spMatSignUnit s hs ∈ Subgroup.closure (Set.range (wE6Gen ε)) :=
    spMatSignUnit_mem hε hs hs0 hprod
  have hA' : A = spMatPermUnit σ * spMatSignUnit s hs := by
    refine Units.ext ?_
    rw [Units.val_mul, hAeq]
    rw [show (spMatPermUnit σ).val = spMat σ (fun _ => 1) from rfl,
      show (spMatSignUnit s hs).val = spMat 1 s from rfl, spMat_mul]
    simp
  rw [hA']
  exact Subgroup.mul_mem _ hperm hdiag

theorem closure_range_wE6Gen {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) :
    Subgroup.closure (Set.range (wE6Gen ε)) = wE6 ε := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact wE6Gen_mem ε i
  · simp only [wE6]
    rw [Subgroup.closure_le]
    rintro A (hA | hA)
    · exact spMat_mem_of_evenFix0 hε hA
    · have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> decide
      have hAu : A = rE6Unit ε hε0 := Units.ext hA
      rw [hAu]
      exact rE6Unit_mem hε hε0

theorem card_wE6_dvd
    {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) : Nat.card (wE6 ε) ∣ 51840 := by
  let φ : (CoxeterMatrix.E₆).Group →* GL (Fin 6) (ZMod 3) :=
    (CoxeterMatrix.E₆).toCoxeterSystem.lift ⟨wE6Gen ε, isLiftable_wE6Gen hε⟩
  have hrange : φ.range = wE6 ε := by
    calc φ.range
        = (⊤ : Subgroup (CoxeterMatrix.E₆).Group).map φ :=
            MonoidHom.range_eq_map φ
      _ = (Subgroup.closure (Set.range
            (CoxeterMatrix.E₆).toCoxeterSystem.simple)).map φ := by
            rw [(CoxeterMatrix.E₆).toCoxeterSystem.subgroup_closure_range_simple]
      _ = Subgroup.closure (φ '' Set.range
            (CoxeterMatrix.E₆).toCoxeterSystem.simple) := MonoidHom.map_closure φ _
      _ = Subgroup.closure (Set.range (wE6Gen ε)) := by
            rw [← Set.range_comp]
            have hfun : φ ∘ (CoxeterMatrix.E₆).toCoxeterSystem.simple = wE6Gen ε := by
              funext i
              change (CoxeterMatrix.E₆).toCoxeterSystem.lift
                ⟨wE6Gen ε, isLiftable_wE6Gen hε⟩
                ((CoxeterMatrix.E₆).toCoxeterSystem.simple i) = wE6Gen ε i
              exact (CoxeterMatrix.E₆).toCoxeterSystem.lift_apply_simple
                (isLiftable_wE6Gen hε) i
            rw [hfun]
      _ = wE6 ε := closure_range_wE6Gen hε
  have hdvd := Subgroup.card_range_dvd φ
  rw [hrange, card_coxeterE6_group] at hdvd
  exact hdvd

end CFSG.StandardType.FrameRoute.FS81

end

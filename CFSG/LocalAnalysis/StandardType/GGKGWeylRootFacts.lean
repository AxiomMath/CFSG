module

public import CFSG.LocalAnalysis.StandardType.GGKGAdjDefs
public import CFSG.LocalAnalysis.StandardType.GGKGOrthPairs

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.TableBExc.E6Three
  CFSG.SeitzReduction CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.NoOffRest

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def rootPair (γ : Fin Tag.E6.rank → ℤ) (x : Fin Tag.E6.rank → ZMod 3) : ZMod 3 :=
  ∑ j, ((γ j : ℤ) : ZMod 3) * x j

@[expose] def rootRefl (γ : Fin Tag.E6.rank → ℤ) (x : Fin Tag.E6.rank → ZMod 3) :
    Fin Tag.E6.rank → ZMod 3 :=
  x - rootPair γ x • kgExpVec γ

section Finite

private theorem kgExpVec_injective_finite :
    ∀ m₁ m₂ : Fin 72, kgExpVec (CFSG.RankThree.E6.e6RootVec m₁) =
      kgExpVec (CFSG.RankThree.E6.e6RootVec m₂) → m₁ = m₂ := by
  decide +kernel

private theorem rootPair_ne_zero_finite :
    ∀ m : Fin 72, ∃ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 ∧
      rootPair (CFSG.RankThree.E6.e6RootVec m) x ≠ 0 := by
  decide +kernel

private theorem card_fix_rootRefl_finite : ∀ m : Fin 72,
    (Finset.univ.filter fun x : Fin Tag.E6.rank → ZMod 3 =>
      kDotP 3 x = 0 ∧ rootRefl (CFSG.RankThree.E6.e6RootVec m) x = x).card = 81 := by
  decide +kernel

private theorem iform_eq_zero_or_noncommute_finite : ∀ m₁ m₂ : Fin 72,
    iform (CFSG.RankThree.E6.e6RootVec m₁) (CFSG.RankThree.E6.e6RootVec m₂) = 0 ∨
    kgExpVec (CFSG.RankThree.E6.e6RootVec m₁) = kgExpVec (CFSG.RankThree.E6.e6RootVec m₂) ∨
    kgExpVec (CFSG.RankThree.E6.e6RootVec m₁) = -kgExpVec (CFSG.RankThree.E6.e6RootVec m₂) ∨
    ∃ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 ∧
      rootRefl (CFSG.RankThree.E6.e6RootVec m₁) (rootRefl (CFSG.RankThree.E6.e6RootVec m₂) x) ≠
        rootRefl (CFSG.RankThree.E6.e6RootVec m₂) (rootRefl (CFSG.RankThree.E6.e6RootVec m₁) x) := by
  decide +kernel

private theorem stdSpan : ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
    rootPair (highRoot Tag.E6) x = 0 → rootPair (Pi.single 5 1) x = 0 →
    ∃ c₀ c₂ c₃ : ZMod 3, x = c₀ • kgExpVec (Pi.single 0 1) + c₂ • kgExpVec (Pi.single 2 1) +
      c₃ • kgExpVec (Pi.single 3 1) := by
  decide +kernel

private theorem stdOrth : ∀ i : Fin Tag.E6.rank, i = 0 ∨ i = 2 ∨ i = 3 →
    iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (highRoot Tag.E6) = 0 ∧
    iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = 0 := by
  decide +kernel

end Finite

section Facts

private theorem rootPair_zero (γ : Fin Tag.E6.rank → ℤ) :
    rootPair γ (0 : Fin Tag.E6.rank → ZMod 3) = 0 := by
  simp [rootPair]

private theorem iform_E6_self_eq_two {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj]
  simp [Tag.symmetrizer, Matrix.one_apply_eq]

private theorem iform_E6_single_right (x : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    iform x (Pi.single i 1) = (Tag.E6.cartan.mulVec x) i := by
  rw [iform_single_right]
  simp only [Tag.symmetrizer, Matrix.one_apply_eq, one_mul]
  simp [Matrix.mulVec, dotProduct]

private theorem kgExpVec_eq_cast_iform (x : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    kgExpVec x i = ((iform x (Pi.single i 1) : ℤ) : ZMod 3) := by
  simp only [kgExpVec]
  rw [← iform_E6_single_right x i]

private theorem corootPair_E6_single_eq_kgExpVec {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (i : Fin Tag.E6.rank) :
    ((corootPair γ (Pi.single i 1) : ℤ) : ZMod 3) = kgExpVec γ i := by
  have hmul := corootPair_mul hγ (Pi.single i 1)
  rw [iform_E6_self_eq_two hγ] at hmul
  have hc : corootPair γ (Pi.single i 1) = iform γ (Pi.single i 1) := by
    have h2 : corootPair γ (Pi.single i 1) * 2 = iform γ (Pi.single i 1) * 2 := by
      rw [hmul]; ring
    exact mul_right_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2
  rw [hc, kgExpVec_eq_cast_iform γ i]

private theorem rootPair_sub (γ : Fin Tag.E6.rank → ℤ) (x y : Fin Tag.E6.rank → ZMod 3) :
    rootPair γ (x - y) = rootPair γ x - rootPair γ y := by
  simp only [rootPair, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem rootPair_smul (γ : Fin Tag.E6.rank → ℤ) (c : ZMod 3)
    (v : Fin Tag.E6.rank → ZMod 3) :
    rootPair γ (c • v) = c * rootPair γ v := by
  simp only [rootPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem adAct_rootReflection_eq_rootRefl {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (y : Fin Tag.E6.rank → ZMod 3) :
    adAct Tag.E6 3 (rootReflection γ) y = rootRefl γ y := by
  rw [rootRefl, rootPair]
  funext i
  rw [adAct, rootReflection_inv hγ, rootReflection_smul hγ (Pi.single i 1)]
  have hsplit : (∑ j, ((((Pi.single i 1 : Fin Tag.E6.rank → ℤ) -
          corootPair γ (Pi.single i 1) • γ) j : ℤ) : ZMod 3) * y j) =
      (∑ j, (((Pi.single i 1 : Fin Tag.E6.rank → ℤ) j : ℤ) : ZMod 3) * y j) -
        (∑ j, (((corootPair γ (Pi.single i 1) • γ) j : ℤ) : ZMod 3) * y j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.sub_apply, Int.cast_sub, sub_mul]
  have hfirst : (∑ j, (((Pi.single i 1 : Fin Tag.E6.rank → ℤ) j : ℤ) : ZMod 3) * y j) = y i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_apply, hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hsecond : (∑ j, (((corootPair γ (Pi.single i 1) • γ) j : ℤ) : ZMod 3) * y j) =
      ((corootPair γ (Pi.single i 1) : ℤ) : ZMod 3) *
        (∑ j, ((γ j : ℤ) : ZMod 3) * y j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    ring
  rw [hsplit, hfirst, hsecond, corootPair_E6_single_eq_kgExpVec hγ i]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem rootPair_kgExpVec (γ δ : Fin Tag.E6.rank → ℤ) :
    rootPair γ (kgExpVec δ) = ((iform γ δ : ℤ) : ZMod 3) := by
  rw [rootPair, iform_E6_eq γ δ]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [kgExpVec]

theorem kgExpVec_neg (β : Fin Tag.E6.rank → ℤ) : kgExpVec (-β) = -kgExpVec β := by
  funext i
  simp [kgExpVec, Matrix.mulVec_neg]

theorem rootPair_neg_left (γ : Fin Tag.E6.rank → ℤ) (x : Fin Tag.E6.rank → ZMod 3) :
    rootPair (-γ) x = -rootPair γ x := by
  simp [rootPair, Finset.sum_neg_distrib]

theorem rootRefl_neg (γ : Fin Tag.E6.rank → ℤ) (x : Fin Tag.E6.rank → ZMod 3) :
    rootRefl (-γ) x = rootRefl γ x := by
  simp only [rootRefl, rootPair_neg_left, kgExpVec_neg, neg_smul, smul_neg, neg_neg]

theorem kgExpVec_ne_zero {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) : kgExpVec γ ≠ 0 := by
  intro h0
  have hzero : rootPair γ (kgExpVec γ) = 0 := by rw [h0, rootPair_zero]
  rw [rootPair_kgExpVec, iform_E6_self_eq_two hγ] at hzero
  exact (by decide +kernel : ¬(((2 : ℤ) : ZMod 3) = 0)) hzero

theorem rootRefl_rootRefl {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (x : Fin Tag.E6.rank → ZMod 3) : rootRefl γ (rootRefl γ x) = x := by
  have hp : rootPair γ (rootRefl γ x) = -rootPair γ x := by
    rw [rootRefl, rootPair_sub, rootPair_smul, rootPair_kgExpVec, iform_E6_self_eq_two hγ]
    ring
  calc rootRefl γ (rootRefl γ x)
      = rootRefl γ x - rootPair γ (rootRefl γ x) • kgExpVec γ := rfl
    _ = rootRefl γ x - (-rootPair γ x) • kgExpVec γ := by rw [hp]
    _ = x := by
      rw [rootRefl, neg_smul, sub_neg_eq_add]
      abel

theorem rootRefl_mem_hypE6 {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ hypE6) : rootRefl γ x ∈ hypE6 := by
  rw [← adAct_rootReflection_eq_rootRefl hγ x]
  exact adAct_mem_hypE6 (rootReflection γ) hx

theorem rootPair_eq_zero_of_rootRefl_eq {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    {x : Fin Tag.E6.rank → ZMod 3} (h : rootRefl γ x = x) : rootPair γ x = 0 := by
  by_contra hp
  have h0 : rootPair γ x • kgExpVec γ = 0 := by
    rw [rootRefl] at h
    exact sub_eq_self.mp h
  have hkg : kgExpVec γ = 0 := by
    funext i
    have hi := congrFun h0 i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left hp
  exact kgExpVec_ne_zero hγ hkg

theorem exists_rootPair_ne_zero {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ∃ x ∈ hypE6, rootPair γ x ≠ 0 := by
  obtain ⟨m, rfl⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.mp hγ
  obtain ⟨x, hx, hpx⟩ := rootPair_ne_zero_finite m
  exact ⟨x, mem_hypE6.mpr hx, hpx⟩

theorem card_fix_rootRefl {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ rootRefl γ x = x} = 3 ^ 4 := by
  obtain ⟨m, rfl⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.mp hγ
  rw [Nat.subtype_card (Finset.univ.filter fun x : Fin Tag.E6.rank → ZMod 3 =>
    kDotP 3 x = 0 ∧ rootRefl (CFSG.RankThree.E6.e6RootVec m) x = x) (by
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_hypE6])]
  rw [card_fix_rootRefl_finite m]
  norm_num

theorem kgExpVec_injective_of_isRoot {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (h : kgExpVec α = kgExpVec β) : α = β := by
  obtain ⟨m₁, rfl⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.mp hα
  obtain ⟨m₂, rfl⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.mp hβ
  exact congrArg CFSG.RankThree.E6.e6RootVec (kgExpVec_injective_finite m₁ m₂ h)

theorem iform_eq_zero_of_commute {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (h1 : kgExpVec α ≠ kgExpVec β) (h2 : kgExpVec α ≠ -kgExpVec β)
    (hcomm : ∀ x ∈ hypE6, rootRefl α (rootRefl β x) = rootRefl β (rootRefl α x)) :
    iform α β = 0 := by
  obtain ⟨m₁, rfl⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.mp hα
  obtain ⟨m₂, rfl⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.mp hβ
  rcases iform_eq_zero_or_noncommute_finite m₁ m₂ with h0 | h | h | ⟨x, hx, hxne⟩
  · exact h0
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd (hcomm x (mem_hypE6.mpr hx)) hxne

private theorem kGL_adAct_smul (w : WeylGroup Tag.E6) (c : ZMod 3)
    (x : Fin Tag.E6.rank → ZMod 3) : adAct Tag.E6 3 w (c • x) = c • adAct Tag.E6 3 w x := by
  funext i
  simp only [adAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem kGL_rootPair_adAct (γ : Fin Tag.E6.rank → ℤ) (w : WeylGroup Tag.E6)
    (y : Fin Tag.E6.rank → ZMod 3) :
    rootPair γ (adAct Tag.E6 3 w y) = rootPair (w⁻¹ • γ) y := by
  simp only [rootPair, adAct]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weyl_smul_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem kGL_adAct_kgExpVec (w : WeylGroup Tag.E6) (δ : Fin Tag.E6.rank → ℤ) :
    adAct Tag.E6 3 w (kgExpVec δ) = kgExpVec (w • δ) := by
  funext i
  change rootPair (w⁻¹ • Pi.single i 1) (kgExpVec δ) = kgExpVec (w • δ) i
  rw [rootPair_kgExpVec, kgExpVec_eq_cast_iform]
  congr 1
  rw [show iform (w • δ) (Pi.single i 1) = iform (Pi.single i 1) (w • δ) from iform_comm _ _,
    ← iform_smul w (w⁻¹ • Pi.single i 1) δ, smul_inv_smul]

private theorem kGL_adAct_stdSpan (w : WeylGroup Tag.E6) (c₀ c₂ c₃ : ZMod 3) :
    adAct Tag.E6 3 w (c₀ • kgExpVec (Pi.single 0 1) + c₂ • kgExpVec (Pi.single 2 1) +
        c₃ • kgExpVec (Pi.single 3 1)) =
      c₀ • kgExpVec (w • Pi.single 0 1) + c₂ • kgExpVec (w • Pi.single 2 1) +
        c₃ • kgExpVec (w • Pi.single 3 1) := by
  rw [adAct_add, adAct_add, kGL_adAct_smul, kGL_adAct_smul, kGL_adAct_smul,
    kGL_adAct_kgExpVec, kGL_adAct_kgExpVec, kGL_adAct_kgExpVec]

private theorem kGL_closure_smul_mem (S : Set (Fin Tag.E6.rank → ZMod 3)) (c : ZMod 3)
    {v : Fin Tag.E6.rank → ZMod 3} (hv : v ∈ AddSubgroup.closure S) :
    c • v ∈ AddSubgroup.closure S := by
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem _ hv c.val

theorem mem_closure_of_rootPair_eq_zero {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (hαβ : iform α β = 0) {x : Fin Tag.E6.rank → ZMod 3}
    (hx : x ∈ hypE6) (h1 : rootPair α x = 0) (h2 : rootPair β x = 0) :
    x ∈ AddSubgroup.closure {y : Fin Tag.E6.rank → ZMod 3 |
      ∃ γ, IsRoot Tag.E6 γ ∧ iform γ α = 0 ∧ iform γ β = 0 ∧ y = kgExpVec γ} := by
  obtain ⟨w, hwθ, hwβ⟩ := exists_weyl_smul_orthPair hα hβ hαβ
  have hx'hyp : adAct Tag.E6 3 w⁻¹ x ∈ hypE6 := adAct_mem_hypE6 w⁻¹ hx
  have h1' : rootPair (highRoot Tag.E6) (adAct Tag.E6 3 w⁻¹ x) = 0 := by
    rw [kGL_rootPair_adAct, inv_inv, hwθ, h1]
  have h2' : rootPair (Pi.single 5 1) (adAct Tag.E6 3 w⁻¹ x) = 0 := by
    rw [kGL_rootPair_adAct, inv_inv, hwβ, h2]
  obtain ⟨c₀, c₂, c₃, hspan⟩ :=
    stdSpan (adAct Tag.E6 3 w⁻¹ x) (mem_hypE6.mp hx'hyp) h1' h2'
  have hx_eq : x = adAct Tag.E6 3 w (adAct Tag.E6 3 w⁻¹ x) := by
    rw [← adAct_mul, mul_inv_cancel, adAct_one]
  have hS : ∀ i : Fin Tag.E6.rank, i = 0 ∨ i = 2 ∨ i = 3 →
      kgExpVec (w • Pi.single i 1) ∈ AddSubgroup.closure {y : Fin Tag.E6.rank → ZMod 3 |
        ∃ γ, IsRoot Tag.E6 γ ∧ iform γ α = 0 ∧ iform γ β = 0 ∧ y = kgExpVec γ} := by
    intro i hi
    refine AddSubgroup.subset_closure
      ⟨w • Pi.single i 1, IsRoot.smul (isRoot_single Tag.E6 i) w, ?_, ?_, rfl⟩
    · rw [← hwθ, iform_smul]
      exact (stdOrth i hi).1
    · rw [← hwβ, iform_smul]
      exact (stdOrth i hi).2
  rw [hx_eq, hspan, kGL_adAct_stdSpan]
  exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _
    (kGL_closure_smul_mem _ c₀ (hS 0 (Or.inl rfl)))
    (kGL_closure_smul_mem _ c₂ (hS 2 (Or.inr (Or.inl rfl)))))
    (kGL_closure_smul_mem _ c₃ (hS 3 (Or.inr (Or.inr rfl))))

end Facts

end CFSG.StandardType.KGL

end

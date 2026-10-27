module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Subgroup.Center
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusWeyl

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.WeakClosure81

private theorem pnd_coxeterMatrixD_eq (r : ℕ) :
    ggCoxeterMatrixD r = coxeterMatrix (isFiniteType_cartanD r) := by
  ext i j
  rw [ggCoxeterMatrixD_apply, ← cartanD_eq r]
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    simp [cartanD, TauCeti.coxeterOrder_four]
  · rw [if_neg hij]
    have hsymm : cartanD r j i = cartanD r i j := by
      rw [cartanD_eq]
      exact (CartanMatrix.D_isSymm r).apply i j
    rw [hsymm]
    have h01 : cartanD r i j = -1 ∨ cartanD r i j = 0 := by
      rw [cartanD_eq]
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    rcases h01 with h | h
    · rw [h]
      simp [TauCeti.coxeterOrder_one]
    · rw [h]
      simp [TauCeti.coxeterOrder_zero]

private theorem pnd_exists (n : ℕ) (hn : 2 ≤ n)
    (w : (coxeterMatrix (isFiniteType_cartanD n)).Group) :
    ∃ q : Equiv.Perm (Fin n) × (Fin n → ℤ),
      SpIsSign q.2 ∧ (∏ a, q.2 a = 1) ∧ OmRealizes n w q.1 q.2 := by
  obtain ⟨π, s, hs, hprod, h⟩ := exists_omRealizes hn w
  exact ⟨(π, s), hs, hprod, h⟩

private noncomputable def pnd_rep (n : ℕ)
    (w : (coxeterMatrix (isFiniteType_cartanD n)).Group) :
    Equiv.Perm (Fin n) × (Fin n → ℤ) :=
  if h : 2 ≤ n then Classical.choose (pnd_exists n h w) else (1, fun _ => 1)

private theorem pnd_rep_spec (n : ℕ) (hn : 2 ≤ n)
    (w : (coxeterMatrix (isFiniteType_cartanD n)).Group) :
    SpIsSign (pnd_rep n w).2 ∧ (∏ a, (pnd_rep n w).2 a = 1) ∧
      OmRealizes n w (pnd_rep n w).1 (pnd_rep n w).2 := by
  unfold pnd_rep
  rw [dif_pos hn]
  exact Classical.choose_spec (pnd_exists n hn w)

private theorem pnd_rep_mul (n : ℕ) (hn : 2 ≤ n)
    (w₁ w₂ : (coxeterMatrix (isFiniteType_cartanD n)).Group) :
    pnd_rep n (w₁ * w₂) =
      ((pnd_rep n w₁).1 * (pnd_rep n w₂).1,
        fun c => (pnd_rep n w₂).2 c * (pnd_rep n w₁).2 ((pnd_rep n w₂).1 c)) := by
  have h := OmRealizes.mul (pnd_rep_spec n hn w₁).2.2 (pnd_rep_spec n hn w₂).2.2
  obtain ⟨hπ, hs⟩ := omRealizes_unique hn (pnd_rep_spec n hn (w₁ * w₂)).2.2 h
    (pnd_rep_spec n hn (w₁ * w₂)).1
  exact Prod.ext hπ hs

private theorem pnd_rep_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (pnd_rep n) := by
  intro w w' h
  apply weylAction_injective (isFiniteType_cartanD n)
  refine LinearMap.ext fun γ => ?_
  apply toStdD_injective n
  rw [(pnd_rep_spec n hn w).2.2 γ, (pnd_rep_spec n hn w').2.2 γ, h]

private theorem pnd_central_rep (n : ℕ) (hn : 4 ≤ n)
    {z : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    (hz : z ∈ Subgroup.center (coxeterMatrix (isFiniteType_cartanD n)).Group) :
    (pnd_rep n z).1 = 1 ∧
      ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ (pnd_rep n z).2 = fun _ => t := by
  classical
  have hspec := pnd_rep_spec n (by omega) z
  have hcomm : ∀ σ : Equiv.Perm (Fin n),
      (pnd_rep n z).1 * σ = σ * (pnd_rep n z).1 ∧
        (fun c => (1 : ℤ) * (pnd_rep n z).2 (σ c)) = (pnd_rep n z).2 := by
    intro σ
    obtain ⟨u, hu⟩ := exists_omRealizes_of_even (by omega) σ spIsSign_one (by simp)
    have hpu : pnd_rep n u = (σ, fun _ => (1 : ℤ)) := by
      obtain ⟨h1, h2⟩ := omRealizes_unique (by omega) (pnd_rep_spec n (by omega) u).2.2 hu
        (pnd_rep_spec n (by omega) u).1
      exact Prod.ext h1 h2
    have hzu : z * u = u * z := (Subgroup.mem_center_iff.mp hz u).symm
    have hrep1 : pnd_rep n (z * u) = ((pnd_rep n z).1 * σ,
        fun c => (1 : ℤ) * (pnd_rep n z).2 (σ c)) := by
      rw [pnd_rep_mul n (by omega) z u, hpu]
    have hrep2 : pnd_rep n (u * z) = (σ * (pnd_rep n z).1,
        fun c => (pnd_rep n z).2 c * (1 : ℤ)) := by
      rw [pnd_rep_mul n (by omega) u z, hpu]
    have heq := hrep1.symm.trans (hzu ▸ hrep2)
    refine ⟨congrArg Prod.fst heq, ?_⟩
    have hsnd := congrArg Prod.snd heq
    funext c
    simpa using congrFun hsnd c
  have hπ : (pnd_rep n z).1 = 1 := by
    have hmem : (pnd_rep n z).1 ∈ Subgroup.center (Equiv.Perm (Fin n)) :=
      Subgroup.mem_center_iff.mpr fun σ => (hcomm σ).1.symm
    by_contra hne
    obtain ⟨c, hc⟩ : ∃ c, (pnd_rep n z).1 c ≠ c := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext h)
    obtain ⟨z', -, hz'⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({c, (pnd_rep n z).1 c} : Finset (Fin n))) (t := Finset.univ) (by
        rw [Finset.card_univ, Fintype.card_fin]
        have hle : ({c, (pnd_rep n z).1 c} : Finset (Fin n)).card ≤ 2 := by
          calc ({c, (pnd_rep n z).1 c} : Finset (Fin n)).card
              ≤ ({(pnd_rep n z).1 c} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
            _ = 2 := by simp
        omega)
    rw [Finset.mem_insert, Finset.mem_singleton] at hz'
    have hz'c : z' ≠ c := fun h => hz' (Or.inl h)
    have hz'pc : z' ≠ (pnd_rep n z).1 c := fun h => hz' (Or.inr h)
    have he : (pnd_rep n z).1 z' = (pnd_rep n z).1 c := by
      have h' := congrFun (congrArg DFunLike.coe ((hcomm (Equiv.swap c z')).1.symm)) c
      change (Equiv.swap c z') ((pnd_rep n z).1 c) = (pnd_rep n z).1
        ((Equiv.swap c z') c) at h'
      rw [Equiv.swap_apply_of_ne_of_ne hc (Ne.symm hz'pc), Equiv.swap_apply_left] at h'
      exact h'.symm
    exact hz'c ((pnd_rep n z).1.injective he)
  refine ⟨hπ, ⟨(pnd_rep n z).2 ⟨0, by omega⟩, hspec.1 _, ?_⟩⟩
  funext c
  have h2 := congrFun (hcomm (Equiv.swap ⟨0, by omega⟩ c)).2 ⟨0, by omega⟩
  simpa [Equiv.swap_apply_left] using h2

private theorem pnd_mem_center_of_rep (n : ℕ) (hn : 4 ≤ n)
    {z : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    (hπ : (pnd_rep n z).1 = 1)
    {t : ℤ} (hs : (pnd_rep n z).2 = fun _ => t) :
    z ∈ Subgroup.center (coxeterMatrix (isFiniteType_cartanD n)).Group := by
  refine Subgroup.mem_center_iff.mpr fun u => ?_
  apply pnd_rep_injective n (by omega)
  rw [pnd_rep_mul n (by omega) z u, pnd_rep_mul n (by omega) u z, hπ, hs]
  refine Prod.ext ?_ ?_
  · simp
  · funext c
    simp only [Equiv.Perm.one_apply]
    rw [mul_comm]

private theorem pnd_center_eq_bot_of_odd (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n) :
    Subgroup.center (coxeterMatrix (isFiniteType_cartanD n)).Group = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨hπ, t, ht, hs⟩ := pnd_central_rep n hn hz
  have hprod := (pnd_rep_spec n (by omega) z).2.1
  rw [hs] at hprod
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have ht1 : t = 1 := by
    rcases ht with h | h
    · exact h
    · rw [h, hodd.neg_one_pow] at hprod
      norm_num at hprod
  have h1rep : pnd_rep n (1 : (coxeterMatrix (isFiniteType_cartanD n)).Group) =
      ((1 : Equiv.Perm (Fin n)), fun _ : Fin n => (1 : ℤ)) := by
    obtain ⟨h1, h2⟩ := omRealizes_unique (by omega) (pnd_rep_spec n (by omega) 1).2.2
      (omRealizes_one n) (pnd_rep_spec n (by omega) 1).1
    exact Prod.ext h1 h2
  apply pnd_rep_injective n (by omega)
  have hzrep : pnd_rep n z = ((1 : Equiv.Perm (Fin n)), fun _ : Fin n => (1 : ℤ)) := by
    refine Prod.ext ?_ ?_
    · exact hπ
    · rw [hs, ht1]
  rw [hzrep, h1rep]

private theorem pnd_card_center_of_even (n : ℕ) (hn : 4 ≤ n) (heven : Even n) :
    Nat.card ↥(Subgroup.center (coxeterMatrix (isFiniteType_cartanD n)).Group) = 2 := by
  classical
  obtain ⟨z₀, hz₀⟩ := exists_omRealizes_of_even (n := n) (by omega) (1 : Equiv.Perm (Fin n))
    (s := fun _ : Fin n => (-1 : ℤ)) (fun _ : Fin n => Or.inr rfl) (by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact heven.neg_one_pow)
  have hz₀rep : pnd_rep n z₀ = ((1 : Equiv.Perm (Fin n)), fun _ : Fin n => (-1 : ℤ)) := by
    obtain ⟨h1, h2⟩ := omRealizes_unique (by omega) (pnd_rep_spec n (by omega) z₀).2.2 hz₀
      (pnd_rep_spec n (by omega) z₀).1
    exact Prod.ext h1 h2
  have hz₀mem : z₀ ∈ Subgroup.center (coxeterMatrix (isFiniteType_cartanD n)).Group :=
    pnd_mem_center_of_rep n hn (congrArg Prod.fst hz₀rep) (congrArg Prod.snd hz₀rep)
  have h1rep : pnd_rep n (1 : (coxeterMatrix (isFiniteType_cartanD n)).Group) =
      ((1 : Equiv.Perm (Fin n)), fun _ : Fin n => (1 : ℤ)) := by
    obtain ⟨h1, h2⟩ := omRealizes_unique (by omega) (pnd_rep_spec n (by omega) 1).2.2
      (omRealizes_one n) (pnd_rep_spec n (by omega) 1).1
    exact Prod.ext h1 h2
  have hz₀ne : z₀ ≠ 1 := by
    intro h
    have h' : pnd_rep n z₀ = pnd_rep n 1 := by rw [h]
    rw [hz₀rep, h1rep] at h'
    have := congrFun (congrArg Prod.snd h') ⟨0, by omega⟩
    norm_num at this
  have hz₀sq : z₀ * z₀ = 1 := by
    apply pnd_rep_injective n (by omega)
    rw [pnd_rep_mul n (by omega) z₀ z₀, hz₀rep, h1rep]
    refine Prod.ext ?_ ?_
    · simp
    · funext c
      norm_num
  have hcenter_le : Subgroup.center (coxeterMatrix (isFiniteType_cartanD n)).Group ≤
      Subgroup.zpowers z₀ := by
    intro z hz
    obtain ⟨hπ, t, ht, hs⟩ := pnd_central_rep n hn hz
    have hzeq : z = 1 ∨ z = z₀ := by
      rcases ht with h | h
      · left
        apply pnd_rep_injective n (by omega)
        have hzrep : pnd_rep n z =
            ((1 : Equiv.Perm (Fin n)), fun _ : Fin n => (1 : ℤ)) := by
          refine Prod.ext ?_ ?_
          · exact hπ
          · rw [hs, h]
        exact hzrep.trans h1rep.symm
      · right
        apply pnd_rep_injective n (by omega)
        have hzrep : pnd_rep n z =
            ((1 : Equiv.Perm (Fin n)), fun _ : Fin n => (-1 : ℤ)) := by
          refine Prod.ext ?_ ?_
          · exact hπ
          · rw [hs, h]
        exact hzrep.trans hz₀rep.symm
    rcases hzeq with h | h
    · rw [h, Subgroup.mem_zpowers_iff]
      exact ⟨0, by rw [zpow_zero]⟩
    · rw [h, Subgroup.mem_zpowers_iff]
      exact ⟨1, by rw [zpow_one]⟩
  have hcenter_eq : Subgroup.center (coxeterMatrix (isFiniteType_cartanD n)).Group =
      Subgroup.zpowers z₀ := le_antisymm hcenter_le (Subgroup.zpowers_le.mpr hz₀mem)
  rw [hcenter_eq, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hz₀sq) hz₀ne

private theorem pnd_card_center_cartanD (n : ℕ) (hn : 4 ≤ n) :
    Nat.card ↥(Subgroup.center (coxeterMatrix (isFiniteType_cartanD n)).Group) =
      if Even n then 2 else 1 := by
  by_cases heven : Even n
  · rw [if_pos heven]
    exact pnd_card_center_of_even n hn heven
  · rw [if_neg heven, pnd_center_eq_bot_of_odd n hn (Nat.not_even_iff_odd.mp heven)]
    exact Subgroup.card_bot

theorem ggCoxeterD_center (n : ℕ) (hn : 4 ≤ n) :
    Nat.card ↥(Subgroup.center (ggCoxeterMatrixD n).Group) = if Even n then 2 else 1 := by
  rw [pnd_coxeterMatrixD_eq]
  exact pnd_card_center_cartanD n hn

end CFSG.StandardType

end
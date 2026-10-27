module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleSym
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleE
public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep
public import CFSG.LocalAnalysis.StandardType.GGForkClassify
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflCartan
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.TripleEdge
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import CFSG.LocalAnalysis.StandardType.GGForkCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def ggQ2xKDa_sum (K : Type) [Field K] (n : ℕ) : (Fin (n+1) → K) →ₗ[K] K where
  toFun x := ∑ k, x k
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

private def ggQ2xKDa_S (K : Type) [Field K] (n : ℕ) : Submodule (K) (Fin (n+1) → K) :=
  LinearMap.ker (ggQ2xKDa_sum K n)

private lemma ggQ2xKDa_sum_single (K : Type) [Field K] (n : ℕ) (k : Fin (n+1)) (c : K) :
    ggQ2xKDa_sum K n (Pi.single k c) = c := by
  simp [ggQ2xKDa_sum, Pi.single_apply]

private def ggQ2xKDa_A (K : Type) [Field K] (n : ℕ) (j : Fin n) : ggQ2xKDa_S K n :=
  ⟨Pi.single j.castSucc 1 - Pi.single j.succ 1, by
    rw [ggQ2xKDa_S, LinearMap.mem_ker, map_sub, ggQ2xKDa_sum_single, ggQ2xKDa_sum_single, sub_self]⟩

private noncomputable def ggQ2xKDa_lam (K : Type) [Field K] (n : ℕ) (i : Fin n) :
    (Fin (n+1) → K) →ₗ[K] K where
  toFun x := ∑ k ∈ Finset.Iic i.castSucc, x k
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

private lemma ggQ2xKDa_ite (K : Type) [Field K] (n : ℕ) (i j : Fin n) :
    ((if j ≤ i then (1 : K) else 0) - (if j < i then 1 else 0)) =
      if i = j then 1 else 0 := by
  by_cases h : i = j
  · rw [h, if_pos le_rfl, if_neg (lt_irrefl j), if_pos rfl]; ring
  · rcases lt_or_gt_of_ne h with hlt | hlt
    · rw [if_neg (not_le.mpr hlt), if_neg (not_lt.mpr (le_of_lt hlt)), if_neg h]; ring
    · rw [if_pos (le_of_lt hlt), if_pos hlt, if_neg h]; ring

private lemma ggQ2xKDa_lam_A (K : Type) [Field K] (n : ℕ) (i j : Fin n) :
    ggQ2xKDa_lam K n i (ggQ2xKDa_A K n j : Fin (n+1) → K) = if i = j then 1 else 0 := by
  change (∑ k ∈ Finset.Iic i.castSucc,
      (Pi.single j.castSucc 1 - Pi.single j.succ 1 : Fin (n+1) → K) k) = _
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib]
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_Iic, Fin.castSucc_le_castSucc_iff, Fin.succ_le_castSucc_iff]
  exact ggQ2xKDa_ite K n i j

private noncomputable def ggQ2xKDa_lamPi (K : Type) [Field K] (n : ℕ) :
    ggQ2xKDa_S K n →ₗ[K] (Fin n → K) where
  toFun x i := ggQ2xKDa_lam K n i (x : Fin (n+1) → K)
  map_add' x y := by funext i; exact map_add (ggQ2xKDa_lam K n i) _ _
  map_smul' c x := by funext i; exact map_smul (ggQ2xKDa_lam K n i) c _

private lemma ggQ2xKDa_lamPi_A (K : Type) [Field K] (n : ℕ) (j : Fin n) :
    ggQ2xKDa_lamPi K n (ggQ2xKDa_A K n j) = Pi.single j 1 := by
  funext i
  show ggQ2xKDa_lam K n i (ggQ2xKDa_A K n j : Fin (n+1) → K) = (Pi.single j 1 : Fin n → K) i
  rw [ggQ2xKDa_lam_A, Pi.single_apply]

private theorem ggQ2xKDa_A_linIndep (K : Type) [Field K] (n : ℕ) :
    LinearIndependent (K) (ggQ2xKDa_A K n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h3 : (ggQ2xKDa_lamPi K n (∑ j, g j • ggQ2xKDa_A K n j)) i = g i := by
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, ggQ2xKDa_lamPi_A, Pi.smul_apply, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [if_neg (Ne.symm hj), smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [← h3, hg, map_zero]
  rfl

private lemma ggQ2xKDa_S_finrank (K : Type) [Field K] (n : ℕ) :
    finrank (K) (ggQ2xKDa_S K n) = n := by
  have hrange : (ggQ2xKDa_sum K n).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨Pi.single ⟨0, Nat.succ_pos n⟩ c, ggQ2xKDa_sum_single K n ⟨0, Nat.succ_pos n⟩ c⟩
  have h1 : finrank (K) (ggQ2xKDa_sum K n).range = 1 := by
    rw [hrange, finrank_top, Module.finrank_self]
  have h2 : finrank (K) (Fin (n+1) → K) = n + 1 := Module.finrank_fin_fun (K)
  have h := LinearMap.finrank_range_add_finrank_ker (ggQ2xKDa_sum K n)
  rw [h1, h2] at h
  change 1 + finrank (K) (ggQ2xKDa_S K n) = n + 1 at h
  omega

private lemma ggQ2xKDa_A_span_top (K : Type) [Field K] (n : ℕ) :
    Submodule.span (K) (Set.range (ggQ2xKDa_A K n)) = ⊤ := by
  have hfin : finrank (K) (Submodule.span (K) (Set.range (ggQ2xKDa_A K n))) = n := by
    rw [finrank_span_eq_card (ggQ2xKDa_A_linIndep K n), Fintype.card_fin]
  apply Submodule.eq_top_of_finrank_eq
  rw [hfin, ggQ2xKDa_S_finrank]

private noncomputable def ggQ2xKDa_Pe (K : Type) [Field K] (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    (Fin (n+1) → K) ≃ₗ[K] (Fin (n+1) → K) :=
  LinearEquiv.funCongrLeft (K) (K) σ.symm

private lemma ggQ2xKDa_Pe_single (K : Type) [Field K] (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (m : Fin (n+1)) (c : K) :
    ggQ2xKDa_Pe K n σ (Pi.single m c) = Pi.single (σ m) c := by
  funext k
  simp only [ggQ2xKDa_Pe, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Pi.single_apply,
    Equiv.symm_apply_eq]

private lemma ggQ2xKDa_sum_Pe (K : Type) [Field K] (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (x : Fin (n+1) → K) : ggQ2xKDa_sum K n (ggQ2xKDa_Pe K n σ x) = ggQ2xKDa_sum K n x := by
  simp only [ggQ2xKDa_sum, ggQ2xKDa_Pe, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  exact Equiv.sum_comp σ.symm x

private lemma ggQ2xKDa_S_mem_Pe (K : Type) [Field K] (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    {x : Fin (n+1) → K} (hx : x ∈ ggQ2xKDa_S K n) : ggQ2xKDa_Pe K n σ x ∈ ggQ2xKDa_S K n := by
  rw [ggQ2xKDa_S, LinearMap.mem_ker] at hx ⊢
  rw [ggQ2xKDa_sum_Pe, hx]

private noncomputable def ggQ2xKDa_P (K : Type) [Field K] (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    ggQ2xKDa_S K n ≃ₗ[K] ggQ2xKDa_S K n :=
  LinearEquiv.ofLinearMap
    ((ggQ2xKDa_Pe K n σ).toLinearMap.restrict (fun _ hx => ggQ2xKDa_S_mem_Pe K n σ hx))
    ((ggQ2xKDa_Pe K n σ.symm).toLinearMap.restrict (fun _ hx => ggQ2xKDa_S_mem_Pe K n σ.symm hx))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change ggQ2xKDa_Pe K n σ ((ggQ2xKDa_Pe K n σ).symm (x : Fin (n+1) → K)) = _
      rw [LinearEquiv.apply_symm_apply]
      rfl)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change (ggQ2xKDa_Pe K n σ).symm (ggQ2xKDa_Pe K n σ (x : Fin (n+1) → K)) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl)

private lemma ggQ2xKDa_P_apply (K : Type) [Field K] (n : ℕ)
    (σ : Equiv.Perm (Fin (n+1))) (x : ggQ2xKDa_S K n) :
    ((ggQ2xKDa_P K n σ x : ggQ2xKDa_S K n) : Fin (n+1) → K) =
      ggQ2xKDa_Pe K n σ (x : Fin (n+1) → K) := rfl

private lemma ggQ2xKDa_symm_mul {α : Type*} (σ τ : Equiv.Perm α) :
    (σ * τ).symm = τ.symm * σ.symm := by ext x; rfl

private lemma ggQ2xKDa_Pe_mul (K : Type) [Field K] (n : ℕ) (σ τ : Equiv.Perm (Fin (n+1))) :
    ggQ2xKDa_Pe K n (σ * τ) = ggQ2xKDa_Pe K n σ * ggQ2xKDa_Pe K n τ := by
  ext x k
  simp only [ggQ2xKDa_Pe, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    LinearEquiv.mul_apply, Equiv.Perm.mul_apply, ggQ2xKDa_symm_mul]

private lemma ggQ2xKDa_P_mul (K : Type) [Field K] (n : ℕ) (σ τ : Equiv.Perm (Fin (n+1))) :
    ggQ2xKDa_P K n (σ * τ) = ggQ2xKDa_P K n σ * ggQ2xKDa_P K n τ := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp only [LinearEquiv.mul_apply, ggQ2xKDa_P_apply, ggQ2xKDa_Pe_mul]

private lemma ggQ2xKDa_Pe_swap_left (K : Type) [Field K] (n : ℕ) (i : Fin n) (c : K) :
    ggQ2xKDa_Pe K n (Equiv.swap i.castSucc i.succ) (Pi.single i.castSucc c) =
      Pi.single i.succ c := by
  rw [ggQ2xKDa_Pe_single, Equiv.swap_apply_left]

private lemma ggQ2xKDa_Pe_swap_right (K : Type) [Field K] (n : ℕ) (i : Fin n) (c : K) :
    ggQ2xKDa_Pe K n (Equiv.swap i.castSucc i.succ) (Pi.single i.succ c) =
      Pi.single i.castSucc c := by
  rw [ggQ2xKDa_Pe_single, Equiv.swap_apply_right]

private lemma ggQ2xKDa_Pe_swap_fixed (K : Type) [Field K] (n : ℕ) (i : Fin n) {m : Fin (n+1)}
    (hm1 : m ≠ i.castSucc) (hm2 : m ≠ i.succ) (c : K) :
    ggQ2xKDa_Pe K n (Equiv.swap i.castSucc i.succ) (Pi.single m c) = Pi.single m c := by
  rw [ggQ2xKDa_Pe_single, Equiv.swap_apply_of_ne_of_ne hm1 hm2]

lemma ggQ2xKDa_coeff_self (n : ℕ) (i : Fin n) : CartanMatrix.A n i i = 2 := by
  simp [CartanMatrix.A]

private lemma ggQ2xKDa_coeff_adj (n : ℕ) {i j : Fin n} (hne : i ≠ j)
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) : CartanMatrix.A n i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hne, if_pos h]

private lemma ggQ2xKDa_coeff_other (n : ℕ) {i j : Fin n} (hne : i ≠ j)
    (h1 : i.val + 1 ≠ j.val) (h2 : j.val + 1 ≠ i.val) : CartanMatrix.A n i j = 0 := by
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hne,
    if_neg (show ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) from fun h => h.elim h1 h2)]

private lemma ggQ2xKDa_Pe_swap_A (K : Type) [Field K] (n : ℕ) (i j : Fin n) :
    ggQ2xKDa_Pe K n (Equiv.swap i.castSucc i.succ) (ggQ2xKDa_A K n j : Fin (n+1) → K) =
      (ggQ2xKDa_A K n j : Fin (n+1) → K) -
        ((CartanMatrix.A n i j : ℤ) : K) • (ggQ2xKDa_A K n i : Fin (n+1) → K) := by
  change ggQ2xKDa_Pe K n (Equiv.swap i.castSucc i.succ)
      (Pi.single j.castSucc 1 - Pi.single j.succ 1) =
    (Pi.single j.castSucc 1 - Pi.single j.succ 1) -
      ((CartanMatrix.A n i j : ℤ) : K) • (Pi.single i.castSucc 1 - Pi.single i.succ 1)
  rw [map_sub]
  by_cases h1 : j.castSucc = i.castSucc
  · have hji : j = i := Fin.ext (by simpa using congrArg Fin.val h1)
    subst j
    rw [ggQ2xKDa_Pe_swap_left, ggQ2xKDa_Pe_swap_right, ggQ2xKDa_coeff_self, Int.cast_ofNat,
      two_smul]
    abel
  · by_cases h2 : j.castSucc = i.succ
    · have hne : i ≠ j := fun hh => h1 (by rw [hh])
      have hA : CartanMatrix.A n i j = -1 :=
        ggQ2xKDa_coeff_adj n hne (Or.inl (by simpa using (congrArg Fin.val h2).symm))
      have hjc : j.succ ≠ i.castSucc := by
        intro hh
        have h3 := congrArg Fin.val hh
        have h4 := congrArg Fin.val h2
        simp only [Fin.val_succ, Fin.val_castSucc] at h3 h4
        omega
      have hjs : j.succ ≠ i.succ := by
        intro hh
        have h3 := congrArg Fin.val hh
        have h4 := congrArg Fin.val h2
        simp only [Fin.val_succ] at h3 h4
        omega
      rw [hA, Int.cast_neg, Int.cast_one, neg_one_smul]
      rw [h2, ggQ2xKDa_Pe_swap_right, ggQ2xKDa_Pe_swap_fixed K n i hjc hjs]
      abel
    · by_cases h3 : j.succ = i.castSucc
      · have hne : i ≠ j := fun hh => h1 (by rw [hh])
        have hA : CartanMatrix.A n i j = -1 :=
          ggQ2xKDa_coeff_adj n hne (Or.inr (by simpa using congrArg Fin.val h3))
        have hjs : j.castSucc ≠ i.succ := by
          intro hh
          have h4 := congrArg Fin.val hh
          have h5 := congrArg Fin.val h3
          simp only [Fin.val_succ, Fin.val_castSucc] at h4 h5
          omega
        rw [hA, Int.cast_neg, Int.cast_one, neg_one_smul]
        rw [h3, ggQ2xKDa_Pe_swap_left, ggQ2xKDa_Pe_swap_fixed K n i h1 hjs]
        abel
      · have hne : i ≠ j := fun hh => h1 (by rw [hh])
        have hA : CartanMatrix.A n i j = 0 :=
          ggQ2xKDa_coeff_other n hne
            (fun hh => h2 (by
              apply Fin.ext
              simpa only [Fin.val_succ, Fin.val_castSucc] using hh.symm))
            (fun hh => h3 (by
              apply Fin.ext
              simpa only [Fin.val_succ, Fin.val_castSucc] using hh))
        have hjs : j.succ ≠ i.succ := by
          intro hh
          exact h1 (by rw [Fin.succ_injective n hh])
        rw [hA, Int.cast_zero, zero_smul, sub_zero]
        rw [ggQ2xKDa_Pe_swap_fixed K n i h1 h2, ggQ2xKDa_Pe_swap_fixed K n i h3 hjs]

private lemma ggQ2xKDa_P_eq_one_imp (K : Type) [Field K] [CharP K 3] (n : ℕ) (hn : 4 ≤ n)
    (σ : Equiv.Perm (Fin (n+1))) (h : ggQ2xKDa_P K n σ = 1) : σ = 1 := by
  have hfix : ∀ x : ggQ2xKDa_S K n, ggQ2xKDa_P K n σ x = x := by
    intro x; rw [h]; rfl
  have hvec : ∀ x ∈ ggQ2xKDa_S K n, ggQ2xKDa_Pe K n σ x = x := by
    intro x hx
    have := congrArg (Subtype.val) (hfix ⟨x, hx⟩)
    simpa [ggQ2xKDa_P_apply] using this
  apply Equiv.ext
  intro m
  obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin (n+1))
    (by rw [Fintype.card_fin]; omega) m
  have hmq : m ≠ q := fun hh => hq hh.symm
  have hx : (Pi.single m 1 - Pi.single q 1 : Fin (n+1) → K) ∈ ggQ2xKDa_S K n := by
    rw [ggQ2xKDa_S, LinearMap.mem_ker, map_sub, ggQ2xKDa_sum_single, ggQ2xKDa_sum_single, sub_self]
  have hp := congrFun (hvec _ hx) m
  simp only [map_sub, ggQ2xKDa_Pe_single, Pi.sub_apply] at hp
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hmq, sub_zero] at hp
  by_cases hm : m = σ m
  · exact hm.symm
  · exfalso
    have h1 : (Pi.single (σ m) (1 : K) : Fin (n+1) → K) m = 0 :=
      Pi.single_eq_of_ne (M := fun _ : Fin (n+1) => K) hm (1 : K)
    rw [h1] at hp
    by_cases hq' : m = σ q
    · have h2 : (Pi.single (σ q) (1 : K) : Fin (n+1) → K) m = 1 := by
        rw [← hq', Pi.single_eq_same]
      rw [h2] at hp
      have hne : ((0 : K) - 1) ≠ 1 := by
        intro hc
        have h2 : (2 : K) = 0 := by
          have hh := congrArg (fun x : K => x + 1) hc
          have hh' : (1 : K) + 1 = 0 := by simpa using hh.symm
          rwa [one_add_one_eq_two] at hh'
        exact absurd ((CharP.cast_eq_zero_iff K 3 2).mp h2) (by decide)
      exact absurd hp hne
    · have h2 : (Pi.single (σ q) (1 : K) : Fin (n+1) → K) m = 0 :=
        Pi.single_eq_of_ne (M := fun _ : Fin (n+1) => K) hq' (1 : K)
      rw [h2] at hp
      have hne : ((0 : K) - 0) ≠ 1 := by
        intro hc
        exact (zero_ne_one : (0 : K) ≠ 1) (by simpa using hc)
      exact absurd hp hne

theorem ggQ2xKD_A_model {n : ℕ} (hn : 4 ≤ n) {U : Type} [AddCommGroup U]
    [Module (ZMod 3) U] (h : Fin n → U) (hb : LinearIndependent (ZMod 3) h)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤) (α : Fin n → Module.Dual (ZMod 3) U)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A n i j : ℤ) : ZMod 3)) :
    ∃ Φ : Equiv.Perm (Fin (n + 1)) →* (U ≃ₗ[ZMod 3] U), Function.Injective Φ ∧
      ∀ (i : Fin n) (v : U), Φ (Equiv.swap i.castSucc i.succ) v = v - α i v • h i := by
  let bU : Basis (Fin n) (ZMod 3) U := Basis.mk hb (le_of_eq hspan.symm)
  let bS : Basis (Fin n) (ZMod 3) (ggQ2xKDa_S (ZMod 3) n) :=
    Basis.mk (ggQ2xKDa_A_linIndep (ZMod 3) n) (le_of_eq (ggQ2xKDa_A_span_top (ZMod 3) n).symm)
  let ψ : U ≃ₗ[ZMod 3] ggQ2xKDa_S (ZMod 3) n := bU.equiv bS (Equiv.refl (Fin n))
  have hψ : ∀ j, ψ (h j) = ggQ2xKDa_A (ZMod 3) n j := by
    intro j
    dsimp only [ψ, bU, bS]
    rw [← Basis.mk_apply hb (le_of_eq hspan.symm) j]
    rw [Basis.equiv_apply, Equiv.refl_apply, Basis.mk_apply]
  let Φ : Equiv.Perm (Fin (n+1)) →* (U ≃ₗ[ZMod 3] U) :=
    MonoidHom.mk' (fun σ => ψ.trans ((ggQ2xKDa_P (ZMod 3) n σ).trans ψ.symm)) (by
      intro σ τ
      ext v
      simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply, ggQ2xKDa_P_mul,
        LinearEquiv.apply_symm_apply])
  refine ⟨Φ, ?_, ?_⟩
  · intro σ τ hστ
    have h1 : Φ (σ * τ⁻¹) = 1 := by rw [map_mul, map_inv, hστ, mul_inv_cancel]
    have hcomp : ψ.trans ((ggQ2xKDa_P (ZMod 3) n (σ * τ⁻¹)).trans ψ.symm) = 1 := h1
    have hP : ggQ2xKDa_P (ZMod 3) n (σ * τ⁻¹) = 1 := by
      apply LinearEquiv.ext
      intro y
      have hy : ψ.symm (ggQ2xKDa_P (ZMod 3) n (σ * τ⁻¹) (ψ (ψ.symm y))) = ψ.symm y := by
        have := congrFun (congrArg (fun e : U ≃ₗ[ZMod 3] U => (e : U → U)) hcomp)
          (ψ.symm y)
        simpa [LinearEquiv.trans_apply] using this
      rw [LinearEquiv.apply_symm_apply] at hy
      change ggQ2xKDa_P (ZMod 3) n (σ * τ⁻¹) y = y
      exact ψ.symm.injective hy
    have h2 : σ * τ⁻¹ = 1 := ggQ2xKDa_P_eq_one_imp (ZMod 3) n hn (σ * τ⁻¹) hP
    calc σ = σ * τ⁻¹ * τ := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = 1 * τ := by rw [h2]
      _ = τ := one_mul τ
  · intro i v
    have hPj : ∀ j, ggQ2xKDa_P (ZMod 3) n (Equiv.swap i.castSucc i.succ)
        (ggQ2xKDa_A (ZMod 3) n j) =
        ggQ2xKDa_A (ZMod 3) n j -
          ((CartanMatrix.A n i j : ℤ) : ZMod 3) • ggQ2xKDa_A (ZMod 3) n i := by
      intro j
      apply Subtype.ext
      rw [ggQ2xKDa_P_apply, ggQ2xKDa_Pe_swap_A]
      rfl
    have hrefl : α i (h i) = 2 := by rw [hα i i, ggQ2xKDa_coeff_self n i]; decide
    have hEq : (Φ (Equiv.swap i.castSucc i.succ)).toLinearMap =
        (Module.reflection hrefl).toLinearMap := by
      apply bU.ext
      intro j
      have hΦj : (Φ (Equiv.swap i.castSucc i.succ)) (h j) =
          h j - ((CartanMatrix.A n i j : ℤ) : ZMod 3) • h i := by
        change ψ.symm (ggQ2xKDa_P (ZMod 3) n (Equiv.swap i.castSucc i.succ) (ψ (h j))) =
          h j - ((CartanMatrix.A n i j : ℤ) : ZMod 3) • h i
        rw [hψ j, hPj j, map_sub, map_smul]
        congr 1
        · rw [← hψ j, LinearEquiv.symm_apply_apply]
        · rw [← hψ i, LinearEquiv.symm_apply_apply]
      have hRj : (Module.reflection hrefl) (h j) =
          h j - ((CartanMatrix.A n i j : ℤ) : ZMod 3) • h i := by
        rw [Module.reflection_apply, hα i j]
      simp only [bU, Basis.mk_apply]
      change (Φ (Equiv.swap i.castSucc i.succ)) (h j) = (Module.reflection hrefl) (h j)
      rw [hΦj, hRj]
    have hfin := congrArg (fun f : U →ₗ[ZMod 3] U => f v) hEq
    simpa [Module.reflection_apply] using hfin
end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpComp
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpCompPair
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp StatedSL)
open CFSG.StandardType.ClassicalPosition
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open Matrix

theorem ggTBJSpB_mem_statedSL_of_mul_self {E : Type} [Field E] [CharP E 2] {d : ℕ}
    {g : GL (Fin d) E} (hg : g * g = 1) : g ∈ StatedSL d E := by
  rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker]
  have h1 : (GeneralLinearGroup.det g) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hg, map_one]
  have h2 : (((GeneralLinearGroup.det g : Eˣ) : E)) ^ 2 = (1 : E) ^ 2 := by
    have := congrArg (fun u : Eˣ => (u : E)) h1
    simpa using this
  have h3 : ((GeneralLinearGroup.det g : Eˣ) : E) = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · exact h
    · rw [CharTwo.neg_eq] at h; exact h
  exact Units.ext h3

theorem ggTBJSpB_permMatrix_apply_of_perm {K : Type} [Field K] {ι : Type} [DecidableEq ι]
    (σ : Equiv.Perm ι) (a b : ι) : σ.permMatrix K a b = if σ a = b then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp

theorem ggTBJSpB_spIncl_mul {n : ℕ} {K : Type} [Field K] (σ τ : Fin n → Fin n) :
    spIncl (K := K) σ * spIncl (K := K) τ = spIncl (K := K) (σ ∘ τ) := by
  ext a b
  simp only [Matrix.mul_apply, spIncl_apply]
  rw [Finset.sum_eq_single (Sum.map τ τ b)]
  · have h1 : (if Sum.map τ τ b = Sum.map τ τ b then (1:K) else 0) = 1 := if_pos rfl
    rw [h1, mul_one]
    have h2 : Sum.map σ σ (Sum.map τ τ b) = Sum.map (σ ∘ τ) (σ ∘ τ) b := by
      cases b <;> rfl
    rw [h2]
  · intro c _ hc
    have h1 : (if c = Sum.map τ τ b then (1:K) else 0) = 0 := if_neg hc
    rw [h1, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ggTBJSpB_permSp_coe_GL {K : Type} [Field K] {m : ℕ} (π : Equiv.Perm (Fin m)) :
    ((permSp K π : StatedSp m K) : GL (Fin m ⊕ Fin m) K) =
      TauCeti.permutationGL (Equiv.sumCongr π π) := by
  apply Units.ext
  change mat m K (permSp K π) =
    ((TauCeti.permutationGL (Equiv.sumCongr π π) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
  rw [mat_permSp, TauCeti.permutationGL_coe]
  ext a b
  rw [spIncl_apply, ggTBJSpB_permMatrix_apply_of_perm]
  have hiff : (Equiv.sumCongr π π)⁻¹ a = b ↔ a = Sum.map π π b := by
    change (Equiv.sumCongr π π).symm a = b ↔ _
    rw [Equiv.symm_apply_eq, Equiv.sumCongr_apply]
  by_cases h : a = Sum.map π π b
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

theorem ggTBJSpB_permSp_swap_mul_self {K : Type} [Field K] {m : ℕ} (i k : Fin m) :
    permSp K (Equiv.swap i k) * permSp K (Equiv.swap i k) = 1 := by
  refine mat_injective ?_
  rw [map_mul, map_one, mat_permSp, ggTBJSpB_spIncl_mul]
  have h : (Equiv.swap i k : Fin m → Fin m) ∘ (Equiv.swap i k : Fin m → Fin m) = id := by
    funext x
    by_cases hx : x = i
    · subst hx; simp
    · by_cases hx2 : x = k
      · subst hx2; simp
      · simp [Function.comp_apply, Equiv.swap_apply_def, hx, hx2]
  rw [h]
  ext a b
  rw [spIncl_apply, Matrix.one_apply]
  by_cases hab : a = b <;> simp [hab]

theorem ggTBJSpB_spSwapSp_mul_self {K : Type} [Field K] [CharP K 2] {m : ℕ} (i : Fin m) :
    TableBSymp.spSwapSp (K := K) (m := m) i * TableBSymp.spSwapSp i = 1 := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_one, TableBSymp.spSwapSp_coe]
  rw [← map_mul]
  have h : TableBSymp.pairSwap i * TableBSymp.pairSwap i = 1 := by
    rw [TableBSymp.pairSwap]
    exact Equiv.swap_mul_self (Sum.inl i) (Sum.inr i)
  rw [h, map_one]

theorem ggTBJSpB_diagonal_mul_eq_mul_of_block {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (v w dv : ι → K) (j : Matrix ι ι K)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hfix : j * (1 - Matrix.diagonal v) = 1 - Matrix.diagonal v)
    (hcomm : j * Matrix.diagonal w = Matrix.diagonal w * j)
    (hconst : ∀ a b, w a = w b → v a = v b)
    (hx : ∀ a b, v a = 1 → v b = 1 → w a = w b → dv a = dv b) :
    Matrix.diagonal dv * j = j * Matrix.diagonal dv := by
  have hD : (1 : Matrix ι ι K) - Matrix.diagonal v = Matrix.diagonal (fun c => 1 - v c) := by
    ext c d; by_cases hcd : c = d <;> simp [Matrix.sub_apply, hcd]
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hab : j a b = 0
  · rw [hab, mul_zero, zero_mul]
  · have hdv : dv a = dv b := by
      have hw : w a = w b := by
        have h := congrFun (congrFun hcomm a) b
        simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
        have h' : j a b * w b = j a b * w a := by rw [h, mul_comm]
        exact (mul_left_cancel₀ hab h').symm
      have hvab : v a = v b := hconst a b hw
      rcases hv b with hb0 | hb1
      · have hfix_ab : j a b = (if a = b then 1 - v a else 0) := by
          have h := congrFun (congrFun hfix a) b
          rw [hD, Matrix.mul_diagonal, Matrix.diagonal_apply] at h
          simpa [hb0] using h
        have hab' : a = b := by
          by_contra hne
          rw [if_neg hne] at hfix_ab
          exact hab hfix_ab
        subst hab'
        rfl
      · exact hx a b (by rw [hvab]; exact hb1) hb1 hw
    rw [hdv, mul_comm]

theorem ggTBJSpB_spSwapSp_mul_permSp_swap_mul_self {K : Type} [Field K] [CharP K 2] {m : ℕ}
    {i k : Fin m} (hik : i ≠ k) :
    (TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k)) *
      (TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k)) = 1 := by
  let σ : Equiv.Perm (Fin m ⊕ Fin m) :=
    TableBSymp.pairSwap i * TableBSymp.pairSwap k *
      Equiv.sumCongr (Equiv.swap i k) (Equiv.swap i k)
  have hσsq : σ * σ = 1 := by
    ext a
    rcases a with j | j <;>
      by_cases hji : j = i <;> by_cases hjk : j = k
    all_goals simp_all [σ, Equiv.Perm.mul_apply, TableBSymp.pairSwap, Equiv.sumCongr_apply,
      Equiv.swap_apply_def, Ne.symm hik]
  have hw : ((TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) :
      StatedSp m K) : GL (Fin m ⊕ Fin m) K) = TauCeti.permutationGL σ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, TableBSymp.spSwapSp_coe,
      TableBSymp.spSwapSp_coe, ggTBJSpB_permSp_coe_GL]
    rw [← map_mul, ← map_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, hw]
  rw [← map_mul, hσsq, map_one]

theorem ggTBJSpB_permutationGL_mem_block {K : Type} [Field K] {m : ℕ} (t : Fin m → Kˣ)
    (v : Fin m ⊕ Fin m → K) (hv : ∀ a, v a = 0 ∨ v a = 1)
    (σ : Equiv.Perm (Fin m ⊕ Fin m))
    (hσt : ∀ a, diagSpEntry t (σ a) = diagSpEntry t a)
    (hfix : ∀ a, v a = 0 → σ a = a) :
    (TauCeti.permutationGL σ : GL (Fin m ⊕ Fin m) K) ∈
      Subgroup.centralizer
        ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
          Set (GL (Fin m ⊕ Fin m) K)) ⊓ glFixing (1 - Matrix.diagonal v) := by
  classical
  have hmat : (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal (diagSpEntry t) := by
    simpa [mat] using mat_diagSp t
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, TauCeti.permutationGL_coe, hmat]
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, ggTBJSpB_permMatrix_apply_of_perm]
    by_cases h : a = σ b
    · have h' : σ⁻¹ a = b := by
        calc σ⁻¹ a = σ⁻¹ (σ b) := by rw [h]
             _ = b := Equiv.symm_apply_apply σ b
      rw [if_pos h']
      simp [h, hσt b]
    · have h' : σ⁻¹ a ≠ b := by
        intro e
        apply h
        calc a = σ (σ⁻¹ a) := (Equiv.apply_symm_apply σ a).symm
             _ = σ b := by rw [e]
      rw [if_neg h']
      simp
  · change (TauCeti.permutationGL σ : GL (Fin m ⊕ Fin m) K) *
      (1 - Matrix.diagonal v) = 1 - Matrix.diagonal v
    have hD : (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - Matrix.diagonal v =
        Matrix.diagonal (fun a => 1 - v a) := by
      ext a b
      by_cases hab : a = b <;>
        simp [Matrix.sub_apply, hab]
    rw [hD, TauCeti.permutationGL_coe]
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_apply, ggTBJSpB_permMatrix_apply_of_perm]
    by_cases hab : a = b
    · subst hab
      by_cases hv0 : v a = 0
      · have hfix' : σ⁻¹ a = a := by
          calc σ⁻¹ a = σ⁻¹ (σ a) := by rw [hfix a hv0]
               _ = a := Equiv.symm_apply_apply σ a
        rw [if_pos hfix', if_pos rfl, hv0]
        simp
      · have hv1 : v a = 1 := by
          rcases hv a with h | h
          · exact absurd h hv0
          · exact h
        rw [hv1]
        simp
    · rw [if_neg hab]
      have hleft : (if σ⁻¹ a = b then 1 else 0) * (1 - v b) = 0 := by
        by_cases hv0 : v b = 0
        · have hb : σ b = b := hfix b hv0
          have hne : σ⁻¹ a ≠ b := by
            intro h
            apply hab
            calc a = σ (σ⁻¹ a) := (Equiv.apply_symm_apply σ a).symm
                 _ = σ b := by rw [h]
                 _ = b := hb
          rw [if_neg hne, zero_mul]
        · have hv1 : v b = 1 := by
            rcases hv b with h | h
            · exact absurd h hv0
            · exact h
          rw [hv1, sub_self, mul_zero]
      rw [hleft]

theorem ggTBJSpB_spSwapSp_mem_glBlockCentralizer_diagSp {K : Type} [Field K] [CharP K 2]
    {m : ℕ} (t : Fin m → Kˣ) (v : Fin m ⊕ Fin m → K) (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hsym : ∀ a, v a = v (Equiv.sumComm (Fin m) (Fin m) a)) {i : Fin m} (hi : t i = 1)
    (hvi : v (Sum.inl i) = 1) :
    TableBSymp.spSwapSp (K := K) (m := m) i ∈ glBlockCentralizer (StatedSp m K).subtype
      ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
        Set (GL (Fin m ⊕ Fin m) K)) (Matrix.diagonal v) := by
  have hσt : ∀ a, diagSpEntry t (TableBSymp.pairSwap i a) = diagSpEntry t a := by
    intro a
    rcases a with j | j <;> by_cases hji : j = i
    · subst hji; simp [TableBSymp.pairSwap, hi]
    · simp [TableBSymp.pairSwap, Equiv.swap_apply_def, hji]
    · subst hji; simp [TableBSymp.pairSwap, hi]
    · simp [TableBSymp.pairSwap, Equiv.swap_apply_def, hji]
  have hfix : ∀ a, v a = 0 → TableBSymp.pairSwap i a = a := by
    have hii : v (Sum.inr i) = 1 := by
      have h := hsym (Sum.inl i)
      rw [show Equiv.sumComm (Fin m) (Fin m) (Sum.inl i) = Sum.inr i from rfl] at h
      rw [← h]; exact hvi
    intro a ha
    rcases a with j | j <;> by_cases hji : j = i
    · subst hji; exfalso; rw [hvi] at ha; exact one_ne_zero ha
    · simp [TableBSymp.pairSwap, Equiv.swap_apply_def, hji]
    · subst hji; exfalso; rw [hii] at ha; exact one_ne_zero ha
    · simp [TableBSymp.pairSwap, Equiv.swap_apply_def, hji]
  rw [glBlockCentralizer, Subgroup.mem_comap]
  change ((TableBSymp.spSwapSp (K := K) (m := m) i : StatedSp m K) : GL (Fin m ⊕ Fin m) K) ∈
    Subgroup.centralizer ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
      Set (GL (Fin m ⊕ Fin m) K)) ⊓ glFixing (1 - Matrix.diagonal v)
  rw [TableBSymp.spSwapSp_coe]
  exact ggTBJSpB_permutationGL_mem_block t v hv (TableBSymp.pairSwap i) hσt hfix

theorem ggTBJSpB_eq_one_of_sq_eq_one {K : Type} [Field K] [CharP K 2] {x : K}
    (h : x ^ 2 = 1) : x = 1 := by
  have h2 : x ^ 2 = (1 : K) ^ 2 := by simpa using h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h' | h'
  · exact h'
  · rwa [CharTwo.neg_eq] at h'

theorem ggTBJSpB_eq_one_of_mul_self {K : Type} [Field K] [CharP K 2] {u : Kˣ}
    (h : u * u = 1) : u = 1 := by
  apply Units.ext
  apply ggTBJSpB_eq_one_of_sq_eq_one
  have h' := congrArg (fun v : Kˣ => (v : K)) h
  simpa [pow_two] using h'

theorem ggTBJSpB_orderOf_diagSp_dvd {K : Type} [Field K] [Finite K] {m : ℕ}
    (t : Fin m → Kˣ) :
    orderOf (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K)) ∣ Nat.card K - 1 := by
  classical
  have hmat : (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal (diagSpEntry t) := by
    simpa [mat] using mat_diagSp t
  rw [orderOf_dvd_iff_pow_eq_one]; apply Units.ext
  ext a b; rw [Units.val_pow_eq_pow_val, Units.val_one, hmat, Matrix.diagonal_pow,
    Matrix.diagonal_apply, Matrix.one_apply]
  let F : Fintype K := Fintype.ofFinite K
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl, @Nat.card_eq_fintype_card K F]
    exact @FiniteField.pow_card_sub_one_eq_one K _ F (diagSpEntry t a) (by
      rcases a with i | i <;> simp)
  · simp [hab]

theorem ggTBJSpB_odd_orderOf_diagSp {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (t : Fin m → Kˣ) : Odd (orderOf (((diagSp K m t : StatedSp m K) :
      GL (Fin m ⊕ Fin m) K))) := by
  let F : Fintype K := Fintype.ofFinite K
  have hcard : Even (Nat.card K) := by
    obtain ⟨n, -, hn⟩ := @FiniteField.card K _ F 2 (inferInstance : CharP K 2)
    rw [@Nat.card_eq_fintype_card K F, hn]
    refine Nat.even_pow.mpr ⟨by norm_num, ?_⟩; intro h0
    have h1 : 1 < @Fintype.card K F := @Fintype.one_lt_card K F _
    rw [h0] at hn; simp at hn; omega
  have h1 : 1 ≤ Nat.card K := Nat.succ_le_of_lt (Nat.card_pos (α := K))
  exact Odd.of_dvd_nat (Nat.Even.sub_odd h1 hcard odd_one)
    (ggTBJSpB_orderOf_diagSp_dvd t)

end CFSG.StandardType


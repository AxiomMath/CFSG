module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpCompFibre
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpGen

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open scoped commutatorElement

private lemma permMatrix_apply_of_perm {K : Type} [Field K] {ι : Type} [DecidableEq ι]
    (σ : Equiv.Perm ι) (a b : ι) : σ.permMatrix K a b = if σ a = b then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp

private lemma permutationGL_mem_block {K : Type} [Field K] {m : ℕ} (t : Fin m → Kˣ)
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
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, permMatrix_apply_of_perm]
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
    rw [Matrix.mul_diagonal, Matrix.diagonal_apply, permMatrix_apply_of_perm]
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

private lemma permSp_coe_GL {K : Type} [Field K] {m : ℕ} (π : Equiv.Perm (Fin m)) :
    ((permSp K π : StatedSp m K) : GL (Fin m ⊕ Fin m) K) =
      TauCeti.permutationGL (Equiv.sumCongr π π) := by
  apply Units.ext
  change mat m K (permSp K π) =
    ((TauCeti.permutationGL (Equiv.sumCongr π π) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
  rw [mat_permSp, TauCeti.permutationGL_coe]
  ext a b
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.spIncl_apply, permMatrix_apply_of_perm]
  have hiff : (Equiv.sumCongr π π)⁻¹ a = b ↔ a = Sum.map π π b := by
    change (Equiv.sumCongr π π).symm a = b ↔ _
    rw [Equiv.symm_apply_eq, Equiv.sumCongr_apply]
  by_cases h : a = Sum.map π π b
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

private lemma support_inr_of {K : Type} [Field K] {m : ℕ} (v : Fin m ⊕ Fin m → K)
    (hsym : ∀ a, v a = v (Equiv.sumComm (Fin m) (Fin m) a)) {i : Fin m}
    (hi : v (Sum.inl i) = 1) : v (Sum.inr i) = 1 := by
  have h := hsym (Sum.inl i)
  rw [show Equiv.sumComm (Fin m) (Fin m) (Sum.inl i) = Sum.inr i from rfl] at h
  rw [← h]
  exact hi

theorem diagSp_mem_glBlockCentralizer_iff {K : Type} [Field K] {m : ℕ} (t x : Fin m → Kˣ)
    (v : Fin m ⊕ Fin m → K) (hv : ∀ a, v a = 0 ∨ v a = 1) :
    diagSp K m x ∈ glBlockCentralizer (StatedSp m K).subtype
      ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
        Set (GL (Fin m ⊕ Fin m) K)) (Matrix.diagonal v) ↔
    ∀ a, v a = 0 → diagSpEntry x a = 1 := by
  have hmatx : (((diagSp K m x : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal (diagSpEntry x) := by
    rw [← mat_apply, mat_diagSp]
  have hmatt : (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal (diagSpEntry t) := by
    rw [← mat_apply, mat_diagSp]
  have hD : (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - Matrix.diagonal v =
      Matrix.diagonal (fun c => 1 - v c) := by
    ext c d; by_cases hcd : c = d <;> simp [Matrix.sub_apply, hcd]
  rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
  constructor
  · intro h a ha
    have hfix := h.2
    change (((diagSp K m x : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * (1 - Matrix.diagonal v) =
      1 - Matrix.diagonal v at hfix
    rw [hmatx, hD, Matrix.diagonal_mul_diagonal] at hfix
    have hcc := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K => M a a) hfix
    simp only [Matrix.diagonal_apply] at hcc; rw [ha] at hcc; simpa using hcc
  · intro h
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · apply Units.ext
      simp only [Subgroup.coe_subtype]
      ext a b; rw [Units.val_mul, Units.val_mul, hmatx, hmatt, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      by_cases hab : a = b <;> simp [hab, mul_comm]
    · change (((diagSp K m x : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * (1 - Matrix.diagonal v) =
        1 - Matrix.diagonal v
      rw [hmatx, hD, Matrix.diagonal_mul_diagonal]
      congr 1
      funext c
      by_cases hc : v c = 0
      · rw [h c hc, one_mul]
      · rcases hv c with h0 | h1
        · exact absurd h0 hc
        · rw [h1]
          ring

theorem permSp_swap_mem_glBlockCentralizer_diagSp {K : Type} [Field K] {m : ℕ} (t : Fin m → Kˣ)
    (v : Fin m ⊕ Fin m → K) (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hsym : ∀ a, v a = v (Equiv.sumComm (Fin m) (Fin m) a))
    {i k : Fin m} (hik : t k = t i)
    (hi : v (Sum.inl i) = 1) (hk : v (Sum.inl k) = 1) :
    permSp K (Equiv.swap i k) ∈ glBlockCentralizer (StatedSp m K).subtype
      ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
        Set (GL (Fin m ⊕ Fin m) K)) (Matrix.diagonal v) := by
  classical
  let σ : Equiv.Perm (Fin m ⊕ Fin m) :=
    Equiv.sumCongr (Equiv.swap i k) (Equiv.swap i k)
  have hσt : ∀ a, diagSpEntry t (σ a) = diagSpEntry t a := by
    intro a
    rcases a with j | j <;> by_cases hji : j = i <;> by_cases hjk : j = k
    · subst hji; subst hjk; simp [σ]
    · subst hji; simp [σ, Equiv.sumCongr_apply, hik]
    · subst hjk; simp [σ, Equiv.sumCongr_apply, hik]
    · simp [σ, Equiv.sumCongr_apply, Equiv.swap_apply_def, hji, hjk]
    · subst hji; subst hjk; simp [σ]
    · subst hji; simp [σ, Equiv.sumCongr_apply, hik]
    · subst hjk; simp [σ, Equiv.sumCongr_apply, hik]
    · simp [σ, Equiv.sumCongr_apply, Equiv.swap_apply_def, hji, hjk]
  have hfix : ∀ a, v a = 0 → σ a = a := by
    have hii := support_inr_of v hsym hi
    have hkk := support_inr_of v hsym hk
    intro a ha
    rcases a with j | j <;> by_cases hji : j = i <;> by_cases hjk : j = k
    · subst hji; exfalso; rw [hi] at ha; exact one_ne_zero ha
    · subst hji; exfalso; rw [hi] at ha; exact one_ne_zero ha
    · subst hjk; exfalso; rw [hk] at ha; exact one_ne_zero ha
    · simp [σ, Equiv.sumCongr_apply, Equiv.swap_apply_def, hji, hjk]
    · subst hji; exfalso; rw [hii] at ha; exact one_ne_zero ha
    · subst hji; exfalso; rw [hii] at ha; exact one_ne_zero ha
    · subst hjk; exfalso; rw [hkk] at ha; exact one_ne_zero ha
    · simp [σ, Equiv.sumCongr_apply, Equiv.swap_apply_def, hji, hjk]
  have hw : ((permSp K (Equiv.swap i k) : StatedSp m K) :
      GL (Fin m ⊕ Fin m) K) = TauCeti.permutationGL σ := permSp_coe_GL (Equiv.swap i k)
  rw [glBlockCentralizer, Subgroup.mem_comap]
  change ((permSp K (Equiv.swap i k) : StatedSp m K) : GL (Fin m ⊕ Fin m) K) ∈
    Subgroup.centralizer ({(((diagSp K m t : StatedSp m K) :
      GL (Fin m ⊕ Fin m) K))} : Set (GL (Fin m ⊕ Fin m) K)) ⊓
      glFixing (1 - Matrix.diagonal v)
  rw [hw]
  exact permutationGL_mem_block t v hv σ hσt hfix

theorem spSwapSp_mul_permSp_swap_mem_glBlockCentralizer_diagSp {K : Type} [Field K] [CharP K 2]
    {m : ℕ} (t : Fin m → Kˣ)
    (v : Fin m ⊕ Fin m → K) (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hsym : ∀ a, v a = v (Equiv.sumComm (Fin m) (Fin m) a))
    {i k : Fin m} (hik : t k = (t i)⁻¹)
    (hi : v (Sum.inl i) = 1) (hk : v (Sum.inl k) = 1) :
    TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) ∈
      glBlockCentralizer (StatedSp m K).subtype
        ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
          Set (GL (Fin m ⊕ Fin m) K)) (Matrix.diagonal v) := by
  classical
  let σ : Equiv.Perm (Fin m ⊕ Fin m) :=
    TableBSymp.pairSwap i * TableBSymp.pairSwap k *
      Equiv.sumCongr (Equiv.swap i k) (Equiv.swap i k)
  have hσt : ∀ a, diagSpEntry t (σ a) = diagSpEntry t a := by
    intro a
    rcases a with j | j <;> by_cases hji : j = i <;> by_cases hjk : j = k
    · subst hji; subst hjk
      simp [σ, TableBSymp.pairSwap]
    · subst hji
      simp [σ, Equiv.Perm.mul_apply, TableBSymp.pairSwap, Equiv.sumCongr_apply,
        Equiv.swap_apply_def, Ne.symm hjk, hik]
    · subst hjk
      simp [σ, Equiv.Perm.mul_apply, TableBSymp.pairSwap, Equiv.sumCongr_apply,
        Equiv.swap_apply_def, Ne.symm hji, hik]
    · simp [σ, Equiv.Perm.mul_apply, TableBSymp.pairSwap, Equiv.sumCongr_apply,
        Equiv.swap_apply_def, hji, hjk]
    · subst hji; subst hjk
      simp [σ, TableBSymp.pairSwap]
    · subst hji
      simp [σ, Equiv.Perm.mul_apply, TableBSymp.pairSwap, Equiv.sumCongr_apply,
        Equiv.swap_apply_def, Ne.symm hjk, hik]
    · subst hjk
      simp [σ, Equiv.Perm.mul_apply, TableBSymp.pairSwap, Equiv.sumCongr_apply,
        Equiv.swap_apply_def, Ne.symm hji, hik]
    · simp [σ, Equiv.Perm.mul_apply, TableBSymp.pairSwap, Equiv.sumCongr_apply,
        Equiv.swap_apply_def, hji, hjk]
  have hfix : ∀ a, v a = 0 → σ a = a := by
    have hii := support_inr_of v hsym hi
    have hkk := support_inr_of v hsym hk
    intro a ha
    rcases a with j | j <;> by_cases hji : j = i <;> by_cases hjk : j = k
    · subst hji; exfalso; rw [hi] at ha; exact one_ne_zero ha
    · subst hji; exfalso; rw [hi] at ha; exact one_ne_zero ha
    · subst hjk; exfalso; rw [hk] at ha; exact one_ne_zero ha
    · simp [σ, Equiv.Perm.mul_apply, TableBSymp.pairSwap, Equiv.sumCongr_apply,
        Equiv.swap_apply_def, hji, hjk]
    · subst hji; exfalso; rw [hii] at ha; exact one_ne_zero ha
    · subst hji; exfalso; rw [hii] at ha; exact one_ne_zero ha
    · subst hjk; exfalso; rw [hkk] at ha; exact one_ne_zero ha
    · simp [σ, Equiv.Perm.mul_apply, TableBSymp.pairSwap, Equiv.sumCongr_apply,
        Equiv.swap_apply_def, hji, hjk]
  have hw : ((TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) :
      StatedSp m K) : GL (Fin m ⊕ Fin m) K) = TauCeti.permutationGL σ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, TableBSymp.spSwapSp_coe,
      TableBSymp.spSwapSp_coe, permSp_coe_GL]
    rw [← map_mul, ← map_mul]
  rw [glBlockCentralizer, Subgroup.mem_comap]
  change ((TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) :
      StatedSp m K) : GL (Fin m ⊕ Fin m) K) ∈
    Subgroup.centralizer ({(((diagSp K m t : StatedSp m K) :
      GL (Fin m ⊕ Fin m) K))} : Set (GL (Fin m ⊕ Fin m) K)) ⊓
      glFixing (1 - Matrix.diagonal v)
  rw [hw]
  exact permutationGL_mem_block t v hv σ hσt hfix

theorem commutator_diagSp_mulSingle_permSp_swap {K : Type} [Field K] {m : ℕ}
    (i k : Fin m) (ζ : Kˣ) :
    ⁅diagSp K m (Pi.mulSingle i ζ), permSp K (Equiv.swap i k)⁆ =
      diagSp K m (Pi.mulSingle i ζ * Pi.mulSingle k ζ⁻¹) := by
  have hconj : permSp K (Equiv.swap i k) * diagSp K m (Pi.mulSingle i ζ) *
      (permSp K (Equiv.swap i k))⁻¹ = diagSp K m (Pi.mulSingle k ζ) := by
    rw [conj_permSp_diagSp, mulSingle_comp_symm, Equiv.swap_apply_left]
  have hinv : permSp K (Equiv.swap i k) * (diagSp K m (Pi.mulSingle i ζ))⁻¹ *
      (permSp K (Equiv.swap i k))⁻¹ = (diagSp K m (Pi.mulSingle k ζ))⁻¹ := by
    rw [← hconj]; group
  rw [commutatorElement_def]
  have h1 : diagSp K m (Pi.mulSingle i ζ) * permSp K (Equiv.swap i k) *
      (diagSp K m (Pi.mulSingle i ζ))⁻¹ * (permSp K (Equiv.swap i k))⁻¹ =
      diagSp K m (Pi.mulSingle i ζ) *
        (permSp K (Equiv.swap i k) * (diagSp K m (Pi.mulSingle i ζ))⁻¹ *
          (permSp K (Equiv.swap i k))⁻¹) := by group
  rw [h1, hinv, ← map_inv, ← map_mul]
  congr 1
  rw [← Pi.mulSingle_inv]

theorem commutator_diagSp_mulSingle_spSwapSp_permSp_swap {K : Type} [Field K] [CharP K 2]
    {m : ℕ} (i k : Fin m)
    (hikne : i ≠ k) (ζ : Kˣ) :
    ⁅diagSp K m (Pi.mulSingle i ζ),
      TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k)⁆ =
      diagSp K m (Pi.mulSingle i ζ * Pi.mulSingle k ζ) := by
  have hP : permSp K (Equiv.swap i k) * diagSp K m (Pi.mulSingle i ζ) *
      (permSp K (Equiv.swap i k))⁻¹ = diagSp K m (Pi.mulSingle k ζ) := by
    rw [conj_permSp_diagSp, mulSingle_comp_symm, Equiv.swap_apply_left]
  have hk : TableBSymp.spSwapSp k * diagSp K m (Pi.mulSingle k ζ) *
      (TableBSymp.spSwapSp k)⁻¹ = diagSp K m (Pi.mulSingle k ζ⁻¹) := by
    rw [spSwapSp_conj_diagSp]
    congr 1
    funext a
    by_cases ha : a = k <;> simp [Function.update, ha]
  have hi : TableBSymp.spSwapSp i * diagSp K m (Pi.mulSingle k ζ⁻¹) *
      (TableBSymp.spSwapSp i)⁻¹ = diagSp K m (Pi.mulSingle k ζ⁻¹) := by
    rw [spSwapSp_conj_diagSp]
    congr 1
    funext a
    by_cases ha : a = i
    · subst ha
      simp [Function.update, Pi.mulSingle_eq_of_ne hikne]
    · simp [Function.update, ha]
  have hconj : TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) *
      diagSp K m (Pi.mulSingle i ζ) *
      (TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k))⁻¹ =
      diagSp K m (Pi.mulSingle k ζ⁻¹) := by
    calc TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) *
        diagSp K m (Pi.mulSingle i ζ) *
        (TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k))⁻¹
        = TableBSymp.spSwapSp i * TableBSymp.spSwapSp k *
          (permSp K (Equiv.swap i k) * diagSp K m (Pi.mulSingle i ζ) *
            (permSp K (Equiv.swap i k))⁻¹) *
          (TableBSymp.spSwapSp i * TableBSymp.spSwapSp k)⁻¹ := by group
      _ = TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * diagSp K m (Pi.mulSingle k ζ) *
          (TableBSymp.spSwapSp i * TableBSymp.spSwapSp k)⁻¹ := by rw [hP]
      _ = TableBSymp.spSwapSp i * (TableBSymp.spSwapSp k * diagSp K m (Pi.mulSingle k ζ) *
          (TableBSymp.spSwapSp k)⁻¹) * (TableBSymp.spSwapSp i)⁻¹ := by group
      _ = TableBSymp.spSwapSp i * diagSp K m (Pi.mulSingle k ζ⁻¹) *
          (TableBSymp.spSwapSp i)⁻¹ := by rw [hk]
      _ = diagSp K m (Pi.mulSingle k ζ⁻¹) := hi
  have hinv : TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) *
      (diagSp K m (Pi.mulSingle i ζ))⁻¹ *
      (TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k))⁻¹ =
      (diagSp K m (Pi.mulSingle k ζ⁻¹))⁻¹ := by
    rw [← hconj]; group
  rw [commutatorElement_def]
  have h1 : diagSp K m (Pi.mulSingle i ζ) *
      (TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k)) *
      (diagSp K m (Pi.mulSingle i ζ))⁻¹ *
      (TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k))⁻¹ =
      diagSp K m (Pi.mulSingle i ζ) *
        ((TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k)) *
          (diagSp K m (Pi.mulSingle i ζ))⁻¹ *
          (TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k))⁻¹) := by
    group
  rw [h1, hinv, ← map_inv, ← map_mul]
  congr 1
  ext a
  by_cases ha : a = k <;> simp [Pi.mulSingle_apply, ha]

end CFSG.StandardType

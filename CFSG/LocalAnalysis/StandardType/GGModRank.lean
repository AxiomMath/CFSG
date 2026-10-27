module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Localization.Module
public import CFSG.LocalAnalysis.StandardType.GGSpFrameRefl

public section

namespace CFSG.StandardType

private theorem rank_eq_finrank_range_toLin' {F : Type*} [Field F] {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n F) :
    M.rank = Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by
  rw [Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun F m) (Pi.basisFun F n),
    Matrix.toLin_eq_toLin']

private theorem finrank_range_add_finrank_ker_toLin' {F : Type*} [Field F] {n : Type*}
    [Fintype n] [DecidableEq n] (M : Matrix n n F) :
    Module.finrank F (LinearMap.range (Matrix.toLin' M)) +
      Module.finrank F (LinearMap.ker (Matrix.toLin' M)) = Fintype.card n := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  rwa [Module.finrank_fintype_fun_eq_card] at h

private theorem ker_toLin'_add_one_eq_eigenspace_neg_one {F : Type*} [Field F] {n : Type*}
    [Fintype n] [DecidableEq n] (Z : Matrix n n F) :
    LinearMap.ker (Matrix.toLin' (Z + 1)) = Module.End.eigenspace (Matrix.toLin' Z) (-1) := by
  rw [Module.End.eigenspace_def]
  apply congrArg LinearMap.ker
  ext v
  simp [map_add, Matrix.toLin'_one]

private theorem ker_toLin'_sub_one_eq_eigenspace_one {F : Type*} [Field F] {n : Type*}
    [Fintype n] [DecidableEq n] (Z : Matrix n n F) :
    LinearMap.ker (Matrix.toLin' (Z - 1)) = Module.End.eigenspace (Matrix.toLin' Z) 1 := by
  rw [Module.End.eigenspace_def]
  apply congrArg LinearMap.ker
  ext v
  simp [map_sub, Matrix.toLin'_one]

private theorem isCompl_ker_add_one_ker_sub_one {F : Type*} [Field F] {n : Type*}
    [Fintype n] [DecidableEq n] (h2 : (2 : F) ≠ 0) (Z : Matrix n n F) (hZ : Z * Z = 1) :
    IsCompl (LinearMap.ker (Matrix.toLin' (Z + 1))) (LinearMap.ker (Matrix.toLin' (Z - 1))) := by
  have hg : Matrix.toLin' Z * Matrix.toLin' Z = 1 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hZ, Matrix.toLin'_one]
    rfl
  have hcompl := SpFrame.isCompl_eigenspace_one_neg_one (k := F) (V := n → F) h2 hg
  rw [ker_toLin'_add_one_eq_eigenspace_neg_one Z, ker_toLin'_sub_one_eq_eigenspace_one Z]
  exact hcompl.symm

private theorem finrank_ker_add_add_ker_sub {F : Type*} [Field F] {n : Type*}
    [Fintype n] [DecidableEq n] (h2 : (2 : F) ≠ 0) (Z : Matrix n n F) (hZ : Z * Z = 1) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' (Z + 1))) +
      Module.finrank F (LinearMap.ker (Matrix.toLin' (Z - 1))) = Fintype.card n := by
  have hcompl := isCompl_ker_add_one_ker_sub_one h2 Z hZ
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rwa [Module.finrank_fintype_fun_eq_card] at hsum

private theorem linearIndependent_rat_of_zmod_linearIndependent {p : ℕ} (hp : p.Prime)
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] {w : ι → (n → ℤ)}
    (h : LinearIndependent (ZMod p) (fun i => fun a => (w i a : ZMod p))) :
    LinearIndependent ℚ (fun i => fun a => (w i a : ℚ)) := by
  rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hgi
  have hrel : ∑ j ∈ s, g j • w j = 0 := by
    funext a
    have hthis := congrFun hg a
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hthis
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    exact_mod_cast (show ((∑ j ∈ s, g j * w j a : ℤ) : ℚ) = 0 by
      push_cast
      simpa using hthis)
  obtain ⟨g', hg', hgcd⟩ := Finset.extract_gcd (s := s) g ⟨i, hi⟩
  have hrel' : ∑ j ∈ s, g' j • w j = 0 := by
    have hgg : ∑ j ∈ s, g j • w j = s.gcd g • (∑ j ∈ s, g' j • w j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hg' j hj, smul_smul]
    rw [hgg] at hrel
    have hgne : s.gcd g ≠ 0 := by
      intro h0
      exact hgi (by have := (Finset.gcd_eq_zero_iff.mp h0) i hi; simpa using this)
    exact (smul_eq_zero.mp hrel).resolve_left hgne
  have hrelmod : ∑ j ∈ s, (g' j : ZMod p) • (fun a => (w j a : ZMod p)) = 0 := by
    funext a
    have hthis := congrFun (congrArg (fun v : n → ℤ => fun a => (v a : ZMod p)) hrel') a
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hthis ⊢
    push_cast
    simpa using hthis
  have hex : ∃ j ∈ s, (g' j : ZMod p) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hdvd : ∀ j ∈ s, (p : ℤ) ∣ g' j := by
      intro j hj
      have hj0 : ((g' j : ZMod p) = 0) := hcon j hj
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj0
    have hpg : (p : ℤ) ∣ s.gcd g' := Finset.dvd_gcd hdvd
    rw [hgcd] at hpg
    have h1 : (p : ℤ) ∣ (1 : ℤ) := by simpa using hpg
    have : p ∣ 1 := by exact_mod_cast h1
    exact hp.not_dvd_one this
  obtain ⟨j, hj, hjne⟩ := hex
  exact hjne ((linearIndependent_iff'.mp h) s (fun j => (g' j : ZMod p)) hrelmod j hj)

private theorem rank_map_zmod_le_rank_map_rat {p : ℕ} (hp : p.Prime)
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (X : Matrix m n ℤ) :
    (X.map (Int.castRingHom (ZMod p))).rank ≤ (X.map (Int.castRingHom ℚ)).rank := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let Xp := X.map (Int.castRingHom (ZMod p))
  let Xq := X.map (Int.castRingHom ℚ)
  let s : Set (m → ZMod p) := Set.range Xp.col
  let W : Submodule (ZMod p) (m → ZMod p) := Submodule.span (ZMod p) s
  haveI hfinW : Module.Finite (ZMod p) W := by
    haveI : Module.Finite (ZMod p) (m → ZMod p) := inferInstance
    exact Module.Finite.of_injective W.subtype W.subtype_injective
  let k := Module.finrank (ZMod p) W
  obtain ⟨f, hf_mem, _hf_span, hf_ind⟩ :=
    @Submodule.exists_fun_fin_finrank_span_eq (ZMod p) (m → ZMod p)
      (inferInstance : DivisionRing (ZMod p)) (inferInstance : AddCommGroup (m → ZMod p))
      (inferInstance : Module (ZMod p) (m → ZMod p)) s hfinW
  choose σ hσ using hf_mem
  let w : Fin k → (m → ℤ) := fun i => X.col (σ i)
  have hfp : f = (fun i => fun a => (w i a : ZMod p)) := by
    funext i a
    have h1 := hσ i
    rw [← h1]
    simp [Xp, w, Matrix.col_apply]
  rw [hfp] at hf_ind
  have hindq : LinearIndependent ℚ (fun i => fun a => (w i a : ℚ)) :=
    linearIndependent_rat_of_zmod_linearIndependent hp hf_ind
  have hfun : (fun i => fun a => (w i a : ℚ)) = Xq.col ∘ σ := by
    funext i a
    show (X a (σ i) : ℚ) = Xq a (σ i)
    rfl
  rw [hfun] at hindq
  have hk_le : k ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range Xq.col)) := by
    have hcard := finrank_span_eq_card hindq
    have hle : Submodule.span ℚ (Set.range (Xq.col ∘ σ)) ≤
        Submodule.span ℚ (Set.range Xq.col) := by
      apply Submodule.span_mono
      rintro y ⟨i, rfl⟩
      exact ⟨σ i, rfl⟩
    calc k = Fintype.card (Fin k) := (Fintype.card_fin k).symm
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range (Xq.col ∘ σ))) := hcard.symm
      _ ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range Xq.col)) := Submodule.finrank_mono hle
  rw [Matrix.rank_eq_finrank_span_cols Xp, Matrix.rank_eq_finrank_span_cols Xq]
  exact hk_le

theorem ggFinrankKerAddOne_zmod_eq_rat {n : Type} [Fintype n] [DecidableEq n] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (X : Matrix n n ℤ) (hX : X * X = 1) :
    Module.finrank (ZMod p)
        (LinearMap.ker (Matrix.toLin' (X.map (Int.castRingHom (ZMod p)) + 1))) =
      Module.finrank ℚ (LinearMap.ker (Matrix.toLin' (X.map (Int.castRingHom ℚ) + 1))) := by
  classical
  let f : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let g : ℤ →+* ℚ := Int.castRingHom ℚ
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have h2q : (2 : ℚ) ≠ 0 := by norm_num
  have hXf : (X.map f) * (X.map f) = 1 := by
    rw [← RingHom.mapMatrix_apply f X, ← map_mul, hX, map_one]
  have hXg : (X.map g) * (X.map g) = 1 := by
    rw [← RingHom.mapMatrix_apply g X, ← map_mul, hX, map_one]
  have hPmap_f : X.map f + 1 = (X + 1).map f := by
    rw [Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f)]
  have hPmap_g : X.map g + 1 = (X + 1).map g := by
    rw [Matrix.map_add g (map_add g), Matrix.map_one g (map_zero g) (map_one g)]
  have hNmap_f : X.map f - 1 = (X - 1).map f := by
    rw [Matrix.map_sub f (map_sub f), Matrix.map_one f (map_zero f) (map_one f)]
  have hNmap_g : X.map g - 1 = (X - 1).map g := by
    rw [Matrix.map_sub g (map_sub g), Matrix.map_one g (map_zero g) (map_one g)]
  have hplus_le : Module.finrank (ZMod p)
        (LinearMap.range (Matrix.toLin' (X.map f + 1))) ≤
      Module.finrank ℚ (LinearMap.range (Matrix.toLin' (X.map g + 1))) := by
    have hb := rank_map_zmod_le_rank_map_rat (Fact.out : p.Prime) (X + 1)
    rw [rank_eq_finrank_range_toLin'] at hb
    rw [← hPmap_f, ← hPmap_g] at hb
    exact hb
  have hminus_le : Module.finrank (ZMod p)
        (LinearMap.range (Matrix.toLin' (X.map f - 1))) ≤
      Module.finrank ℚ (LinearMap.range (Matrix.toLin' (X.map g - 1))) := by
    have hb := rank_map_zmod_le_rank_map_rat (Fact.out : p.Prime) (X - 1)
    rw [rank_eq_finrank_range_toLin'] at hb
    rw [← hNmap_f, ← hNmap_g] at hb
    exact hb
  have hdec_p := finrank_ker_add_add_ker_sub h2p (X.map f) hXf
  have hdec_q := finrank_ker_add_add_ker_sub h2q (X.map g) hXg
  have hrn_plus_p := finrank_range_add_finrank_ker_toLin' (X.map f + 1)
  have hrn_plus_q := finrank_range_add_finrank_ker_toLin' (X.map g + 1)
  have hrn_minus_p := finrank_range_add_finrank_ker_toLin' (X.map f - 1)
  have hrn_minus_q := finrank_range_add_finrank_ker_toLin' (X.map g - 1)
  show Module.finrank (ZMod p) (LinearMap.ker (Matrix.toLin' (X.map f + 1))) =
      Module.finrank ℚ (LinearMap.ker (Matrix.toLin' (X.map g + 1)))
  omega

end CFSG.StandardType

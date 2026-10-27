module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTriplePair
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleGramDefs
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Int.CharZero
public import Mathlib.Algebra.Group.Submonoid.Pointwise

public section

namespace CFSG.StandardType.CoxTriple

open CFSG.LieType.RootSystem
open Matrix

private noncomputable def ct_em_ratExt {I : Type} [Fintype I] [DecidableEq I]
    (f : Module.End ℤ (I → ℤ)) : Module.End ℚ (I → ℚ) :=
  Matrix.toLin' ((Int.castRingHom ℚ).mapMatrix (LinearMap.toMatrix' f))

private theorem ct_em_ratExt_toRat {I : Type} [Fintype I] [DecidableEq I]
    (f : Module.End ℤ (I → ℤ)) (v : I → ℤ) :
    ct_em_ratExt f (toRat v) = toRat (f v) := by
  funext k
  rw [ct_em_ratExt, Matrix.toLin'_apply, toRat_apply, ← LinearMap.toMatrix'_mulVec f v]
  simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, toRat_apply]
  push_cast
  rfl

private theorem ct_em_ratExt_mul {I : Type} [Fintype I] [DecidableEq I]
    (f g : Module.End ℤ (I → ℤ)) :
    ct_em_ratExt (f * g) = ct_em_ratExt f * ct_em_ratExt g := by
  rw [ct_em_ratExt, ct_em_ratExt, ct_em_ratExt, LinearMap.toMatrix'_mul, map_mul,
    Matrix.toLin'_mul, Module.End.mul_eq_comp]

private theorem ct_em_ratExt_one {I : Type} [Fintype I] [DecidableEq I] :
    ct_em_ratExt (1 : Module.End ℤ (I → ℤ)) = 1 := by
  rw [ct_em_ratExt, LinearMap.toMatrix'_one, map_one, Matrix.toLin'_one,
    Module.End.one_eq_id]

private noncomputable def ct_em_W {I : Type} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C) :
    (coxeterMatrix hC).Group →* Module.End ℚ (I → ℚ) where
  toFun h := ct_em_ratExt (weylAction hC h)
  map_one' := by rw [map_one, ct_em_ratExt_one]
  map_mul' h g := by rw [map_mul, ct_em_ratExt_mul]

private noncomputable def ct_em_refl {I : Type} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C) (w : I → ℚ) : Module.End ℚ (I → ℚ) where
  toFun x := x - (2 * form hC x w / form hC w w) • w
  map_add' x y := by
    have h : 2 * form hC (x + y) w / form hC w w =
        2 * form hC x w / form hC w w + 2 * form hC y w / form hC w w := by
      simp only [map_add, LinearMap.add_apply]; ring
    rw [h, add_smul]; abel
  map_smul' a x := by
    have h : 2 * form hC (a • x) w / form hC w w =
        a * (2 * form hC x w / form hC w w) := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
    rw [h, smul_sub, smul_smul]; simp

private theorem ct_em_gram_basic {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (N : Matrix (Fin 3) (Fin 3) ℤ) (c : ℚ) (ε : Fin 3 → ℚ) (hc : 0 < c)
    (hε : ∀ k, ε k = 1 ∨ ε k = -1) (hN : AdmGram N)
    (hgram : ∀ k l : Fin 3, (N k l : ℚ) * c =
      ε k * ε l * form hC (toRat (coxRoot hC (g k) (i k)))
        (toRat (coxRoot hC (g l) (i l)))) :
    (∀ k : Fin 3, N k k = 2 ∨ N k k = 4) ∧
    (∀ k : Fin 3, (N k k : ℚ) ≠ 0) ∧
    (∀ k : Fin 3, ε k * ε k = 1) ∧
    (∀ k l : Fin 3, form hC (ε k • toRat (coxRoot hC (g k) (i k)))
        (ε l • toRat (coxRoot hC (g l) (i l))) = (N k l : ℚ) * c) ∧
    (∀ k : Fin 3, form hC (ε k • toRat (coxRoot hC (g k) (i k)))
        (ε k • toRat (coxRoot hC (g k) (i k))) ≠ 0) ∧
    (Matrix.of fun k l : Fin 3 =>
      form hC (ε k • toRat (coxRoot hC (g k) (i k)))
        (ε l • toRat (coxRoot hC (g l) (i l)))).det ≠ 0 := by
  classical
  obtain ⟨hNsym, hN00, hN11, hN22, hN01, hNdiv, hNprod, hNp01, hNp02, hNp12, hNdet⟩ := hN
  have hdiag : ∀ k : Fin 3, N k k = 2 ∨ N k k = 4 := by
    intro k
    fin_cases k
    · exact hN00
    · show N 1 1 = 2 ∨ N 1 1 = 4
      rw [hN11]; exact hN00
    · exact hN22
  have hNkk_ne : ∀ k : Fin 3, (N k k : ℚ) ≠ 0 := by
    intro k
    rcases hdiag k with h | h <;> rw [h] <;> norm_num
  have hε_sq : ∀ k : Fin 3, ε k * ε k = 1 := by
    intro k
    rcases hε k with h | h <;> rw [h] <;> norm_num
  have hgramB : ∀ k l : Fin 3, form hC (ε k • toRat (coxRoot hC (g k) (i k)))
      (ε l • toRat (coxRoot hC (g l) (i l))) = (N k l : ℚ) * c := by
    intro k l
    rw [show form hC (ε k • toRat (coxRoot hC (g k) (i k)))
        (ε l • toRat (coxRoot hC (g l) (i l))) =
        ε k * ε l * form hC (toRat (coxRoot hC (g k) (i k)))
          (toRat (coxRoot hC (g l) (i l))) by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring]
    exact (hgram k l).symm
  have hBkk_ne : ∀ k : Fin 3, form hC (ε k • toRat (coxRoot hC (g k) (i k)))
      (ε k • toRat (coxRoot hC (g k) (i k))) ≠ 0 := by
    intro k
    rw [hgramB k k]
    exact mul_ne_zero (by exact_mod_cast hNkk_ne k) (ne_of_gt hc)
  refine ⟨hdiag, hNkk_ne, hε_sq, hgramB, hBkk_ne, ?_⟩
  have hcast (k l : Fin 3) :
      (Int.castRingHom ℚ).mapMatrix N k l = (N k l : ℚ) := rfl
  have hG : (Matrix.of fun k l : Fin 3 =>
      form hC (ε k • toRat (coxRoot hC (g k) (i k)))
        (ε l • toRat (coxRoot hC (g l) (i l)))) =
      c • (Int.castRingHom ℚ).mapMatrix N := by
    ext k l
    show form hC (ε k • toRat (coxRoot hC (g k) (i k)))
        (ε l • toRat (coxRoot hC (g l) (i l))) =
      c * (Int.castRingHom ℚ).mapMatrix N k l
    rw [hgramB k l, hcast k l, mul_comm]
  rw [hG, Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det]
  exact mul_ne_zero (pow_ne_zero 3 (ne_of_gt hc))
    (by change ((N.det : ℤ) : ℚ) ≠ 0; rw [Int.cast_ne_zero]; exact ne_of_gt hNdet)

private theorem ct_em_coeff_basic {I : Type} [Fintype I] [DecidableEq I]
    (e : Fin 3 → I → ℚ) (B : LinearMap.BilinForm ℚ (I → ℚ))
    (G : Matrix (Fin 3) (Fin 3) ℚ) (coeff : (I → ℚ) → (Fin 3 → ℚ))
    (proj : (I → ℚ) → (I → ℚ))
    (hG : ∀ k l, G k l = B (e k) (e l)) (hdet : G.det ≠ 0)
    (hcoeff : ∀ x, coeff x = G⁻¹ *ᵥ (fun m => B (e m) x))
    (hproj : ∀ x, proj x = ∑ l, coeff x l • e l) :
    (∀ j : Fin 3, coeff (e j) = Pi.single j 1) ∧
    (∀ x y : I → ℚ, coeff (x + y) = coeff x + coeff y) ∧
    (∀ (a : ℚ) (x : I → ℚ), coeff (a • x) = a • coeff x) ∧
    (∀ x : I → ℚ, proj x ∈ Submodule.span ℚ (Set.range e)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    rw [hcoeff (e j)]
    have hb : (fun m => B (e m) (e j)) = G *ᵥ (Pi.single j (1 : ℚ)) := by
      rw [Matrix.mulVec_single_one]
      ext m
      exact (hG m j).symm
    rw [hb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  · intro x y
    rw [hcoeff (x + y), hcoeff x, hcoeff y]
    rw [show (fun m => B (e m) (x + y)) = (fun m => B (e m) x) + (fun m => B (e m) y) by
      ext m; simp]
    rw [Matrix.mulVec_add]
  · intro a x
    rw [hcoeff (a • x), hcoeff x]
    rw [show (fun m => B (e m) (a • x)) = a • (fun m => B (e m) x) by
      ext m; simp]
    rw [Matrix.mulVec_smul]
  · intro x
    rw [hproj x]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self l))

private theorem ct_em_proj_self {I : Type} [Fintype I] [DecidableEq I]
    (e : Fin 3 → I → ℚ) (coeff : (I → ℚ) → (Fin 3 → ℚ)) (proj : (I → ℚ) → (I → ℚ))
    (hcoeff_single : ∀ j : Fin 3, coeff (e j) = Pi.single j 1)
    (hcoeff_add : ∀ x y : I → ℚ, coeff (x + y) = coeff x + coeff y)
    (hcoeff_smul : ∀ (a : ℚ) (x : I → ℚ), coeff (a • x) = a • coeff x)
    (hproj : ∀ x, proj x = ∑ l, coeff x l • e l) :
    ∀ x ∈ Submodule.span ℚ (Set.range e), proj x = x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [hproj (e j), hcoeff_single j]
      simp
  | zero =>
      rw [hproj 0]
      have h0 : coeff (0 : I → ℚ) = 0 := by
        have h := hcoeff_smul 0 (0 : I → ℚ)
        simpa using h
      simp [h0]
  | add y z hy hz ihy ihz =>
      have ihy' : (∑ l, coeff y l • e l) = y := by rw [← hproj y]; exact ihy
      have ihz' : (∑ l, coeff z l • e l) = z := by rw [← hproj z]; exact ihz
      rw [hproj (y + z), hcoeff_add y z]
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      rw [ihy', ihz']
  | smul a y hy ihy =>
      have ihy' : (∑ l, coeff y l • e l) = y := by rw [← hproj y]; exact ihy
      rw [hproj (a • y), hcoeff_smul a y]
      simp only [Pi.smul_apply]
      conv_rhs => rw [← ihy', Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_eq_mul, mul_smul]

private theorem ct_em_proj_orth_sup {I : Type} [Fintype I] [DecidableEq I]
    (e : Fin 3 → I → ℚ) (B : LinearMap.BilinForm ℚ (I → ℚ))
    (G : Matrix (Fin 3) (Fin 3) ℚ) (coeff : (I → ℚ) → (Fin 3 → ℚ))
    (proj : (I → ℚ) → (I → ℚ))
    (hG : ∀ k l, G k l = B (e k) (e l)) (hdet : G.det ≠ 0)
    (hcoeff : ∀ x, coeff x = G⁻¹ *ᵥ (fun m => B (e m) x))
    (hproj : ∀ x, proj x = ∑ l, coeff x l • e l)
    (hproj_mem : ∀ x, proj x ∈ Submodule.span ℚ (Set.range e)) :
    (∀ (x : I → ℚ) (m : Fin 3), B (e m) (x - proj x) = 0) ∧
    Submodule.span ℚ (Set.range e) ⊔ B.orthogonal (Submodule.span ℚ (Set.range e)) = ⊤ := by
  have horth : ∀ (x : I → ℚ) (m : Fin 3), B (e m) (x - proj x) = 0 := by
    intro x m
    rw [map_sub]
    have h1 : B (e m) (proj x) = (G *ᵥ coeff x) m := by
      rw [hproj x, Matrix.mulVec_apply_eq_sum]
      simp only [map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hG m l]
      ring
    rw [h1]
    have h2 : G *ᵥ coeff x = fun m => B (e m) x := by
      rw [hcoeff x, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
    rw [h2, sub_self]
  refine ⟨horth, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : x = proj x + (x - proj x) := by abel
  rw [hx]
  refine Submodule.add_mem_sup (hproj_mem x) ?_
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  induction hn using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact horth x j
  | zero => simp
  | add y z hy hz ihy ihz => simp [map_add, ihy, ihz]
  | smul a y hy ihy => simp [map_smul, ihy]

private theorem ct_em_W_tk {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (ε : Fin 3 → ℚ) (hε_sq : ∀ k : Fin 3, ε k * ε k = 1)
    (hBkk_ne : ∀ k : Fin 3, form hC (ε k • toRat (coxRoot hC (g k) (i k)))
      (ε k • toRat (coxRoot hC (g k) (i k))) ≠ 0) :
    (∀ (k : Fin 3) (v : I → ℤ), ct_em_W hC (coxRefl hC (g k) (i k)) (toRat v) =
      toRat v - coxPairing hC v (coxRoot hC (g k) (i k)) •
        toRat (coxRoot hC (g k) (i k))) ∧
    (∀ k l : Fin 3, ct_em_W hC (coxRefl hC (g k) (i k))
        (ε l • toRat (coxRoot hC (g l) (i l))) =
      ε l • toRat (coxRoot hC (g l) (i l)) -
        (2 * form hC (ε l • toRat (coxRoot hC (g l) (i l)))
          (ε k • toRat (coxRoot hC (g k) (i k))) /
        form hC (ε k • toRat (coxRoot hC (g k) (i k)))
          (ε k • toRat (coxRoot hC (g k) (i k)))) •
        (ε k • toRat (coxRoot hC (g k) (i k)))) := by
  let t : Fin 3 → (coxeterMatrix hC).Group := fun k => coxRefl hC (g k) (i k)
  let r : Fin 3 → I → ℤ := fun k => coxRoot hC (g k) (i k)
  let e : Fin 3 → I → ℚ := fun k => ε k • toRat (r k)
  let B : LinearMap.BilinForm ℚ (I → ℚ) := form hC
  let W : (coxeterMatrix hC).Group →* Module.End ℚ (I → ℚ) := ct_em_W hC
  change (∀ (k : Fin 3) (v : I → ℤ), W (t k) (toRat v) =
      toRat v - coxPairing hC v (r k) • toRat (r k)) ∧
    (∀ k l : Fin 3, W (t k) (e l) =
      e l - (2 * B (e l) (e k) / B (e k) (e k)) • e k)
  have hW_tk (k : Fin 3) (v : I → ℤ) :
      W (t k) (toRat v) = toRat v - coxPairing hC v (r k) • toRat (r k) := by
    change ct_em_ratExt (weylAction hC (t k)) (toRat v) = _
    rw [ct_em_ratExt_toRat]
    exact toRat_weylAction_coxRefl hC (g k) (i k) v
  refine ⟨hW_tk, ?_⟩
  intro k l
  have hcoef : ε l * coxPairing hC (r l) (r k) =
      (2 * B (e l) (e k) / B (e k) (e k)) * ε k := by
    have hBlk : B (e l) (e k) = ε l * ε k * B (toRat (r l)) (toRat (r k)) := by
      simp only [B, e, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
    have hBkk : B (e k) (e k) = B (toRat (r k)) (toRat (r k)) := by
      rw [show B (e k) (e k) = ε k * ε k * B (toRat (r k)) (toRat (r k)) by
        simp only [B, e, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring]
      rw [hε_sq k, one_mul]
    have hBrr_ne : B (toRat (r k)) (toRat (r k)) ≠ 0 := by
      rw [← hBkk]; exact hBkk_ne k
    simp only [B] at *
    rw [coxPairing, hBlk, hBkk]
    field_simp
    rw [show ε k ^ 2 = 1 by rw [sq, hε_sq k]]
    field_simp
  rw [map_smul, hW_tk k (r l)]
  rw [show e l = ε l • toRat (r l) from rfl, show e k = ε k • toRat (r k) from rfl]
  rw [smul_sub, smul_smul, smul_smul, hcoef]

private theorem ct_em_U_tk {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (e : Fin 3 → I → ℚ)
    (hW_tk_el : ∀ k l : Fin 3, ct_em_W hC (coxRefl hC (g k) (i k)) (e l) =
      e l - (2 * form hC (e l) (e k) / form hC (e k) (e k)) • e k) :
    (∀ k : Fin 3, coxRefl hC (g k) (i k) * coxRefl hC (g k) (i k) = 1) ∧
    (∀ k : Fin 3, (Submodule.span ℚ (Set.range e)).map
        (ct_em_W hC (coxRefl hC (g k) (i k))) = Submodule.span ℚ (Set.range e)) := by
  let t : Fin 3 → (coxeterMatrix hC).Group := fun k => coxRefl hC (g k) (i k)
  let B : LinearMap.BilinForm ℚ (I → ℚ) := form hC
  let U : Submodule ℚ (I → ℚ) := Submodule.span ℚ (Set.range e)
  let W : (coxeterMatrix hC).Group →* Module.End ℚ (I → ℚ) := ct_em_W hC
  change (∀ k : Fin 3, t k * t k = 1) ∧ (∀ k : Fin 3, U.map (W (t k)) = U)
  change (∀ k l : Fin 3, W (t k) (e l) =
    e l - (2 * B (e l) (e k) / B (e k) (e k)) • e k) at hW_tk_el
  have ht_mul_self (k : Fin 3) : t k * t k = 1 := by
    have hss : (coxeterMatrix hC).simple (i k) * (coxeterMatrix hC).simple (i k) = 1 := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple (coxeterMatrix hC)]
      exact CoxeterSystem.simple_mul_simple_self _ (i k)
    show coxRefl hC (g k) (i k) * coxRefl hC (g k) (i k) = 1
    rw [show coxRefl hC (g k) (i k) * coxRefl hC (g k) (i k) =
        g k * ((coxeterMatrix hC).simple (i k) * (coxeterMatrix hC).simple (i k)) *
          (g k)⁻¹ by
      simp only [coxRefl]; group]
    rw [hss, mul_one, mul_inv_cancel]
  refine ⟨ht_mul_self, ?_⟩
  intro k
  have hle : U.map (W (t k)) ≤ U := by
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨l, rfl⟩ := hy
        rw [Submodule.mem_comap, hW_tk_el k l]
        exact Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self l))
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k)))
    | zero => simp
    | add y z hy hz ihy ihz => exact Submodule.add_mem _ ihy ihz
    | smul a y hy ihy => exact Submodule.smul_mem _ a ihy
  refine le_antisymm hle ?_
  calc U = U.map (1 : Module.End ℚ (I → ℚ)) := (Submodule.map_id (p := U)).symm
    _ = U.map (W (t k) * W (t k)) := by rw [← map_mul, ht_mul_self k, map_one]
    _ = (U.map (W (t k))).map (W (t k)) := by
        rw [Module.End.mul_eq_comp (W (t k)) (W (t k)),
          Submodule.map_comp (W (t k)) (W (t k)) U]
    _ ≤ U.map (W (t k)) := Submodule.map_mono hle

private theorem ct_em_hconv {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (ε : Fin 3 → ℚ) (hε_sq : ∀ k : Fin 3, ε k * ε k = 1) :
    ∀ (k : Fin 3) (v : I → ℤ),
      (2 * form hC (toRat v) (ε k • toRat (coxRoot hC (g k) (i k))) /
        form hC (ε k • toRat (coxRoot hC (g k) (i k)))
          (ε k • toRat (coxRoot hC (g k) (i k)))) •
        (ε k • toRat (coxRoot hC (g k) (i k))) =
      coxPairing hC v (coxRoot hC (g k) (i k)) • toRat (coxRoot hC (g k) (i k)) := by
  let r : Fin 3 → I → ℤ := fun k => coxRoot hC (g k) (i k)
  let e : Fin 3 → I → ℚ := fun k => ε k • toRat (r k)
  let B : LinearMap.BilinForm ℚ (I → ℚ) := form hC
  change ∀ (k : Fin 3) (v : I → ℤ),
    (2 * B (toRat v) (e k) / B (e k) (e k)) • e k = coxPairing hC v (r k) • toRat (r k)
  intro k v
  have hB1 : B (toRat v) (e k) = ε k * B (toRat v) (toRat (r k)) := by
    rw [show e k = ε k • toRat (r k) from rfl, map_smul, smul_eq_mul]
  have hB2 : B (e k) (e k) = B (toRat (r k)) (toRat (r k)) := by
    rw [show B (e k) (e k) = ε k * ε k * B (toRat (r k)) (toRat (r k)) by
      rw [show e k = ε k • toRat (r k) from rfl]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring]
    rw [hε_sq k, one_mul]
  rw [coxPairing, hB1, hB2, show e k = ε k • toRat (r k) from rfl, smul_smul]
  congr 1
  field_simp
  rw [show ε k ^ 2 = 1 by rw [sq, hε_sq k]]
  ring

private theorem ct_em_W_tk_eq {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (ε : Fin 3 → ℚ)
    (hW_tk_toRat : ∀ (k : Fin 3) (v : I → ℤ),
      ct_em_W hC (coxRefl hC (g k) (i k)) (toRat v) =
        toRat v - coxPairing hC v (coxRoot hC (g k) (i k)) •
          toRat (coxRoot hC (g k) (i k)))
    (hconv : ∀ (k : Fin 3) (v : I → ℤ),
      (2 * form hC (toRat v) (ε k • toRat (coxRoot hC (g k) (i k))) /
        form hC (ε k • toRat (coxRoot hC (g k) (i k)))
          (ε k • toRat (coxRoot hC (g k) (i k)))) •
        (ε k • toRat (coxRoot hC (g k) (i k))) =
      coxPairing hC v (coxRoot hC (g k) (i k)) • toRat (coxRoot hC (g k) (i k))) :
    ∀ k : Fin 3, ct_em_W hC (coxRefl hC (g k) (i k)) =
      ct_em_refl hC (ε k • toRat (coxRoot hC (g k) (i k))) := by
  let t : Fin 3 → (coxeterMatrix hC).Group := fun k => coxRefl hC (g k) (i k)
  let r : Fin 3 → I → ℤ := fun k => coxRoot hC (g k) (i k)
  let e : Fin 3 → I → ℚ := fun k => ε k • toRat (r k)
  let B : LinearMap.BilinForm ℚ (I → ℚ) := form hC
  let W : (coxeterMatrix hC).Group →* Module.End ℚ (I → ℚ) := ct_em_W hC
  change ∀ k : Fin 3, W (t k) = ct_em_refl hC (e k)
  change (∀ (k : Fin 3) (v : I → ℤ), W (t k) (toRat v) =
    toRat v - coxPairing hC v (r k) • toRat (r k)) at hW_tk_toRat
  change (∀ (k : Fin 3) (v : I → ℤ),
    (2 * B (toRat v) (e k) / B (e k) (e k)) • e k =
      coxPairing hC v (r k) • toRat (r k)) at hconv
  intro k
  refine (Pi.basisFun ℚ I).ext fun i => ?_
  rw [Pi.basisFun_apply]
  rw [show (Pi.single i (1 : ℚ) : I → ℚ) = toRat (Pi.single i (1 : ℤ)) from
    (toRat_single i).symm]
  rw [hW_tk_toRat k (Pi.single i (1 : ℤ))]
  have hc := hconv k (Pi.single i (1 : ℤ))
  change toRat (Pi.single i (1 : ℤ)) -
      coxPairing hC (Pi.single i (1 : ℤ)) (r k) • toRat (r k) =
    toRat (Pi.single i (1 : ℤ)) - (2 * B (toRat (Pi.single i (1 : ℤ))) (e k) /
      B (e k) (e k)) • e k
  rw [← hc]

private theorem ct_em_hfix_orth {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (e : Fin 3 → I → ℚ)
    (hW_tk_eq : ∀ k : Fin 3, ct_em_W hC (coxRefl hC (g k) (i k)) =
      ct_em_refl hC (e k)) :
    (∀ (k : Fin 3) {x : I → ℚ},
      x ∈ (form hC).orthogonal (Submodule.span ℚ (Set.range e)) →
      ct_em_refl hC (e k) x = x) ∧
    (∀ h ∈ Subgroup.closure ({coxRefl hC (g 0) (i 0), coxRefl hC (g 1) (i 1),
      coxRefl hC (g 2) (i 2)} : Set (coxeterMatrix hC).Group),
      ∀ x ∈ (form hC).orthogonal (Submodule.span ℚ (Set.range e)),
        ct_em_W hC h x = x) := by
  let t : Fin 3 → (coxeterMatrix hC).Group := fun k => coxRefl hC (g k) (i k)
  let B : LinearMap.BilinForm ℚ (I → ℚ) := form hC
  let U : Submodule ℚ (I → ℚ) := Submodule.span ℚ (Set.range e)
  let S : Set (coxeterMatrix hC).Group := {t 0, t 1, t 2}
  let H : Subgroup (coxeterMatrix hC).Group := Subgroup.closure S
  let W : (coxeterMatrix hC).Group →* Module.End ℚ (I → ℚ) := ct_em_W hC
  change (∀ (k : Fin 3) {x : I → ℚ}, x ∈ B.orthogonal U → ct_em_refl hC (e k) x = x) ∧
    (∀ h ∈ H, ∀ x ∈ B.orthogonal U, W h x = x)
  change (∀ k : Fin 3, W (t k) = ct_em_refl hC (e k)) at hW_tk_eq
  have hrefl_mem (k : Fin 3) {x : I → ℚ} (hx : x ∈ B.orthogonal U) :
      ct_em_refl hC (e k) x = x := by
    have hke : B x (e k) = 0 := by
      change form hC x (e k) = 0
      rw [form_comm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) (e k)
        (Submodule.subset_span (Set.mem_range_self k))
    change x - (2 * B x (e k) / B (e k) (e k)) • e k = x
    rw [hke]; simp
  have hfix_gen (k : Fin 3) : ∀ x ∈ B.orthogonal U, W (t k) x = x :=
    fun x hx => by rw [hW_tk_eq k, hrefl_mem k hx]
  refine ⟨hrefl_mem, ?_⟩
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem y hy =>
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact hfix_gen 0
      · exact hfix_gen 1
      · exact hfix_gen 2
  | one => intro x hx; rw [map_one, Module.End.one_apply]
  | mul y z hy hz ihy ihz =>
      intro x hx
      rw [map_mul, Module.End.mul_apply, ihz x hx, ihy x hx]
  | inv y hy ihy =>
      intro x hx
      have hinj : Function.Injective (W y) := by
        have hleft : Function.LeftInverse (W y⁻¹) (W y) := by
          intro z
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]
        exact hleft.injective
      have h1 : W y (W y⁻¹ x - x) = W y 0 := by
        rw [map_zero, map_sub, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply, ihy x hx, sub_self]
      exact sub_eq_zero.mp (hinj h1)

private theorem ct_em_hUmap {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (e : Fin 3 → I → ℚ)
    (hUmap_gen : ∀ k : Fin 3, (Submodule.span ℚ (Set.range e)).map
      (ct_em_W hC (coxRefl hC (g k) (i k))) = Submodule.span ℚ (Set.range e)) :
    ∀ h ∈ Subgroup.closure ({coxRefl hC (g 0) (i 0), coxRefl hC (g 1) (i 1),
      coxRefl hC (g 2) (i 2)} : Set (coxeterMatrix hC).Group),
      (Submodule.span ℚ (Set.range e)).map (ct_em_W hC h) =
        Submodule.span ℚ (Set.range e) := by
  let t : Fin 3 → (coxeterMatrix hC).Group := fun k => coxRefl hC (g k) (i k)
  let U : Submodule ℚ (I → ℚ) := Submodule.span ℚ (Set.range e)
  let S : Set (coxeterMatrix hC).Group := {t 0, t 1, t 2}
  let H : Subgroup (coxeterMatrix hC).Group := Subgroup.closure S
  let W : (coxeterMatrix hC).Group →* Module.End ℚ (I → ℚ) := ct_em_W hC
  change ∀ h ∈ H, U.map (W h) = U
  change ∀ k : Fin 3, U.map (W (t k)) = U at hUmap_gen
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem y hy =>
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact hUmap_gen 0
      · exact hUmap_gen 1
      · exact hUmap_gen 2
  | one => rw [map_one, Module.End.one_eq_id, Submodule.map_id]
  | mul y z hy hz ihy ihz =>
      rw [map_mul, Module.End.mul_eq_comp (W y) (W z),
        Submodule.map_comp (W z) (W y) U, ihz, ihy]
  | inv y hy ihy =>
      calc U.map (W y⁻¹) = (U.map (W y)).map (W y⁻¹) := by rw [ihy]
        _ = U.map ((W y⁻¹).comp (W y)) := (Submodule.map_comp (W y) (W y⁻¹) U).symm
        _ = U.map (W y⁻¹ * W y) := by rw [Module.End.mul_eq_comp]
        _ = U.map (W (y⁻¹ * y)) := by rw [← map_mul]
        _ = U.map 1 := by rw [inv_mul_cancel, map_one]
        _ = U := by rw [Module.End.one_eq_id, Submodule.map_id]

private theorem ct_em_coeff_facts {I : Type} [Fintype I] [DecidableEq I]
    (e : Fin 3 → I → ℚ) (B : LinearMap.BilinForm ℚ (I → ℚ))
    (G : Matrix (Fin 3) (Fin 3) ℚ) (coeff : (I → ℚ) → (Fin 3 → ℚ))
    (proj : (I → ℚ) → (I → ℚ))
    (hcoeff : ∀ x, coeff x = G⁻¹ *ᵥ (fun m => B (e m) x))
    (hcoeff_single : ∀ j : Fin 3, coeff (e j) = Pi.single j 1)
    (hcoeff_add : ∀ x y : I → ℚ, coeff (x + y) = coeff x + coeff y)
    (hcoeff_smul : ∀ (a : ℚ) (x : I → ℚ), coeff (a • x) = a • coeff x)
    (hproj_orth : ∀ (x : I → ℚ) (m : Fin 3), B (e m) (x - proj x) = 0) :
    (∀ x y : I → ℚ, coeff (x - y) = coeff x - coeff y) ∧
    (∀ a : Fin 3 → ℚ, coeff (∑ j, a j • e j) = a) ∧
    (∀ z : I → ℚ, z ∈ B.orthogonal (Submodule.span ℚ (Set.range e)) → coeff z = 0) ∧
    (∀ y : I → ℚ, y - proj y ∈ B.orthogonal (Submodule.span ℚ (Set.range e))) := by
  let coeffL : (I → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) :=
    { toFun := coeff, map_add' := hcoeff_add, map_smul' := hcoeff_smul }
  have hcoeffL_apply (x : I → ℚ) : coeffL x = coeff x := rfl
  have hcoeff_sub (x y : I → ℚ) : coeff (x - y) = coeff x - coeff y := by
    change coeffL (x - y) = coeff x - coeff y
    rw [map_sub, hcoeffL_apply, hcoeffL_apply]
  have hcoeff_sum (a : Fin 3 → ℚ) : coeff (∑ j, a j • e j) = a := by
    have h : coeffL (∑ j, a j • e j) = a := by
      rw [map_sum]
      have hs : ∀ j : Fin 3, coeffL (a j • e j) = a j • Pi.single j 1 := by
        intro j; rw [map_smul, hcoeffL_apply, hcoeff_single]
      simp only [hs]
      ext i
      simp [Pi.single_apply]
    exact h
  have hcoeff_orth {z : I → ℚ} (hz : z ∈ B.orthogonal (Submodule.span ℚ (Set.range e))) :
      coeff z = 0 := by
    have h0 : (fun m => B (e m) z) = 0 := by
      ext m
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz) (e m)
        (Submodule.subset_span (Set.mem_range_self m))
    rw [hcoeff z, h0, Matrix.mulVec_zero]
  have hproj_orth_mem (y : I → ℚ) :
      y - proj y ∈ B.orthogonal (Submodule.span ℚ (Set.range e)) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    induction hn using Submodule.span_induction with
    | mem z hz => obtain ⟨m, rfl⟩ := hz; exact hproj_orth y m
    | zero => simp
    | add a b ha hb iha ihb => simp [map_add, iha, ihb]
    | smul c a ha iha => simp [map_smul, iha]
  exact ⟨hcoeff_sub, hcoeff_sum, fun z hz => hcoeff_orth hz, hproj_orth_mem⟩

private theorem ct_em_Phi_basic {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C)
    (e : Fin 3 → I → ℚ) (coeff : (I → ℚ) → (Fin 3 → ℚ)) (proj : (I → ℚ) → (I → ℚ))
    (H : Subgroup (coxeterMatrix hC).Group)
    (Φm : (coxeterMatrix hC).Group → Matrix (Fin 3) (Fin 3) ℚ)
    (hΦm : ∀ h, Φm h = Matrix.of fun k l => coeff (ct_em_W hC h (e l)) k)
    (hcoeff_add : ∀ x y : I → ℚ, coeff (x + y) = coeff x + coeff y)
    (hcoeff_smul : ∀ (a : ℚ) (x : I → ℚ), coeff (a • x) = a • coeff x)
    (hcoeff_single : ∀ j : Fin 3, coeff (e j) = Pi.single j 1)
    (hproj : ∀ x, proj x = ∑ l, coeff x l • e l)
    (hfix_orth : ∀ h ∈ H, ∀ y : I → ℚ,
      y ∈ (form hC).orthogonal (Submodule.span ℚ (Set.range e)) → ct_em_W hC h y = y)
    (hproj_orth_mem : ∀ y : I → ℚ,
      y - proj y ∈ (form hC).orthogonal (Submodule.span ℚ (Set.range e)))
    (hcoeff_orth : ∀ z : I → ℚ,
      z ∈ (form hC).orthogonal (Submodule.span ℚ (Set.range e)) → coeff z = 0) :
    (∀ (h : (coxeterMatrix hC).Group), h ∈ H → ∀ y : I → ℚ,
      coeff (ct_em_W hC h y) = Φm h *ᵥ coeff y) ∧
    (∀ (h g : (coxeterMatrix hC).Group), h ∈ H → g ∈ H →
      Φm (h * g) = Φm h * Φm g) ∧
    Φm 1 = 1 := by
  let coeffL : (I → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) :=
    { toFun := coeff, map_add' := hcoeff_add, map_smul' := hcoeff_smul }
  have hcoeffL_apply (x : I → ℚ) : coeffL x = coeff x := rfl
  have hcoeff_W (h : (coxeterMatrix hC).Group) (hh : h ∈ H) (y : I → ℚ) :
      coeff (ct_em_W hC h y) = Φm h *ᵥ coeff y := by
    conv_lhs => rw [show y = proj y + (y - proj y) from by abel]
    rw [map_add, hcoeff_add, hfix_orth h hh (y - proj y) (hproj_orth_mem y),
      hcoeff_orth (y - proj y) (hproj_orth_mem y), add_zero]
    have h1 : ct_em_W hC h (proj y) = ∑ j, coeff y j • ct_em_W hC h (e j) := by
      rw [hproj y, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
    rw [h1]
    have h3 : coeff (∑ j, coeff y j • ct_em_W hC h (e j)) =
        ∑ j, coeff y j • coeff (ct_em_W hC h (e j)) := by
      change coeffL (∑ j, coeff y j • ct_em_W hC h (e j)) =
        ∑ j, coeff y j • coeff (ct_em_W hC h (e j))
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hcoeffL_apply]
    rw [h3]
    have h4 : ∀ j : Fin 3, coeff (ct_em_W hC h (e j)) = Φm h *ᵥ (Pi.single j (1 : ℚ)) := by
      intro j
      rw [hΦm h, Matrix.mulVec_single_one]
      rfl
    simp only [h4]
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.mulVec_single_one, Matrix.col_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hPhi_mul (h g : (coxeterMatrix hC).Group) (hh : h ∈ H) (hg : g ∈ H) :
      Φm (h * g) = Φm h * Φm g := by
    ext i l
    rw [hΦm (h * g)]
    change coeff (ct_em_W hC (h * g) (e l)) i = (Φm h * Φm g) i l
    rw [show ct_em_W hC (h * g) (e l) = ct_em_W hC h (ct_em_W hC g (e l)) by
        rw [map_mul, Module.End.mul_apply],
      hcoeff_W h hh (ct_em_W hC g (e l)), hcoeff_W g hg (e l), hcoeff_single l,
      Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply]
  have hPhi_one : Φm 1 = 1 := by
    ext i l
    rw [hΦm 1]
    change coeff (ct_em_W hC 1 (e l)) i = (1 : Matrix (Fin 3) (Fin 3) ℚ) i l
    rw [map_one, Module.End.one_apply, hcoeff_single l]
    simp [Matrix.one_apply, Pi.single_apply]
  exact ⟨hcoeff_W, hPhi_mul, hPhi_one⟩

private theorem ct_em_Phi_tk {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (N : Matrix (Fin 3) (Fin 3) ℤ) (c : ℚ) (hc : 0 < c)
    (e : Fin 3 → I → ℚ) (coeff : (I → ℚ) → (Fin 3 → ℚ))
    (Φm : (coxeterMatrix hC).Group → Matrix (Fin 3) (Fin 3) ℚ)
    (hΦm : ∀ h, Φm h = Matrix.of fun k l => coeff (ct_em_W hC h (e l)) k)
    (hW_tk_el : ∀ k l : Fin 3, ct_em_W hC (coxRefl hC (g k) (i k)) (e l) =
      e l - (2 * form hC (e l) (e k) / form hC (e k) (e k)) • e k)
    (hgramB : ∀ k l : Fin 3, form hC (e k) (e l) = (N k l : ℚ) * c)
    (hNsym : ∀ k l : Fin 3, N k l = N l k)
    (hNdiv : ∀ k l : Fin 3, N k k ∣ 2 * N k l)
    (hNkk_ne : ∀ k : Fin 3, (N k k : ℚ) ≠ 0)
    (hcoeff_sub : ∀ x y : I → ℚ, coeff (x - y) = coeff x - coeff y)
    (hcoeff_single : ∀ j : Fin 3, coeff (e j) = Pi.single j 1)
    (hcoeff_smul : ∀ (a : ℚ) (x : I → ℚ), coeff (a • x) = a • coeff x) :
    ∀ k : Fin 3, Φm (coxRefl hC (g k) (i k)) =
      (Int.castRingHom ℚ).mapMatrix (gramRefl N k) := by
  intro k
  ext a b
  rw [hΦm (coxRefl hC (g k) (i k))]
  change coeff (ct_em_W hC (coxRefl hC (g k) (i k)) (e b)) a =
    (Int.castRingHom ℚ).mapMatrix (gramRefl N k) a b
  rw [hW_tk_el k b]
  have ha : (2 * form hC (e b) (e k) / form hC (e k) (e k)) =
      ((2 * N k b / N k k : ℤ) : ℚ) := by
    have hc0 : c ≠ 0 := ne_of_gt hc
    have hkk : (N k k : ℚ) ≠ 0 := hNkk_ne k
    rw [hgramB b k, hgramB k k, hNsym b k, Int.cast_div_charZero (hNdiv k b)]
    push_cast
    field_simp
  have hcl : coeff (e b - (2 * form hC (e b) (e k) / form hC (e k) (e k)) • e k) =
      Pi.single b 1 - ((2 * N k b / N k k : ℤ) : ℚ) • Pi.single k 1 := by
    rw [hcoeff_sub, hcoeff_single b, hcoeff_smul, hcoeff_single k, ha]
  rw [hcl]
  have hA : ((2 * N k b / N k k : ℤ) : ℚ) = ↑(2 * N k b) / ↑(N k k) :=
    Int.cast_div_charZero (hNdiv k b)
  by_cases hab : a = b <;> by_cases hak : a = k
  all_goals simp_all [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gramRefl,
    Matrix.sub_apply, Matrix.of_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
  all_goals ring

private theorem ct_em_hHmono {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (ht_mul_self : ∀ k : Fin 3,
      coxRefl hC (g k) (i k) * coxRefl hC (g k) (i k) = 1) :
    (Subgroup.closure ({coxRefl hC (g 0) (i 0), coxRefl hC (g 1) (i 1),
      coxRefl hC (g 2) (i 2)} : Set (coxeterMatrix hC).Group)).toSubmonoid =
      Submonoid.closure (Set.range fun k => coxRefl hC (g k) (i k)) := by
  let t : Fin 3 → (coxeterMatrix hC).Group := fun k => coxRefl hC (g k) (i k)
  let S : Set (coxeterMatrix hC).Group := {t 0, t 1, t 2}
  let H : Subgroup (coxeterMatrix hC).Group := Subgroup.closure S
  change H.toSubmonoid = Submonoid.closure (Set.range t)
  change (∀ k : Fin 3, t k * t k = 1) at ht_mul_self
  have hSrange : S = Set.range t := by
    ext x; constructor
    · intro hx
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · rintro ⟨k, rfl⟩
      fin_cases k <;> simp [S]
  have hSinv : (Set.range t)⁻¹ = Set.range t := by
    ext x; constructor
    · intro hx
      obtain ⟨k, hk⟩ := hx
      refine ⟨k, ?_⟩
      rw [show x = (x⁻¹)⁻¹ from (inv_inv x).symm, ← hk,
        inv_eq_of_mul_eq_one_right (ht_mul_self k)]
    · intro hx
      obtain ⟨k, rfl⟩ := hx
      exact ⟨k, by rw [inv_eq_of_mul_eq_one_right (ht_mul_self k)]⟩
  change (Subgroup.closure S).toSubmonoid = Submonoid.closure (Set.range t)
  rw [hSrange, Subgroup.closure_toSubmonoid, hSinv, Set.union_self]

private theorem ct_em_Phi_mem {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (N : Matrix (Fin 3) (Fin 3) ℤ)
    (t : Fin 3 → (coxeterMatrix hC).Group) (H : Subgroup (coxeterMatrix hC).Group)
    (Φm : (coxeterMatrix hC).Group → Matrix (Fin 3) (Fin 3) ℚ)
    (castM : Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) ℚ)
    (hHmono : H.toSubmonoid = Submonoid.closure (Set.range t))
    (hPhi_tk : ∀ k : Fin 3, Φm (t k) = castM (gramRefl N k))
    (hPhi_one : Φm 1 = 1)
    (hPhi_mul : ∀ h g : (coxeterMatrix hC).Group, h ∈ H → g ∈ H →
      Φm (h * g) = Φm h * Φm g) :
    ∀ h ∈ H, Φm h ∈ (gramReflGroup N).map castM := by
  have hPhi_mem_aux : ∀ h ∈ Submonoid.closure (Set.range t),
      Φm h ∈ (gramReflGroup N).map castM := by
    intro h hh'
    induction hh' using Submonoid.closure_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [hPhi_tk k]
        exact Submonoid.mem_map_of_mem castM (Submonoid.subset_closure (Set.mem_range_self k))
    | one => rw [hPhi_one]; exact Submonoid.one_mem _
    | mul x y hx hy ihx ihy =>
        rw [hPhi_mul x y (by change x ∈ H.toSubmonoid; rw [hHmono]; exact hx)
          (by change y ∈ H.toSubmonoid; rw [hHmono]; exact hy)]
        exact Submonoid.mul_mem _ ihx ihy
  intro h hh
  refine hPhi_mem_aux h ?_
  rw [← hHmono]; exact hh

private theorem ct_em_W_e_surj {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (N : Matrix (Fin 3) (Fin 3) ℤ)
    (t : Fin 3 → (coxeterMatrix hC).Group) (H : Subgroup (coxeterMatrix hC).Group)
    (hgen : ∀ k : Fin 3, t k ∈ H)
    (e : Fin 3 → I → ℚ) (coeff : (I → ℚ) → (Fin 3 → ℚ)) (proj : (I → ℚ) → (I → ℚ))
    (Φm : (coxeterMatrix hC).Group → Matrix (Fin 3) (Fin 3) ℚ)
    (castM : Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) ℚ)
    (hΦm : ∀ h, Φm h = Matrix.of fun k l => coeff (ct_em_W hC h (e l)) k)
    (hproj : ∀ x, proj x = ∑ l, coeff x l • e l)
    (hproj_self : ∀ x ∈ Submodule.span ℚ (Set.range e), proj x = x)
    (hUmap : ∀ h ∈ H, (Submodule.span ℚ (Set.range e)).map (ct_em_W hC h) =
      Submodule.span ℚ (Set.range e))
    (hPhi_tk : ∀ k : Fin 3, Φm (t k) = castM (gramRefl N k))
    (hPhi_one : Φm 1 = 1)
    (hPhi_mul : ∀ h g : (coxeterMatrix hC).Group, h ∈ H → g ∈ H →
      Φm (h * g) = Φm h * Φm g) :
    (∀ h ∈ H, ∀ l : Fin 3, ct_em_W hC h (e l) = ∑ j, Φm h j l • e j) ∧
    (∀ M ∈ gramReflGroup N, ∃ h : H, Φm h.1 = castM M) := by
  have hW_e (h : (coxeterMatrix hC).Group) (hh : h ∈ H) (l : Fin 3) :
      ct_em_W hC h (e l) = ∑ j, Φm h j l • e j := by
    have hmem : ct_em_W hC h (e l) ∈ Submodule.span ℚ (Set.range e) := by
      rw [← hUmap h hh]
      exact Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self l))
    rw [← hproj_self _ hmem, hproj, hΦm h]
    rfl
  refine ⟨hW_e, ?_⟩
  intro M hM
  induction hM using Submonoid.closure_induction with
  | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      exact ⟨⟨t k, hgen k⟩, hPhi_tk k⟩
  | one => exact ⟨1, by
      change Φm (1 : (coxeterMatrix hC).Group) = castM 1
      rw [hPhi_one, map_one]⟩
  | mul a b ha hb iha ihb =>
      obtain ⟨ha', hha'⟩ := iha
      obtain ⟨hb', hhb'⟩ := ihb
      exact ⟨ha' * hb', by
        change Φm (ha'.1 * hb'.1) = castM (a * b)
        rw [hPhi_mul ha'.1 hb'.1 ha'.2 hb'.2, hha', hhb', map_mul]⟩

private theorem ct_em_castM_injective :
    Function.Injective ((Int.castRingHom ℚ).mapMatrix :
      Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) ℚ) := by
  intro A B hAB
  ext i j
  exact Int.cast_injective (congrFun (congrFun hAB i) j)

private theorem ct_em_Phi_eq_one {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C)
    (e : Fin 3 → I → ℚ) (coeff : (I → ℚ) → (Fin 3 → ℚ)) (proj : (I → ℚ) → (I → ℚ))
    (H : Subgroup (coxeterMatrix hC).Group)
    (hproj : ∀ x, proj x = ∑ l, coeff x l • e l)
    (hfix_orth : ∀ h ∈ H, ∀ y : I → ℚ,
      y ∈ (form hC).orthogonal (Submodule.span ℚ (Set.range e)) → ct_em_W hC h y = y)
    (hproj_orth_mem : ∀ y : I → ℚ,
      y - proj y ∈ (form hC).orthogonal (Submodule.span ℚ (Set.range e))) :
    ∀ h ∈ H, (∀ l : Fin 3, ct_em_W hC h (e l) = e l) → h = 1 := by
  intro h hh hfix
  have hWh : ct_em_W hC h = 1 := by
    apply LinearMap.ext
    intro x
    have hpx : ct_em_W hC h (proj x) = proj x := by
      rw [hproj x, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, hfix l]
    have hqx : ct_em_W hC h (x - proj x) = x - proj x :=
      hfix_orth h hh (x - proj x) (hproj_orth_mem x)
    calc ct_em_W hC h x = ct_em_W hC h (proj x + (x - proj x)) := by
            rw [show proj x + (x - proj x) = x from by abel]
      _ = ct_em_W hC h (proj x) + ct_em_W hC h (x - proj x) := by rw [map_add]
      _ = proj x + (x - proj x) := by rw [hpx, hqx]
      _ = x := by abel
  have hw1 : weylAction hC h = 1 := by
    apply LinearMap.ext
    intro v
    apply toRat_injective
    rw [← ct_em_ratExt_toRat (weylAction hC h) v]
    change ct_em_ratExt (weylAction hC h) (toRat v) = toRat v
    rw [show ct_em_ratExt (weylAction hC h) = ct_em_W hC h from rfl, hWh,
      Module.End.one_apply]
  exact weylAction_injective hC (by rw [hw1, map_one])

private theorem ct_em_Phi_injective {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (N : Matrix (Fin 3) (Fin 3) ℤ)
    (e : Fin 3 → I → ℚ) (H : Subgroup (coxeterMatrix hC).Group)
    (Φm : (coxeterMatrix hC).Group → Matrix (Fin 3) (Fin 3) ℚ)
    (castM : Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) ℚ)
    (Φ : H → ↥((gramReflGroup N).map castM))
    (hΦ : ∀ h : H, (Φ h : Matrix (Fin 3) (Fin 3) ℚ) = Φm h.1)
    (hW_e : ∀ h ∈ H, ∀ l : Fin 3, ct_em_W hC h (e l) = ∑ j, Φm h j l • e j)
    (hPhi_eq_one : ∀ h ∈ H, (∀ l : Fin 3, ct_em_W hC h (e l) = e l) → h = 1) :
    Function.Injective Φ := by
  intro h g hhg
  have hΦm : Φm h.1 = Φm g.1 := by
    have hval : (Φ h).1 = (Φ g).1 := congrArg Subtype.val hhg
    rw [hΦ h, hΦ g] at hval
    exact hval
  have heq : ∀ l : Fin 3, ct_em_W hC h.1 (e l) = ct_em_W hC g.1 (e l) := fun l => by
    rw [hW_e h.1 h.2 l, hW_e g.1 g.2 l, hΦm]
  have hfix : ∀ l : Fin 3, ct_em_W hC (g.1⁻¹ * h.1) (e l) = e l := by
    intro l
    rw [map_mul, Module.End.mul_apply, heq l, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hk := hPhi_eq_one (g.1⁻¹ * h.1) (H.mul_mem (H.inv_mem g.2) h.2) hfix
  have : h.1 = g.1 := by
    have h1 : g.1 * (g.1⁻¹ * h.1) = h.1 := by group
    rw [hk, mul_one] at h1
    exact h1.symm
  exact Subtype.ext this

private theorem ct_em_Phi_surjective {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (N : Matrix (Fin 3) (Fin 3) ℤ)
    (H : Subgroup (coxeterMatrix hC).Group)
    (Φm : (coxeterMatrix hC).Group → Matrix (Fin 3) (Fin 3) ℚ)
    (castM : Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) ℚ)
    (Φ : H → ↥((gramReflGroup N).map castM))
    (hΦ : ∀ h : H, (Φ h : Matrix (Fin 3) (Fin 3) ℚ) = Φm h.1)
    (hsurj : ∀ M ∈ gramReflGroup N, ∃ h : H, Φm h.1 = castM M) :
    Function.Surjective Φ := by
  intro y
  obtain ⟨M, hM, hMy⟩ := Submonoid.mem_map.mp y.2
  obtain ⟨h, hh⟩ := hsurj M hM
  exact ⟨h, Subtype.ext (by rw [hΦ h]; exact hh.trans hMy)⟩

private theorem ct_em_data {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (N : Matrix (Fin 3) (Fin 3) ℤ) (c : ℚ) (ε : Fin 3 → ℚ) (hc : 0 < c)
    (hε : ∀ k, ε k = 1 ∨ ε k = -1) (hN : AdmGram N)
    (hgram : ∀ k l : Fin 3, (N k l : ℚ) * c =
      ε k * ε l * form hC (toRat (coxRoot hC (g k) (i k)))
        (toRat (coxRoot hC (g l) (i l)))) :
    ∃ (e : Fin 3 → I → ℚ) (coeff : (I → ℚ) → (Fin 3 → ℚ)) (proj : (I → ℚ) → (I → ℚ))
      (Φm : (coxeterMatrix hC).Group → Matrix (Fin 3) (Fin 3) ℚ),
      (∀ x : I → ℚ, proj x = ∑ l, coeff x l • e l) ∧
      (∀ h : (coxeterMatrix hC).Group,
        Φm h = Matrix.of fun k l => coeff (ct_em_W hC h (e l)) k) ∧
      (∀ k l : Fin 3, form hC (e k) (e l) = (N k l : ℚ) * c) ∧
      (∀ k : Fin 3, (N k k : ℚ) ≠ 0) ∧
      (∀ k l : Fin 3, ct_em_W hC (coxRefl hC (g k) (i k)) (e l) =
        e l - (2 * form hC (e l) (e k) / form hC (e k) (e k)) • e k) ∧
      (∀ j : Fin 3, coeff (e j) = Pi.single j 1) ∧
      (∀ x y : I → ℚ, coeff (x + y) = coeff x + coeff y) ∧
      (∀ (a : ℚ) (x : I → ℚ), coeff (a • x) = a • coeff x) ∧
      (∀ x y : I → ℚ, coeff (x - y) = coeff x - coeff y) ∧
      (∀ x ∈ Submodule.span ℚ (Set.range e), proj x = x) ∧
      (∀ y : I → ℚ, y - proj y ∈
        (form hC).orthogonal (Submodule.span ℚ (Set.range e))) ∧
      (∀ z : I → ℚ, z ∈
        (form hC).orthogonal (Submodule.span ℚ (Set.range e)) → coeff z = 0) ∧
      (∀ h ∈ Subgroup.closure ({coxRefl hC (g 0) (i 0), coxRefl hC (g 1) (i 1),
        coxRefl hC (g 2) (i 2)} : Set (coxeterMatrix hC).Group),
        ∀ x ∈ (form hC).orthogonal (Submodule.span ℚ (Set.range e)),
          ct_em_W hC h x = x) ∧
      (∀ h ∈ Subgroup.closure ({coxRefl hC (g 0) (i 0), coxRefl hC (g 1) (i 1),
        coxRefl hC (g 2) (i 2)} : Set (coxeterMatrix hC).Group),
        (Submodule.span ℚ (Set.range e)).map (ct_em_W hC h) =
          Submodule.span ℚ (Set.range e)) ∧
      (∀ k : Fin 3, coxRefl hC (g k) (i k) * coxRefl hC (g k) (i k) = 1) := by
  classical
  let e : Fin 3 → I → ℚ := fun k => ε k • toRat (coxRoot hC (g k) (i k))
  let B : LinearMap.BilinForm ℚ (I → ℚ) := form hC
  let G : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun k l => B (e k) (e l)
  let coeff : (I → ℚ) → (Fin 3 → ℚ) := fun x => G⁻¹ *ᵥ (fun m => B (e m) x)
  let proj : (I → ℚ) → (I → ℚ) := fun x => ∑ l, coeff x l • e l
  let Φm : (coxeterMatrix hC).Group → Matrix (Fin 3) (Fin 3) ℚ :=
    fun h => Matrix.of fun k l => coeff (ct_em_W hC h (e l)) k
  obtain ⟨_, hNkk_ne, hε_sq, hgramB, hBkk_ne, hdet⟩ :=
    ct_em_gram_basic hC g i N c ε hc hε hN hgram
  obtain ⟨hcoeff_single, hcoeff_add, hcoeff_smul, hproj_mem⟩ :=
    ct_em_coeff_basic e B G coeff proj (fun k l => rfl) hdet (fun x => rfl) (fun x => rfl)
  have hproj_self := ct_em_proj_self e coeff proj hcoeff_single hcoeff_add hcoeff_smul
    (fun x => rfl)
  obtain ⟨hproj_orth, _⟩ := ct_em_proj_orth_sup e B G coeff proj (fun k l => rfl) hdet
    (fun x => rfl) (fun x => rfl) hproj_mem
  obtain ⟨hW_tk_toRat, hW_tk_el⟩ := ct_em_W_tk hC g i ε hε_sq hBkk_ne
  obtain ⟨ht_mul_self, hUmap_gen⟩ := ct_em_U_tk hC g i e hW_tk_el
  have hconv := ct_em_hconv hC g i ε hε_sq
  have hW_tk_eq := ct_em_W_tk_eq hC g i ε hW_tk_toRat hconv
  obtain ⟨_, hfix_orth⟩ := ct_em_hfix_orth hC g i e hW_tk_eq
  have hUmap := ct_em_hUmap hC g i e hUmap_gen
  obtain ⟨hcoeff_sub, _, hcoeff_orth, hproj_orth_mem⟩ :=
    ct_em_coeff_facts e B G coeff proj (fun x => rfl) hcoeff_single hcoeff_add hcoeff_smul
      hproj_orth
  refine ⟨e, coeff, proj, Φm, ?_⟩
  exact ⟨fun x => rfl, fun h => rfl, hgramB, hNkk_ne, hW_tk_el, hcoeff_single, hcoeff_add,
    hcoeff_smul, hcoeff_sub, hproj_self, hproj_orth_mem, hcoeff_orth, hfix_orth, hUmap,
    ht_mul_self⟩

private theorem ct_em_final {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (N : Matrix (Fin 3) (Fin 3) ℤ) (c : ℚ) (hc : 0 < c) (hN : AdmGram N)
    (e : Fin 3 → I → ℚ) (coeff : (I → ℚ) → (Fin 3 → ℚ)) (proj : (I → ℚ) → (I → ℚ))
    (Φm : (coxeterMatrix hC).Group → Matrix (Fin 3) (Fin 3) ℚ)
    (hproj : ∀ x : I → ℚ, proj x = ∑ l, coeff x l • e l)
    (hΦm : ∀ h : (coxeterMatrix hC).Group,
      Φm h = Matrix.of fun k l => coeff (ct_em_W hC h (e l)) k)
    (hgramB : ∀ k l : Fin 3, form hC (e k) (e l) = (N k l : ℚ) * c)
    (hNkk_ne : ∀ k : Fin 3, (N k k : ℚ) ≠ 0)
    (hW_tk_el : ∀ k l : Fin 3, ct_em_W hC (coxRefl hC (g k) (i k)) (e l) =
      e l - (2 * form hC (e l) (e k) / form hC (e k) (e k)) • e k)
    (hcoeff_single : ∀ j : Fin 3, coeff (e j) = Pi.single j 1)
    (hcoeff_add : ∀ x y : I → ℚ, coeff (x + y) = coeff x + coeff y)
    (hcoeff_smul : ∀ (a : ℚ) (x : I → ℚ), coeff (a • x) = a • coeff x)
    (hcoeff_sub : ∀ x y : I → ℚ, coeff (x - y) = coeff x - coeff y)
    (hproj_self : ∀ x ∈ Submodule.span ℚ (Set.range e), proj x = x)
    (hproj_orth_mem : ∀ y : I → ℚ, y - proj y ∈
      (form hC).orthogonal (Submodule.span ℚ (Set.range e)))
    (hcoeff_orth : ∀ z : I → ℚ, z ∈
      (form hC).orthogonal (Submodule.span ℚ (Set.range e)) → coeff z = 0)
    (hfix_orth : ∀ h ∈ Subgroup.closure ({coxRefl hC (g 0) (i 0), coxRefl hC (g 1) (i 1),
      coxRefl hC (g 2) (i 2)} : Set (coxeterMatrix hC).Group),
      ∀ x ∈ (form hC).orthogonal (Submodule.span ℚ (Set.range e)), ct_em_W hC h x = x)
    (hUmap : ∀ h ∈ Subgroup.closure ({coxRefl hC (g 0) (i 0), coxRefl hC (g 1) (i 1),
      coxRefl hC (g 2) (i 2)} : Set (coxeterMatrix hC).Group),
      (Submodule.span ℚ (Set.range e)).map (ct_em_W hC h) =
        Submodule.span ℚ (Set.range e))
    (ht_mul_self : ∀ k : Fin 3, coxRefl hC (g k) (i k) * coxRefl hC (g k) (i k) = 1) :
    Nat.card (Subgroup.closure ({coxRefl hC (g 0) (i 0), coxRefl hC (g 1) (i 1),
      coxRefl hC (g 2) (i 2)} : Set (coxeterMatrix hC).Group)) =
      Nat.card ↥(gramReflGroup N) := by
  classical
  let t : Fin 3 → (coxeterMatrix hC).Group := fun k => coxRefl hC (g k) (i k)
  let S : Set (coxeterMatrix hC).Group := {t 0, t 1, t 2}
  let H : Subgroup (coxeterMatrix hC).Group := Subgroup.closure S
  let castM : Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) ℚ :=
    (Int.castRingHom ℚ).mapMatrix
  change Nat.card H = Nat.card ↥(gramReflGroup N)
  change (∀ h ∈ H, ∀ x ∈ (form hC).orthogonal (Submodule.span ℚ (Set.range e)),
    ct_em_W hC h x = x) at hfix_orth
  change (∀ h ∈ H, (Submodule.span ℚ (Set.range e)).map (ct_em_W hC h) =
    Submodule.span ℚ (Set.range e)) at hUmap
  change (∀ k : Fin 3, t k * t k = 1) at ht_mul_self
  obtain ⟨hNsym, _, _, _, _, hNdiv, _, _, _, _, _⟩ := hN
  obtain ⟨hcoeff_W, hPhi_mul, hPhi_one⟩ := ct_em_Phi_basic hC e coeff proj H Φm hΦm
    hcoeff_add hcoeff_smul hcoeff_single hproj hfix_orth hproj_orth_mem hcoeff_orth
  have hPhi_tk := ct_em_Phi_tk hC g i N c hc e coeff Φm hΦm hW_tk_el hgramB hNsym hNdiv
    hNkk_ne hcoeff_sub hcoeff_single hcoeff_smul
  have hHmono := ct_em_hHmono hC g i ht_mul_self
  have hPhi_mem := ct_em_Phi_mem hC N t H Φm castM hHmono hPhi_tk hPhi_one hPhi_mul
  have hgen : ∀ k : Fin 3, t k ∈ H := fun k =>
    Subgroup.subset_closure (by fin_cases k <;> simp [S])
  obtain ⟨hW_e, hsurj_aux⟩ := ct_em_W_e_surj hC N t H hgen e coeff proj Φm castM hΦm hproj
    hproj_self hUmap hPhi_tk hPhi_one hPhi_mul
  have hcast : Function.Injective castM := ct_em_castM_injective
  have hPhi_eq_one := ct_em_Phi_eq_one hC e coeff proj H hproj hfix_orth hproj_orth_mem
  let Φ : H → ↥((gramReflGroup N).map castM) := fun h => ⟨Φm h.1, hPhi_mem h.1 h.2⟩
  have hΦ : ∀ h : H, (Φ h : Matrix (Fin 3) (Fin 3) ℚ) = Φm h.1 := fun h => rfl
  have hΦ_inj := ct_em_Phi_injective hC N e H Φm castM Φ hΦ hW_e hPhi_eq_one
  have hΦ_surj := ct_em_Phi_surjective hC N H Φm castM Φ hΦ hsurj_aux
  have hcard1 : Nat.card H = Nat.card ↥((gramReflGroup N).map castM) :=
    Nat.card_congr (Equiv.ofBijective Φ ⟨hΦ_inj, hΦ_surj⟩)
  have hcard2 : Nat.card ↥((gramReflGroup N).map castM) = Nat.card ↥(gramReflGroup N) :=
    Nat.card_congr (Submonoid.equivMapOfInjective (S := gramReflGroup N)
      (f := castM.toMonoidHom) (hf := hcast)).toEquiv.symm
  rw [hcard1, hcard2]

theorem coxTriple_embed
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (N : Matrix (Fin 3) (Fin 3) ℤ) (c : ℚ) (ε : Fin 3 → ℚ) (hc : 0 < c)
    (hε : ∀ k, ε k = 1 ∨ ε k = -1)
    (hN : AdmGram N)
    (hgram : ∀ k l : Fin 3, (N k l : ℚ) * c =
      ε k * ε l * form hC (toRat (coxRoot hC (g k) (i k))) (toRat (coxRoot hC (g l) (i l)))) :
    Nat.card (Subgroup.closure ({coxRefl hC (g 0) (i 0), coxRefl hC (g 1) (i 1),
      coxRefl hC (g 2) (i 2)} :
        Set (coxeterMatrix hC).Group)) = Nat.card ↥(gramReflGroup N) := by
  obtain ⟨e, coeff, proj, Φm, hproj, hΦm, hgramB, hNkk_ne, hW_tk_el, hcoeff_single,
    hcoeff_add, hcoeff_smul, hcoeff_sub, hproj_self, hproj_orth_mem, hcoeff_orth,
    hfix_orth, hUmap, ht_mul_self⟩ := ct_em_data hC g i N c ε hc hε hN hgram
  exact ct_em_final hC g i N c hc hN e coeff proj Φm hproj hΦm hgramB hNkk_ne hW_tk_el
    hcoeff_single hcoeff_add hcoeff_smul hcoeff_sub hproj_self hproj_orth_mem hcoeff_orth
    hfix_orth hUmap ht_mul_self
end CFSG.StandardType.CoxTriple
end

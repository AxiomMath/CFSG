module

public import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.StandardType.SpJoin CFSG.StandardType.TorC
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram ofSymplecticMat mat_ofSymplecticMat
  mat_transpose_mul_gram_mul)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open Matrix Multiplicative


theorem sympMinusLoc_pow_eq_one {p : ℕ} (hp : p ≠ 0) (y : Multiplicative (ZMod p)) : y ^ p = 1 := by
  haveI : NeZero p := ⟨hp⟩
  obtain ⟨z, rfl⟩ : ∃ z : ZMod p, ofAdd z = y := ⟨toAdd y, rfl⟩
  rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem sympMinusLoc_gram_eq_planeMat {K : Type} [Field K] {m : ℕ} :
    gram K m = WitSpNs.planeMat (fun _ : Fin m => !![(0 : K), 1; -1, 0]) := by
  ext a b
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, WitSpNs.planeMat_apply]
  rcases a with i | i <;> rcases b with j | j <;>
    by_cases hij : i = j <;>
    simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.par,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.sgn, WitSpNs.plane, WitSpNs.side,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hij,
      eq_comm]

theorem sympMinusLoc_blk_eq_zero_of_mem_centralizer {K : Type} [Field K] {m : ℕ} [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p)) {h : StatedSp m K}
    (hh : h * spPlaneTorus m ζ f₀ = spPlaneTorus m ζ f₀ * h) (x y : Fin m)
    (hyx : f₀ y ≠ f₀ x) (hyxi : f₀ y ≠ (f₀ x)⁻¹) :
    blk (mat m K h) y x = 0 := by
  classical
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hG : mat m K (spPlaneTorus m ζ f₀) =
      WitSpNs.planeMat
        (fun i => ((ζ (f₀ i) : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) := by
    rw [mat_apply]; exact coe_spPlaneTorus m ζ f₀
  have hmat : mat m K h * WitSpNs.planeMat
        (fun i => ((ζ (f₀ i) : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) =
      WitSpNs.planeMat
        (fun i => ((ζ (f₀ i) : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) * mat m K h := by
    have h' := congrArg (mat m K) hh
    rwa [map_mul, map_mul, hG] at h'
  by_contra hblk
  have htr := trace_eq_of_mul_eq hblk (blk_mul_eq hmat y x)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcomm : ζ (f₀ x) * ζ (f₀ y) = ζ (f₀ y) * ζ (f₀ x) := by
    rw [← map_mul, ← map_mul, mul_comm]
  have hp1 : ((ζ (f₀ x))⁻¹ * ζ (f₀ y)) ^ p = 1 := by
    rw [← map_inv, ← map_mul, ← map_pow, sympMinusLoc_pow_eq_one hp.ne_zero, map_one]
  rcases eq_or_eq_inv_of_trace_eq hpodd hcomm hp1 htr with hcase | hcase
  · exact hyx (hζ hcase)
  · exact hyxi (hζ (hcase.trans (map_inv ζ (f₀ x)).symm))

@[expose] noncomputable def sympMinusLocPlaneProj {K : Type} [Field K] {m : ℕ}
    (S : Finset (Fin m)) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  WitSpNs.planeMat fun i => if i ∈ S then (1 : Matrix (Fin 2) (Fin 2) K) else 0

@[expose] def sympMinusLocCoordSet {m : ℕ} (S : Finset (Fin m)) : Set (Fin m ⊕ Fin m) :=
  {a | WitSpNs.plane a ∈ S}

theorem sympMinusLocPlaneProj_mul_self {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m)) :
    sympMinusLocPlaneProj (K := K) (m := m) S * sympMinusLocPlaneProj S =
      sympMinusLocPlaneProj S := by
  rw [sympMinusLocPlaneProj, WitSpNs.planeMat_mul]
  congr 1
  funext i
  by_cases h : i ∈ S <;> simp [h]

theorem sympMinusLocPlaneProj_transpose {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m)) :
    (sympMinusLocPlaneProj (K := K) (m := m) S)ᵀ = sympMinusLocPlaneProj S := by
  ext a b
  rw [Matrix.transpose_apply, sympMinusLocPlaneProj, WitSpNs.planeMat_apply, WitSpNs.planeMat_apply]
  by_cases hab : WitSpNs.plane a = WitSpNs.plane b
  · rw [hab, if_pos rfl, if_pos rfl]
    by_cases hS : WitSpNs.plane b ∈ S
    · simp [hS, Matrix.one_apply, eq_comm]
    · simp [hS]
  · rw [if_neg hab, if_neg (Ne.symm hab)]

theorem sympMinusLocPlaneProj_mul_gram {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m)) :
    sympMinusLocPlaneProj (K := K) (m := m) S * gram K m = gram K m * sympMinusLocPlaneProj S := by
  rw [sympMinusLoc_gram_eq_planeMat, sympMinusLocPlaneProj, WitSpNs.planeMat_mul,
    WitSpNs.planeMat_mul]
  congr 1
  funext i
  by_cases h : i ∈ S <;> simp [h]

theorem sympMinusLocPlaneProj_commute_planeMat {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m))
    (M : Fin m → Matrix (Fin 2) (Fin 2) K) :
    WitSpNs.planeMat M * sympMinusLocPlaneProj (K := K) (m := m) S =
      sympMinusLocPlaneProj S * WitSpNs.planeMat M := by
  rw [sympMinusLocPlaneProj, WitSpNs.planeMat_mul, WitSpNs.planeMat_mul]
  congr 1
  funext i
  by_cases h : i ∈ S <;> simp [h]

theorem sympMinusLocPlaneProj_apply_of_mem {K : Type} [Field K] {m : ℕ} {S : Finset (Fin m)}
    {b : Fin m ⊕ Fin m}
    (hb : WitSpNs.plane b ∈ S) (z : Fin m ⊕ Fin m) :
    sympMinusLocPlaneProj (K := K) (m := m) S z b =
      (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) z b := by
  rw [sympMinusLocPlaneProj, WitSpNs.planeMat_apply]
  by_cases hz : WitSpNs.plane z = WitSpNs.plane b
  · rw [if_pos hz, if_pos (hz ▸ hb), Matrix.one_apply, Matrix.one_apply]
    by_cases hs : WitSpNs.side z = WitSpNs.side b
    · rw [if_pos hs, if_pos (WitSpNs.eq_of_plane_side hz hs)]
    · rw [if_neg hs, if_neg fun h => hs (by rw [h])]
  · rw [if_neg hz, Matrix.one_apply, if_neg fun h => hz (by rw [h])]

theorem sympMinusLocPlaneProj_apply_of_mem_row {K : Type} [Field K] {m : ℕ} {S : Finset (Fin m)}
    {a : Fin m ⊕ Fin m}
    (ha : WitSpNs.plane a ∈ S) (z : Fin m ⊕ Fin m) :
    sympMinusLocPlaneProj (K := K) (m := m) S a z =
      (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a z := by
  rw [sympMinusLocPlaneProj, WitSpNs.planeMat_apply]
  by_cases hz : WitSpNs.plane a = WitSpNs.plane z
  · rw [if_pos hz, if_pos (hz.symm ▸ ha), Matrix.one_apply, Matrix.one_apply]
    by_cases hs : WitSpNs.side a = WitSpNs.side z
    · rw [if_pos hs, if_pos (WitSpNs.eq_of_plane_side hz hs)]
    · rw [if_neg hs, if_neg fun h => hs (by rw [h])]
  · rw [if_neg hz, Matrix.one_apply, if_neg fun h => hz (by rw [h])]

theorem sympMinusLocPlaneProj_apply_of_notMem {K : Type} [Field K] {m : ℕ} {S : Finset (Fin m)}
    {b : Fin m ⊕ Fin m}
    (hb : WitSpNs.plane b ∉ S) (z : Fin m ⊕ Fin m) :
    sympMinusLocPlaneProj (K := K) (m := m) S z b = 0 := by
  rw [sympMinusLocPlaneProj, WitSpNs.planeMat_apply]
  by_cases hz : WitSpNs.plane z = WitSpNs.plane b
  · rw [if_pos hz, if_neg hb]
    simp
  · rw [if_neg hz]

theorem sympMinusLocPlaneProj_apply_of_notMem_row {K : Type} [Field K] {m : ℕ} {S : Finset (Fin m)}
    {a : Fin m ⊕ Fin m}
    (ha : WitSpNs.plane a ∉ S) (z : Fin m ⊕ Fin m) :
    sympMinusLocPlaneProj (K := K) (m := m) S a z = 0 := by
  rw [sympMinusLocPlaneProj, WitSpNs.planeMat_apply]
  by_cases hz : WitSpNs.plane a = WitSpNs.plane z
  · rw [if_pos hz, if_neg fun h => ha (hz.symm ▸ h)]
    simp
  · rw [if_neg hz]

theorem sympMinusLocPlaneProj_mul_apply {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m))
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (a b : Fin m ⊕ Fin m) :
    (H * sympMinusLocPlaneProj (K := K) (m := m) S) a b =
      if WitSpNs.plane b ∈ S then H a b else 0 := by
  by_cases hb : WitSpNs.plane b ∈ S
  · rw [if_pos hb]
    calc (H * sympMinusLocPlaneProj (K := K) (m := m) S) a b
        = ∑ z, H a z * sympMinusLocPlaneProj (K := K) (m := m) S z b := Matrix.mul_apply
      _ = ∑ z, H a z * (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) z b :=
            Finset.sum_congr rfl fun z _ => by rw [sympMinusLocPlaneProj_apply_of_mem hb z]
      _ = H a b := by rw [← Matrix.mul_apply, Matrix.mul_one]
  · rw [if_neg hb]
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [sympMinusLocPlaneProj_apply_of_notMem hb z, mul_zero]

theorem sympMinusLocPlaneProj_mul_apply' {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m))
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (a b : Fin m ⊕ Fin m) :
    (sympMinusLocPlaneProj (K := K) (m := m) S * H) a b =
      if WitSpNs.plane a ∈ S then H a b else 0 := by
  by_cases ha : WitSpNs.plane a ∈ S
  · rw [if_pos ha]
    calc (sympMinusLocPlaneProj (K := K) (m := m) S * H) a b
        = ∑ z, sympMinusLocPlaneProj (K := K) (m := m) S a z * H z b := Matrix.mul_apply
      _ = ∑ z, (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a z * H z b :=
            Finset.sum_congr rfl fun z _ => by rw [sympMinusLocPlaneProj_apply_of_mem_row ha z]
      _ = H a b := by rw [← Matrix.mul_apply, Matrix.one_mul]
  · rw [if_neg ha]
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [sympMinusLocPlaneProj_apply_of_notMem_row ha z, zero_mul]

theorem sympMinusLocPlaneProj_commute {K : Type} [Field K] {m : ℕ} {S : Finset (Fin m)}
    {H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hout : ∀ a b, WitSpNs.plane a ∈ S → WitSpNs.plane b ∉ S → H a b = 0)
    (hin : ∀ a b, WitSpNs.plane a ∉ S → WitSpNs.plane b ∈ S → H a b = 0) :
    H * sympMinusLocPlaneProj (K := K) (m := m) S = sympMinusLocPlaneProj S * H := by
  ext a b
  rw [sympMinusLocPlaneProj_mul_apply, sympMinusLocPlaneProj_mul_apply']
  by_cases ha : WitSpNs.plane a ∈ S <;> by_cases hb : WitSpNs.plane b ∈ S
  · rw [if_pos hb, if_pos ha]
  · rw [if_neg hb, if_pos ha, hout a b ha hb]
  · rw [if_pos hb, if_neg ha, hin a b ha hb]
  · rw [if_neg hb, if_neg ha]

@[expose] noncomputable def sympMinusLocProjSet {K : Type} [Field K] {m : ℕ}
    (A : Set (Fin m ⊕ Fin m))
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := by
  classical
  exact Matrix.of fun x y => if x ∈ A ∧ y ∈ A then H x y else
    (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y

@[expose] noncomputable def sympMinusLocProjMat {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m))
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  H * sympMinusLocPlaneProj (K := K) (m := m) S + (1 - sympMinusLocPlaneProj (K := K) (m := m) S)

theorem sympMinusLocProjSet_isSupp {K : Type} [Field K] {m : ℕ} (A : Set (Fin m ⊕ Fin m))
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    IsSupp A (sympMinusLocProjSet (K := K) (m := m) A H) := by
  intro x y hxy
  simp only [sympMinusLocProjSet, Matrix.of_apply]
  rw [if_neg (not_and_or.mpr hxy)]

theorem sympMinusLocProjSet_pos {K : Type} [Field K] {m : ℕ} {A : Set (Fin m ⊕ Fin m)}
    {H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K} {x y : Fin m ⊕ Fin m}
    (hx : x ∈ A) (hy : y ∈ A) :
    sympMinusLocProjSet (K := K) (m := m) A H x y = H x y := by
  simp only [sympMinusLocProjSet, Matrix.of_apply]
  rw [if_pos ⟨hx, hy⟩]

theorem sympMinusLocProjSet_neg {K : Type} [Field K] {m : ℕ} {A : Set (Fin m ⊕ Fin m)}
    {H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K} {x y : Fin m ⊕ Fin m}
    (h : ¬(x ∈ A ∧ y ∈ A)) :
    sympMinusLocProjSet (K := K) (m := m) A H x y =
      (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y := by
  simp only [sympMinusLocProjSet, Matrix.of_apply]
  rw [if_neg h]

theorem sympMinusLocProjMat_eq_projSet {K : Type} [Field K] {m : ℕ} {S : Finset (Fin m)}
    {H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hcross : ∀ a b, WitSpNs.plane a ∉ S → WitSpNs.plane b ∈ S → H a b = 0) :
    sympMinusLocProjMat (K := K) (m := m) S H = sympMinusLocProjSet (sympMinusLocCoordSet S) H := by
  ext a b
  rw [sympMinusLocProjMat, Matrix.add_apply, Matrix.sub_apply, sympMinusLocPlaneProj_mul_apply,
    sympMinusLocProjSet, Matrix.of_apply]
  by_cases hb : WitSpNs.plane b ∈ S
  · rw [if_pos hb, sympMinusLocPlaneProj_apply_of_mem hb a]
    by_cases ha : WitSpNs.plane a ∈ S
    · rw [if_pos ⟨ha, hb⟩, sub_self, add_zero]
    · rw [if_neg fun hc => ha hc.1, hcross a b ha hb, Matrix.one_apply,
        if_neg fun hab => ha (by rw [hab]; exact hb), zero_add, sub_self]
  · rw [if_neg hb, sympMinusLocPlaneProj_apply_of_notMem hb a, if_neg fun hc => hb hc.2, sub_zero,
      zero_add]

theorem sympMinusLocProjMat_isSupp {K : Type} [Field K] {m : ℕ} {S : Finset (Fin m)}
    {H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hcross : ∀ a b, WitSpNs.plane a ∉ S → WitSpNs.plane b ∈ S → H a b = 0) :
    IsSupp (sympMinusLocCoordSet S) (sympMinusLocProjMat (K := K) (m := m) S H) := by
  rw [sympMinusLocProjMat_eq_projSet hcross]
  exact sympMinusLocProjSet_isSupp _ _

theorem sympMinusLocProjMat_symplectic {K : Type} [Field K] {m : ℕ} {S : Finset (Fin m)}
    {H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hH : Hᵀ * gram K m * H = gram K m)
    (hHP : H * sympMinusLocPlaneProj (K := K) (m := m) S = sympMinusLocPlaneProj S * H) :
    (sympMinusLocProjMat (K := K) (m := m) S H)ᵀ * gram K m * sympMinusLocProjMat S H =
      gram K m := by
  rw [sympMinusLocProjMat]
  set P := sympMinusLocPlaneProj (K := K) (m := m) S with hP
  have hPP : P * P = P := sympMinusLocPlaneProj_mul_self S
  have hPt : Pᵀ = P := sympMinusLocPlaneProj_transpose S
  have hPg : P * gram K m = gram K m * P := sympMinusLocPlaneProj_mul_gram S
  have h1 : P * H = H * P := hHP.symm
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by rw [mul_sub, mul_one, hQP, sub_zero]
  have hQg : (1 - P) * gram K m = gram K m * (1 - P) := by
    rw [sub_mul, one_mul, hPg, Matrix.mul_sub, Matrix.mul_one]
  have hQH : (1 - P) * H = H * (1 - P) := by
    rw [sub_mul, one_mul, h1, Matrix.mul_sub, Matrix.mul_one]
  have hQHP : (1 - P) * H * P = 0 := by
    rw [show (1 - P) * H * P = ((1 - P) * H) * P from rfl, hQH, Matrix.mul_assoc, hQP,
      Matrix.mul_zero]
  have hPHQ : P * H * (1 - P) = 0 := by
    rw [show P * H * (1 - P) = (P * H) * (1 - P) from rfl, h1, Matrix.mul_assoc, hPQ,
      Matrix.mul_zero]
  have hPHQt : P * Hᵀ * (1 - P) = 0 := by
    have h' := congrArg Matrix.transpose hQHP
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      hPt, Matrix.transpose_zero] at h'
    rwa [← Matrix.mul_assoc] at h'
  have t1 : P * Hᵀ * gram K m * H * P = P * gram K m * P := by
    rw [show P * Hᵀ * gram K m * H * P = P * (Hᵀ * gram K m * H) * P from by noncomm_ring, hH]
  have t1' : P * gram K m * P = P * gram K m := by
    rw [show P * gram K m * P = (P * gram K m) * P from rfl, hPg, Matrix.mul_assoc, hPP,
      ← hPg]
  have t2 : P * Hᵀ * gram K m * (1 - P) = 0 := by
    have e : P * Hᵀ * gram K m * (1 - P) = (P * Hᵀ * (1 - P)) * gram K m := by
      rw [show P * Hᵀ * gram K m * (1 - P) = P * Hᵀ * (gram K m * (1 - P)) from by
            noncomm_ring,
        ← hQg,
        show P * Hᵀ * ((1 - P) * gram K m) = (P * Hᵀ * (1 - P)) * gram K m from by noncomm_ring]
    rw [e, hPHQt, Matrix.zero_mul]
  have t3 : (1 - P) * gram K m * H * P = 0 := by
    have e : (1 - P) * gram K m * H * P = gram K m * ((1 - P) * H * P) := by
      rw [show (1 - P) * gram K m = gram K m * (1 - P) from hQg]
      noncomm_ring
    rw [e, hQHP, Matrix.mul_zero]
  have t4 : (1 - P) * gram K m * (1 - P) = (1 - P) * gram K m := by
    rw [show (1 - P) * gram K m * (1 - P) = ((1 - P) * gram K m) * (1 - P) from rfl, hQg,
      Matrix.mul_assoc, hQQ, ← hQg]
  have hA : (H * P + (1 - P))ᵀ = P * Hᵀ + (1 - P) := by
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      hPt]
  have hexp : (P * Hᵀ + (1 - P)) * gram K m * (H * P + (1 - P)) =
      P * Hᵀ * gram K m * H * P + P * Hᵀ * gram K m * (1 - P) +
        (1 - P) * gram K m * H * P + (1 - P) * gram K m * (1 - P) := by
    noncomm_ring
  rw [hA, hexp, t1, t2, t3, t4, t1', add_zero, add_zero, ← add_mul, add_sub_cancel, one_mul]

theorem sympMinusLocIsSupp_mul {K : Type} [Field K] {m : ℕ} {A : Set (Fin m ⊕ Fin m)}
    {M N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hM : IsSupp A M) (hN : IsSupp A N) : IsSupp A (M * N) := by
  intro x y hxy
  by_cases hy : y ∈ A
  · have hx : x ∉ A := by
      rcases hxy with hx | hx
      · exact hx
      · exact absurd hy hx
    rw [Matrix.mul_apply]
    calc ∑ z, M x z * N z y =
          ∑ z, (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x z * N z y :=
          Finset.sum_congr rfl fun z _ => by rw [hM x z (Or.inl hx)]
      _ = N x y := by rw [← Matrix.mul_apply, Matrix.one_mul]
      _ = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y := hN x y (Or.inl hx)
  · rw [Matrix.mul_apply]
    calc ∑ z, M x z * N z y =
          ∑ z, M x z * (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) z y :=
          Finset.sum_congr rfl fun z _ => by rw [hN z y (Or.inr hy)]
      _ = M x y := by rw [← Matrix.mul_apply, Matrix.mul_one]
      _ = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y := hM x y (Or.inr hy)

theorem sympMinusLocIsSupp_inv {K : Type} [Field K] {m : ℕ} {A : Set (Fin m ⊕ Fin m)}
    {M N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hM : IsSupp A M) (hNM : N * M = 1) (hMN : M * N = 1) : IsSupp A N := by
  intro x y hxy
  rcases hxy with hx | hy
  · have h : ∀ z, M x z = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x z :=
      fun z => hM x z (Or.inl hx)
    have e : (M * N) x y = N x y := by
      rw [Matrix.mul_apply]
      calc ∑ z, M x z * N z y =
            ∑ z, (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x z * N z y :=
            Finset.sum_congr rfl fun z _ => by rw [h z]
        _ = N x y := by rw [← Matrix.mul_apply, Matrix.one_mul]
    rw [← e, hMN]
  · have h : ∀ z, M z y = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) z y :=
      fun z => hM z y (Or.inr hy)
    have e : (N * M) x y = N x y := by
      rw [Matrix.mul_apply]
      calc ∑ z, N x z * M z y =
            ∑ z, N x z * (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) z y :=
            Finset.sum_congr rfl fun z _ => by rw [h z]
        _ = N x y := by rw [← Matrix.mul_apply, Matrix.mul_one]
    rw [← e, hNM]

@[expose] def sympMinusLocSupp {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m)) :
    Subgroup (StatedSp m K) where
  carrier := {x | IsSupp (sympMinusLocCoordSet S) (mat m K x)}
  one_mem' := by
    change IsSupp (sympMinusLocCoordSet S) (mat m K (1 : StatedSp m K))
    rw [map_one]
    intro x y _
    rfl
  mul_mem' := by
    intro x y hx hy
    change IsSupp (sympMinusLocCoordSet S) (mat m K (x * y))
    rw [map_mul]
    exact sympMinusLocIsSupp_mul hx hy
  inv_mem' := by
    intro x hx
    change IsSupp (sympMinusLocCoordSet S) (mat m K x⁻¹)
    refine sympMinusLocIsSupp_inv hx ?_ ?_
    · rw [← map_mul, inv_mul_cancel, map_one]
    · rw [← map_mul, mul_inv_cancel, map_one]

@[expose] noncomputable def sympMinusLocMS {K : Type} [Field K] {m : ℕ} {p : ℕ}
    (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) (S : Finset (Fin m)) :
    Subgroup (StatedSp m K) :=
  Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)) ⊓ sympMinusLocSupp S

@[expose] noncomputable def sympMinusLocProjSp {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m))
    (h : StatedSp m K)
    (hcross : ∀ a b, WitSpNs.plane a ∉ S → WitSpNs.plane b ∈ S → mat m K h a b = 0)
    (hcross' : ∀ a b, WitSpNs.plane a ∈ S → WitSpNs.plane b ∉ S → mat m K h a b = 0) :
    StatedSp m K :=
  ofSymplecticMat (sympMinusLocProjMat S (mat m K h))
    (sympMinusLocProjMat_symplectic (mat_transpose_mul_gram_mul h)
      (sympMinusLocPlaneProj_commute hcross' hcross))

theorem sympMinusLocProjSp_mat {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m)) (h : StatedSp m K)
    (hcross : ∀ a b, WitSpNs.plane a ∉ S → WitSpNs.plane b ∈ S → mat m K h a b = 0)
    (hcross' : ∀ a b, WitSpNs.plane a ∈ S → WitSpNs.plane b ∉ S → mat m K h a b = 0) :
    mat m K (sympMinusLocProjSp S h hcross hcross') = sympMinusLocProjMat S (mat m K h) :=
  mat_ofSymplecticMat _ _

theorem sympMinusLocProjSp_mem_supp {K : Type} [Field K] {m : ℕ} (S : Finset (Fin m))
    (h : StatedSp m K)
    (hcross : ∀ a b, WitSpNs.plane a ∉ S → WitSpNs.plane b ∈ S → mat m K h a b = 0)
    (hcross' : ∀ a b, WitSpNs.plane a ∈ S → WitSpNs.plane b ∉ S → mat m K h a b = 0) :
    sympMinusLocProjSp S h hcross hcross' ∈ sympMinusLocSupp S := by
  change IsSupp (sympMinusLocCoordSet S) (mat m K (sympMinusLocProjSp S h hcross hcross'))
  rw [sympMinusLocProjSp_mat]
  exact sympMinusLocProjMat_isSupp hcross

theorem sympMinusLocProjSp_mem_centralizer {K : Type} [Field K] {m : ℕ} {p : ℕ}
    (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {S : Finset (Fin m)} {h : StatedSp m K}
    (hcross : ∀ a b, WitSpNs.plane a ∉ S → WitSpNs.plane b ∈ S → mat m K h a b = 0)
    (hcross' : ∀ a b, WitSpNs.plane a ∈ S → WitSpNs.plane b ∉ S → mat m K h a b = 0)
    (hh : h ∈ Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))) :
    sympMinusLocProjSp S h hcross hcross' ∈
      Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
  apply mat_injective
  rw [map_mul, map_mul, sympMinusLocProjSp_mat, sympMinusLocProjMat]
  set P := sympMinusLocPlaneProj (K := K) (m := m) S with hP
  set G := mat m K (spPlaneTorus m ζ f₀) with hG
  set H := mat m K h with hH
  have hHG : H * G = G * H := by
    have h' := congrArg (mat m K) hh
    rwa [map_mul, map_mul] at h'
  have hPG : P * G = G * P := by
    rw [hG, mat_apply, coe_spPlaneTorus, hP]
    exact (sympMinusLocPlaneProj_commute_planeMat (K := K) (m := m) S
      (fun j => ((ζ (f₀ j) : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K))).symm
  have hQG : (1 - P) * G = G * (1 - P) := by
    rw [sub_mul, one_mul, hPG, Matrix.mul_sub, Matrix.mul_one]
  calc (H * P + (1 - P)) * G
      = H * (P * G) + (1 - P) * G := by noncomm_ring
    _ = H * (G * P) + G * (1 - P) := by rw [hPG, hQG]
    _ = (H * G) * P + G * (1 - P) := by rw [← Matrix.mul_assoc]
    _ = (G * H) * P + G * (1 - P) := by rw [hHG]
    _ = G * (H * P) + G * (1 - P) := by rw [Matrix.mul_assoc]
    _ = G * (H * P + (1 - P)) := by rw [Matrix.mul_add]

end CFSG.StandardType.SympMinus

end

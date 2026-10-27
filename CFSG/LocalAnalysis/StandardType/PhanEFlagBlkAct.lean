module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagBlkMap
public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {n : ℕ} {d : List ℕ}

@[expose] noncomputable def blkMat (d : List ℕ) (b : ℕ) (g : GL (Fin n) K) :
    (Fin (blockSize d b) → K) →ₗ[K] (Fin (blockSize d b) → K) :=
  blkOut n d b ∘ₗ (glLin g).toLinearMap ∘ₗ blkIn n d b

private theorem q2cFBA_glLin_one :
    glLin (1 : GL (Fin n) K) = LinearEquiv.refl K (Fin n → K) := by
  ext v
  rw [glLin_apply]
  simp

private theorem q2cFBA_glLin_mul (g h : GL (Fin n) K) :
    glLin (g * h) = (glLin h).trans (glLin g) := by
  ext v
  rw [glLin_apply, LinearEquiv.trans_apply, glLin_apply, glLin_apply,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem blkMat_one (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length) :
    blkMat d b (1 : GL (Fin n) K) = LinearMap.id := by
  apply LinearMap.ext
  intro w
  change blkOut n d b (glLin (1 : GL (Fin n) K) (blkIn n d b w)) = w
  rw [q2cFBA_glLin_one]
  exact blkOut_blkIn hd hb w

private theorem q2cFBA_blkOut_glLin_eq (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    {g : GL (Fin n) K} (hg : StabV n d g) {v : Fin n → K}
    (hv : v ∈ Vsub n (d.getD (b + 1) 0)) :
    blkOut n d b ((glLin g).toLinearMap v) =
      blkOut n d b ((glLin g).toLinearMap (blkIn n d b (blkOut n d b v))) := by
  have hb' : b < d.length := by omega
  have hr : v - blkIn n d b (blkOut n d b v) ∈ Vsub n (d.getD b 0) :=
    sub_blkIn_blkOut_mem_Vsub hd hb hv
  have hr' :
      (glLin g).toLinearMap (v - blkIn n d b (blkOut n d b v)) ∈ Vsub n (d.getD b 0) := by
    have h := hg b hb'
    rw [← h]
    exact ⟨_, hr, rfl⟩
  have hzero :
      blkOut n d b ((glLin g).toLinearMap v
        - (glLin g).toLinearMap (blkIn n d b (blkOut n d b v))) = 0 := by
    rw [show (glLin g).toLinearMap v
          - (glLin g).toLinearMap (blkIn n d b (blkOut n d b v)) =
        (glLin g).toLinearMap (v - blkIn n d b (blkOut n d b v)) from by rw [map_sub]]
    exact blkOut_of_mem_Vsub hr'
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

theorem blkMat_mul (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length) {g h : GL (Fin n) K}
    (hg : StabV n d g) (hh : StabV n d h) :
    blkMat d b (g * h) = blkMat d b g ∘ₗ blkMat d b h := by
  apply LinearMap.ext
  intro w
  simp only [blkMat, LinearMap.comp_apply]
  rw [q2cFBA_glLin_mul]
  rw [show ((glLin h).trans (glLin g)).toLinearMap
      = (glLin g).toLinearMap.comp (glLin h).toLinearMap from rfl]
  rw [LinearMap.comp_apply]
  exact q2cFBA_blkOut_glLin_eq hd hb hg (by
    have h := hh (b + 1) hb
    rw [← h]
    exact ⟨_, blkIn_mem_Vsub w, rfl⟩)

theorem blkMat_bijective (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length) {g : GL (Fin n) K}
    (hg : StabV n d g) : Function.Bijective (blkMat d b g) := by
  have h1 : blkMat d b g ∘ₗ blkMat d b g⁻¹ = LinearMap.id := by
    rw [← blkMat_mul hd hb hg (StabV.inv hg), mul_inv_cancel, blkMat_one hd hb]
  have h2 : blkMat d b g⁻¹ ∘ₗ blkMat d b g = LinearMap.id := by
    rw [← blkMat_mul hd hb (StabV.inv hg) hg, inv_mul_cancel, blkMat_one hd hb]
  refine Function.bijective_iff_has_inverse.mpr ⟨blkMat d b g⁻¹, ?_, ?_⟩
  · intro x
    have := congrArg
      (fun f : (Fin (blockSize d b) → K) →ₗ[K] (Fin (blockSize d b) → K) => f x) h2
    simpa using this
  · intro x
    have := congrArg
      (fun f : (Fin (blockSize d b) → K) →ₗ[K] (Fin (blockSize d b) → K) => f x) h1
    simpa using this

private theorem q2cFBA_glLin_blkIn_decomp (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    {g : GL (Fin n) K} (hg : StabV n d g) (w : Fin (blockSize d b) → K) :
    ∃ r ∈ Vsub n (d.getD b 0),
      (glLin g).toLinearMap (blkIn n d b w) = blkIn n d b (blkMat d b g w) + r := by
  refine ⟨(glLin g).toLinearMap (blkIn n d b w) - blkIn n d b (blkMat d b g w), ?_, by abel⟩
  have hv : (glLin g).toLinearMap (blkIn n d b w) ∈ Vsub n (d.getD (b + 1) 0) := by
    have h := hg (b + 1) hb
    rw [← h]
    exact ⟨_, blkIn_mem_Vsub w, rfl⟩
  have hmem : (glLin g).toLinearMap (blkIn n d b w)
      - blkIn n d b (blkOut n d b ((glLin g).toLinearMap (blkIn n d b w)))
        ∈ Vsub n (d.getD b 0) :=
    sub_blkIn_blkOut_mem_Vsub hd hb hv
  rw [show blkIn n d b (blkMat d b g w)
      = blkIn n d b (blkOut n d b ((glLin g).toLinearMap (blkIn n d b w))) from rfl]
  exact hmem

theorem map_sup_map_blkIn (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length) {g : GL (Fin n) K}
    (hg : StabV n d g) (U : Submodule K (Fin (blockSize d b) → K)) :
    (Vsub n (d.getD b 0) ⊔ U.map (blkIn n d b)).map (glLin g).toLinearMap =
      Vsub n (d.getD b 0) ⊔ (U.map (blkMat d b g)).map (blkIn n d b) := by
  have hb' : b < d.length := by omega
  have hgA : (Vsub n (d.getD b 0)).map (glLin g).toLinearMap = Vsub n (d.getD b 0) := hg b hb'
  rw [Submodule.map_sup, hgA]
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rintro x ⟨v, hv, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨r, hr, hdecomp⟩ := q2cFBA_glLin_blkIn_decomp hd hb hg w
    rw [hdecomp]
    exact add_mem
      (Submodule.mem_sup_right
        (Submodule.mem_map.mpr ⟨blkMat d b g w, Submodule.mem_map.mpr ⟨w, hw, rfl⟩, rfl⟩))
      (Submodule.mem_sup_left hr)
  · refine sup_le le_sup_left ?_
    rintro x ⟨v, hv, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨r, hr, hdecomp⟩ := q2cFBA_glLin_blkIn_decomp hd hb hg w
    have hx : blkIn n d b (blkMat d b g w) = (glLin g).toLinearMap (blkIn n d b w) - r := by
      rw [hdecomp]
      abel
    rw [hx]
    exact sub_mem
      (Submodule.mem_sup_right
        (Submodule.mem_map.mpr ⟨blkIn n d b w, Submodule.mem_map.mpr ⟨w, hw, rfl⟩, rfl⟩))
      (Submodule.mem_sup_left hr)

private noncomputable def q2cFBA_diagMap (n : ℕ) (d : List ℕ)
    (E : ∀ b, (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K)) :
    (Fin n → K) →ₗ[K] (Fin n → K) :=
  ∑ b ∈ Finset.range (d.length - 1),
    (blkIn n d b) ∘ₗ ((E b).toLinearMap ∘ₗ (blkOut n d b))

private theorem q2cFBA_diagMap_blkIn (hd : IsCut n d) {b' : ℕ} (hb' : b' + 1 < d.length)
    (E : ∀ b, (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K))
    (w : Fin (blockSize d b') → K) :
    q2cFBA_diagMap n d E (blkIn n d b' w) = blkIn n d b' ((E b').toLinearMap w) := by
  simp only [q2cFBA_diagMap, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [Finset.sum_eq_single b']
  · rw [blkOut_blkIn hd hb']
  · intro b hb hne
    rw [Finset.mem_range] at hb
    rw [blkOut_blkIn_of_ne hd (by omega) hb' hne, map_zero, map_zero]
  · intro hb
    exact absurd (by rw [Finset.mem_range]; omega) hb

private theorem q2cFBA_diagMap_mem_Vsub (hd : IsCut n d) {i : ℕ} (hi : i < d.length)
    (E : ∀ b, (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K))
    {v : Fin n → K} (hv : v ∈ Vsub n (d.getD i 0)) :
    q2cFBA_diagMap n d E v ∈ Vsub n (d.getD i 0) := by
  have hsum : q2cFBA_diagMap n d E v =
      ∑ b ∈ Finset.range (d.length - 1),
        (blkIn n d b) ((E b).toLinearMap (blkOut n d b v)) := by
    simp only [q2cFBA_diagMap, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [hsum]
  refine Submodule.sum_mem (Vsub n (d.getD i 0)) ?_
  intro b hb
  rw [Finset.mem_range] at hb
  have hblen : b < d.length := by omega
  by_cases hbi : b + 1 ≤ i
  · exact Vsub_mono (K := K) (q2cFPt_getD_le hd hbi hi) (blkIn_mem_Vsub _)
  · have hib : i ≤ b := by omega
    have hcb : d.getD i 0 ≤ d.getD b 0 := q2cFPt_getD_le hd hib hblen
    rw [blkOut_of_mem_Vsub (Vsub_mono (K := K) hcb hv), map_zero, map_zero]
    exact Submodule.zero_mem _

private theorem q2cFBA_diagMap_comp (hd : IsCut n d)
    (E E' : ∀ b, (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K))
    (h : ∀ b w, (E' b).toLinearMap ((E b).toLinearMap w) = w) :
    (q2cFBA_diagMap n d E').comp (q2cFBA_diagMap n d E) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have hv : q2cFBA_diagMap n d E v =
      ∑ b ∈ Finset.range (d.length - 1),
        blkIn n d b ((E b).toLinearMap (blkOut n d b v)) := by
    simp only [q2cFBA_diagMap, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [hv, map_sum]
  conv_rhs => rw [← sum_blkIn_blkOut hd v]
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [Finset.mem_range] at hb
  rw [q2cFBA_diagMap_blkIn hd (by omega) E' ((E b).toLinearMap (blkOut n d b v)),
    h b (blkOut n d b v)]

private theorem q2cFBA_diagMap_comp' (hd : IsCut n d)
    (E E' : ∀ b, (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K))
    (h : ∀ b w, (E b).toLinearMap ((E' b).toLinearMap w) = w) :
    (q2cFBA_diagMap n d E).comp (q2cFBA_diagMap n d E') = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have hv : q2cFBA_diagMap n d E' v =
      ∑ b ∈ Finset.range (d.length - 1),
        blkIn n d b ((E' b).toLinearMap (blkOut n d b v)) := by
    simp only [q2cFBA_diagMap, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [hv, map_sum]
  conv_rhs => rw [← sum_blkIn_blkOut hd v]
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [Finset.mem_range] at hb
  rw [q2cFBA_diagMap_blkIn hd (by omega) E ((E' b).toLinearMap (blkOut n d b v)),
    h b (blkOut n d b v)]

private theorem q2cFBA_glLin_toLin_symm (F : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    glLin (Matrix.GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv F)) = F := by
  simp only [glLin]
  rw [MulEquiv.apply_symm_apply]
  ext x
  rfl

theorem exists_blockDiag (hd : IsCut n d)
    (E : ∀ b, (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K)) :
    ∃ e : GL (Fin n) K, StabV n d e ∧ ∀ b, b + 1 < d.length → ∀ w,
      glLin e (blkIn n d b w) = blkIn n d b (E b w) := by
  have hGF : (q2cFBA_diagMap n d (fun b => (E b).symm)).comp (q2cFBA_diagMap n d E) =
      LinearMap.id :=
    q2cFBA_diagMap_comp hd E (fun b => (E b).symm)
      (fun b w => LinearEquiv.symm_apply_apply (E b) w)
  have hFG : (q2cFBA_diagMap n d E).comp (q2cFBA_diagMap n d (fun b => (E b).symm)) =
      LinearMap.id :=
    q2cFBA_diagMap_comp' hd E (fun b => (E b).symm)
      (fun b w => LinearEquiv.apply_symm_apply (E b) w)
  let Feq : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofLinearMap (q2cFBA_diagMap n d E)
      (q2cFBA_diagMap n d (fun b => (E b).symm)) hFG hGF
  let e : GL (Fin n) K := Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv Feq)
  have he : glLin e = Feq := q2cFBA_glLin_toLin_symm Feq
  refine ⟨e, ?_, ?_⟩
  · intro i hi
    rw [he]
    change (Vsub n (d.getD i 0)).map (q2cFBA_diagMap n d E) = Vsub n (d.getD i 0)
    apply le_antisymm
    · rintro v ⟨w, hw, rfl⟩
      exact q2cFBA_diagMap_mem_Vsub hd hi E hw
    · intro v hv
      have hv' : q2cFBA_diagMap n d (fun b => (E b).symm) v ∈ Vsub n (d.getD i 0) :=
        q2cFBA_diagMap_mem_Vsub hd hi (fun b => (E b).symm) hv
      refine Submodule.mem_map.mpr ⟨_, hv', ?_⟩
      have hcomp := congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f v) hFG
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hcomp
  · intro b hb w
    rw [he]
    change q2cFBA_diagMap n d E (blkIn n d b w) = blkIn n d b ((E b).toLinearMap w)
    exact q2cFBA_diagMap_blkIn hd hb E w

section Sigma

variable [Finite K] (f : ℕ) [CharP K 2]

private theorem q2cFBA_blkOut_apply (b : ℕ) (v : Fin n → K) (t : Fin (blockSize d b)) :
    blkOut n d b v t =
      if h : d.getD b 0 + t.val < n then v ⟨d.getD b 0 + t.val, h⟩ else 0 :=
  rfl

private theorem q2cFBA_blkIn_apply (b : ℕ) (w : Fin (blockSize d b) → K) (k : Fin n) :
    blkIn n d b w k =
      if h : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0 then
        w ⟨k.val - d.getD b 0, by simp only [blockSize]; omega⟩ else 0 :=
  rfl

theorem sgv_blkIn {b : ℕ} (w : Fin (blockSize d b) → K) :
    sgv K f n (blkIn n d b w) = blkIn n d b (sgv K f (blockSize d b) w) := by
  funext k
  simp only [sgv_apply, q2cFBA_blkIn_apply]
  by_cases h : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, map_zero]

private theorem q2cFBA_hermLin_apply (lo hi : ℕ) (u v : Fin n → K) :
    hermLin K f n lo hi u v =
      ∑ i : Fin n, if lo ≤ i.val ∧ i.val < hi then sg K f (u i) * v i else 0 := by
  rw [hermLin, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : lo ≤ i.val ∧ i.val < hi <;> simp [h]

private theorem q2cFBA_hermLin_blkOut (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (u v : Fin n → K) :
    hermLin K f n (d.getD b 0) (d.getD (b + 1) 0) u v =
      hermLin K f (blockSize d b) 0 (blockSize d b) (blkOut n d b u) (blkOut n d b v) := by
  have hc : d.getD (b + 1) 0 ≤ n := q2cFPt_le_last hd hb
  rw [q2cFBA_hermLin_apply, q2cFBA_hermLin_apply]
  have hR : (∑ t : Fin (blockSize d b),
      (if 0 ≤ t.val ∧ t.val < blockSize d b then
        sg K f (blkOut n d b u t) * blkOut n d b v t else 0))
      = ∑ t : Fin (blockSize d b), sg K f (blkOut n d b u t) * blkOut n d b v t := by
    exact Finset.sum_congr rfl fun t _ => by rw [if_pos ⟨Nat.zero_le _, t.isLt⟩]
  rw [hR, ← Finset.sum_filter]
  have hab : d.getD b 0 ≤ d.getD (b + 1) 0 := le_of_lt (hd.strict b hb)
  have hc : d.getD (b + 1) 0 ≤ n := q2cFPt_le_last hd hb
  let hii : ∀ a ∈ Finset.univ.filter (fun i : Fin n =>
      d.getD b 0 ≤ i.val ∧ i.val < d.getD (b + 1) 0), Fin (blockSize d b) :=
    fun i hi => ⟨i.val - d.getD b 0, by
      have h1 : d.getD b 0 ≤ i.val := (Finset.mem_filter.mp hi).2.1
      have h2 : i.val < d.getD (b + 1) 0 := (Finset.mem_filter.mp hi).2.2
      simp only [blockSize]
      omega⟩
  let hjj : ∀ t ∈ (Finset.univ : Finset (Fin (blockSize d b))), Fin n :=
    fun t _ => ⟨d.getD b 0 + t.val, by
      have := t.isLt
      simp only [blockSize] at this
      omega⟩
  refine Finset.sum_bij' hii hjj (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · dsimp only [hjj]
      omega
    · dsimp only [hjj]
      have := t.isLt
      simp only [blockSize] at this
      omega
  · intro a ha
    apply Fin.ext
    dsimp only [hjj, hii]
    have h1 : d.getD b 0 ≤ a.val := (Finset.mem_filter.mp ha).2.1
    omega
  · intro t ht
    apply Fin.ext
    dsimp only [hii, hjj]
    have := t.isLt
    simp only [blockSize] at this
    omega
  · intro a ha
    have h1 : d.getD b 0 ≤ a.val := (Finset.mem_filter.mp ha).2.1
    have h2 : a.val < d.getD (b + 1) 0 := (Finset.mem_filter.mp ha).2.2
    have hbu : (blkOut n d b u) (hii a ha) = u a := by
      dsimp only [hii]
      rw [q2cFBA_blkOut_apply,
        dif_pos (show d.getD b 0 + (a.val - d.getD b 0) < n by omega)]
      exact congrArg u (Fin.ext (Nat.add_sub_of_le h1))
    have hbv : (blkOut n d b v) (hii a ha) = v a := by
      dsimp only [hii]
      rw [q2cFBA_blkOut_apply,
        dif_pos (show d.getD b 0 + (a.val - d.getD b 0) < n by omega)]
      exact congrArg v (Fin.ext (Nat.add_sub_of_le h1))
    rw [hbu, hbv]

private theorem q2cFBA_sgS_map_blkIn (hK : Nat.card K = (2 ^ f) ^ 2) {b : ℕ}
    (U : Submodule K (Fin (blockSize d b) → K)) :
    sgS K f n (U.map (blkIn n d b)) = (sgS K f (blockSize d b) U).map (blkIn n d b) := by
  ext v
  rw [mem_sgS, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    refine Submodule.mem_map.mpr ⟨sgv K f (blockSize d b) w, ?_, ?_⟩
    · rw [mem_sgS, sgv_sgv hK]
      exact hw
    · have h := congrArg (sgv K f n) hwv
      rw [sgv_blkIn, sgv_sgv hK] at h
      exact h
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hv
    refine ⟨sgv K f (blockSize d b) w, ?_, ?_⟩
    · rwa [mem_sgS] at hw
    · have h := congrArg (sgv K f n) hwv
      rw [sgv_blkIn] at h
      exact h

theorem sgS_sup_map_blkIn (hK : Nat.card K = (2 ^ f) ^ 2) {b : ℕ}
    (U : Submodule K (Fin (blockSize d b) → K)) :
    sgS K f n (Vsub n (d.getD b 0) ⊔ U.map (blkIn n d b)) =
      Vsub n (d.getD b 0) ⊔ (sgS K f (blockSize d b) U).map (blkIn n d b) := by
  rw [sgS_sup hK, sgS_Vsub, q2cFBA_sgS_map_blkIn (f := f) hK]

private theorem q2cFBA_perpB_eq_comap (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (X : Submodule K (Fin n → K)) :
    perpB K f n (d.getD b 0) (d.getD (b + 1) 0) X =
      (perpB K f (blockSize d b) 0 (blockSize d b) (X.map (blkOut n d b))).comap
        (blkOut n d b) := by
  ext v
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_comap]
  constructor
  · intro hv w hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [← q2cFBA_hermLin_blkOut (f := f) hd hb u v]
    exact hv u hu
  · intro hv u hu
    rw [q2cFBA_hermLin_blkOut (f := f) hd hb u v]
    exact hv (blkOut n d b u) ⟨u, hu, rfl⟩

theorem perpB_inf_Vsub_eq (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (X : Submodule K (Fin n → K)) :
    perpB K f n (d.getD b 0) (d.getD (b + 1) 0) X ⊓ Vsub n (d.getD (b + 1) 0) =
      Vsub n (d.getD b 0) ⊔
        (perpB K f (blockSize d b) 0 (blockSize d b) (X.map (blkOut n d b))).map
          (blkIn n d b) := by
  rw [q2cFBA_perpB_eq_comap (f := f) hd hb X]
  apply le_antisymm
  · rintro v ⟨hv, hvc⟩
    have hdecomp : v - blkIn n d b (blkOut n d b v) ∈ Vsub n (d.getD b 0) :=
      sub_blkIn_blkOut_mem_Vsub hd hb hvc
    have h2 : blkIn n d b (blkOut n d b v) ∈
        (perpB K f (blockSize d b) 0 (blockSize d b) (X.map (blkOut n d b))).map
          (blkIn n d b) :=
      Submodule.mem_map.mpr ⟨blkOut n d b v, hv, rfl⟩
    have : v = (v - blkIn n d b (blkOut n d b v)) + blkIn n d b (blkOut n d b v) := by abel
    rw [this]
    exact add_mem (Submodule.mem_sup_left hdecomp) (Submodule.mem_sup_right h2)
  · refine le_inf (sup_le ?_ ?_) (sup_le ?_ ?_)
    · intro v hv
      rw [Submodule.mem_comap, blkOut_of_mem_Vsub hv]
      exact Submodule.zero_mem _
    · intro v hv
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
      rw [Submodule.mem_comap, blkOut_blkIn hd hb]
      exact hy
    · intro v hv
      exact Vsub_mono (K := K) (q2cFPt_getD_le hd (by omega) hb) hv
    · intro v hv
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
      exact blkIn_mem_Vsub y

end Sigma

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

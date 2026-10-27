module

public import CFSG.Monster.B.Dyadic.Data
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.Algebra.BigOperators.Field
public import Certificates.Certificate3106
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Dyadic

open Module CFSG.Monster.B.Dyadic.Native CFSG.KC.BM.Lat

@[expose] def Bq : Matrix (Fin 4371) (Fin 4371) ℚ := fun i j => (Bmat i j : ℚ) / 128

theorem Bmat_lower {i j : Fin 4371} (h : j < i) : Bmat i j = 0 := by
  rw [Bmat_apply, Bz, basis_facts.lower i i.2 j h]
  rfl

theorem Bmat_diag
    (i : Fin 4371) : Bmat i i = 2 ^ diagExpK[(i : ℕ)]! := by
  rw [Bmat_apply, Bz, basis_facts.diag i i.2]
  push_cast
  rfl

theorem Bq_isUpperTriangular :
    Bq.IsUpperTriangular := fun i j h => by
  rw [Bq, Bmat_lower (show j < i from h), Int.cast_zero, zero_div]

theorem diagExp_le
    (i : Fin 4371) : diagExpK[(i : ℕ)]! ≤ 7 := basis_facts.pexp_le i i.2

theorem Bq_diag
    (i : Fin 4371) : Bq i i = ((2 : ℚ) ^ (7 - diagExpK[(i : ℕ)]!))⁻¹ := by
  have h := diagExp_le i
  have e : (128 : ℚ) = 2 ^ diagExpK[(i : ℕ)]! * 2 ^ (7 - diagExpK[(i : ℕ)]!) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
    norm_num
  rw [Bq, Bmat_diag]
  push_cast
  rw [e]
  field_simp

theorem list_sum_range (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.sum_range_succ, Finset.sum_range_succ, list_sum_range f n]

theorem diag_stats :
    (List.range 8).map (expCountOf diagExpK) = [0, 12, 284, 993, 1782, 1035, 243, 22] ∧
      expDefectOf diagExpK = 13123 :=
  Certificates.certificate3103.1

theorem expDefect_eq :
    ∑ i : Fin 4371, (7 - diagExpK[(i : ℕ)]!) = 13123 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => 7 - diagExpK[i]!) 4371, ← list_sum_range]
  exact diag_stats.2

theorem det_Bq :
    Bq.det = ((2 : ℚ) ^ 13123)⁻¹ := by
  rw [Matrix.det_of_isUpperTriangular Bq_isUpperTriangular]
  simp_rw [Bq_diag]
  rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, expDefect_eq]

theorem det_Bq_ne_zero :
    Bq.det ≠ 0 := by
  rw [det_Bq]
  positivity

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (R : Basis (Fin 4371) ℚ V)

theorem ell_eq (i : Fin 4371) : ell R i = ∑ j, Bq i j • R j := by
  rw [ell, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, Bq, one_div, inv_mul_eq_div]
  norm_num

theorem repr_ell (i j : Fin 4371) : R.repr (ell R i) j = Bq i j := by
  rw [ell_eq, Basis.repr_sum_self]

theorem toMatrix_ell : R.toMatrix (ell R) = Bq.transpose := by
  ext i j
  rw [Basis.toMatrix_apply, repr_ell, Matrix.transpose_apply]

theorem det_ell :
    R.det (ell R) = ((2 : ℚ) ^ 13123)⁻¹ := by
  rw [Basis.det_apply, toMatrix_ell, Matrix.det_transpose, det_Bq]

@[expose] noncomputable def ellBasis :
    Basis (Fin 4371) ℚ V :=
  have h := (R.is_basis_iff_det (v := ell R)).2 (by
    rw [det_ell]
    exact isUnit_iff_ne_zero.2 (by positivity))
  Basis.mk h.1 h.2.ge

theorem coe_ellBasis :
    ⇑(ellBasis R) = ell R := by
  unfold ellBasis
  rw [Basis.coe_mk]

theorem ell_linIndep_int :
    LinearIndependent ℤ (ell R) := by
  have := (ellBasis R).linearIndependent
  rw [coe_ellBasis] at this
  exact this.restrict_scalars' ℤ

@[expose] noncomputable def ellZBasis :
    Basis (Fin 4371) ℤ (Lam R) :=
  Basis.span (ell_linIndep_int R)

theorem coe_ellZBasis
    (i : Fin 4371) : (ellZBasis R i : V) = ell R i := by
  unfold ellZBasis
  exact congrArg Subtype.val (Basis.span_apply (ell_linIndep_int R) i)

theorem span_Lam :
    Submodule.span ℚ (Lam R : Set V) = ⊤ := by
  rw [eq_top_iff, ← (ellBasis R).span_eq, coe_ellBasis]
  exact Submodule.span_mono (Submodule.subset_span (R := ℤ))

@[expose] def rawLat : Submodule ℤ V := Submodule.span ℤ (Set.range R)

theorem ell_mem_Lam (i : Fin 4371) : ell R i ∈ Lam R := Submodule.subset_span ⟨i, rfl⟩

theorem zsum_ell (c : Fin 4371 → ℤ) :
    ∑ t, c t • ell R t = ∑ j, (∑ t, (c t : ℚ) * Bq t j) • R j := by
  simp_rw [ell_eq, Finset.smul_sum, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_smul]

theorem R_mem_Lam (k : Fin 4371) : R k ∈ Lam R := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (sing_mem_rowLat k k.2)
  have key : ∀ j : Fin 4371, ∑ t, (c t : ℚ) * Bq t j = if k = j then 1 else 0 := by
    intro j
    have hj := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Bvec, byteVec, sing] at hj
    have hj' : ∑ t, (c t : ℚ) * (Bmat t j : ℚ) = if (j : ℕ) = k then 128 else 0 := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hj
      rw [Finset.sum_congr rfl fun t _ => by rw [Bmat_apply, Bz]]
      simpa [apply_ite] using this
    simp only [Bq, mul_div_assoc']
    rw [← Finset.sum_div, hj']
    by_cases h : k = j
    · subst h
      simp
    · rw [ite_eq_right (fun e => h (Fin.ext e.symm)), ite_eq_right h]
      simp
  have : ∑ t, c t • ell R t = R k := by
    rw [zsum_ell]
    simp_rw [key, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp
  rw [← this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (ell_mem_Lam R t)

theorem rawLat_le_Lam : rawLat R ≤ Lam R :=
  Submodule.span_le.2 (Set.range_subset_iff.2 (R_mem_Lam R))

set_option exponentiation.threshold 16384 in
theorem relIndex_rawLat_Lam :
    (rawLat R).toAddSubgroup.relIndex (Lam R).toAddSubgroup = 2 ^ 13123 := by
  have h := AddSubgroup.relIndex_eq_abs_det (rawLat R).toAddSubgroup (Lam R).toAddSubgroup
    (rawLat_le_Lam R) R (ellBasis R) (Submodule.span_int_eq_addSubgroupClosure _)
    (by rw [coe_ellBasis]; exact Submodule.span_int_eq_addSubgroupClosure _)
  have h1 := Basis.toMatrix_mul_toMatrix_flip (ellBasis R) R
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one, ← Basis.det_apply, ← Basis.det_apply, coe_ellBasis,
    det_ell] at h2
  rw [eq_inv_of_mul_eq_one_left h2, inv_inv, abs_of_pos (by positivity)] at h
  exact_mod_cast h

@[expose] def parMat (sh : ℕ) (M : Array (Array (ℕ × UInt32))) :
    Matrix (Fin 4371) (Fin 4371) (ZMod 2) :=
  fun k t => if Binary.Native.rowBit (binRow sh basisRowsK diagExpK M k) t then 1 else 0

structure ReducesOn (N : V →ₗ[ℚ] V) (sh : ℕ) (M : Array (Array (ℕ × UInt32)))
    (num : ℕ → ℕ → ℤ) : Prop where
  sh_le : sh ≤ 24
  num_eq : ∀ s u, entrySum (M[s]!).toList u = (num s u : ZMod 4294967296)
  act : ∀ t, N (R t) = ∑ u : Fin 4371, ((num t u : ℚ) / 2 ^ sh) • R u
  ok : ∀ i < 4371, (reduceRow sh basisRowsK diagExpK M i).isSome

variable {R} in
theorem ell_image_of
    {N : V →ₗ[ℚ] V} {sh : ℕ} {M : Array (Array (ℕ × UInt32))}
    {num : ℕ → ℕ → ℤ} (h : ReducesOn R N sh M num) (i : Fin 4371) :
    ∃ c : Fin 4371 → ℤ, N (ell R i) = ∑ t, (c t : ℚ) • ell R t ∧
      ∀ t, (c t : ZMod 2) = parMat sh M i t := by
  obtain ⟨qs, hqs⟩ := Option.isSome_iff_exists.1 (h.ok i i.2)
  obtain ⟨hdiv, c, hc1, hc2⟩ := reduce_row_of sh h.sh_le M num h.num_eq hqs
  refine ⟨c, ?_, fun t => by rw [hc2 t, parMat, rowBit_binRow sh M hqs t.2]⟩
  have hpos : (2 : ℚ) ^ sh ≠ 0 := by positivity
  have hX : ∀ u : Fin 4371, ∑ s : Fin 4371, Bq i s * ((num s u : ℚ) / 2 ^ sh) =
      ∑ t : Fin 4371, (c t : ℚ) * Bq t u := by
    intro u
    have h1 : ((∑ t : Fin 4371, Bz i t * num t u : ℤ) : ℚ) =
        2 ^ sh * ∑ t : Fin 4371, (c t : ℚ) * (Bz t u : ℚ) := by
      rw [← Int.ediv_mul_cancel (hdiv u), hc1 u]
      push_cast [Int.cast_sum]
      ring
    push_cast [Int.cast_sum] at h1
    simp only [Bq, Bmat_apply]
    rw [show ∑ x : Fin 4371, (Bz i x : ℚ) / 128 * ((num x u : ℚ) / 2 ^ sh) =
        (∑ x : Fin 4371, (Bz i x : ℚ) * (num x u : ℚ)) / (2 ^ sh * 128) by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      field_simp, h1, mul_div_mul_left _ _ hpos,
      show ∑ x : Fin 4371, (c x : ℚ) * ((Bz x u : ℚ) / 128) =
        (∑ x : Fin 4371, (c x : ℚ) * (Bz x u : ℚ)) / 128 by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring]
  have hL : N (ell R i) =
      ∑ u : Fin 4371, (∑ s : Fin 4371, Bq i s * ((num s u : ℚ) / 2 ^ sh)) • R u := by
    rw [ell_eq, map_sum]
    simp_rw [map_smul, h.act, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_smul]
  have hR : ∑ t, (c t : ℚ) • ell R t = ∑ u : Fin 4371, (∑ t, (c t : ℚ) * Bq t u) • R u := by
    simp_rw [ell_eq, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_smul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun u _ => by rw [hX u]

variable {R} in
theorem lam_mapsTo_of
    {N : V →ₗ[ℚ] V} {sh : ℕ} {M : Array (Array (ℕ × UInt32))}
    {num : ℕ → ℕ → ℤ} (h : ReducesOn R N sh M num) : ∀ x ∈ Lam R, N x ∈ Lam R := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => N x ∈ Lam R) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc, -⟩ := ell_image_of h i
    rw [hc]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (ell_mem_Lam R t)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [map_zsmul]
    exact Submodule.smul_mem _ a hx

@[expose] noncomputable def lamEnd (N : V →ₗ[ℚ] V) (h : ∀ x ∈ Lam R, N x ∈ Lam R) :
    Lam R →ₗ[ℤ] Lam R :=
  (N.restrictScalars ℤ).restrict h

theorem coe_lamEnd (N : V →ₗ[ℚ] V) (h : ∀ x ∈ Lam R, N x ∈ Lam R) (x : Lam R) :
    (lamEnd R N h x : V) = N x := rfl

@[expose] noncomputable def modTwoMap {M : Type*} [AddCommGroup M] (φ : M →ₗ[ℤ] M) :
    ModN M 2 →ₗ[ZMod 2] ModN M 2 :=
  ((LinearMap.range (LinearMap.lsmul ℤ M ((2 : ℕ) : ℤ))).mapQ _ φ (by
    rintro _ ⟨y, rfl⟩
    exact ⟨φ y, by simp⟩)).toAddMonoidHom.toZModLinearMap 2

theorem modTwoMap_mkQ {M : Type*} [AddCommGroup M] (φ : M →ₗ[ℤ] M) (x : M) :
    modTwoMap φ (ModN.mkQ 2 x) = ModN.mkQ 2 (φ x) := rfl

theorem mkQ_zsmul {M : Type*} [AddCommGroup M] (c : ℤ) (x : M) :
    ModN.mkQ 2 (c • x) = (c : ZMod 2) • ModN.mkQ 2 x := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

variable {R} in
theorem modTwo_ell_of
    {N : V →ₗ[ℚ] V} {sh : ℕ} {M : Array (Array (ℕ × UInt32))}
    {num : ℕ → ℕ → ℤ} (h : ReducesOn R N sh M num) (hm : ∀ x ∈ Lam R, N x ∈ Lam R)
    (k : Fin 4371) :
    modTwoMap (lamEnd R N hm) (ModN.basis (ellZBasis R) k) =
      ∑ l, parMat sh M k l • ModN.basis (ellZBasis R) l := by
  rw [ModN.basis_apply_eq_mkQ, modTwoMap_mkQ]
  obtain ⟨c, hc, hpar⟩ := ell_image_of h k
  have h' : lamEnd R N hm (ellZBasis R k) = ∑ l, c l • ellZBasis R l := by
    apply Subtype.ext
    rw [Submodule.coe_sum, coe_lamEnd, coe_ellZBasis, hc]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Submodule.coe_smul, coe_ellZBasis, Int.cast_smul_eq_zsmul]
  rw [h', map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mkQ_zsmul, hpar, ModN.basis_apply_eq_mkQ]

theorem reducesOn_packet (j : ℕ) (N : V →ₗ[ℚ] V)
    (hN : ∀ t, N (R t) = ∑ u : Fin 4371, ((numerAt j t u : ℚ) / 8) • R u)
    (hok : ∀ i < 4371, (reduceRow 3 basisRowsK diagExpK (packetMat j) i).isSome) :
    ReducesOn R N 3 (packetMat j) (numerAt j) where
  sh_le := by norm_num
  num_eq := entrySum_packetMat j
  act t := by rw [hN t]; norm_num
  ok := hok

theorem Bzq_isUpperTriangular :
    Bzq.IsUpperTriangular := fun i j h => by
  change (Bz i j : ℚ) = 0
  rw [← Bmat_apply, Bmat_lower (show j < i from h), Int.cast_zero]

theorem isUnit_det_Bzq : IsUnit Bzq.det := by
  rw [Matrix.det_of_isUpperTriangular Bzq_isUpperTriangular]
  refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
  change (Bz i i : ℚ) ≠ 0
  rw [← Bmat_apply, Bmat_diag]
  positivity

theorem Cnum_mul_Bzq (g : Fin 26) : Cnum g * Bzq = Bzq * Mq g := by
  rw [Cnum, Matrix.mul_assoc (Bzq * Mq g), Matrix.nonsing_inv_mul (A := Bzq) isUnit_det_Bzq,
    Matrix.mul_one]

theorem Cnum_num (g : Fin 26) (i t : Fin 4371) :
    ((Cnum g i t).num : ℚ) = Cnum g i t :=
  Rat.coe_int_num_of_den_eq_one (Certificates.certificate3106 g i t)

theorem ell_image
    (g : Fin 26) (N : V →ₗ[ℚ] V)
    (hN : ∀ t, N (R t) = ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) (i : Fin 4371) :
    ∃ c : Fin 4371 → ℤ, N (ell R i) = ∑ t, (c t : ℚ) • ell R t ∧
      ∀ t, (c t : ZMod 2) = Cmat g i t := by
  refine ⟨fun t => (Cnum g i t).num, ?_, fun t => rfl⟩
  have hX : ∀ u : Fin 4371, ∑ s : Fin 4371, Bq i s * ((numer g s u : ℚ) / 8) =
      ∑ t : Fin 4371, ((Cnum g i t).num : ℚ) * Bq t u := by
    intro u
    have h := congrFun (congrFun (Cnum_mul_Bzq g) i) u
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    simp only [Cnum_num]
    calc ∑ s : Fin 4371, Bq i s * ((numer g s u : ℚ) / 8) =
        (∑ s : Fin 4371, Bzq i s * Mq g s u) / 128 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun s _ => ?_
          change (Bz i s : ℚ) / 128 * ((numer g s u : ℚ) / 8) =
            (Bz i s : ℚ) * ((numer g s u : ℚ) / 8) / 128
          ring
      _ = (∑ t : Fin 4371, Cnum g i t * Bzq t u) / 128 := by rw [h]
      _ = ∑ t : Fin 4371, Cnum g i t * Bq t u := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun t _ => ?_
          change Cnum g i t * (Bz t u : ℚ) / 128 = Cnum g i t * ((Bz t u : ℚ) / 128)
          ring
  have hL : N (ell R i) =
      ∑ u : Fin 4371, (∑ s : Fin 4371, Bq i s * ((numer g s u : ℚ) / 8)) • R u := by
    rw [ell_eq, map_sum]
    simp_rw [map_smul, hN, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_smul]
  have hR : ∑ t, ((Cnum g i t).num : ℚ) • ell R t =
      ∑ u : Fin 4371, (∑ t, ((Cnum g i t).num : ℚ) * Bq t u) • R u := by
    simp_rw [ell_eq, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_smul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun u _ => by rw [hX u]

theorem lam_mapsTo
    (g : Fin 26) (N : V →ₗ[ℚ] V)
    (hN : ∀ t, N (R t) = ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) :
    ∀ x ∈ Lam R, N x ∈ Lam R := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => N x ∈ Lam R) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc, -⟩ := ell_image R g N hN i
    rw [hc]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (ell_mem_Lam R t)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [map_zsmul]
    exact Submodule.smul_mem _ a hx

theorem modTwo_ell
    (g : Fin 26) (N : V →ₗ[ℚ] V)
    (hN : ∀ t, N (R t) = ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u)
    (hm : ∀ x ∈ Lam R, N x ∈ Lam R) (k : Fin 4371) :
    modTwoMap (lamEnd R N hm) (ModN.basis (ellZBasis R) k) =
      ∑ l, Cmat g k l • ModN.basis (ellZBasis R) l := by
  rw [ModN.basis_apply_eq_mkQ, modTwoMap_mkQ]
  obtain ⟨c, hc, hpar⟩ := ell_image R g N hN k
  have h' : lamEnd R N hm (ellZBasis R k) = ∑ l, c l • ellZBasis R l := by
    apply Subtype.ext
    rw [Submodule.coe_sum, coe_lamEnd, coe_ellZBasis, hc]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Submodule.coe_smul, coe_ellZBasis, Int.cast_smul_eq_zsmul]
  rw [h', map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mkQ_zsmul, hpar, ModN.basis_apply_eq_mkQ]

theorem toMatrix_modTwo
    (g : Fin 26) (N : V →ₗ[ℚ] V)
    (hN : ∀ t, N (R t) = ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u)
    (hm : ∀ x ∈ Lam R, N x ∈ Lam R) :
    (LinearMap.toMatrix (ModN.basis (ellZBasis R)) (ModN.basis (ellZBasis R))
      (modTwoMap (lamEnd R N hm))).transpose = Cmat g := by
  ext k l
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, modTwo_ell R g N hN hm,
    Basis.repr_sum_self]

theorem den_Bq_diag
    (i : Fin 4371) : (Bq i i).den = 2 ^ (7 - diagExpK[(i : ℕ)]!) := by
  rw [Bq_diag, show ((2 : ℚ) ^ (7 - diagExpK[(i : ℕ)]!)) = ((2 ^ (7 - diagExpK[(i : ℕ)]!) : ℕ) : ℚ)
    by push_cast; rfl, Rat.inv_natCast_den, ite_eq_right (by positivity)]

theorem expCount_card (k : ℕ) :
    (Finset.univ.filter fun i : Fin 4371 => diagExpK[(i : ℕ)]! = k).card = expCountOf diagExpK k := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if diagExpK[i]! = k then 1 else 0)
    4371, ← list_sum_range]
  rfl

theorem diag_den_count (e : Fin 7) :
    (Finset.univ.filter fun i : Fin 4371 => (Bq i i).den = 2 ^ (e : ℕ)).card =
      ![22, 243, 1035, 1782, 993, 284, 12] e := by
  have hfilter : (Finset.univ.filter fun i : Fin 4371 => (Bq i i).den = 2 ^ (e : ℕ)) =
      Finset.univ.filter fun i : Fin 4371 => diagExpK[(i : ℕ)]! = 7 - e := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, den_Bq_diag]
    rw [Nat.pow_right_injective (le_refl 2) |>.eq_iff]
    have := diagExp_le i
    have := e.2
    omega
  rw [hfilter, expCount_card]
  have h := diag_stats.1
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq] at h
  fin_cases e <;> simp [h]

theorem den_Bq_diag_le
    (i : Fin 4371) : ∃ e < 7, (Bq i i).den = 2 ^ e := by
  refine ⟨7 - diagExpK[(i : ℕ)]!, ?_, den_Bq_diag i⟩
  by_contra hcon
  have h0 : diagExpK[(i : ℕ)]! = 0 := by omega
  have hc := expCount_card 0
  have h := diag_stats.1
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq] at h
  rw [h.1] at hc
  have : i ∈ Finset.univ.filter fun i : Fin 4371 => diagExpK[(i : ℕ)]! = 0 := by simp [h0]
  rw [Finset.card_eq_zero.1 hc] at this
  simp at this

theorem den_Bq_dvd (i j : Fin 4371) : (Bq i j).den ∣ 128 := by
  have h := Rat.den_dvd (Bmat i j) 128
  rw [← Rat.intCast_div_eq_divInt] at h
  have : (Bq i j) = ((Bmat i j : ℤ) : ℚ) / ((128 : ℤ) : ℚ) := by simp [Bq]
  rw [this]
  exact_mod_cast h

end CFSG.Monster.B.Dyadic

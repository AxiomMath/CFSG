module

public import CFSG.Monster.B.CTIB.Rep4371SpinBasis
public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphAdjBase
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Griess CFSG.Monster.Visible
  CFSG.Monster.SpinLattice CFSG.Monster.Spin CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.Rep4371
open CFSG.Monster.B.Co2 (v0)

theorem abs_trace_le_of_pow_eq_one {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) {n : ℕ} (hn : n ≠ 0)
    (hA : A ^ n = 1) : |A.trace| ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Matrix.trace]
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set B : Matrix (Fin d) (Fin d) ℂ := A.map (algebraMap ℚ ℂ) with hB
  have hBn : B ^ n = 1 := by
    rw [hB, ← RingHom.mapMatrix_apply, ← map_pow, hA, map_one]
  have htr : B.trace = ((A.trace : ℚ) : ℂ) := by
    rw [hB, ← AddMonoidHom.map_trace (algebraMap ℚ ℂ) A]
    rfl
  have hroot : ∀ μ ∈ B.charpoly.roots, ‖μ‖ = 1 := by
    intro μ hμ
    have hsp : μ ∈ spectrum ℂ B :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (Polynomial.isRoot_of_mem_roots hμ)
    have h1 : μ ^ n ∈ spectrum ℂ (B ^ n) := spectrum.pow_mem_pow B n hsp
    rw [hBn, spectrum.one_eq, Set.mem_singleton_iff] at h1
    exact Complex.norm_eq_one_of_pow_eq_one h1 hn
  have key : ‖B.trace‖ ≤ d := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine (norm_multiset_sum_le _).trans ?_
    rw [Multiset.map_congr rfl hroot, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
      mul_one]
    have := Polynomial.card_roots' B.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    exact_mod_cast this
  rw [htr, Complex.norm_ratCast] at key
  exact_mod_cast key

theorem abs_trace_le_of_basis {M : Type*} [AddCommMonoid M] [Module ℚ M] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ M) (f : Module.End ℚ M) {n : ℕ} (hn : n ≠ 0) (hf : f ^ n = 1) :
    |LinearMap.trace ℚ M f| ≤ d := by
  rw [LinearMap.trace_eq_matrix_trace ℚ b]
  refine abs_trace_le_of_pow_eq_one _ hn ?_
  rw [LinearMap.toMatrix_pow, hf, LinearMap.toMatrix_one]

theorem restrict_pow_eq_one {M : Type*} [AddCommMonoid M] [Module ℚ M] {f : Module.End ℚ M}
    {p : Submodule ℚ M} (hf : ∀ x ∈ p, f x ∈ p) {n : ℕ} (hn : f ^ n = 1) :
    (f.restrict hf) ^ n = 1 := by
  ext x
  have h : (((f.restrict hf) ^ n) x : M) = (f ^ n) x := by
    rw [Module.End.pow_restrict]
    rfl
  rw [h, hn]
  rfl

theorem trace_rhoV
    (h : Shat) : LinearMap.trace ℚ Vst (rhoV h : Vst →ₗ[ℚ] Vst) =
    ∑ t : Fin 4371, Rbasis.repr (rhoV h (Rbasis t)) t := by
  rw [LinearMap.trace_eq_matrix_trace ℚ Rbasis, Matrix.trace]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rfl

theorem sum_fin_4371 (F : Fin 4371 → ℚ) :
    ∑ t, F t = ∑ t : Fin 23, F ⟨t, by omega⟩ + ∑ t : Fin 2300, F (xIdx t) +
      ∑ t : Fin 2048, F (tIdx t) := by
  have h1 := Fin.sum_univ_add (a := 23 + 2300) (b := 2048) F
  have h2 := Fin.sum_univ_add (a := 23) (b := 2300) fun t => F (Fin.castAdd 2048 t)
  rw [h1, h2]
  rfl

theorem rhoV_pow_apply (h : Shat) (n : ℕ) (v : Vst) :
    ((rhoV h : Vst →ₗ[ℚ] Vst) ^ n) v = rhoV (h ^ n) v := by
  induction n with
  | zero => rw [pow_zero, pow_zero, map_one]; rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', map_mul, LinearEquiv.mul_apply]
    rfl

theorem rhoV_pow_orderOf
    (h : Shat) : (rhoV h : Vst →ₗ[ℚ] Vst) ^ orderOf h = 1 := by
  refine LinearMap.ext fun v => ?_
  rw [rhoV_pow_apply, pow_orderOf_eq_one, map_one]
  rfl

theorem abs_eq_one_of_rhoV_eq_smul
    {h : Shat} {v : Vst} (hv : v ≠ 0) {c : ℚ}
    (hc : rhoV h v = c • v) : |c| = 1 := by
  have hk : ∀ k : ℕ, rhoV (h ^ k) v = c ^ k • v := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, map_one, one_smul]; rfl
    | succ k ih =>
      rw [pow_succ, map_mul, LinearEquiv.mul_apply, hc, map_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have h1 := hk (orderOf h)
  rw [pow_orderOf_eq_one, map_one, LinearEquiv.coe_one, id_eq] at h1
  obtain ⟨k, hk0⟩ : ∃ k, Rbasis.repr v k ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (Rbasis.ext_elem fun k => by rw [hc k, repr_zero'])
  have h2 : Rbasis.repr v k = Rbasis.repr (c ^ orderOf h • v) k :=
    congrArg (fun x => Rbasis.repr x k) h1
  rw [repr_smul] at h2
  have h3 : c ^ orderOf h = 1 := by
    have h4 : (c ^ orderOf h - 1) * Rbasis.repr v k = 0 := by rw [sub_mul, ← h2, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_right hk0)
  have h4 : |c| ^ orderOf h = 1 := by rw [← abs_pow, h3, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg c) (orderOf_pos h).ne').1 h4

theorem bV_sigma_eq_one_iff
    {x : Wv v0} (hx : x ∈ Unitary.OmegaW) :
    bV Unitary.sigmaW x = 1 ↔ x ∈ Unitary.usigOrbit Unitary.tauW := by
  constructor
  · intro h
    rw [Unitary.OmegaW_eq_union] at hx
    rcases hx with (hx | ⟨j, rfl⟩) | hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [bV_self] at h
      exact absurd h (by decide)
    · have h0 : bV Unitary.sigmaW (Unitary.sigmaW + Unitary.n6vec j) = 0 := by
        rw [map_add, bV_self, zero_add]
        exact LinearMap.mem_ker.1 (Unitary.n6vec_mem_sigmaPerp j)
      rw [h0] at h
      exact absurd h (by decide)
    · exact hx
  · exact bV_sigmaW_of_mem_tauOrb

theorem card_filter_bV_sigma :
    (Finset.univ.filter fun t : Fin 2300 => bV Unitary.sigmaW (aW t) = 1).card = 1408 := by
  rw [← Unitary.ncard_usigOrbit_tau, ← Set.ncard_coe_finset,
    ← Set.ncard_image_of_injective _ aW_injective]
  congr 1
  ext x
  simp only [Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (bV_sigma_eq_one_iff (aW_mem_OmegaW t)).1 ht
  · intro hx
    have hΩ := Unitary.tauOrb_subset hx
    rw [← range_aW] at hΩ
    obtain ⟨t, rfl⟩ := hΩ
    exact ⟨t, (bV_sigma_eq_one_iff (aW_mem_OmegaW t)).2 hx, rfl⟩

theorem sgn_eq_ite (b : ZMod 2) : sgn b = if b = 1 then -1 else 1 := by
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl
  · rw [sgn, ite_eq_left rfl, ite_eq_right (by decide)]
  · rw [sgn, ite_eq_right (by decide), ite_eq_left rfl]

theorem sum_sgn_bV_sigma :
    ∑ t : Fin 2300, sgn (bV Unitary.sigmaW (aW t)) = -516 := by
  simp_rw [sgn_eq_ite]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, card_filter_bV_sigma]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun t : Fin 2300 => bV Unitary.sigmaW (aW t) = 1)
  rw [card_filter_bV_sigma, Finset.card_univ, Fintype.card_fin] at hc
  rw [show (Finset.univ.filter fun t : Fin 2300 => ¬ bV Unitary.sigmaW (aW t) = 1).card = 892 by
    omega]
  norm_num

theorem trace_rhoV_cE :

    LinearMap.trace ℚ Vst (rhoV (ehatS cE) : Vst →ₗ[ℚ] Vst) = -493 := by
  rw [trace_rhoV, sum_fin_4371]
  have hA : ∑ t : Fin 23, Rbasis.repr (rhoV (ehatS cE) (Rbasis ⟨t, by omega⟩)) ⟨t, by omega⟩ =
      23 := by
    have h1 : ∀ t : Fin 23,
        Rbasis.repr (rhoV (ehatS cE) (Rbasis ⟨t, by omega⟩)) ⟨t, by omega⟩ = 1 := by
      intro t
      have hmem : Rbasis ⟨t, by omega⟩ ∈ V23 := by
        rw [mem_V23, coe_Rbasis]
        exact Rraw_mem_Across (k := (t : ℕ)) (by omega)
      rw [Ehat_trivial_V23 cE.2 hmem, Module.Basis.repr_self, Finsupp.single_eq_same]
    rw [Finset.sum_congr rfl fun t _ => h1 t, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  have hX : ∑ t : Fin 2300, Rbasis.repr (rhoV (ehatS cE) (Rbasis (xIdx t))) (xIdx t) =
      -516 := by
    rw [← sum_sgn_bV_sigma]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h1 := rhoV_Ehat_R (e := ehatS cE) cE.2 t
    rw [show (Rbasis ⟨23 + (t : ℕ), by omega⟩ : Vst) = Rbasis (xIdx t) from rfl] at h1
    rw [h1, repr_smul, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
    have e : (⟨((ehatS cE : Shat) : Dfull), cE.2⟩ : Ehat) = cE := rfl
    rw [e, psiW_cE]
  have hT : ∑ t : Fin 2048, Rbasis.repr (rhoV (ehatS cE) (Rbasis (tIdx t))) (tIdx t) =
      0 := by
    have h1 := trace_blkM_Ehat_eq_zero (e := cE) (by rw [psiW_cE]; exact Unitary.sigmaW_ne_zero)
    rw [Matrix.trace] at h1
    exact h1
  rw [hA, hX, hT]
  norm_num

theorem trace_rhoV_conj (g s : Shat) :
    LinearMap.trace ℚ Vst (rhoV (g⁻¹ * s * g) : Vst →ₗ[ℚ] Vst) =
      LinearMap.trace ℚ Vst (rhoV s : Vst →ₗ[ℚ] Vst) := by
  have e : (rhoV (g⁻¹ * s * g) : Vst →ₗ[ℚ] Vst) =
      ((rhoV g⁻¹ : Vst →ₗ[ℚ] Vst) * (rhoV s : Vst →ₗ[ℚ] Vst)) * (rhoV g : Vst →ₗ[ℚ] Vst) := by
    rw [map_mul, map_mul]
    rfl
  have e2 : (rhoV g : Vst →ₗ[ℚ] Vst) * (rhoV g⁻¹ : Vst →ₗ[ℚ] Vst) = 1 := by
    refine LinearMap.ext fun v => ?_
    show rhoV g (rhoV g⁻¹ v) = v
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [e, LinearMap.trace_mul_comm, ← mul_assoc, e2, one_mul]

theorem trace_rhoV_clabel
    (z : CVert) :
    ∃ s : Shat, (s : Dfull) = clabel z ∧ LinearMap.trace ℚ Vst (rhoV s : Vst →ₗ[ℚ] Vst) = -493 := by
  obtain ⟨g, rfl⟩ := cvOf_surjective z
  refine ⟨g⁻¹ * ehatS cE * g, ?_, by rw [trace_rhoV_conj, trace_rhoV_cE]⟩
  rw [clabel_cvOf]
  rfl

theorem trace_rhoV_clabel'
    (z : CVert) :
    (∃ s : Shat, (s : Dfull) = clabel z) ∧ ∀ s : Shat, (s : Dfull) = clabel z →
      LinearMap.trace ℚ Vst (rhoV s : Vst →ₗ[ℚ] Vst) = -493 := by
  obtain ⟨s₀, hs₀, htr⟩ := trace_rhoV_clabel z
  refine ⟨⟨s₀, hs₀⟩, fun s hs => ?_⟩
  rw [show s = s₀ from Subtype.ext (hs.trans hs₀.symm), htr]

@[expose] noncomputable def aIdx (k : Fin 23) : Fin 4371 := ⟨k, by omega⟩

theorem aIdx_injective : Function.Injective aIdx := fun k k' h =>
  Fin.ext (by simpa [aIdx] using congrArg Fin.val h)

theorem linearIndependent_RbA :
    LinearIndependent ℚ fun k : Fin 23 => Rbasis (aIdx k) :=
  Rbasis.linearIndependent.comp _ aIdx_injective

theorem Rbasis_aIdx_mem (k : Fin 23) : Rbasis (aIdx k) ∈ V23 := by
  rw [mem_V23, coe_Rbasis]
  exact Rraw_mem_Across (k := (k : ℕ)) (by omega)

theorem V23_eq_span :
    V23 = Submodule.span ℚ (Set.range fun k : Fin 23 => Rbasis (aIdx k)) := by
  apply le_antisymm
  · intro v hv
    have hv' : (v : SpaceB) ∈ Across isShortCoord_rStar := hv
    rw [Across_eq_span] at hv'
    have hmap : Submodule.span ℚ (Set.range fun k : Fin 23 => Rraw k) =
        (Submodule.span ℚ (Set.range fun k : Fin 23 => Rbasis (aIdx k))).map Vst.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 1
      ext x
      simp only [Set.mem_range, Function.comp_apply, Submodule.subtype_apply]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, by rw [coe_Rbasis]; rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, by rw [coe_Rbasis]; rfl⟩
    rw [hmap] at hv'
    obtain ⟨w, hw, hwv⟩ := hv'
    rw [← Subtype.ext hwv]
    exact hw
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Rbasis_aIdx_mem k

@[expose] noncomputable def basisV23 : Module.Basis (Fin 23) ℚ V23 :=
  (Module.Basis.span linearIndependent_RbA).map (LinearEquiv.ofEq _ _ V23_eq_span.symm)

@[expose] noncomputable def resV23
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) : Module.End ℚ V23 :=
  (rhoV h : Vst →ₗ[ℚ] Vst).restrict (Jhat_preserves hh).1

theorem abs_trace_resV23_le
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    |LinearMap.trace ℚ V23 (resV23 hh)| ≤ 23 := by
  have h1 := abs_trace_le_of_basis basisV23 (resV23 hh) (orderOf_pos h).ne'
    (restrict_pow_eq_one (Jhat_preserves hh).1 (rhoV_pow_orderOf h))
  exact_mod_cast h1

@[expose] noncomputable def basisV2300 :
    Module.Basis (Fin 2300) ℚ V2300 :=
  (Module.Basis.span linearIndependent_Rt).map (LinearEquiv.ofEq _ _ V2300_eq_span.symm)

theorem coe_basisV2300
    (t : Fin 2300) : (basisV2300 t : Vst) = Rt t := by
  rw [basisV2300, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]

theorem basisV2300_repr (x : V2300) (t : Fin 2300) :
    basisV2300.repr x t = Rbasis.repr (x : Vst) (xIdx t) := by
  have h : (Finsupp.lapply t).comp basisV2300.repr.toLinearMap =
      (Finsupp.lapply (xIdx t)).comp (Rbasis.repr.toLinearMap.comp V2300.subtype) := by
    refine basisV2300.ext fun s => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      Finsupp.lapply_apply, Submodule.subtype_apply, coe_basisV2300]
    rw [repr_Rt, Finsupp.single_apply]
    by_cases hst : s = t
    · rw [ite_eq_left hst, ite_eq_left (congrArg xIdx hst)]
    · rw [ite_eq_right hst, ite_eq_right (fun h' => hst (xIdx_injective h'))]
  exact LinearMap.congr_fun h x

@[expose] noncomputable def resV2300
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    Module.End ℚ V2300 :=
  (rhoV h : Vst →ₗ[ℚ] Vst).restrict (Jhat_preserves hh).2.1

theorem trace_resV2300
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    LinearMap.trace ℚ V2300 (resV2300 hh) =
      ∑ t : Fin 2300, Rbasis.repr (rhoV h (Rt t)) (xIdx t) := by
  rw [LinearMap.trace_eq_matrix_trace ℚ basisV2300, Matrix.trace]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, basisV2300_repr, resV2300,
    LinearMap.coe_restrict_apply, coe_basisV2300]
  rfl

theorem diag_eq_zero_of_moved
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) {t : Fin 2300}
    (hfix : wAct v0 (jhatToKv0 ⟨h, hh⟩) (aW t) ≠ aW t) :
    Rbasis.repr (rhoV h (Rt t)) (xIdx t) = 0 := by
  obtain ⟨t', ht', hmem⟩ := rhoV_Jhat_Rt hh t
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  rw [← hc, repr_smul, repr_Rt]
  have htt : t' ≠ t := by
    rintro rfl
    apply hfix
    have h1 := congrArg (wAct v0 (jhatToKv0 ⟨h, hh⟩)) ht'
    rw [Co2.wAct_apply_inv] at h1
    exact h1
  rw [ite_eq_right (fun h' => htt (xIdx_injective h')), mul_zero]

theorem abs_diag_le_one
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) (t : Fin 2300) :
    |Rbasis.repr (rhoV h (Rt t)) (xIdx t)| ≤ 1 := by
  obtain ⟨t', ht', hmem⟩ := rhoV_Jhat_Rt hh t
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  rw [← hc, repr_smul, repr_Rt]
  by_cases htt : t' = t
  · subst htt
    rw [ite_eq_left rfl, mul_one]
    exact (abs_eq_one_of_rhoV_eq_smul (Rt_ne_zero t') hc.symm).le
  · rw [ite_eq_right (fun h' => htt (xIdx_injective h')), mul_zero, abs_zero]
    norm_num

theorem abs_trace_resV2300_le
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    |LinearMap.trace ℚ V2300 (resV2300 hh)| ≤
      {x | x ∈ Unitary.OmegaW ∧ wAct v0 (jhatToKv0 ⟨h, hh⟩) x = x}.ncard := by
  classical
  rw [trace_resV2300]
  have hle : ∀ t : Fin 2300, |Rbasis.repr (rhoV h (Rt t)) (xIdx t)| ≤
      if wAct v0 (jhatToKv0 ⟨h, hh⟩) (aW t) = aW t then 1 else 0 := by
    intro t
    split_ifs with hfix
    · exact abs_diag_le_one hh t
    · rw [diag_eq_zero_of_moved hh hfix, abs_zero]
  have hset : aW '' ↑(Finset.univ.filter fun t : Fin 2300 =>
      wAct v0 (jhatToKv0 ⟨h, hh⟩) (aW t) = aW t) =
      {x | x ∈ Unitary.OmegaW ∧ wAct v0 (jhatToKv0 ⟨h, hh⟩) x = x} := by
    ext x
    simp only [Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨aW_mem_OmegaW t, ht⟩
    · rintro ⟨hx, hfix⟩
      rw [← range_aW] at hx
      obtain ⟨t, rfl⟩ := hx
      exact ⟨t, hfix, rfl⟩
  have hcard : (Finset.univ.filter fun t : Fin 2300 =>
      wAct v0 (jhatToKv0 ⟨h, hh⟩) (aW t) = aW t).card =
      {x | x ∈ Unitary.OmegaW ∧ wAct v0 (jhatToKv0 ⟨h, hh⟩) x = x}.ncard := by
    rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ aW_injective, hset]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun t _ => hle t).trans
    (le_of_eq ?_))
  rw [Finset.sum_boole, hcard]

end CFSG.Monster.B.CTIB

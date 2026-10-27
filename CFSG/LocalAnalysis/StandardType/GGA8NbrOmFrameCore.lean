module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmCompAlign
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpCompBlock

public section

namespace CFSG.StandardType

namespace A8Coord

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal SevOm CoordOm
open CFSG.RankThree.Classical2 (orthDerived)

theorem omf_const_of_spAligned {p n : ℕ} {β : Fin n → ZMod p} (hβal : CoordSp.SpAligned β)
    {c : ZMod p} (hc : c ≠ 0) (hpm : ∀ i, β i = c ∨ β i = -c) :
    ∃ c' : ZMod p, c' ≠ 0 ∧ ∀ i, β i = c' := by
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i₀⟩⟩
  · exact ⟨c, hc, fun i => isEmptyElim i⟩
  have hne : ∀ i, β i ≠ 0 := fun i h0 => by
    rcases hpm i with h | h
    · exact hc (h ▸ h0)
    · exact hc (neg_eq_zero.mp (h ▸ h0))
  refine ⟨β i₀, hne i₀, fun i => ?_⟩
  rcases hpm i with hi | hi <;> rcases hpm i₀ with h0 | h0
  · rw [hi, h0]
  · exact absurd (hβal i i₀ (by rw [hi, h0, neg_neg])) (hne i)
  · exact absurd (hβal i i₀ (by rw [hi, h0])) (hne i)
  · rw [hi, h0]

theorem omf_reciprocalPolynomial_X_sub_C {K : Type*} [Field K] {μ : K} (hμ : μ ≠ 0) :
    reciprocalPolynomial (X - C μ) = X - C μ⁻¹ := by
  have hc : -μ ≠ 0 := neg_ne_zero.mpr hμ
  have h0 : (X + C (-μ) : K[X]).coeff 0 = -μ := by simp
  have hX : (X : K[X]).reverse = 1 := by
    have := reverse_mul_X (1 : K[X])
    rw [one_mul] at this
    rw [this, show (1 : K[X]) = C 1 from C_1.symm, reverse_C]
  have h1 : (X + C (-μ) : K[X]).reverse = 1 + C (-μ) * X := by
    rw [reverse_add_C, hX, natDegree_X, pow_one]
  have e : (X - C μ : K[X]) = X + C (-μ) := by rw [C_neg, sub_eq_add_neg]
  rw [e, reciprocalPolynomial, h0, h1, mul_add, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1,
    one_mul, mul_one, inv_neg, C_neg, sub_eq_add_neg]
  ring

theorem omf_exists_inv_eigen_plane {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} [FiniteDimensional K V] {U : Submodule K V}
    (hU2 : finrank K U = 2)
    (hnd : ∀ u ∈ U, (∀ v ∈ U, QuadraticMap.polar Q v u = 0) → u = 0)
    {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) (hTU : ∀ u ∈ U, T u ∈ U)
    {u : V} (hu : u ∈ U) (hu0 : u ≠ 0) {ν : K} (hTu : T u = ν • u) (hν : ν ^ 2 ≠ 1) :
    ∃ w ∈ U, w ≠ 0 ∧ T w = ν⁻¹ • w ∧ ∀ v ∈ U, ∃ α γ : K, v = α • u + γ • w := by
  have hpolT : ∀ a b, QuadraticMap.polar Q (T a) (T b) = QuadraticMap.polar Q a b := by
    intro a b
    simp only [QuadraticMap.polar, ← map_add, hT]
  have huu : QuadraticMap.polar Q u u = 0 := by
    rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  obtain ⟨w', hw'U, hw'⟩ : ∃ w' ∈ U, QuadraticMap.polar Q u w' ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (hnd u hu fun v hv => by rw [QuadraticMap.polar_comm]; exact h v hv)
  have hind : ∀ s t : K, s • u + t • w' = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    have h1 := congrArg (QuadraticMap.polar Q u) hst
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_smul_right, huu, smul_zero, zero_add, QuadraticMap.polar_zero_right,
      smul_eq_mul] at h1
    have ht : t = 0 := (mul_eq_zero.mp h1).resolve_right hw'
    subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hu0, rfl⟩
  have hspan : ∀ v ∈ U, ∃ a b : K, v = a • u + b • w' := by
    have hli : LinearIndependent K ![u, w'] := LinearIndependent.pair_iff.mpr hind
    have hle : Submodule.span K (Set.range ![u, w']) ≤ U := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hu
      · exact hw'U
    have heq : Submodule.span K (Set.range ![u, w']) = U :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hli]; simp [hU2])
    intro v hv
    rw [← heq] at hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
    refine ⟨c 0, c 1, ?_⟩
    rw [← hc, Fin.sum_univ_two]
    simp
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hTu
    exact hu0 (T.injective (by rw [hTu, map_zero]))
  have hνne : ν⁻¹ - ν ≠ 0 := by
    intro h
    apply hν
    have : ν⁻¹ = ν := sub_eq_zero.mp h
    calc ν ^ 2 = ν * ν := sq ν
      _ = ν⁻¹ * ν := by rw [this]
      _ = 1 := inv_mul_cancel₀ hν0
  obtain ⟨α, δ, hTw'⟩ := hspan (T w') (hTU w' hw'U)
  have hδ : δ = ν⁻¹ := by
    have h1 := hpolT u w'
    rw [hTu, hTw', QuadraticMap.polar_smul_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, huu, smul_zero, zero_add,
      smul_eq_mul, smul_eq_mul] at h1
    have h2 : (ν * δ - 1) * QuadraticMap.polar Q u w' = 0 := by
      rw [sub_mul, mul_assoc, h1]; ring
    have h3 : ν * δ = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hw')
    exact eq_inv_of_mul_eq_one_right h3
  set γ := α / (ν⁻¹ - ν) with hγ
  refine ⟨w' + γ • u, U.add_mem hw'U (U.smul_mem _ hu), ?_, ?_, ?_⟩
  · intro h0
    have := hind γ 1 (by rw [add_comm, one_smul]; exact h0)
    exact one_ne_zero this.2
  · rw [map_add, map_smul, hTw', hTu, hδ, smul_add, smul_smul, smul_smul]
    have hα : α = γ * (ν⁻¹ - ν) := by rw [hγ, div_mul_cancel₀ _ hνne]
    rw [hα]
    module
  · intro v hv
    obtain ⟨a, b, rfl⟩ := hspan v hv
    refine ⟨a - b * γ, b, ?_⟩
    module

theorem omf_exists_eq_X_sub_C {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp0 : p ≠ 0) {ζ : Kˣ}
    (hζ : orderOf ζ = p) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) :
    ∃ k : ℕ, k < p ∧ h = X - C ((ζ : K) ^ k) := by
  obtain ⟨hirr, hmon, hdvd⟩ := mem_primaryFactors.mp hh
  have hprim : IsPrimitiveRoot (ζ : K) p := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  have : NeZero p := ⟨hp0⟩
  have hmin : minpoly K x.toLinearMap ∣ (X ^ p - C 1 : K[X]) := by
    apply minpoly.dvd
    rw [C_1]
    exact hx.aeval_X_pow_sub_one
  have hne : (X ^ p - C 1 : K[X]) ≠ 0 := X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hp0) 1
  have hsplit : h.Splits := (X_pow_sub_one_splits hprim).of_dvd hne (hdvd.trans hmin)
  have hdeg : h.natDegree = 1 := hsplit.natDegree_eq_one_of_irreducible hirr
  have heq := hmon.eq_X_add_C hdeg
  set μ := -h.coeff 0 with hμ
  have hroot : μ ^ p = 1 := by
    have h1 : (X ^ p - C 1 : K[X]).eval μ = 0 := by
      obtain ⟨g, hg⟩ := hdvd.trans hmin
      rw [hg, eval_mul]
      have : h.eval μ = 0 := by
        rw [heq]
        simp [hμ]
      rw [this, zero_mul]
    simpa [sub_eq_zero] using h1
  obtain ⟨k, hk, hkμ⟩ := hprim.eq_pow_of_pow_eq_one hroot
  refine ⟨k, hk, ?_⟩
  rw [heq, hkμ, hμ, C_neg, sub_eq_add_neg, neg_neg]

private theorem omf_pow_apply_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {T : V ≃ₗ[K] V} {u : V} {ν : K} (h : T u = ν • u) (n : ℕ) :
    (T ^ n) u = ν ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, h, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem omf_piece_eigen {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q p A r) {ζ : Kˣ} (hζ : orderOf ζ = p)
    (hal : CoordOm.FrameAligned F ζ) (hdim : ∀ i, finrank K (F.U i) = 2) (β : Fin r → ZMod p)
    (i : Fin r) :
    ∃ up ∈ F.U i, ∃ um ∈ F.U i, up ≠ 0 ∧ um ≠ 0 ∧
      F.ι (ofAdd β) up = ((ζ : K) ^ (β i).val) • up ∧
      F.ι (ofAdd β) um = ((ζ : K) ^ (β i).val)⁻¹ • um ∧
      ∀ v ∈ F.U i, ∃ α γ : K, v = α • up + γ • um := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨u, hu, hu0, hTu⟩ := hal i
  set T := F.ι (ofAdd (Pi.single i (1 : ZMod p))) with hTdef
  have hTO : ∀ v, Q (T v) = Q v :=
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).mp
      (orthDerived_le_orthogonalGroup (hAΩ (F.mem _)))
  have hζ2 : (ζ : K) ^ 2 ≠ 1 := by
    intro h2
    have h2' : ζ ^ 2 = 1 := Units.ext (by simpa using h2)
    have hdvd := orderOf_dvd_of_pow_eq_one h2'
    rw [hζ] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    have := hp.two_le
    have : p = 2 := by omega
    exact hp2 this
  obtain ⟨w, hw, hw0, hTw, hspan⟩ := omf_exists_inv_eigen_plane (hdim i) (F.nondeg i) hTO
    (F.mapsTo _ i) hu hu0 hTu hζ2
  refine ⟨u, hu, w, hw, hu0, hw0, ?_, ?_, hspan⟩
  · rw [frame_apply_eq_pow F β i hu, omf_pow_apply_of_eigen hTu]
  · rw [frame_apply_eq_pow F β i hw, omf_pow_apply_of_eigen hTw, inv_pow]

private theorem omf_zeta_pow_eq_iff {K : Type} [Field K] {p : ℕ} {ζ : Kˣ}
    (hζ : orderOf ζ = p) (m n : ℕ) :
    (ζ : K) ^ m = (ζ : K) ^ n ↔ (m : ZMod p) = n := by
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_inj,
    pow_eq_pow_iff_modEq, hζ, ZMod.natCast_eq_natCast_iff]

private theorem omf_mem_primaryComponent_of_eigen {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] {x : Module.End K V} {u : V} {ν : K} (h : x u = ν • u) :
    u ∈ primaryComponent x (X - C ν) := by
  rw [mem_primaryComponent]
  simp [h]

private theorem omf_mem_primaryFactors_of_eigen {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {x : Module.End K V} {u : V}
    (hu : u ≠ 0) {ν : K} (h : x u = ν • u) : X - C ν ∈ primaryFactors x := by
  refine mem_primaryFactors.mpr ⟨irreducible_X_sub_C ν, monic_X_sub_C ν, ?_⟩
  rw [dvd_iff_isRoot]
  exact Module.End.isRoot_of_hasEigenvalue
    (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr h, hu⟩)

private theorem omf_mem_othersSpace_of_mem {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} {h k : K[X]}
    (hk : k ∈ primaryFactors x) (hkh : k ≠ h) (hkh' : k ≠ reciprocalPolynomial h) {v : V}
    (hv : v ∈ primaryComponent x k) :
    v ∈ othersSpace x h :=
  Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem ⟨hk, hkh, hkh'⟩ hv)

theorem omf_piece_dichotomy {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q)
    (F : SevOm.Frame Q p A r) {ζ : Kˣ} (hζ : orderOf ζ = p) (hal : CoordOm.FrameAligned F ζ)
    (hdim : ∀ i, finrank K (F.U i) = 2) (β : Fin r → ZMod p) {k : ℕ} (i : Fin r) :
    ((β i = k ∨ β i = -k) →
      F.U i ≤ orbitSpace (F.ι (ofAdd β)).toLinearMap (X - C ((ζ : K) ^ k))) ∧
    (¬ (β i = k ∨ β i = -k) →
      F.U i ≤ othersSpace (F.ι (ofAdd β)).toLinearMap (X - C ((ζ : K) ^ k))) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨up, hup, um, hum, hup0, hum0, hxp, hxm, hspan⟩ :=
    omf_piece_eigen hp hp2 hAΩ F hζ hal hdim β i
  set x := (F.ι (ofAdd β)).toLinearMap with hx
  set b := (β i).val with hb
  have hz0 : ((ζ : K) ^ k) ≠ 0 := pow_ne_zero _ (Units.ne_zero ζ)
  have hrec : reciprocalPolynomial (X - C ((ζ : K) ^ k)) = X - C ((ζ : K) ^ k)⁻¹ :=
    omf_reciprocalPolynomial_X_sub_C hz0
  have hβb : β i = (b : ZMod p) := (ZMod.natCast_zmod_val (β i)).symm
  have e1 : (ζ : K) ^ b = (ζ : K) ^ k ↔ β i = k := by rw [omf_zeta_pow_eq_iff hζ, ← hβb]
  have e2 : (ζ : K) ^ b = ((ζ : K) ^ k)⁻¹ ↔ β i = -k := by
    have h1 : (ζ : K) ^ b = ((ζ : K) ^ k)⁻¹ ↔ (ζ : K) ^ b * (ζ : K) ^ k = 1 :=
      ⟨fun h => by rw [h, inv_mul_cancel₀ hz0], fun h => eq_inv_of_mul_eq_one_left h⟩
    rw [h1, ← pow_add, show (1 : K) = (ζ : K) ^ 0 from (pow_zero _).symm,
      omf_zeta_pow_eq_iff hζ, Nat.cast_add, Nat.cast_zero, ← hβb, add_eq_zero_iff_eq_neg]
  have hxp' : x up = (ζ : K) ^ b • up := hxp
  have hxm' : x um = ((ζ : K) ^ b)⁻¹ • um := hxm
  have hspanle : ∀ W : Submodule K V, up ∈ W → um ∈ W → F.U i ≤ W := by
    intro W h1 h2 v hv
    obtain ⟨α, γ, rfl⟩ := hspan v hv
    exact W.add_mem (W.smul_mem _ h1) (W.smul_mem _ h2)
  constructor
  · rintro (h | h)
    · have hb' : (ζ : K) ^ b = (ζ : K) ^ k := e1.mpr h
      refine hspanle _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
      · exact omf_mem_primaryComponent_of_eigen (by rw [hxp', hb'])
      · rw [hrec]
        exact omf_mem_primaryComponent_of_eigen (by rw [hxm', hb'])
    · have hb' : (ζ : K) ^ b = ((ζ : K) ^ k)⁻¹ := e2.mpr h
      refine hspanle _ (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left ?_)
      · rw [hrec]
        exact omf_mem_primaryComponent_of_eigen (by rw [hxp', hb'])
      · exact omf_mem_primaryComponent_of_eigen (by rw [hxm', hb', inv_inv])
  · intro hn
    push Not at hn
    have n1 : (ζ : K) ^ b ≠ (ζ : K) ^ k := fun h => hn.1 (e1.mp h)
    have n2 : (ζ : K) ^ b ≠ ((ζ : K) ^ k)⁻¹ := fun h => hn.2 (e2.mp h)
    have hne : ∀ ν : K, ν ≠ (ζ : K) ^ k → ν ≠ ((ζ : K) ^ k)⁻¹ →
        X - C ν ≠ X - C ((ζ : K) ^ k) ∧ X - C ν ≠ reciprocalPolynomial (X - C ((ζ : K) ^ k)) := by
      intro ν h1 h2
      rw [hrec]
      exact ⟨fun h => h1 (by simpa using congrArg (eval 0) h),
        fun h => h2 (by simpa using congrArg (eval 0) h)⟩
    refine hspanle _ ?_ ?_
    · obtain ⟨h1, h2⟩ := hne _ n1 n2
      exact omf_mem_othersSpace_of_mem (omf_mem_primaryFactors_of_eigen hup0 hxp') h1 h2
        (omf_mem_primaryComponent_of_eigen hxp')
    · have m1 : ((ζ : K) ^ b)⁻¹ ≠ (ζ : K) ^ k := fun h => n2 (by rw [← h, inv_inv])
      have m2 : ((ζ : K) ^ b)⁻¹ ≠ ((ζ : K) ^ k)⁻¹ := fun h => n1 (inv_injective h)
      obtain ⟨h1, h2⟩ := hne _ m1 m2
      exact omf_mem_othersSpace_of_mem (omf_mem_primaryFactors_of_eigen hum0 hxm') h1 h2
        (omf_mem_primaryComponent_of_eigen hxm')

private theorem omf_piece_indep {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) {v : Fin r → V} (hv : ∀ i, v i ∈ F.U i)
    (hsum : ∑ i, v i = 0) (j : Fin r) : v j = 0 := by
  classical
  refine F.nondeg j (v j) (hv j) fun u hu => ?_
  have h0 : QuadraticMap.polarBilin Q u (∑ i, v i) = 0 := by rw [hsum, map_zero]
  rw [map_sum, Finset.sum_eq_single j] at h0
  · exact h0
  · intro i _ hij
    exact F.orth j i (Ne.symm hij) u hu (v i) (hv i)
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private theorem omf_le_finrank_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) {x : Module.End K V} {ν : K}
    {u : Fin r → V} (hu : ∀ i, u i ∈ F.U i) (hu0 : ∀ i, u i ≠ 0)
    (hxu : ∀ i, x (u i) = ν • u i) :
    r ≤ finrank K (primaryComponent x (X - C ν)) := by
  classical
  have hli : LinearIndependent K u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := omf_piece_indep F (v := fun i => g i • u i) (fun i => (F.U i).smul_mem _ (hu i)) hg i
    exact (smul_eq_zero.mp h1).resolve_right (hu0 i)
  have hle : Submodule.span K (Set.range u) ≤ primaryComponent x (X - C ν) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact omf_mem_primaryComponent_of_eigen (hxu i)
  have := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_fin] at this
  exact this

theorem omf_primaryMultiplicity_eq_three {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q p A 3) {ζ : Kˣ}
    (hζ : orderOf ζ = p) (hal : CoordOm.FrameAligned F ζ) (hdim : ∀ i, finrank K (F.U i) = 2)
    (hV : finrank K V = 8) {c : ZMod p} (hc : c ≠ 0) {β : Fin 3 → ZMod p} (hβ : ∀ i, β i = c)
    {h : K[X]} (hh : h ∈ primaryFactors (F.ι (ofAdd β)).toLinearMap) (hX : h ≠ X - 1) :
    primaryMultiplicity (F.ι (ofAdd β)).toLinearMap h = 3 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  set x := F.ι (ofAdd β) with hxdef
  have hx : OddOrderIsometry Q p x := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd β)
  set ν : K := (ζ : K) ^ c.val with hνdef
  have hcv : ((c.val : ℕ) : ZMod p) = c := ZMod.natCast_zmod_val c
  have hν1 : ν ≠ 1 := by
    intro h1
    rw [hνdef, show (1 : K) = (ζ : K) ^ 0 from (pow_zero _).symm, omf_zeta_pow_eq_iff hζ, hcv,
      Nat.cast_zero] at h1
    exact hc h1
  have hν0 : ν ≠ 0 := pow_ne_zero _ (Units.ne_zero ζ)
  have hνinv : ν ≠ ν⁻¹ := by
    intro h1
    have h2 : ν * ν = 1 := by
      calc ν * ν = ν * ν⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel₀ hν0
    have h3 : (ζ : K) ^ (c.val + c.val) = (ζ : K) ^ 0 := by rw [pow_add, pow_zero]; exact h2
    rw [omf_zeta_pow_eq_iff hζ, Nat.cast_add, hcv, Nat.cast_zero, ← two_mul] at h3
    have h2p : (2 : ZMod p) ≠ 0 := by
      intro h0
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    exact hc ((mul_eq_zero.mp h3).resolve_left h2p)
  have hE := fun i => omf_piece_eigen hp hp2 hAΩ F hζ hal hdim β i
  choose up hup um hum hup0 hum0 hxp hxm _ using hE
  have hxp' : ∀ i, x.toLinearMap (up i) = ν • up i := fun i => by
    show x (up i) = _
    rw [hxp i, hβ i]
  have hxm' : ∀ i, x.toLinearMap (um i) = ν⁻¹ • um i := fun i => by
    show x (um i) = _
    rw [hxm i, hβ i]
  have hdp := omf_le_finrank_of_eigen F hup hup0 hxp'
  have hdm := omf_le_finrank_of_eigen F hum hum0 hxm'
  set W := F.U 0 ⊔ F.U 1 ⊔ F.U 2 with hW
  have hWle : finrank K W ≤ 6 := by
    rw [hW]
    have h1 := Submodule.finrank_add_le_finrank_add_finrank (F.U 0 ⊔ F.U 1) (F.U 2)
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (F.U 0) (F.U 1)
    have := hdim 0
    have := hdim 1
    have := hdim 2
    omega
  have horth : LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W ≤
      primaryComponent x.toLinearMap (X - 1) := by
    intro v hv
    rw [← fixedSpace_eq_primaryComponent, mem_fixedSpace, F.fix]
    intro j _ u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
    have huW : u ∈ W := by
      fin_cases j
      · exact Submodule.mem_sup_left (Submodule.mem_sup_left hu)
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right hu)
      · exact Submodule.mem_sup_right hu
    exact hv u huW
  have hd0 : 2 ≤ finrank K (primaryComponent x.toLinearMap (X - 1)) := by
    have h1 := Submodule.finrank_mono horth
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, hV] at h1
    omega
  have hpos : ∀ {k : K[X]}, 1 ≤ finrank K (primaryComponent x.toLinearMap k) →
      ∃ v ∈ primaryComponent x.toLinearMap k, v ≠ 0 := fun h1 =>
    (Submodule.ne_bot_iff _).mp (fun hb => by rw [hb, finrank_bot] at h1; omega)
  have hf0 : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    obtain ⟨v, hv, hv0⟩ := hpos (by omega : 1 ≤ finrank K (primaryComponent x.toLinearMap (X - 1)))
    have : x.toLinearMap v = (1 : K) • v := by
      rw [← fixedSpace_eq_primaryComponent, mem_fixedSpace] at hv
      rw [one_smul]
      exact hv
    have := omf_mem_primaryFactors_of_eigen hv0 this
    rwa [C_1] at this
  have hfp : X - C ν ∈ primaryFactors x.toLinearMap :=
    omf_mem_primaryFactors_of_eigen (hup0 0) (hxp' 0)
  have hfm : X - C ν⁻¹ ∈ primaryFactors x.toLinearMap :=
    omf_mem_primaryFactors_of_eigen (hum0 0) (hxm' 0)
  have hne : ∀ a b : K, a ≠ b → (X - C a : K[X]) ≠ X - C b := fun a b hab he =>
    hab (by simpa using congrArg (eval 0) he)
  have n01 : (X - 1 : K[X]) ≠ X - C ν := by rw [← C_1]; exact hne _ _ (Ne.symm hν1)
  have n02 : (X - 1 : K[X]) ≠ X - C ν⁻¹ := by
    rw [← C_1]; exact hne _ _ (fun h1 => hν1 (inv_eq_one.mp h1.symm))
  have n12 : (X - C ν : K[X]) ≠ X - C ν⁻¹ := hne _ _ hνinv
  set f : K[X] → ℕ := fun k => finrank K (primaryComponent x.toLinearMap k) with hfdef
  have htot : ∑ k ∈ primaryFactors x.toLinearMap, f k = 8 := by
    rw [← hV, finrank_eq_sum_primaryComponent hx.squarefree_minpoly]
    exact (Finset.sum_coe_sort _ f).symm
  have a0 : 2 ≤ f (X - 1) := hd0
  have ap : 3 ≤ f (X - C ν) := hdp
  have am : 3 ≤ f (X - C ν⁻¹) := hdm
  set S : Finset K[X] := {X - 1, X - C ν, X - C ν⁻¹} with hS
  have hSsub : S ⊆ primaryFactors x.toLinearMap := by
    intro k hk
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    exacts [hf0, hfp, hfm]
  have hSsum : ∑ k ∈ S, f k = f (X - 1) + f (X - C ν) + f (X - C ν⁻¹) := by
    rw [hS, Finset.sum_insert (by simp [n01, n02]), Finset.sum_insert (by simp [n12]),
      Finset.sum_singleton, add_assoc]
  have hfpos : ∀ k ∈ primaryFactors x.toLinearMap, 1 ≤ f k := fun k hk =>
    Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hx.squarefree_minpoly hk)
  have hhS : h ∈ S := by
    by_contra hhS
    have h1 := Finset.sum_le_sum_of_subset (f := f) (Finset.insert_subset hh hSsub)
    rw [Finset.sum_insert hhS, hSsum, htot] at h1
    have := hfpos h hh
    omega
  have hfh : f h = 3 := by
    have h1 := Finset.sum_le_sum_of_subset (f := f) hSsub
    rw [hSsum, htot] at h1
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hhS
    rcases hhS with rfl | rfl | rfl
    · exact absurd rfl hX
    · omega
    · omega
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hdeg : h.natDegree = 1 := by
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hhS
    rcases hhS with rfl | rfl | rfl
    · exact absurd rfl hX
    · simp
    · simp
  have h2 := finrank_primaryComponent (x := x.toLinearMap) (a := h)
  simp only [hfdef] at hfh
  rw [hfh, hdeg, one_mul] at h2
  exact h2.symm

end A8Coord

end CFSG.StandardType

end

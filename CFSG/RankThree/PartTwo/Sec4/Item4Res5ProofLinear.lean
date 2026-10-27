module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Trace

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Res5L34

open Module Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Weights

theorem isSemisimple_of_pow_eq_one {f : Module.End K V} {n : ℕ} (hnK : (n : K) ≠ 0)
    (hf : f ^ n = 1) : f.IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ n - C 1)
  · exact (Polynomial.separable_X_pow_sub_C (1 : K) hnK one_ne_zero).squarefree
  · simp [hf]

theorem pow_apply_of_apply_eq_smul {f : Module.End K V} {v : V} {c : K} (h : f v = c • v)
    (m : ℕ) : (f ^ m) v = c ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, h, map_smul, ih, smul_smul, pow_succ, mul_comm]

variable [IsAlgClosed K] [FiniteDimensional K V]

theorem card_le_pow_finrank {n : ℕ} (hn0 : 0 < n) (hnK : (n : K) ≠ 0) {A : Type*} [CommGroup A]
    [Finite A] (f : A →* Module.End K V) (hf : Function.Injective f) (hA : ∀ a : A, a ^ n = 1) :
    Nat.card A ≤ n ^ Module.finrank K V := by
  classical
  have hss : ∀ a : A, (f a).IsSemisimple := fun a =>
    isSemisimple_of_pow_eq_one hnK (by rw [← map_pow, hA, map_one])
  have hcomm : ∀ a b : A, Commute (f a) (f b) := fun a b => by
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, mul_comm]
  set piece : (A → K) → Submodule K V := fun χ => ⨅ a, (f a).maxGenEigenspace (χ a) with hpiece
  have htop : ⨆ χ, piece χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun a b _ => hcomm a b) (fun a => Module.End.iSup_maxGenEigenspace_eq_top (f a))
  have hind : iSupIndep piece :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun a b φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) φ)
  let _ : Fintype { χ // piece χ ≠ ⊥ } := hind.fintypeNeBotOfFiniteDimensional
  have hS : Fintype.card { χ // piece χ ≠ ⊥ } ≤ Module.finrank K V :=
    hind.subtype_ne_bot_le_finrank
  have heig : ∀ (χ : A → K) (v : V), v ∈ piece χ → ∀ a, f a v = χ a • v := by
    intro χ v hv a
    have hv' : v ∈ (f a).maxGenEigenspace (χ a) := (Submodule.mem_iInf _).mp hv a
    rw [(hss a).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hv'
    exact Module.End.mem_eigenspace_iff.mp hv'
  have hroot : ∀ (χ : { χ // piece χ ≠ ⊥ }) (a : A), (χ.1 a) ∈ nthRootsFinset n (1 : K) := by
    intro χ a
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.2
    rw [mem_nthRootsFinset hn0]
    have h1 : f (a ^ n) v = (χ.1 a) ^ n • v := by
      rw [map_pow]
      exact pow_apply_of_apply_eq_smul (heig χ.1 v hv a) n
    rw [hA, map_one, Module.End.one_apply] at h1
    have h2 : ((χ.1 a) ^ n - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)
  let Φ : A → ({ χ // piece χ ≠ ⊥ } → nthRootsFinset n (1 : K)) :=
    fun a χ => ⟨χ.1 a, hroot χ a⟩
  have hΦ : Function.Injective Φ := by
    intro a b hab
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ ⨆ χ, piece χ := by rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction piece (motive := fun v => f a v = f b v) hv ?_ ?_ ?_
    · intro χ w hw
      by_cases hχ : piece χ = ⊥
      · rw [hχ, Submodule.mem_bot] at hw
        rw [hw, map_zero, map_zero]
      · have h := congrArg Subtype.val (congrFun hab ⟨χ, hχ⟩)
        simp only [Φ] at h
        rw [heig χ w hw a, heig χ w hw b, h]
    · rw [map_zero, map_zero]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := { χ // piece χ ≠ ⊥ })] at hcard
  have hroots : Nat.card (nthRootsFinset n (1 : K)) ≤ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact (Multiset.toFinset_card_le _).trans (card_nthRoots n 1)
  calc Nat.card A ≤ Nat.card (nthRootsFinset n (1 : K)) ^ Fintype.card { χ // piece χ ≠ ⊥ } :=
        hcard
    _ ≤ n ^ Fintype.card { χ // piece χ ≠ ⊥ } := Nat.pow_le_pow_left hroots _
    _ ≤ n ^ Module.finrank K V := Nat.pow_le_pow_right hn0 hS

end Weights

section E9

theorem exists_omega [IsAlgClosed K] : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  have hdeg : (X ^ 2 + X + 1 : K[X]).degree = 2 := by compute_degree!
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (X ^ 2 + X + 1 : K[X]) (by rw [hdeg]; decide)
  exact ⟨ω, by simpa [Polynomial.IsRoot] using hω⟩

variable {ω : K}

@[expose] def pw (ω : K) (m : ZMod 3) : K := ω ^ m.val

theorem omega_pow_three (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

theorem pw_add (hω : ω ^ 2 + ω + 1 = 0) (m n : ZMod 3) : pw ω (m + n) = pw ω m * pw ω n := by
  have h3 := omega_pow_three hω
  have key : ∀ k : ℕ, ω ^ k = ω ^ (k % 3) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [pw, pw, pw, ZMod.val_add, ← pow_add, key (m.val + n.val)]

theorem pw_zero : pw ω 0 = 1 := by simp [pw]

theorem exists_pw_eq (hω : ω ^ 2 + ω + 1 = 0) {x : K} (hx : x ^ 3 = 1) :
    ∃ m : ZMod 3, x = pw ω m := by
  have h : (x - 1) * (x - ω) * (x - ω ^ 2) = 0 := by
    linear_combination hx + (x - 1) * (ω - 1 - x) * hω
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨0, by rw [pw_zero]; exact sub_eq_zero.mp h⟩
    · exact ⟨1, by
        rw [sub_eq_zero.mp h, pw, show (1 : ZMod 3).val = 1 from rfl, pow_one]⟩
  · exact ⟨2, by rw [sub_eq_zero.mp h, pw, show (2 : ZMod 3).val = 2 from rfl]⟩

theorem pw_injective (h3 : (3 : K) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Injective (pw ω) := by
  have hω1 : ω ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    have h3' := omega_pow_three hω
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [h3', h, inv_one, one_mul]
  have hω12 : ω ≠ ω ^ 2 := by
    intro h
    apply hω1
    have : ω * (ω - 1) = 0 := by linear_combination -h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hω0)
  intro m n h
  apply ZMod.val_injective
  have hm := ZMod.val_lt m
  have hn := ZMod.val_lt n
  simp only [pw] at h
  generalize m.val = i at h hm ⊢
  generalize n.val = j at h hn ⊢
  interval_cases i <;> interval_cases j <;> simp only [pow_zero, pow_one] at h <;>
    (first
      | rfl
      | exact absurd h.symm hω1
      | exact absurd h hω1
      | exact absurd h.symm hω2
      | exact absurd h hω2
      | exact absurd h hω12
      | exact absurd h.symm hω12)

@[expose] def actF (w : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 := (w.2, 2 * w.1)

@[expose] def actJ (w : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 := (2 * w.1 + w.2, w.1 + w.2)

theorem five_distinct : ∀ w : ZMod 3 × ZMod 3, w ≠ 0 →
    List.Nodup [w, actF w, actF (actF w), actF (actF (actF w)), actJ w] := by
  decide

variable [IsAlgClosed K] [FiniteDimensional K V]

theorem eq_one_of_weights (h3 : (3 : K) ≠ 0) (hV : Module.finrank K V ≤ 4)
    {A B F J : Module.End K V} (hA3 : A ^ 3 = 1) (hB3 : B ^ 3 = 1) (hAB : A * B = B * A)
    (hF : Function.Injective F) (hJ : Function.Injective J) (hAF : A * F = F * B)
    (hBF : B * F = F * A ^ 2) (hAJ : A * J = J * (B * A ^ 2)) (hBJ : B * J = J * (A * B)) :
    A = 1 := by
  classical
  obtain ⟨ω, hω⟩ := exists_omega (K := K)
  have hω3 := omega_pow_three hω
  let Pe : ZMod 3 × ZMod 3 → Prop := fun w =>
    ∃ v : V, v ≠ 0 ∧ A v = pw ω w.1 • v ∧ B v = pw ω w.2 • v
  have hPF : ∀ w, Pe w → Pe (actF w) := by
    rintro ⟨m, n⟩ ⟨v, hv0, hAv, hBv⟩
    refine ⟨F v, fun h => hv0 (hF (by rw [h, map_zero])), ?_, ?_⟩
    · show A (F v) = pw ω n • F v
      rw [← Module.End.mul_apply, hAF, Module.End.mul_apply, hBv, map_smul]
    · show B (F v) = pw ω (2 * m) • F v
      rw [← Module.End.mul_apply, hBF, Module.End.mul_apply, pow_apply_of_apply_eq_smul hAv,
        map_smul, two_mul, pw_add hω, sq]
  have hPJ : ∀ w, Pe w → Pe (actJ w) := by
    rintro ⟨m, n⟩ ⟨v, hv0, hAv, hBv⟩
    refine ⟨J v, fun h => hv0 (hJ (by rw [h, map_zero])), ?_, ?_⟩
    · show A (J v) = pw ω (2 * m + n) • J v
      rw [← Module.End.mul_apply, hAJ, Module.End.mul_apply, Module.End.mul_apply,
        pow_apply_of_apply_eq_smul hAv, map_smul, hBv, smul_smul, map_smul, two_mul, pw_add hω,
        pw_add hω, sq, mul_comm]
    · show B (J v) = pw ω (m + n) • J v
      rw [← Module.End.mul_apply, hBJ, Module.End.mul_apply, Module.End.mul_apply, hBv,
        map_smul, hAv, smul_smul, map_smul, pw_add hω, mul_comm]
  by_contra hA1
  have hss : A.IsSemisimple := isSemisimple_of_pow_eq_one (n := 3) (by exact_mod_cast h3) hA3
  have hex : ∃ μ : K, μ ≠ 1 ∧ A.eigenspace μ ≠ ⊥ := by
    by_contra hno
    push Not at hno
    apply hA1
    have htop := hss.iSup_eigenspace_eq_top
    have hle : ⨆ μ, A.eigenspace μ ≤ A.eigenspace 1 := by
      refine iSup_le fun μ => ?_
      by_cases hμ : μ = 1
      · rw [hμ]
      · rw [hno μ hμ]; exact bot_le
    rw [htop] at hle
    apply LinearMap.ext
    intro v
    have := Module.End.mem_eigenspace_iff.mp (hle Submodule.mem_top (x := v))
    rw [this, one_smul, Module.End.one_apply]
  obtain ⟨μ, hμ1, hμ⟩ := hex
  have hBμ : ∀ x ∈ A.eigenspace μ, B x ∈ A.eigenspace μ := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, hAB, Module.End.mul_apply, hx, map_smul]
  have : Nontrivial (A.eigenspace μ) := Submodule.nontrivial_iff_ne_bot.mpr hμ
  obtain ⟨β, hβ⟩ := Module.End.exists_eigenvalue (B.restrict hBμ)
  obtain ⟨w, hw⟩ := hβ.exists_hasEigenvector
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hAw : A w = μ • (w : V) := Module.End.mem_eigenspace_iff.mp w.2
  have hBw : B w = β • (w : V) := by
    have := Module.End.mem_eigenspace_iff.mp hw.1
    have h' := congrArg Subtype.val this
    simpa [LinearMap.restrict_apply] using h'
  have hμ3 : μ ^ 3 = 1 := by
    have h := pow_apply_of_apply_eq_smul hAw 3
    rw [hA3, Module.End.one_apply] at h
    have h2 : (μ ^ 3 - 1) • (w : V) = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw0)
  have hβ3 : β ^ 3 = 1 := by
    have h := pow_apply_of_apply_eq_smul hBw 3
    rw [hB3, Module.End.one_apply] at h
    have h2 : (β ^ 3 - 1) • (w : V) = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw0)
  obtain ⟨m, rfl⟩ := exists_pw_eq hω hμ3
  obtain ⟨n, rfl⟩ := exists_pw_eq hω hβ3
  have hm : m ≠ 0 := by rintro rfl; exact hμ1 pw_zero
  have hP : Pe (m, n) := ⟨w, hw0, hAw, hBw⟩
  let f : Fin 2 → Module.End K V := ![A, B]
  set piece : (Fin 2 → K) → Submodule K V :=
    fun χ => ⨅ i, (f i).maxGenEigenspace (χ i) with hpiece
  have hcommf : ∀ i j, Commute (f i) (f j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · exact hAB
    · exact hAB.symm
    · exact Commute.refl _
  have hind : iSupIndep piece :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcommf j i) φ)
  let _ : Fintype { χ // piece χ ≠ ⊥ } := hind.fintypeNeBotOfFiniteDimensional
  have hS : Fintype.card { χ // piece χ ≠ ⊥ } ≤ Module.finrank K V :=
    hind.subtype_ne_bot_le_finrank
  let χw : ZMod 3 × ZMod 3 → (Fin 2 → K) := fun w => ![pw ω w.1, pw ω w.2]
  have hχw : Function.Injective χw := by
    intro w w' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [χw, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext (pw_injective h3 hω h0) (pw_injective h3 hω h1)
  have hne : ∀ w, Pe w → piece (χw w) ≠ ⊥ := by
    rintro w ⟨v, hv0, hAv, hBv⟩
    refine Submodule.ne_bot_iff _ |>.mpr ⟨v, ?_, hv0⟩
    refine (Submodule.mem_iInf _).mpr fun i => ?_
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    fin_cases i
    · exact hAv
    · exact hBv
  have hw5 := five_distinct (m, n) (by simp [hm])
  set L5 := [(m, n), actF (m, n), actF (actF (m, n)), actF (actF (actF (m, n))), actJ (m, n)]
    with hL5
  have hPL : ∀ x ∈ L5, Pe x := by
    intro x hx
    simp only [hL5, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hP
    · exact hPF _ hP
    · exact hPF _ (hPF _ hP)
    · exact hPF _ (hPF _ (hPF _ hP))
    · exact hPJ _ hP
  let g : Fin 5 → { χ // piece χ ≠ ⊥ } := fun i =>
    ⟨χw (L5.get ⟨i, by simp [hL5]⟩), hne _ (hPL _ (List.get_mem _ _))⟩
  have hg : Function.Injective g := by
    intro i j hij
    have h := congrArg Subtype.val hij
    have h' := hχw h
    exact Fin.ext (congrArg Fin.val ((List.Nodup.get_inj_iff hw5).mp h'))
  have h5 := Fintype.card_le_of_injective g hg
  rw [Fintype.card_fin] at h5
  omega

end E9

section GLTwo

variable [FiniteDimensional K V]

theorem matrix_mul_self_fin_two (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem trace_eq_zero_of_mul_self_eq_smul (hV : Module.finrank K V = 2) {Y : Module.End K V}
    {c : K} (hY : Y * Y = c • 1) (hns : ∀ d : K, Y ≠ d • 1) : LinearMap.trace K V Y = 0 := by
  classical
  let b := Module.finBasisOfFinrankEq K V hV
  set M := LinearMap.toMatrix b b Y with hM
  have hMM : M * M = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [hM, ← LinearMap.toMatrix_mul, hY, map_smul, LinearMap.toMatrix_one]
  rw [LinearMap.trace_eq_matrix_trace K b Y, ← hM]
  by_contra htr
  apply hns ((c + M.det) / M.trace)
  apply (LinearMap.toMatrix b b).injective
  rw [← hM, map_smul, LinearMap.toMatrix_one]
  have h := matrix_mul_self_fin_two M
  rw [hMM] at h
  have h2 : M.trace • M = (c + M.det) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [add_smul, h]; abel
  calc M = M.trace⁻¹ • (M.trace • M) := by rw [smul_smul, inv_mul_cancel₀ htr, one_smul]
    _ = ((c + M.det) / M.trace) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [h2, smul_smul, div_eq_inv_mul]

theorem card_le_four_of_sq_smul (h2 : (2 : K) ≠ 0) (hV : Module.finrank K V = 2) {F : Type*}
    [Group F] (τ : F →* Module.End K V) (hsq : ∀ x : F, ∃ c : K, τ x * τ x = c • 1)
    {ι : Type*} [Fintype ι] (r : ι → F)
    (hr : ∀ i j, i ≠ j → ∀ d : K, τ (r i * (r j)⁻¹) ≠ d • 1) : Fintype.card ι ≤ 4 := by
  classical
  have hli : LinearIndependent K (fun i => τ (r i)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have h1 : ∑ i, a i • τ (r i * (r j)⁻¹) = 0 := by
      have := congrArg (fun T => T * τ (r j)⁻¹) ha
      simp only [Finset.sum_mul, smul_mul_assoc, zero_mul] at this
      simpa [map_mul] using this
    have ht := congrArg (LinearMap.trace K V) h1
    rw [map_sum, map_zero] at ht
    simp only [map_smul] at ht
    rw [Finset.sum_eq_single j] at ht
    · rw [mul_inv_cancel, map_one, LinearMap.trace_one, hV, smul_eq_mul] at ht
      exact (mul_eq_zero.mp ht).resolve_right (by exact_mod_cast h2)
    · intro i _ hij
      obtain ⟨c, hc⟩ := hsq (r i * (r j)⁻¹)
      rw [trace_eq_zero_of_mul_self_eq_smul hV hc (hr i j hij), smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have h := hli.fintype_card_le_finrank
  rwa [Module.finrank_linearMap, hV] at h

variable [IsAlgClosed K]

theorem exists_eq_smul_of_commute_of_anticommute (h2 : (2 : K) ≠ 0)
    (hV : Module.finrank K V = 2) {X Y U : Module.End K V} (hXY : X * Y = -(Y * X))
    (hX : Function.Injective X) (hY : Function.Injective Y) (hUX : U * X = X * U)
    (hUY : U * Y = Y * U) : ∃ a : K, U = a • 1 := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue X
  obtain ⟨v, hv⟩ := hl.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hXv : X v = l • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hXv
    exact hv0 (hX (by rw [hXv, map_zero]))
  have hXYv : X (Y v) = (-l) • Y v := by
    rw [← Module.End.mul_apply, hXY, LinearMap.neg_apply, Module.End.mul_apply, hXv, map_smul,
      neg_smul]
  have hYv0 : Y v ≠ 0 := fun h => hv0 (hY (by rw [h, map_zero]))
  have hli : LinearIndependent K ![v, Y v] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have hX' := congrArg X hg
    rw [map_add, map_smul, map_smul, hXv, hXYv, map_zero, smul_smul, smul_smul] at hX'
    have h3 : (2 * l * g 1) • Y v = 0 := by
      have : (2 * l * g 1) • Y v = l • (g 0 • v + g 1 • Y v) - ((g 0 * l) • v + (g 1 * -l) • Y v)
        := by
        rw [smul_add, smul_smul, smul_smul]
        module
      rw [this, hg, hX', smul_zero, sub_zero]
    have hg1 : g 1 = 0 := by
      have := (smul_eq_zero.mp h3).resolve_right hYv0
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero h2 hl0)
      · exact h
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hv0
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
  let b : Module.Basis (Fin 2) K V := basisOfLinearIndependentOfCardEqFinrank hli (by
    rw [Fintype.card_fin, hV])
  have hb0 : b 0 = v := by simp [b]
  have hb1 : b 1 = Y v := by simp [b]
  have hUv : ∃ a : K, U v = a • v := by
    have hsum := b.sum_repr (U v)
    rw [Fin.sum_univ_two, hb0, hb1] at hsum
    set a := b.repr (U v) 0
    set c := b.repr (U v) 1
    refine ⟨a, ?_⟩
    have hXU : X (U v) = l • U v := by
      rw [← Module.End.mul_apply, ← hUX, Module.End.mul_apply, hXv, map_smul]
    rw [← hsum, map_add, map_smul, map_smul, hXv, hXYv, smul_add, smul_smul, smul_smul,
      smul_smul, smul_smul] at hXU
    have h3 : ((a * l) - (l * a)) • v + ((c * -l) - (l * c)) • Y v = 0 := by
      have e := sub_eq_zero.mpr hXU
      rw [← e]; module
    obtain ⟨-, hc'⟩ := LinearIndependent.pair_iff.mp hli _ _ h3
    have hc : c = 0 := by
      have h4 : (2 * l) * c = 0 := by linear_combination -hc'
      exact (mul_eq_zero.mp h4).resolve_left (mul_ne_zero h2 hl0)
    rw [← hsum, hc, zero_smul, add_zero]
  obtain ⟨a, ha⟩ := hUv
  refine ⟨a, b.ext fun i => ?_⟩
  fin_cases i
  · simp [hb0, ha]
  · show U (b 1) = (a • (1 : Module.End K V)) (b 1)
    rw [hb1, ← Module.End.mul_apply, hUY, Module.End.mul_apply, ha, map_smul]
    simp

end GLTwo

end CFSG.RankThree.PartTwo.Sec4.Census.Res5L34

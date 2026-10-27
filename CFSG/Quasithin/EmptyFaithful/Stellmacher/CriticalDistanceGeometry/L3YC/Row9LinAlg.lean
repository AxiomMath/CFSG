module

public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.Stellmacher.CD.L3YC.Row9

set_option linter.unusedSectionVars false

open Module LinearMap

variable {F V : Type*} [Field F] [CharP F 7] [AddCommGroup V] [Module F V]

theorem two_ne_zero' : (2 : F) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  have := (CharP.cast_eq_zero_iff F 7 2).mp this
  omega

theorem isCompl_eig (Z : Module.End F V) (hZ : Z * Z = 1) :
    IsCompl (LinearMap.ker (Z - 1)) (LinearMap.ker (Z + 1)) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero'
  have hZv : ∀ v, Z (Z v) = v := fun v => by
    have := congrArg (fun f : Module.End F V => f v) hZ
    simpa using this
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2'
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply,
      sub_eq_zero] at h1 h2'
    have : (2 : F) • v = 0 := by
      rw [two_smul]
      rw [h1] at h2'
      exact h2'
    exact (smul_eq_zero.mp this).resolve_left h2
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro v
    rw [Submodule.mem_sup]
    refine ⟨(2 : F)⁻¹ • (Z v + v), ?_, (2 : F)⁻¹ • (v - Z v), ?_, ?_⟩
    · simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add,
        hZv]
      convert smul_zero ((2 : F)⁻¹) using 2
      abel
    · simp only [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub,
        hZv]
      convert smul_zero ((2 : F)⁻¹) using 2
      abel
    · rw [← smul_add]
      have : Z v + v + (v - Z v) = (2 : F) • v := by rw [two_smul]; abel
      rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]


theorem neg_one_ne_one' : (-1 : F) ≠ 1 := by
  intro h
  have h2 : (2 : F) = 0 := by linear_combination -h
  exact two_ne_zero' h2

variable [FiniteDimensional F V]

theorem det_of_eig (Z : Module.End F V) (hZ : Z * Z = 1) (a μ : F) (T : Module.End F V)
    (hTm : ∀ v ∈ LinearMap.ker (Z + 1), T v = a • v)
    (hTp : ∀ v ∈ LinearMap.ker (Z - 1), T v = μ • v) :
    LinearMap.det T = μ ^ Module.finrank F (LinearMap.ker (Z - 1)) *
      a ^ Module.finrank F (LinearMap.ker (Z + 1)) := by
  have hc := isCompl_eig Z hZ
  set Vp := LinearMap.ker (Z - 1) with hVp
  set Vm := LinearMap.ker (Z + 1) with hVm
  let e : (Vp × Vm) ≃ₗ[F] V := Submodule.prodEquivOfIsCompl Vp Vm hc
  let f : Module.End F (Vp × Vm) := LinearMap.prodMap (μ • LinearMap.id) (a • LinearMap.id)
  have hTe : T = (e : (Vp × Vm) →ₗ[F] V) ∘ₗ f ∘ₗ (e.symm : V →ₗ[F] (Vp × Vm)) := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨p, rfl⟩ := e.surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, f,
      LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_apply]
    simp only [e, Submodule.coe_prodEquivOfIsCompl', map_add]
    rw [hTp _ p.1.2, hTm _ p.2.2]
    simp
  have h1 : LinearMap.det T = LinearMap.det f := by
    rw [hTe]
    exact LinearMap.det_conj f e
  rw [h1]
  simp only [f, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem det_eq_neg_one_pow (Z : Module.End F V) (hZ : Z * Z = 1) :
    LinearMap.det Z = (-1 : F) ^ Module.finrank F (LinearMap.ker (Z + 1)) := by
  have hZp : ∀ x ∈ LinearMap.ker (Z - 1), Z x = (1 : F) • x := fun x hx => by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    simpa using hx
  have hZm : ∀ y ∈ LinearMap.ker (Z + 1), Z y = (-1 : F) • y := fun y hy => by
    simp only [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hy
    rw [neg_one_smul]
    exact eq_neg_of_add_eq_zero_left hy
  rw [det_of_eig Z hZ (-1) 1 Z hZm hZp, one_pow, one_mul]

theorem finrank_eig (hV : Module.finrank F V = 3) (Z : Module.End F V) (hZ : Z * Z = 1)
    (hdet : LinearMap.det Z = 1) (hZ1 : Z ≠ 1) :
    Module.finrank F (LinearMap.ker (Z + 1)) = 2 ∧ Module.finrank F (LinearMap.ker (Z - 1)) = 1 := by
  have hc := isCompl_eig Z hZ
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [hV] at hsum
  have hdet' := det_eq_neg_one_pow Z hZ
  rw [hdet] at hdet'
  have heven : Even (Module.finrank F (LinearMap.ker (Z + 1))) :=
    (neg_one_pow_eq_one_iff_even neg_one_ne_one').mp hdet'.symm
  have hne : Module.finrank F (LinearMap.ker (Z + 1)) ≠ 0 := by
    intro h0
    have hbot : LinearMap.ker (Z + 1) = ⊥ := Submodule.finrank_eq_zero.mp h0
    rw [hbot] at hc
    have htop : LinearMap.ker (Z - 1) = ⊤ := by
      simpa using hc.sup_eq_top
    apply hZ1
    refine LinearMap.ext fun v => ?_
    have : v ∈ LinearMap.ker (Z - 1) := by rw [htop]; trivial
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
    simpa using this
  obtain ⟨k, hk⟩ := heven
  have : Module.finrank F (LinearMap.ker (Z + 1)) = 2 := by omega
  exact ⟨this, by omega⟩

theorem scalar_on_line (W : Submodule F V) (hW : Module.finrank F W = 1) (T : Module.End F V)
    (hT : ∀ v ∈ W, T v ∈ W) : ∃ μ : F, ∀ v ∈ W, T v = μ • v := by
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ W, x ≠ 0 := by
    by_contra h
    push Not at h
    have : W = ⊥ := (Submodule.eq_bot_iff W).mpr h
    rw [this] at hW
    simp at hW
  obtain ⟨μ, hμ⟩ := exists_smul_eq_of_finrank_eq_one hW (x := ⟨x, hx⟩) (by simpa using hx0)
    ⟨T x, hT x hx⟩
  have hμ' : T x = μ • x := by
    have := congrArg Subtype.val hμ
    simpa using this.symm
  refine ⟨μ, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hW (x := ⟨x, hx⟩) (by simpa using hx0)
    ⟨v, hv⟩
  have hc' : v = c • x := by
    have := congrArg Subtype.val hc
    simpa using this.symm
  rw [hc', map_smul, hμ', smul_comm]

omit [CharP F 7] [FiniteDimensional F V] in
theorem pow_finrank_eq_zero_of_nilp {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (φ : Module.End F W) (h : IsNilpotent φ) :
    φ ^ Module.finrank F W = 0 := by
  have h1 := IsNilpotent.charpoly_eq_X_pow_finrank h
  have h2 := LinearMap.aeval_self_charpoly φ
  rw [h1] at h2
  simpa [Polynomial.aeval_X_pow] using h2

omit [FiniteDimensional F V] in
theorem sq_eq_zero_on (W : Submodule F V) [FiniteDimensional F W] (hW : Module.finrank F W = 2)
    (N : Module.End F V) (hN : ∀ v ∈ W, N v ∈ W) (h7 : N ^ 7 = 0) :
    ∀ v ∈ W, N (N v) = 0 := by
  have hnil : IsNilpotent (N.restrict hN) := by
    refine ⟨7, ?_⟩
    rw [Module.End.pow_restrict 7 hN]
    ext v
    simp [h7]
  have h2 := pow_finrank_eq_zero_of_nilp (N.restrict hN) hnil
  rw [hW, Module.End.pow_restrict 2 hN] at h2
  intro v hv
  have := congrArg (fun f : Module.End F W => (f ⟨v, hv⟩ : V)) h2
  simpa [pow_two] using this

omit [CharP F 7] [FiniteDimensional F V] in
theorem scalar_on_plane (W : Submodule F V) [FiniteDimensional F W] (hW : Module.finrank F W = 2)
    (N C : Module.End F V) (hN : ∀ v ∈ W, N v ∈ W) (hC : ∀ v ∈ W, C v ∈ W)
    (hNC : ∀ v, N (C v) = C (N v)) (hN2 : ∀ v ∈ W, N (N v) = 0)
    (w : V) (hw : w ∈ W) (hNw : N w ≠ 0)
    (m : ℕ) (hm : ((m + 1 : ℕ) : F) ≠ 0) (hCk : ∀ v ∈ W, (C ^ (m + 1)) v = v) :
    ∃ α : F, α ^ (m + 1) = 1 ∧ ∀ v ∈ W, C v = α • v := by
  have hu : N w ∈ W := hN w hw
  have hNu : N (N w) = 0 := hN2 w hw
  have hind : ∀ x y : F, x • w + y • N w = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    have h1 := congrArg N h
    rw [map_add, map_smul, map_smul, hNu, smul_zero, add_zero, map_zero] at h1
    have hx : x = 0 := (smul_eq_zero.mp h1).resolve_right hNw
    subst hx
    rw [zero_smul, zero_add] at h
    exact ⟨rfl, (smul_eq_zero.mp h).resolve_right hNw⟩
  have hspan : ∀ v ∈ W, ∃ x y : F, v = x • w + y • N w := by
    have hli : LinearIndependent F ![(⟨w, hw⟩ : W), ⟨N w, hu⟩] := by
      rw [LinearIndependent.pair_iff]
      intro s t h
      apply hind s t
      have := congrArg Subtype.val h
      simpa using this
    have htop := hli.span_eq_top_of_card_eq_finrank (by simp [hW])
    intro v hv
    have : (⟨v, hv⟩ : W) ∈ Submodule.span F (Set.range ![(⟨w, hw⟩ : W), ⟨N w, hu⟩]) := by
      rw [htop]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨c, hc⟩ := this
    refine ⟨c 0, c 1, ?_⟩
    have := congrArg Subtype.val hc
    simpa [Fin.sum_univ_two] using this.symm
  obtain ⟨a, b, hCw⟩ := hspan (C w) (hC w hw)
  have hCu : C (N w) = a • N w := by
    rw [← hNC, hCw, map_add, map_smul, map_smul, hNu, smul_zero, add_zero]
  have hCv : ∀ v ∈ W, C v = a • v + b • N v := by
    intro v hv
    obtain ⟨x, y, rfl⟩ := hspan v hv
    rw [map_add, map_smul, map_smul, hCw, hCu, map_add, map_smul, map_smul, hNu, smul_zero,
      add_zero]
    module
  have hpow : ∀ j : ℕ, ∀ v ∈ W, (C ^ (j + 1)) v =
      a ^ (j + 1) • v + (((j + 1 : ℕ) : F) * a ^ j * b) • N v := by
    intro j
    induction j with
    | zero =>
      intro v hv
      simp [hCv v hv]
    | succ j ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply, hCv v hv, map_add, map_smul, map_smul,
        ih v hv, ih (N v) (hN v hv), hN2 v hv]
      push_cast
      module
  have h1 := hCk w hw
  rw [hpow m w hw] at h1
  have h2 : (a ^ (m + 1) - 1) • w + (((m + 1 : ℕ) : F) * a ^ m * b) • N w = 0 := by
    rw [sub_smul, one_smul, sub_add_eq_add_sub, h1, sub_self]
  obtain ⟨ha, hb⟩ := hind _ _ h2
  have ha1 : a ^ (m + 1) = 1 := sub_eq_zero.mp ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha1
  have hb0 : b = 0 := by
    have : a ^ m ≠ 0 := pow_ne_zero _ ha0
    rcases mul_eq_zero.mp hb with h | h
    · exact absurd h (mul_ne_zero hm this)
    · exact h
  refine ⟨a, ha1, fun v hv => ?_⟩
  rw [hCv v hv, hb0, zero_smul, add_zero]

theorem ker_plus_inv (Z T : Module.End F V) (hT : Z * T = T * Z) :
    ∀ v ∈ LinearMap.ker (Z + 1), T v ∈ LinearMap.ker (Z + 1) := by
  intro v hv
  simp only [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hv ⊢
  have h := congrArg (fun f : Module.End F V => f v) hT
  simp only [Module.End.mul_apply] at h
  rw [h, ← map_add, hv, map_zero]

theorem ker_minus_inv (Z T : Module.End F V) (hT : Z * T = T * Z) :
    ∀ v ∈ LinearMap.ker (Z - 1), T v ∈ LinearMap.ker (Z - 1) := by
  intro v hv
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at hv ⊢
  have h := congrArg (fun f : Module.End F V => f v) hT
  simp only [Module.End.mul_apply] at h
  rw [h, ← map_sub, hv, map_zero]

omit [CharP F 7] [FiniteDimensional F V] in
theorem exists_ne_zero_of_finrank_one (W : Submodule F V) (hW : Module.finrank F W = 1) :
    ∃ x ∈ W, x ≠ 0 := by
  by_contra h
  push Not at h
  have : W = ⊥ := (Submodule.eq_bot_iff W).mpr h
  rw [this] at hW
  simp at hW

theorem elt_form (hV : Module.finrank F V = 3) (Z G C : Module.End F V) (hZ : Z * Z = 1)
    (hZdet : LinearMap.det Z = 1) (hZ1 : Z ≠ 1) (hG7 : G ^ 7 = 1) (hG1 : G ≠ 1)
    (hZG : Z * G = G * Z) (n : ℕ) (hC : C ^ (2 ^ n) = 1) (hdetC : LinearMap.det C = 1)
    (hZC : Z * C = C * Z) (hGC : G * C = C * G) :
    ∃ α : F, α ≠ 0 ∧ α ^ (2 ^ n) = 1 ∧ (∀ v ∈ LinearMap.ker (Z + 1), C v = α • v) ∧
      ∀ v ∈ LinearMap.ker (Z - 1), C v = (α ^ 2)⁻¹ • v := by
  obtain ⟨hdm, hdp⟩ := finrank_eig hV Z hZ hZdet hZ1
  have hc := isCompl_eig Z hZ
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have : CharP (Module.End F V) 7 :=
    charP_of_injective_algebraMap (algebraMap F (Module.End F V)).injective 7
  have : FiniteDimensional F (LinearMap.ker (Z + 1)) := inferInstance
  have : FiniteDimensional F (LinearMap.ker (Z - 1)) := inferInstance
  set N : Module.End F V := G - 1 with hNdef
  have hZN : Z * N = N * Z := by
    rw [hNdef, mul_sub, sub_mul, mul_one, one_mul, hZG]
  have hN7 : N ^ 7 = 0 := by
    have : Commute G 1 := Commute.one_right G
    rw [hNdef, sub_pow_char_of_commute (p := 7) this, hG7, one_pow, sub_self]
  have hNm := ker_plus_inv Z N hZN
  have hNp := ker_minus_inv Z N hZN
  have hGp := ker_minus_inv Z G hZG
  have hCm := ker_plus_inv Z C hZC
  have hCp := ker_minus_inv Z C hZC
  have hN2 := sq_eq_zero_on (LinearMap.ker (Z + 1)) hdm N hNm hN7
  obtain ⟨l0, hl0⟩ := scalar_on_line (LinearMap.ker (Z - 1)) hdp G hGp
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_finrank_one _ hdp
  have hGpow : ∀ k : ℕ, ∀ v ∈ LinearMap.ker (Z - 1), (G ^ k) v = l0 ^ k • v := by
    intro k
    induction k with
    | zero => intro v hv; simp
    | succ k ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply, hl0 v hv, map_smul, ih v hv, smul_smul, pow_succ]
      ring_nf
  have hl7 : l0 ^ 7 = 1 := by
    have h1 := hGpow 7 x hx
    rw [hG7, Module.End.one_apply] at h1
    have h2 : (l0 ^ 7 - 1) • x = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx0)
  have hl1 : l0 = 1 := by
    have : (l0 - 1) ^ 7 = 0 := by rw [sub_pow_char (p := 7), hl7, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  have hGp1 : ∀ v ∈ LinearMap.ker (Z - 1), G v = v := fun v hv => by
    rw [hl0 v hv, hl1, one_smul]
  obtain ⟨w, hw, hNw⟩ : ∃ w ∈ LinearMap.ker (Z + 1), N w ≠ 0 := by
    by_contra h
    push Not at h
    apply hG1
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker (Z - 1) ⊔ LinearMap.ker (Z + 1) := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
    have hNq := h q hq
    have : G q = q := by
      have : (G - 1) q = 0 := hNq
      simpa [sub_eq_zero] using this
    rw [map_add, hGp1 p hp, this]
    simp
  have hNCop : N * C = C * N := by
    rw [hNdef, sub_mul, mul_sub, mul_one, one_mul, hGC]
  have hNC : ∀ v, N (C v) = C (N v) := fun v => by
    have := congrArg (fun f : Module.End F V => f v) hNCop
    simpa using this
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, (Nat.succ_pred_eq_of_pos (by positivity)).symm⟩
  have hcast : ((m + 1 : ℕ) : F) ≠ 0 := by
    rw [← hm]; push_cast; exact pow_ne_zero _ two_ne_zero'
  have hCk : ∀ v ∈ LinearMap.ker (Z + 1), (C ^ (m + 1)) v = v := fun v _ => by
    rw [← hm, hC, Module.End.one_apply]
  obtain ⟨α, hα, hCα⟩ := scalar_on_plane (LinearMap.ker (Z + 1)) hdm N C hNm hCm hNC hN2 w hw hNw m
    hcast hCk
  rw [← hm] at hα
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  obtain ⟨μ, hμ⟩ := scalar_on_line (LinearMap.ker (Z - 1)) hdp C hCp
  have hdet := det_of_eig Z hZ α μ C hCα hμ
  rw [hdetC, hdp, hdm, pow_one] at hdet
  refine ⟨α, hα0, hα, hCα, fun v hv => ?_⟩
  rw [hμ v hv]
  congr 1
  exact eq_inv_of_mul_eq_one_left hdet.symm

omit [FiniteDimensional F V] in
theorem eq_of_eig (Z C : Module.End F V) (hZ : Z * Z = 1) (α μ : F)
    (hm : ∀ v ∈ LinearMap.ker (Z + 1), C v = α • v)
    (hp : ∀ v ∈ LinearMap.ker (Z - 1), C v = μ • v) :
    C = α • ((2 : F)⁻¹ • (1 - Z)) + μ • ((2 : F)⁻¹ • (1 + Z)) := by
  have hc := isCompl_eig Z hZ
  have h2 : (2 : F) ≠ 0 := two_ne_zero'
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ LinearMap.ker (Z - 1) ⊔ LinearMap.ker (Z + 1) := by
    rw [hc.sup_eq_top]; trivial
  obtain ⟨p, hp', q, hq, rfl⟩ := Submodule.mem_sup.mp hv
  have hZp : Z p = p := by
    simpa [sub_eq_zero] using hp'
  have hZq : Z q = -q := by
    have : Z q + q = 0 := by simpa using hq
    exact eq_neg_of_add_eq_zero_left this
  rw [map_add, hp p hp', hm q hq]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_add, hZp, hZq]
  match_scalars <;> field_simp <;> ring

omit [AddCommGroup V] [Module F V] [FiniteDimensional F V] in
theorem elt_form_matrix (Z G C : Matrix (Fin 3) (Fin 3) F) (hZ : Z * Z = 1)
    (hZdet : Z.det = 1) (hZ1 : Z ≠ 1) (hG7 : G ^ 7 = 1) (hG1 : G ≠ 1)
    (hZG : Z * G = G * Z) (n : ℕ) (hC : C ^ (2 ^ n) = 1) (hdetC : C.det = 1)
    (hZC : Z * C = C * Z) (hGC : G * C = C * G) :
    ∃ α : F, α ≠ 0 ∧ α ^ (2 ^ n) = 1 ∧
      C = α • ((2 : F)⁻¹ • (1 - Z)) + (α ^ 2)⁻¹ • ((2 : F)⁻¹ • (1 + Z)) := by
  let e := Matrix.toLinAlgEquiv' (R := F) (n := Fin 3)
  have hdet : ∀ M : Matrix (Fin 3) (Fin 3) F, LinearMap.det (e M) = M.det := fun M => by
    show LinearMap.det (Matrix.toLin' M) = M.det
    exact LinearMap.det_toLin' M
  have hV : Module.finrank F (Fin 3 → F) = 3 := by simp
  obtain ⟨α, hα0, hα, hm, hp⟩ := elt_form (V := Fin 3 → F) hV (e Z) (e G) (e C)
    (by rw [← map_mul, hZ, map_one]) (by rw [hdet, hZdet])
    (fun h => hZ1 (e.injective (by rw [h, map_one])))
    (by rw [← map_pow, hG7, map_one]) (fun h => hG1 (e.injective (by rw [h, map_one])))
    (by rw [← map_mul, ← map_mul, hZG]) n (by rw [← map_pow, hC, map_one]) (by rw [hdet, hdetC])
    (by rw [← map_mul, ← map_mul, hZC]) (by rw [← map_mul, ← map_mul, hGC])
  refine ⟨α, hα0, hα, e.injective ?_⟩
  rw [eq_of_eig (e Z) (e C) (by rw [← map_mul, hZ, map_one]) α (α ^ 2)⁻¹ hm hp]
  simp [map_add, map_smul, map_sub, map_one]

end CFSG.Quasithin.Stellmacher.CD.L3YC.Row9

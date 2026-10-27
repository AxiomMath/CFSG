module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityRank

public section

namespace CFSG.StandardType

open Module Multiplicative CFSG.Assembly CFSG.StandardType.NoOffOm CFSG.StandardType.Triality
  CFSG.StandardType.D4Rank CFSG.StandardType.OrthD4
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace OrdPTri

@[expose] def uvec (i : Fin 4) : Fin 4 → ZMod 3 := Pi.single i 1

theorem card_supp_uvec (i : Fin 4) : (supp (uvec i)).card = 1 := by
  revert i
  decide

theorem card_supp_one_sub_uvec (i : Fin 4) : (supp (1 - uvec i)).card = 3 := by
  revert i
  decide

theorem card_supp_one : (supp (1 : Fin 4 → ZMod 3)).card = 4 := by
  decide

theorem suppLE_uvec_one_sub {i j : Fin 4} (hji : j ≠ i) : SuppLE (uvec j) (1 - uvec i) := by
  have key : ∀ i j : Fin 4, j ≠ i → ∀ k, uvec j k ≠ 0 → (1 - uvec i) k ≠ 0 := by decide
  exact key i j hji

theorem ofAdd_pow_three {H : Type*} [Group H] (ι₁ : Multiplicative (Fin 4 → ZMod 3) →* H)
    (x : Fin 4 → ZMod 3) : ι₁ (ofAdd x) ^ 3 = 1 := by
  rw [← map_pow, ← ofAdd_nsmul]
  have h : (3 • x : Fin 4 → ZMod 3) = 0 := by
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  rw [h, ofAdd_zero, map_one]

theorem one_sub_uvec_add (i : Fin 4) : (1 - uvec i) + uvec i = 1 := by
  rw [sub_add_cancel]

section Ring

variable {R : Type*} [Ring R]

theorem add_pow_two_pow_of_commute (h2 : (2 : R) = 0) {x y : R} (h : Commute x y) (n : ℕ) :
    (x + y) ^ 2 ^ n = x ^ 2 ^ n + y ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : Commute (x ^ 2 ^ n) (y ^ 2 ^ n) := (h.pow_left _).pow_right _
    rw [pow_succ, pow_mul, ih, pow_mul, pow_mul, sq, sq, sq, add_mul, mul_add, mul_add,
      hc.eq]
    have h2' : y ^ 2 ^ n * x ^ 2 ^ n + y ^ 2 ^ n * x ^ 2 ^ n = 0 := by
      rw [← two_mul, h2, zero_mul]
    calc x ^ 2 ^ n * x ^ 2 ^ n + y ^ 2 ^ n * x ^ 2 ^ n + (y ^ 2 ^ n * x ^ 2 ^ n +
          y ^ 2 ^ n * y ^ 2 ^ n)
        = x ^ 2 ^ n * x ^ 2 ^ n + (y ^ 2 ^ n * x ^ 2 ^ n + y ^ 2 ^ n * x ^ 2 ^ n) +
          y ^ 2 ^ n * y ^ 2 ^ n := by abel
      _ = x ^ 2 ^ n * x ^ 2 ^ n + y ^ 2 ^ n * y ^ 2 ^ n := by rw [h2', add_zero]

end Ring

variable {K : Type} [Field K] [CharP K 2]

structure Frame4 (ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K) : Prop where
  kerle : ∀ s s' : Fin 4 → ZMod 3, (LinearMap.ker (omRep (ι₁ (ofAdd s')) - 1) ≤
    LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) ↔ SuppLE s s')
  dim : ∀ s : Fin 4 → ZMod 3, omFixDim (ι₁ (ofAdd s)) + 2 * (supp s).card = 8

namespace Frame4

variable {ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K}

noncomputable abbrev fr (ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K) (s : Fin 4 → ZMod 3) :
    Module.End K (Fin (2 * 4) → K) :=
  omRep (ι₁ (ofAdd s))

noncomputable abbrev pr (ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K) (i : Fin 4) :
    Module.End K (Fin (2 * 4) → K) :=
  fr ι₁ (uvec i) + fr ι₁ (uvec i) ^ 2

noncomputable abbrev plane (ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K) (i : Fin 4) :
    Submodule K (Fin (2 * 4) → K) :=
  LinearMap.ker (fr ι₁ (1 - uvec i) - 1)

omit [CharP K 2] in
theorem fr_add (s t : Fin 4 → ZMod 3) : fr ι₁ (s + t) = fr ι₁ s * fr ι₁ t := by
  rw [fr, fr, fr, ofAdd_add, map_mul, map_mul]

omit [CharP K 2] in
theorem fr_comm (s t : Fin 4 → ZMod 3) : fr ι₁ s * fr ι₁ t = fr ι₁ t * fr ι₁ s := by
  rw [← fr_add, ← fr_add, add_comm]

omit [CharP K 2] in
theorem fr_comm_apply (s t : Fin 4 → ZMod 3) (v : Fin (2 * 4) → K) :
    fr ι₁ s (fr ι₁ t v) = fr ι₁ t (fr ι₁ s v) := by
  rw [← Module.End.mul_apply, fr_comm, Module.End.mul_apply]

omit [CharP K 2] in
theorem fr_cube (s : Fin 4 → ZMod 3) : fr ι₁ s ^ 3 = 1 := by
  rw [fr, ← map_pow, ofAdd_pow_three, map_one]

omit [CharP K 2] in
theorem fr_cube_apply (s : Fin 4 → ZMod 3) (v : Fin (2 * 4) → K) :
    fr ι₁ s (fr ι₁ s (fr ι₁ s v)) = v := by
  have h : (fr ι₁ s ^ 3) v = v := by rw [fr_cube]; rfl
  rwa [pow_succ, pow_succ, pow_one, Module.End.mul_apply, Module.End.mul_apply] at h

omit [CharP K 2] in
theorem fr_injective (s : Fin 4 → ZMod 3) : Function.Injective (fr ι₁ s) := by
  intro v w h
  have h' : fr ι₁ s (fr ι₁ s (fr ι₁ s v)) = fr ι₁ s (fr ι₁ s (fr ι₁ s w)) := by rw [h]
  rwa [fr_cube_apply, fr_cube_apply] at h'

theorem add_self (v : Fin (2 * 4) → K) : v + v = 0 := CharTwo.add_self_eq_zero v

omit [CharP K 2] in
theorem pr_apply (i : Fin 4) (v : Fin (2 * 4) → K) :
    pr ι₁ i v = fr ι₁ (uvec i) v + fr ι₁ (uvec i) (fr ι₁ (uvec i) v) := by
  rw [pr, LinearMap.add_apply, sq, Module.End.mul_apply]

omit [CharP K 2] in
theorem finrank_ker_b (h : Frame4 ι₁) (i : Fin 4) :
    finrank K (LinearMap.ker (fr ι₁ (uvec i) - 1)) = 6 := by
  have := h.dim (uvec i)
  rw [card_supp_uvec] at this
  exact (by omega : omFixDim (ι₁ (ofAdd (uvec i))) = 6)

omit [CharP K 2] in
theorem finrank_plane (h : Frame4 ι₁) (i : Fin 4) : finrank K (plane ι₁ i) = 2 := by
  have := h.dim (1 - uvec i)
  rw [card_supp_one_sub_uvec] at this
  exact (by omega : omFixDim (ι₁ (ofAdd (1 - uvec i))) = 2)

omit [CharP K 2] in
theorem ker_one_eq_bot (h : Frame4 ι₁) : LinearMap.ker (fr ι₁ 1 - 1) = ⊥ := by
  have := h.dim 1
  rw [card_supp_one] at this
  have h0 : omFixDim (ι₁ (ofAdd 1)) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp h0

omit [CharP K 2] in
theorem eq_zero_of_fix (h : Frame4 ι₁) {i : Fin 4} {v : Fin (2 * 4) → K}
    (hc : fr ι₁ (1 - uvec i) v = v) (hb : fr ι₁ (uvec i) v = v) : v = 0 := by
  have h1 : fr ι₁ 1 v = v := by
    rw [← one_sub_uvec_add i, fr_add, Module.End.mul_apply, hb, hc]
  have h2 : v ∈ LinearMap.ker (fr ι₁ 1 - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, h1, Module.End.one_apply, sub_self]
  rw [h.ker_one_eq_bot] at h2
  exact (Submodule.mem_bot K).mp h2

omit [CharP K 2] in
theorem mem_plane_iff {i : Fin 4} {v : Fin (2 * 4) → K} :
    v ∈ plane ι₁ i ↔ fr ι₁ (1 - uvec i) v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem eq_of_add_eq_zero {f : Module.End K (Fin (2 * 4) → K)} {v : Fin (2 * 4) → K}
    (h : v + f v = 0) : f v = v := by
  calc f v = f v + (v + f v) := by rw [h, add_zero]
    _ = (f v + f v) + v := by abel
    _ = v := by rw [add_self, zero_add]

theorem pr_apply_of_mem (h : Frame4 ι₁) {i : Fin 4} {v : Fin (2 * 4) → K}
    (hv : v ∈ plane ι₁ i) : pr ι₁ i v = v := by
  have hc : fr ι₁ (1 - uvec i) v = v := mem_plane_iff.mp hv
  set w := v + fr ι₁ (uvec i) v + fr ι₁ (uvec i) (fr ι₁ (uvec i) v) with hw
  have hbw : fr ι₁ (uvec i) w = w := by
    rw [hw, map_add, map_add, fr_cube_apply]
    abel
  have hcw : fr ι₁ (1 - uvec i) w = w := by
    rw [hw, map_add, map_add, fr_comm_apply (1 - uvec i) (uvec i),
      fr_comm_apply (1 - uvec i) (uvec i) (fr ι₁ (uvec i) v),
      fr_comm_apply (1 - uvec i) (uvec i) v, hc]
  have hw0 := h.eq_zero_of_fix hcw hbw
  rw [pr_apply]
  calc fr ι₁ (uvec i) v + fr ι₁ (uvec i) (fr ι₁ (uvec i) v) = w + v := by
        rw [hw]
        calc fr ι₁ (uvec i) v + fr ι₁ (uvec i) (fr ι₁ (uvec i) v)
            = (v + v) + (fr ι₁ (uvec i) v + fr ι₁ (uvec i) (fr ι₁ (uvec i) v)) := by
              rw [add_self, zero_add]
          _ = v + fr ι₁ (uvec i) v + fr ι₁ (uvec i) (fr ι₁ (uvec i) v) + v := by abel
    _ = v := by rw [hw0, zero_add]

theorem ker_pr (i : Fin 4) : LinearMap.ker (pr ι₁ i) = LinearMap.ker (fr ι₁ (uvec i) - 1) := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, pr_apply, LinearMap.sub_apply, Module.End.one_apply]
  constructor
  · intro h0
    have h1 : fr ι₁ (uvec i) (v + fr ι₁ (uvec i) v) = fr ι₁ (uvec i) 0 := by
      rw [map_add, map_zero]
      exact h0
    have h2 : v + fr ι₁ (uvec i) v = 0 := fr_injective _ h1
    rw [eq_of_add_eq_zero h2, sub_self]
  · intro h0
    have h3 : fr ι₁ (uvec i) v = v := sub_eq_zero.mp h0
    rw [h3, h3, add_self]

theorem finrank_range_pr (h : Frame4 ι₁) (i : Fin 4) :
    finrank K (LinearMap.range (pr ι₁ i)) = 2 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (pr ι₁ i)
  rw [ker_pr, h.finrank_ker_b, Module.finrank_fin_fun] at h1
  omega

theorem plane_eq_range (h : Frame4 ι₁) (i : Fin 4) :
    plane ι₁ i = LinearMap.range (pr ι₁ i) := by
  refine Submodule.eq_of_le_of_finrank_eq (fun v hv => ⟨v, h.pr_apply_of_mem hv⟩) ?_
  rw [h.finrank_plane, h.finrank_range_pr]

theorem pr_mem (h : Frame4 ι₁) (i : Fin 4) (v : Fin (2 * 4) → K) : pr ι₁ i v ∈ plane ι₁ i := by
  rw [h.plane_eq_range]
  exact ⟨v, rfl⟩

omit [CharP K 2] in
theorem fix_of_mem_plane (h : Frame4 ι₁) {i j : Fin 4} (hji : j ≠ i) {v : Fin (2 * 4) → K}
    (hv : v ∈ plane ι₁ i) : fr ι₁ (uvec j) v = v := by
  have h1 := (h.kerle (uvec j) (1 - uvec i)).mpr (suppLE_uvec_one_sub hji) hv
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
  exact h1

theorem pr_eq_zero (h : Frame4 ι₁) {i j : Fin 4} (hji : j ≠ i) {v : Fin (2 * 4) → K}
    (hv : v ∈ plane ι₁ i) : pr ι₁ j v = 0 := by
  rw [pr_apply, h.fix_of_mem_plane hji hv, h.fix_of_mem_plane hji hv, add_self]

theorem eq_sum_pr (h : Frame4 ι₁) (v : Fin (2 * 4) → K) : v = ∑ i, pr ι₁ i v := by
  set w := v - ∑ i, pr ι₁ i v with hw
  have hpr : ∀ j, pr ι₁ j w = 0 := by
    intro j
    rw [hw, map_sub, map_sum, Finset.sum_eq_single j, h.pr_apply_of_mem (h.pr_mem j v),
      sub_self]
    · intro i _ hij
      exact h.pr_eq_zero (Ne.symm hij) (h.pr_mem i v)
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hfix : ∀ j, fr ι₁ (uvec j) w = w := by
    intro j
    have h2 : w ∈ LinearMap.ker (pr ι₁ j) := hpr j
    rw [ker_pr, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero] at h2
    exact h2
  have hc : fr ι₁ (1 - uvec 0) w = w := by
    have e : (1 : Fin 4 → ZMod 3) - uvec 0 = uvec 1 + (uvec 2 + uvec 3) := by decide
    rw [e, fr_add, fr_add, Module.End.mul_apply, Module.End.mul_apply, hfix 3, hfix 2, hfix 1]
  have hw0 := h.eq_zero_of_fix hc (hfix 0)
  rw [hw, sub_eq_zero] at hw0
  exact hw0

omit [CharP K 2] in
theorem polar_omRep (x : Om8 K) (u w : Fin (2 * 4) → K) :
    QuadraticMap.polar (coordinateQuadPlus 4 K) (omRep x u) (omRep x w) =
      QuadraticMap.polar (coordinateQuadPlus 4 K) u w := by
  have hQ : ∀ v, coordinateQuadPlus 4 K (omRep x v) = coordinateQuadPlus 4 K v := fun v => by
    rw [omRep_apply, ← matrixLinearEquiv_apply]
    exact (mem_matrixIsometries_iff _ _).mp (matrixDerived_le_isometries _ x.2) v
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hQ, hQ, hQ]

theorem polar_eq_zero (h : Frame4 ι₁) {i j : Fin 4} (hij : i ≠ j) {u w : Fin (2 * 4) → K}
    (hu : u ∈ plane ι₁ i) (hw : w ∈ plane ι₁ j) :
    QuadraticMap.polar (coordinateQuadPlus 4 K) u w = 0 := by
  have hbw : fr ι₁ (uvec i) w = w := h.fix_of_mem_plane hij hw
  set y := fr ι₁ (uvec i) u with hy
  have hu' : u = y + fr ι₁ (uvec i) y := by
    rw [hy, ← pr_apply, h.pr_apply_of_mem hu]
  have h1 : QuadraticMap.polar (coordinateQuadPlus 4 K) (fr ι₁ (uvec i) y) w =
      QuadraticMap.polar (coordinateQuadPlus 4 K) y w := by
    conv_lhs => rw [← hbw]
    exact polar_omRep _ y w
  rw [hu', QuadraticMap.polar_add_left, h1, CharTwo.add_self_eq_zero]

theorem sq_add_add_one_ne_zero (h3 : ¬ 3 ∣ Nat.card K - 1) (l : K) :
    l ^ 2 + l + 1 ≠ 0 := by
  classical
  intro hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  have hl3 : l ^ 3 = 1 := by linear_combination (l - 1) * hl
  have hl1 : l ≠ 1 := by
    rintro rfl
    have h1 : (1 : K) ^ 2 + 1 + 1 = 1 := by
      rw [one_pow, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [h1] at hl
    exact one_ne_zero hl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set u : Kˣ := Units.mk0 l hl0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, hl3,
    Units.val_one])
  have hu1 : u ≠ 1 := fun h => hl1 (by
    have := congrArg Units.val h
    rwa [hu, Units.val_mk0, Units.val_one] at this)
  have ho : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
  rw [Nat.card_units, ho] at hdvd
  exact h3 hdvd

omit [CharP K 2] in
theorem fr_mem_plane {i : Fin 4} (s : Fin 4 → ZMod 3) {v : Fin (2 * 4) → K}
    (hv : v ∈ plane ι₁ i) : fr ι₁ s v ∈ plane ι₁ i := by
  rw [mem_plane_iff, fr_comm_apply, mem_plane_iff.mp hv]

theorem exists_eq_smul_add (h : Frame4 ι₁) (h3 : ¬ 3 ∣ Nat.card K - 1) {i : Fin 4}
    {v w : Fin (2 * 4) → K} (hv : v ∈ plane ι₁ i) (hv0 : v ≠ 0) (hw : w ∈ plane ι₁ i) :
    ∃ α β : K, w = α • v + β • fr ι₁ (uvec i) v := by
  have hbv : fr ι₁ (uvec i) v ∈ plane ι₁ i := fr_mem_plane _ hv
  have hq : v + fr ι₁ (uvec i) v + fr ι₁ (uvec i) (fr ι₁ (uvec i) v) = 0 := by
    have h1 := h.pr_apply_of_mem hv
    rw [pr_apply] at h1
    calc v + fr ι₁ (uvec i) v + fr ι₁ (uvec i) (fr ι₁ (uvec i) v)
        = v + (fr ι₁ (uvec i) v + fr ι₁ (uvec i) (fr ι₁ (uvec i) v)) := by abel
      _ = v + v := by rw [h1]
      _ = 0 := add_self v
  have hli : LinearIndependent K ![v, fr ι₁ (uvec i) v] := by
    rw [LinearIndependent.pair_iff]
    intro a c hac
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, add_zero] at hac
      exact ⟨(smul_eq_zero.mp hac).resolve_right hv0, rfl⟩
    · exfalso
      have hbv' : fr ι₁ (uvec i) v = (a / c) • v := by
        have e1 : c • fr ι₁ (uvec i) v = a • v := by
          have e2 : a • v + c • fr ι₁ (uvec i) v + a • v = a • v := by rw [hac, zero_add]
          calc c • fr ι₁ (uvec i) v = (a • v + a • v) + c • fr ι₁ (uvec i) v := by
                rw [add_self, zero_add]
            _ = a • v + c • fr ι₁ (uvec i) v + a • v := by abel
            _ = a • v := e2
        calc fr ι₁ (uvec i) v = c⁻¹ • (c • fr ι₁ (uvec i) v) := by
              rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
          _ = (a / c) • v := by rw [e1, smul_smul, div_eq_inv_mul]
      have h2 : ((a / c) ^ 2 + (a / c) + 1) • v = 0 := by
        rw [hbv', map_smul, hbv', smul_smul] at hq
        rw [add_smul, add_smul, one_smul, sq]
        calc (a / c * (a / c)) • v + (a / c) • v + v = v + (a / c) • v + (a / c * (a / c)) • v := by
              abel
          _ = 0 := hq
      exact sq_add_add_one_ne_zero h3 (a / c) ((smul_eq_zero.mp h2).resolve_right hv0)
  set f : Fin 2 → ↥(plane ι₁ i) := ![⟨v, hv⟩, ⟨fr ι₁ (uvec i) v, hbv⟩] with hf
  have hfli : LinearIndependent K f := by
    apply LinearIndependent.of_comp (plane ι₁ i).subtype
    convert hli using 1
    ext j : 1
    fin_cases j <;> rfl
  have htop := hfli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, h.finrank_plane])
  have hw' : (⟨w, hw⟩ : ↥(plane ι₁ i)) ∈ Submodule.span K (Set.range f) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw'
  refine ⟨c 0, c 1, ?_⟩
  have h4 := congrArg Subtype.val hc
  rw [Fin.sum_univ_two] at h4
  simpa [hf] using h4.symm

theorem exists_commute_eq (h : Frame4 ι₁) (h3 : ¬ 3 ∣ Nat.card K - 1)
    {g : Module.End K (Fin (2 * 4) → K)} (hg : ∀ s, g * fr ι₁ s = fr ι₁ s * g) (i : Fin 4) :
    ∃ α β : K, ∀ w ∈ plane ι₁ i, g w = α • w + β • fr ι₁ (uvec i) w := by
  have hgP : ∀ w ∈ plane ι₁ i, g w ∈ plane ι₁ i := by
    intro w hw
    rw [mem_plane_iff] at hw ⊢
    rw [← Module.End.mul_apply, ← hg, Module.End.mul_apply, hw]
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ plane ι₁ i, v ≠ 0 := by
    by_contra hne
    push Not at hne
    have hbot : plane ι₁ i = ⊥ := (Submodule.eq_bot_iff _).mpr hne
    have := h.finrank_plane i
    rw [hbot, finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨α, β, hαβ⟩ := h.exists_eq_smul_add h3 hv hv0 (hgP v hv)
  refine ⟨α, β, fun w hw => ?_⟩
  obtain ⟨a, c, rfl⟩ := h.exists_eq_smul_add h3 hv hv0 hw
  have hgb : g (fr ι₁ (uvec i) v) = fr ι₁ (uvec i) (g v) := by
    rw [← Module.End.mul_apply, hg, Module.End.mul_apply]
  simp only [map_add, map_smul, hgb, hαβ]
  module

theorem pow_card_sq_eq [Finite K] (h : Frame4 ι₁) (h3 : ¬ 3 ∣ Nat.card K - 1)
    {g : Module.End K (Fin (2 * 4) → K)} (hg : ∀ s, g * fr ι₁ s = fr ι₁ s * g) :
    g ^ (Nat.card K ^ 2) = g := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have h2E : (2 : Module.End K (Fin (2 * 4) → K)) = 0 := two_eq_zero_end CharTwo.two_eq_zero
  have hplane : ∀ i, ∀ w ∈ plane ι₁ i, (g ^ (Nat.card K ^ 2)) w = g w := by
    intro i
    obtain ⟨α, β, hαβ⟩ := h.exists_commute_eq h3 hg i
    set T : Module.End K (Fin (2 * 4) → K) := α • 1 + β • fr ι₁ (uvec i) with hT
    have hgT : ∀ m : ℕ, ∀ w ∈ plane ι₁ i, (g ^ m) w = (T ^ m) w ∧ (T ^ m) w ∈ plane ι₁ i := by
      intro m
      induction m with
      | zero => intro w hw; simp [hw]
      | succ m ih =>
        intro w hw
        obtain ⟨h1, h2⟩ := ih w hw
        refine ⟨?_, ?_⟩
        · rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h1, hαβ _ h2,
            hT, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
            Module.End.one_apply]
        · rw [pow_succ', Module.End.mul_apply, hT, LinearMap.add_apply, LinearMap.smul_apply,
            LinearMap.smul_apply, Module.End.one_apply]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ h2)
            (Submodule.smul_mem _ _ (fr_mem_plane _ h2))
    have hTq : T ^ (Nat.card K ^ 2) = T := by
      have hc : Commute (α • (1 : Module.End K (Fin (2 * 4) → K))) (β • fr ι₁ (uvec i)) :=
        (Commute.one_left _).smul_left α |>.smul_right β
      have hq2 : Nat.card K ^ 2 = 2 ^ (2 * (n : ℕ)) := by rw [hKn, ← pow_mul, mul_comm]
      rw [hT, hq2, add_pow_two_pow_of_commute h2E hc, smul_pow, smul_pow, one_pow, ← hq2]
      have hα : α ^ (Nat.card K ^ 2) = α := by
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_pow 2 α
      have hβ : β ^ (Nat.card K ^ 2) = β := by
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_pow 2 β
      have hb : fr ι₁ (uvec i) ^ (Nat.card K ^ 2) = fr ι₁ (uvec i) := by
        have hmod : Nat.card K ^ 2 % 3 = 1 := by
          rw [hKn, ← pow_mul, pow_mul', Nat.pow_mod]
          norm_num
        rw [← Nat.div_add_mod (Nat.card K ^ 2) 3, hmod, pow_add, pow_mul, fr_cube, one_pow,
          one_mul, pow_one]
      rw [hα, hβ, hb]
    intro w hw
    rw [(hgT _ w hw).1, hTq, hαβ w hw, hT, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply]
  refine LinearMap.ext fun v => ?_
  rw [h.eq_sum_pr v, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => hplane i _ (h.pr_mem i v)

end Frame4

end OrdPTri

end CFSG.StandardType

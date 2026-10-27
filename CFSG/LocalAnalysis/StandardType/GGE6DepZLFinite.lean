module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelIndep
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

@[expose] def cartanM : Mat6 := Matrix.of cartanE6

@[expose] def bilU (u v : Vec6) : ZMod 3 := u ⬝ᵥ cartanM.mulVec v

@[expose] def kappa : Vec6 := ![1, 0, 2, 0, 1, 2]

@[expose] def closureU : Submonoid Mat6 := Submonoid.closure (Set.range indepGens)

@[expose] def IsRefl6 (g : Mat6) : Prop :=
  g * g = 1 ∧ Fintype.card {v : Vec6 // g.mulVec v = v} * 3 = 3 ^ 6

theorem cartanM_kappa : cartanM.mulVec kappa = 0 := by decide +kernel

theorem rad_eq : ∀ v : Vec6, cartanM.mulVec v = 0 → ∃ a : ZMod 3, v = a • kappa := by
  decide +kernel

theorem closureU_fix_kappa {g : Mat6} (hg : g ∈ closureU) : g.mulVec kappa = kappa := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    revert i
    decide +kernel
  | one => exact Matrix.one_mulVec _
  | mul g h _ _ ihg ihh => rw [← Matrix.mulVec_mulVec, ihh, ihg]

theorem fixed_gensL_zero :
    ∀ v : Vec6, v 5 = 0 → (∀ i, (gensL i).mulVec v = v) → v = 0 := by
  decide +kernel

theorem closureL_fixed_zero {v : Vec6} (h5 : v 5 = 0) (h : ∀ g ∈ closureL, g.mulVec v = v) :
    v = 0 :=
  fixed_gensL_zero v h5 fun i => h _ (Submonoid.subset_closure ⟨i, rfl⟩)

private lemma zl_one_apply (i : Fin 6) : (1 : Mat6) i = Pi.single i 1 := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Pi.single_apply]

private lemma zl_reflMat_mulVec (α h u : Vec6) :
    (reflMat α h).mulVec u = u - (α ⬝ᵥ u) • h := by
  simp only [reflMat, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul]

private lemma zl_cartanE6_dot_single (j i : Fin 6) :
    cartanE6 j ⬝ᵥ (1 : Mat6) i = cartanE6 j i := by
  rw [zl_one_apply i, dotProduct_single_one]

private lemma zl_cartanM_mulVec_apply (u : Vec6) (i : Fin 6) :
    (cartanM.mulVec u) i = cartanE6 i ⬝ᵥ u := rfl

private lemma zl_basis_step (M : Submodule (ZMod 3) Vec6)
    (hM : ∀ g ∈ closureU, ∀ v ∈ M, g.mulVec v ∈ M) {i j : Fin 6}
    (hi : (1 : Mat6) i ∈ M) (hji : cartanE6 j i ≠ 0) : (1 : Mat6) j ∈ M := by
  have hm : (indepGens j).mulVec ((1 : Mat6) i) ∈ M :=
    hM (indepGens j) (Submonoid.subset_closure ⟨j, rfl⟩) _ hi
  rw [show indepGens j = reflMat (cartanE6 j) ((1 : Mat6) j) from rfl,
    zl_reflMat_mulVec, zl_cartanE6_dot_single j i] at hm
  have hmem : cartanE6 j i • (1 : Mat6) j ∈ M := by
    have hsub := M.sub_mem hi hm
    simpa only [sub_sub_cancel] using hsub
  have h := M.smul_mem (cartanE6 j i)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hji, one_smul] at h

private lemma zl_zmod_entry_diag : ∀ x : ZMod 3, 1 - x - x + 1 = x - 1 := by decide +kernel

private lemma zl_zmod_entry_off : ∀ x : ZMod 3, -x - x = x := by decide +kernel

private lemma zl_zmod_mul_eq_self : ∀ a x : ZMod 3, a * x = x → x ≠ 0 → a = 1 := by
  decide +kernel

private lemma zl_zmod_neg_two_mul : ∀ x : ZMod 3, -(2 * x) = x := by decide +kernel

private lemma zl_mat_sub_one_sq {T : Mat6} (h2 : T * T = 1) :
    (T - 1) * (T - 1) = T - 1 := by
  have h : (T - 1) * (T - 1) = T * T - T - T + 1 := by noncomm_ring
  rw [h, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
      | exact zl_zmod_entry_diag _
      | exact zl_zmod_entry_off _

private lemma zl_exists_vecMulVec_of_idem (N : Mat6) (hNN : N * N = N)
    (hker : Fintype.card {v : Vec6 // N.mulVec v = 0} = 243) :
    ∃ c l : Vec6, c ≠ 0 ∧ N.mulVec c = c ∧ N = Matrix.vecMulVec c l := by
  classical
  let φ : Vec6 →ₗ[ZMod 3] Vec6 := N.mulVecLin
  have hφ : ∀ v : Vec6, φ v = N.mulVec v := fun v => Matrix.mulVecLin_apply N v
  have hkerφ : Fintype.card (LinearMap.ker φ) = 243 := by
    rw [show Fintype.card (LinearMap.ker φ)
        = Fintype.card {v : Vec6 // N.mulVec v = 0} from
      Fintype.card_congr (Equiv.subtypeEquivRight fun v => by
        rw [LinearMap.mem_ker, hφ])]
    exact hker
  have hfrV : Module.finrank (ZMod 3) Vec6 = 6 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 3) (V := Vec6)
    rw [ZMod.card, show Fintype.card Vec6 = 729 from by decide +kernel] at h
    have h' : (3 : ℕ) ^ 6 = 3 ^ Module.finrank (ZMod 3) Vec6 := by
      rw [← h]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ)) h'.symm
  have hfrK : Module.finrank (ZMod 3) (LinearMap.ker φ) = 5 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 3) (V := LinearMap.ker φ)
    rw [ZMod.card, hkerφ] at h
    have h' : (3 : ℕ) ^ 5 = 3 ^ Module.finrank (ZMod 3) (LinearMap.ker φ) := by
      rw [← h]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ)) h'.symm
  have hfrR : Module.finrank (ZMod 3) (LinearMap.range φ) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [hfrV, hfrK] at h
    omega
  have hex : ∃ u : Vec6, N.mulVec u ≠ 0 := by
    by_contra h
    push Not at h
    have hbig : Fintype.card (LinearMap.ker φ) = Fintype.card Vec6 :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv fun v => by
        rw [LinearMap.mem_ker, hφ]; exact h v)
    rw [hkerφ, show Fintype.card Vec6 = 729 from by decide +kernel] at hbig
    norm_num at hbig
  obtain ⟨u₀, hu₀⟩ := hex
  set c : Vec6 := N.mulVec u₀ with hcdef
  have hc0 : c ≠ 0 := by rw [hcdef]; exact hu₀
  have hcmem : c ∈ LinearMap.range φ := ⟨u₀, by rw [hφ, hcdef]⟩
  have hspan : LinearMap.range φ = ZMod 3 ∙ c :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfrR hcmem hc0
  have hmem : ∀ j : Fin 6, φ (Pi.single j 1) ∈ ZMod 3 ∙ c := by
    intro j
    rw [← hspan]
    exact ⟨Pi.single j 1, rfl⟩
  choose l hl using fun j : Fin 6 => Submodule.mem_span_singleton.mp (hmem j)
  have hl' : ∀ j : Fin 6, N.mulVec (Pi.single j 1) = l j • c := by
    intro j
    rw [hl j, hφ]
  have hNl : N = Matrix.vecMulVec c l := by
    ext i j
    have hj := congrFun (hl' j) i
    rw [Matrix.mulVec_single_one] at hj
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hj
    rw [Matrix.vecMulVec_apply, hj, mul_comm]
  have hNc : N.mulVec c = c := by
    rw [hcdef, Matrix.mulVec_mulVec, hNN]
  exact ⟨c, l, hc0, hNc, hNl⟩

private lemma zl_zmod_three_mul (x : ZMod 3) : x * 3 = 0 := by
  rw [show (3 : ZMod 3) = 0 from by decide, mul_zero]

private lemma zl_zmod_t_sq : ∀ t : ZMod 3, t ≠ 0 → t * t = 1 := by decide +kernel

private lemma zl_zmod_refl_aux : ∀ a c d : ZMod 3, a - (2 * c) * d = a + c * d := by
  decide +kernel

private lemma zl_gram6_transpose : Matrix.transpose gram6 = gram6 := by decide +kernel

private lemma zl_bil6_comm (u v : Vec6) : bil6 u v = bil6 v u := by
  simp only [bil6]
  have h := Matrix.dotProduct_transpose_mulVec (A := gram6) (x := u) (y := v)
  rw [zl_gram6_transpose] at h
  exact h

private lemma zl_bil6_add_left (u₁ u₂ w : Vec6) :
    bil6 (u₁ + u₂) w = bil6 u₁ w + bil6 u₂ w := by
  simp only [bil6, add_dotProduct]

private lemma zl_bil6_smul_left (a : ZMod 3) (u w : Vec6) :
    bil6 (a • u) w = a * bil6 u w := by
  simp only [bil6, smul_dotProduct, smul_eq_mul]

private lemma zl_bil6_smul_right (b : ZMod 3) (u w : Vec6) :
    bil6 u (b • w) = b * bil6 u w := by
  simp only [bil6, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma zl_reflNorm_mulVec (u v : Vec6) :
    (reflNorm v).mulVec u = u + bil6 u v • v := by
  simp only [reflNorm, reflMat, bil6, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  rw [smul_dotProduct, dotProduct_comm]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact zl_zmod_refl_aux (u i) (u ⬝ᵥ Matrix.mulVec gram6 v) (v i)

private lemma zl_reflNorm_self (v : Vec6) (hv : norm6 v = 1) :
    reflNorm v * reflNorm v = 1 := by
  have hv' : bil6 v v = 1 := hv
  rw [Matrix.ext_iff_mulVec]
  intro u
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  simp only [zl_reflNorm_mulVec, zl_bil6_add_left, zl_bil6_smul_left, hv', mul_one]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp only [zl_zmod_three_mul, add_zero]

private lemma zl_reflNorm_mul_reflNorm_mulVec (u v w : Vec6) :
    (reflNorm v * reflNorm w).mulVec u
      = u + bil6 u w • w + (bil6 u v + bil6 u w * bil6 v w) • v := by
  rw [← Matrix.mulVec_mulVec]
  simp only [zl_reflNorm_mulVec, zl_bil6_add_left, zl_bil6_smul_left, zl_bil6_comm w v]

private lemma zl_reflNorm_mul_comm (v w : Vec6) (hv : norm6 v = 1) (hw : norm6 w = 1)
    (ht : bil6 v w = 0) : reflNorm v * reflNorm w = reflNorm w * reflNorm v := by
  rw [Matrix.ext_iff_mulVec]
  intro u
  simp only [zl_reflNorm_mul_reflNorm_mulVec, zl_bil6_comm w v, ht, mul_zero, add_zero]
  abel

private lemma zl_reflNorm_braid_left_mulVec (u v w : Vec6) (hv : norm6 v = 1) :
    (reflNorm v * reflNorm w * reflNorm v).mulVec u
      = u + (bil6 u w * bil6 v w + bil6 u v * bil6 v w ^ 2) • v
          + (bil6 u w + bil6 u v * bil6 v w) • w := by
  have hv' : bil6 v v = 1 := hv
  rw [← Matrix.mulVec_mulVec]
  simp only [zl_reflNorm_mulVec, zl_reflNorm_mul_reflNorm_mulVec, zl_bil6_add_left,
    zl_bil6_smul_left, zl_bil6_smul_right, zl_bil6_comm w v, hv', mul_one]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp only [zl_zmod_three_mul, add_zero]

private lemma zl_reflNorm_braid_right_mulVec (u v w : Vec6) (hw : norm6 w = 1) :
    (reflNorm w * reflNorm v * reflNorm w).mulVec u
      = u + (bil6 u v + bil6 u w * bil6 v w) • v
          + (bil6 u v * bil6 v w + bil6 u w * bil6 v w ^ 2) • w := by
  rw [zl_reflNorm_braid_left_mulVec u w v hw, zl_bil6_comm w v]
  abel

private lemma zl_reflNorm_braid (v w : Vec6) (hv : norm6 v = 1) (hw : norm6 w = 1)
    (ht : bil6 v w ≠ 0) :
    reflNorm v * reflNorm w * reflNorm v = reflNorm w * reflNorm v * reflNorm w := by
  rw [Matrix.ext_iff_mulVec]
  intro u
  rw [zl_reflNorm_braid_left_mulVec u v w hv, zl_reflNorm_braid_right_mulVec u v w hw]
  have ht2 : bil6 v w ^ 2 = 1 := by rw [pow_two]; exact zl_zmod_t_sq (bil6 v w) ht
  have hvcoef : bil6 u w * bil6 v w + bil6 u v * bil6 v w ^ 2
      = bil6 u v + bil6 u w * bil6 v w := by rw [ht2, mul_one]; ring
  have hwcoef : bil6 u v * bil6 v w + bil6 u w * bil6 v w ^ 2
      = bil6 u w + bil6 u v * bil6 v w := by rw [ht2, mul_one]; ring
  rw [hvcoef, hwcoef]

theorem refl36_pair : ∀ a ∈ refl36, ∀ b ∈ refl36, (a * b) ^ 2 = 1 ∨ (a * b) ^ 3 = 1 := by
  intro a ha b hb
  obtain ⟨v, hvmem, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨w, hwmem, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨_, _, hvn⟩ := Finset.mem_filter.mp hvmem
  obtain ⟨_, _, hwn⟩ := Finset.mem_filter.mp hwmem
  by_cases ht : bil6 v w = 0
  · left
    have haa : reflNorm v * reflNorm v = 1 := zl_reflNorm_self v hvn
    have hbb : reflNorm w * reflNorm w = 1 := zl_reflNorm_self w hwn
    have hcomm : reflNorm v * reflNorm w = reflNorm w * reflNorm v :=
      zl_reflNorm_mul_comm v w hvn hwn ht
    have h1 : (reflNorm v * reflNorm w) ^ 2
        = (reflNorm v * reflNorm v) * (reflNorm w * reflNorm w) := by
      rw [pow_two]
      calc (reflNorm v * reflNorm w) * (reflNorm v * reflNorm w)
          = reflNorm v * (reflNorm w * reflNorm v) * reflNorm w := by noncomm_ring
        _ = reflNorm v * (reflNorm v * reflNorm w) * reflNorm w := by rw [hcomm]
        _ = (reflNorm v * reflNorm v) * (reflNorm w * reflNorm w) := by noncomm_ring
    rw [h1, haa, hbb, one_mul]
  · right
    have haa : reflNorm v * reflNorm v = 1 := zl_reflNorm_self v hvn
    have hbb : reflNorm w * reflNorm w = 1 := zl_reflNorm_self w hwn
    have hbraid : reflNorm v * reflNorm w * reflNorm v
        = reflNorm w * reflNorm v * reflNorm w :=
      zl_reflNorm_braid v w hvn hwn ht
    have h1 : (reflNorm v * reflNorm w) ^ 3
        = (reflNorm v * reflNorm w * reflNorm v)
            * (reflNorm w * reflNorm v * reflNorm w) := by
      rw [pow_succ, pow_two]
      noncomm_ring
    rw [h1, hbraid]
    calc (reflNorm w * reflNorm v * reflNorm w) * (reflNorm w * reflNorm v * reflNorm w)
        = reflNorm w * (reflNorm v * (reflNorm w * reflNorm w) * reflNorm v) * reflNorm w := by
          noncomm_ring
      _ = reflNorm w * (reflNorm v * 1 * reflNorm v) * reflNorm w := by rw [hbb]
      _ = reflNorm w * (reflNorm v * reflNorm v) * reflNorm w := by rw [mul_one]
      _ = reflNorm w * 1 * reflNorm w := by rw [haa]
      _ = 1 := by rw [mul_one, hbb]

theorem isRefl6_form {g : Mat6} (hg : IsRefl6 g) :
    ∃ α h : Vec6, α ⬝ᵥ h = 2 ∧ g = reflMat α h := by
  classical
  obtain ⟨h2, hfix⟩ := hg
  set N : Mat6 := g - 1 with hN
  have hgN : g = N + 1 := by rw [hN, sub_add_cancel]
  have hNN : N * N = N := by rw [hN]; exact zl_mat_sub_one_sq h2
  have hker : Fintype.card {v : Vec6 // N.mulVec v = 0} = 243 := by
    have hc : Fintype.card {v : Vec6 // N.mulVec v = 0}
        = Fintype.card {v : Vec6 // g.mulVec v = v} := by
      refine Fintype.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      show N.mulVec v = 0 ↔ g.mulVec v = v
      rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    rw [hc]
    omega
  obtain ⟨c, l, hc0, hNc, hNl⟩ := zl_exists_vecMulVec_of_idem N hNN hker
  have hNm : ∀ u : Vec6, N.mulVec u = (l ⬝ᵥ u) • c := by
    intro u
    rw [hNl, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  have hgm : ∀ u : Vec6, g.mulVec u = u + (l ⬝ᵥ u) • c := by
    intro u
    rw [hgN, Matrix.add_mulVec, Matrix.one_mulVec, hNm u, add_comm]
  have hlc : l ⬝ᵥ c = 1 := by
    have h : (l ⬝ᵥ c) • c = c := (hNm c).symm.trans hNc
    obtain ⟨i, hi⟩ : ∃ i : Fin 6, c i ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hc0 (funext fun i => h' i)
    have hi' := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at hi'
    exact zl_zmod_mul_eq_self (l ⬝ᵥ c) (c i) hi' hi
  refine ⟨(2 : ZMod 3) • l, c, ?_, ?_⟩
  · rw [smul_dotProduct, smul_eq_mul, hlc, mul_one]
  · rw [Matrix.ext_iff_mulVec]
    intro u
    rw [hgm u, zl_reflMat_mulVec, smul_dotProduct, smul_eq_mul, sub_eq_add_neg,
      ← neg_smul, zl_zmod_neg_two_mul]

private def zl_roots72 : List Vec6 :=
  [![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1],
   ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 2, 2], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 1, 0],
   ![0, 0, 0, 1, 1, 1], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 2, 2, 0], ![0, 0, 0, 2, 2, 2],
   ![0, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 1],
   ![0, 0, 2, 0, 0, 0], ![0, 0, 2, 2, 0, 0], ![0, 0, 2, 2, 2, 0], ![0, 0, 2, 2, 2, 2],
   ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 0, 1, 1, 1],
   ![0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0],
   ![0, 1, 1, 2, 1, 1], ![0, 1, 1, 2, 2, 1], ![0, 2, 0, 0, 0, 0], ![0, 2, 0, 2, 0, 0],
   ![0, 2, 0, 2, 2, 0], ![0, 2, 0, 2, 2, 2], ![0, 2, 2, 1, 1, 2], ![0, 2, 2, 1, 2, 0],
   ![0, 2, 2, 1, 2, 2], ![0, 2, 2, 2, 0, 0], ![0, 2, 2, 2, 2, 0], ![0, 2, 2, 2, 2, 2],
   ![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 0],
   ![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1],
   ![1, 1, 1, 2, 1, 0], ![1, 1, 1, 2, 1, 1], ![1, 1, 1, 2, 2, 1], ![1, 1, 2, 0, 2, 1],
   ![1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 2, 2, 0, 2, 1],
   ![2, 0, 0, 0, 0, 0], ![2, 0, 2, 0, 0, 0], ![2, 0, 2, 2, 0, 0], ![2, 0, 2, 2, 2, 0],
   ![2, 0, 2, 2, 2, 2], ![2, 1, 1, 0, 1, 2], ![2, 2, 1, 0, 1, 2], ![2, 2, 1, 1, 1, 2],
   ![2, 2, 1, 1, 2, 0], ![2, 2, 1, 1, 2, 2], ![2, 2, 2, 1, 1, 2], ![2, 2, 2, 1, 2, 0],
   ![2, 2, 2, 1, 2, 2], ![2, 2, 2, 2, 0, 0], ![2, 2, 2, 2, 2, 0], ![2, 2, 2, 2, 2, 2]]

private lemma zl_gens_isometry : ∀ i : Fin 6,
    (indepGens i).transpose * cartanM * indepGens i = cartanM := by decide +kernel

private lemma zl_gens_perm : ∀ i : Fin 6, ∀ r ∈ zl_roots72,
    (indepGens i).mulVec r ∈ zl_roots72 := by decide +kernel

private lemma zl_single_mem_roots : ∀ j : Fin 6, (Pi.single j 1 : Vec6) ∈ zl_roots72 := by
  decide +kernel

private lemma zl_norm_one_moves : ∀ h : Vec6, bilU h h = 1 →
    ∃ j : Fin 6,
      (reflMat ((2 : ZMod 3) • cartanM.mulVec h) h).mulVec (Pi.single j 1) ∉ zl_roots72 := by
  decide +kernel

private def zl_good (g : Mat6) : Prop :=
  g.transpose * cartanM * g = cartanM ∧ ∀ r ∈ zl_roots72, g.mulVec r ∈ zl_roots72

private lemma zl_good_one : zl_good 1 := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_one, one_mul, mul_one]
  · intro r hr
    simpa only [Matrix.one_mulVec] using hr

private lemma zl_good_gens (i : Fin 6) : zl_good (indepGens i) :=
  ⟨zl_gens_isometry i, zl_gens_perm i⟩

private lemma zl_good_mul {g h : Mat6} (hg : zl_good g) (hh : zl_good h) :
    zl_good (g * h) := by
  obtain ⟨hgiso, hgperm⟩ := hg
  obtain ⟨hhiso, hhperm⟩ := hh
  refine ⟨?_, ?_⟩
  · calc
      (g * h).transpose * cartanM * (g * h)
          = h.transpose * (g.transpose * cartanM * g) * h := by
            rw [Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
      _ = h.transpose * cartanM * h := by rw [hgiso]
      _ = cartanM := hhiso
  · intro r hr
    rw [← Matrix.mulVec_mulVec]
    exact hgperm _ (hhperm r hr)

private lemma zl_closureU_good {g : Mat6} (hg : g ∈ closureU) : zl_good g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg => obtain ⟨i, rfl⟩ := hg; exact zl_good_gens i
  | one => exact zl_good_one
  | mul g h _ _ ihg ihh => exact zl_good_mul ihg ihh

private lemma zl_bilU_add_left (u₁ u₂ v : Vec6) :
    bilU (u₁ + u₂) v = bilU u₁ v + bilU u₂ v := by
  simp only [bilU, add_dotProduct]

private lemma zl_bilU_smul_left (a : ZMod 3) (u v : Vec6) :
    bilU (a • u) v = a * bilU u v := by
  simp only [bilU, smul_dotProduct, smul_eq_mul]

private lemma zl_bilU_smul_right (a : ZMod 3) (u v : Vec6) :
    bilU u (a • v) = a * bilU u v := by
  simp only [bilU, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma zl_bilU_neg_right (u v : Vec6) : bilU u (-v) = -bilU u v := by
  rw [show -v = (-1 : ZMod 3) • v from by
        funext i; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring,
      zl_bilU_smul_right, show (-1 : ZMod 3) * bilU u v = -bilU u v from by ring]

private lemma zl_isometry_bilU {T : Mat6} (hiso : T.transpose * cartanM * T = cartanM)
    (u w : Vec6) : bilU (T.mulVec u) (T.mulVec w) = bilU u w := by
  simp only [bilU]
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    ← Matrix.mul_assoc, hiso, ← Matrix.dotProduct_mulVec]

private lemma zl_bilU_sub_smul_neg (u h : Vec6) (c : ZMod 3) :
    bilU (u - c • h) (-h) = -bilU u h + c * bilU h h := by
  rw [sub_eq_add_neg, show -(c • h) = (-c) • h from by rw [neg_smul],
    zl_bilU_add_left, zl_bilU_smul_left]
  simp only [zl_bilU_neg_right]
  ring

private lemma zl_zmod_key : ∀ x a n : ZMod 3, -x + a * n = x → a * n = 2 * x := by
  decide +kernel

private lemma zl_zmod_cases : ∀ n : ZMod 3, n = 0 ∨ n = 1 ∨ n = 2 := by decide +kernel

theorem closureU_refl {g : Mat6} (hg : g ∈ closureU) (hr : IsRefl6 g) :
    ∃ h : Vec6, bilU h h = 2 ∧ g = reflMat (cartanM.mulVec h) h := by
  classical
  obtain ⟨α, h, hαh, hgeq⟩ := isRefl6_form hr
  obtain ⟨hiso, hperm⟩ := zl_closureU_good hg
  have hgh : g.mulVec h = -h := by
    rw [hgeq, zl_reflMat_mulVec, hαh]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  have hkey0 : ∀ u : Vec6, bilU (u - (α ⬝ᵥ u) • h) (-h) = bilU u h := by
    intro u
    have h1 := zl_isometry_bilU hiso u h
    rw [show g.mulVec u = u - (α ⬝ᵥ u) • h from by rw [hgeq, zl_reflMat_mulVec],
      hgh] at h1
    exact h1
  have hkey : ∀ u : Vec6, (α ⬝ᵥ u) * bilU h h = 2 * bilU u h := by
    intro u
    have h1 := hkey0 u
    rw [zl_bilU_sub_smul_neg] at h1
    exact zl_zmod_key (bilU u h) (α ⬝ᵥ u) (bilU h h) h1
  have hnα : bilU h h • α = (2 : ZMod 3) • cartanM.mulVec h := by
    funext j
    have hj := hkey (Pi.single j 1)
    rw [dotProduct_single_one] at hj
    have hb : bilU (Pi.single j 1) h = (cartanM.mulVec h) j := by
      simp only [bilU, single_one_dotProduct]
    rw [hb] at hj
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_comm (bilU h h) (α j)]
    exact hj
  rcases zl_zmod_cases (bilU h h) with hn0 | hn1 | hn2
  · exfalso
    have h2zero : (2 : ZMod 3) • cartanM.mulVec h = 0 := by
      rw [← hnα, hn0, zero_smul]
    have hMh : cartanM.mulVec h = 0 :=
      (smul_eq_zero.mp h2zero).resolve_left (by decide +kernel)
    obtain ⟨a, ha⟩ := rad_eq h hMh
    have hne : h ≠ 0 := by
      intro h0
      have hc : (0 : ZMod 3) = 2 := by simpa [h0] using hαh
      exact absurd hc (by decide +kernel)
    have hfixk : (α ⬝ᵥ kappa) • h = 0 := by
      have h1 : g.mulVec kappa = kappa := closureU_fix_kappa hg
      have h2 : kappa - (α ⬝ᵥ kappa) • h = g.mulVec kappa := by
        rw [hgeq, zl_reflMat_mulVec]
      exact sub_eq_self.mp (h2.trans h1)
    have hc0 : α ⬝ᵥ kappa = 0 := (smul_eq_zero.mp hfixk).resolve_right hne
    have hcontra : α ⬝ᵥ h = 0 := by
      rw [ha, dotProduct_smul, smul_eq_mul, hc0, mul_zero]
    rw [hcontra] at hαh
    exact absurd hαh (by decide +kernel)
  · exfalso
    have hα : α = (2 : ZMod 3) • cartanM.mulVec h := by
      have h1 : (1 : ZMod 3) • α = (2 : ZMod 3) • cartanM.mulVec h := by
        rw [← hnα, hn1]
      simpa using h1
    have hgeq' : g = reflMat ((2 : ZMod 3) • cartanM.mulVec h) h := by rw [hgeq, hα]
    obtain ⟨j, hj⟩ := zl_norm_one_moves h hn1
    have hmem := hperm (Pi.single j 1) (zl_single_mem_roots j)
    rw [hgeq'] at hmem
    exact hj hmem
  · refine ⟨h, hn2, ?_⟩
    have hα : α = cartanM.mulVec h := by
      have h1 : (2 : ZMod 3) • α = (2 : ZMod 3) • cartanM.mulVec h := by
        rw [← hnα, hn2]
      have h2 := congrArg (fun y : Vec6 => (2 : ZMod 3)⁻¹ • y) h1
      simpa only [smul_smul, inv_mul_cancel₀ (by decide +kernel : (2 : ZMod 3) ≠ 0),
        one_smul] using h2
    rw [hgeq, hα]

theorem zl_span_top (M : Submodule (ZMod 3) Vec6)
    (hM : ∀ g ∈ closureU, ∀ v ∈ M, g.mulVec v ∈ M) {u : Vec6} (hu : u ∈ M)
    (hu0 : cartanM.mulVec u ≠ 0) : M = ⊤ := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin 6, (cartanM.mulVec u) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext fun i => h i)
  have hcu : cartanE6 i ⬝ᵥ u ≠ 0 := by
    rwa [zl_cartanM_mulVec_apply] at hi
  have hei : (1 : Mat6) i ∈ M := by
    have hm : (indepGens i).mulVec u ∈ M :=
      hM (indepGens i) (Submonoid.subset_closure ⟨i, rfl⟩) u hu
    rw [show indepGens i = reflMat (cartanE6 i) ((1 : Mat6) i) from rfl,
      zl_reflMat_mulVec] at hm
    have hmem : (cartanE6 i ⬝ᵥ u) • (1 : Mat6) i ∈ M := by
      have hsub := M.sub_mem hu hm
      simpa only [sub_sub_cancel] using hsub
    have h := M.smul_mem (cartanE6 i ⬝ᵥ u)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hcu, one_smul] at h
  have h3 : (1 : Mat6) 3 ∈ M := by
    fin_cases i
    · exact zl_basis_step M hM
        (zl_basis_step M hM hei (by decide +kernel : cartanE6 2 0 ≠ 0))
        (by decide +kernel : cartanE6 3 2 ≠ 0)
    · exact zl_basis_step M hM hei (by decide +kernel : cartanE6 3 1 ≠ 0)
    · exact zl_basis_step M hM hei (by decide +kernel : cartanE6 3 2 ≠ 0)
    · exact hei
    · exact zl_basis_step M hM hei (by decide +kernel : cartanE6 3 4 ≠ 0)
    · exact zl_basis_step M hM
        (zl_basis_step M hM hei (by decide +kernel : cartanE6 4 5 ≠ 0))
        (by decide +kernel : cartanE6 3 4 ≠ 0)
  have hall : ∀ k : Fin 6, (1 : Mat6) k ∈ M := by
    intro k
    fin_cases k
    · exact zl_basis_step M hM
        (zl_basis_step M hM h3 (by decide +kernel : cartanE6 2 3 ≠ 0))
        (by decide +kernel : cartanE6 0 2 ≠ 0)
    · exact zl_basis_step M hM h3 (by decide +kernel : cartanE6 1 3 ≠ 0)
    · exact zl_basis_step M hM h3 (by decide +kernel : cartanE6 2 3 ≠ 0)
    · exact h3
    · exact zl_basis_step M hM h3 (by decide +kernel : cartanE6 4 3 ≠ 0)
    · exact zl_basis_step M hM
        (zl_basis_step M hM h3 (by decide +kernel : cartanE6 4 3 ≠ 0))
        (by decide +kernel : cartanE6 5 4 ≠ 0)
  rw [Submodule.eq_top_iff']
  intro v
  have hsum : v = ∑ j, v j • (1 : Mat6) j := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      have hkj : k ≠ j := fun h => hj h.symm
      rw [zl_one_apply j]
      simp [Pi.single_apply, hkj]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [hsum]
  exact M.sum_mem fun j _ => M.smul_mem (v j) (hall j)

end ZL

end E6Dep

end CFSG.StandardType

end

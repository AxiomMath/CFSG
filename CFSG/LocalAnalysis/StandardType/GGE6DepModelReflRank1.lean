module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.StandardType

namespace E6Dep

private lemma zmod_neg_one_mul : ∀ c : ZMod 3, (-1 : ZMod 3) * c = -c := by
  decide +kernel

private lemma zmod_add_self : ∀ c : ZMod 3, c + c = -c := by
  decide +kernel

private lemma zmod_refl_aux : ∀ a c d : ZMod 3, a - (2 * c) * d = a + c * d := by
  decide +kernel

private lemma zmod_key_aux : ∀ x a q : ZMod 3, -x + a * (-q) = x → x = a * q := by
  decide +kernel

private lemma zmod_ne_zero_cases : ∀ q : ZMod 3, q ≠ 0 → q = 1 ∨ q = 2 := by
  decide +kernel

private lemma zmod_solve_two : ∀ x y : ZMod 3, x = y * 2 → y = -x := by
  decide +kernel

private lemma zmod_mul_eq_self : ∀ a x : ZMod 3, a * x = x → x ≠ 0 → a = 1 := by
  decide +kernel

private lemma zmod_entry_diag : ∀ x : ZMod 3, 1 - x - x + 1 = x - 1 := by
  decide +kernel

private lemma zmod_entry_off : ∀ x : ZMod 3, -x - x = x := by
  decide +kernel

private lemma bil6_add_left (u₁ u₂ w : Vec6) :
    bil6 (u₁ + u₂) w = bil6 u₁ w + bil6 u₂ w := by
  simp only [bil6, add_dotProduct]

private lemma bil6_smul_left (a : ZMod 3) (u w : Vec6) :
    bil6 (a • u) w = a * bil6 u w := by
  simp only [bil6, smul_dotProduct, smul_eq_mul]

private lemma bil6_smul_right (b : ZMod 3) (u w : Vec6) :
    bil6 u (b • w) = b * bil6 u w := by
  simp only [bil6, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma neg_eq_neg_one_smul (w : Vec6) : -w = (-1 : ZMod 3) • w := by
  funext i
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [zmod_neg_one_mul]

private lemma bil6_neg_right (u w : Vec6) : bil6 u (-w) = -bil6 u w := by
  rw [neg_eq_neg_one_smul w, bil6_smul_right, zmod_neg_one_mul]

private lemma isometry_bil6 {T : Mat6} (hiso : T.transpose * gram6 * T = gram6) (u w : Vec6) :
    bil6 (T.mulVec u) (T.mulVec w) = bil6 u w := by
  simp only [bil6]
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    ← Matrix.mul_assoc, hiso, ← Matrix.dotProduct_mulVec]

private lemma gram6_mulVec_eq_zero : ∀ c : Vec6, gram6.mulVec c = 0 → c = 0 := by
  decide +kernel

private lemma reflNorm_mulVec (u v : Vec6) :
    (reflNorm v).mulVec u = u + bil6 u v • v := by
  simp only [reflNorm, reflMat, bil6, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  rw [smul_dotProduct, dotProduct_comm]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact zmod_refl_aux (u i) (u ⬝ᵥ Matrix.mulVec gram6 v) (v i)

private lemma reflMat_mulVec (α h u : Vec6) :
    (reflMat α h).mulVec u = u - (α ⬝ᵥ u) • h := by
  simp only [reflMat, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul]

private lemma reflMat_gram_mulVec (c u : Vec6) :
    (reflMat (gram6.mulVec c) c).mulVec u = u - bil6 u c • c := by
  rw [reflMat_mulVec, dotProduct_comm, bil6]

private lemma mat_sub_one_sq {T : Mat6} (h2 : T * T = 1) :
    (T - 1) * (T - 1) = T - 1 := by
  have h : (T - 1) * (T - 1) = T * T - T - T + 1 := by noncomm_ring
  rw [h, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
      | exact zmod_entry_diag _
      | exact zmod_entry_off _

private lemma exists_vecMulVec_of_idem (N : Mat6) (hNN : N * N = N)
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

theorem isRefl6_cases {T : Mat6} (h5 : ∀ v : Vec6, (T.mulVec v) 5 = v 5)
    (hiso : T.transpose * gram6 * T = gram6) (h2 : T * T = 1)
    (hfix : Fintype.card {v : Vec6 // T.mulVec v = v} * 3 = 3 ^ 6) :
    ∃ c : Vec6, c 5 = 0 ∧
      ((norm6 c = 1 ∧ T = reflNorm c) ∨ (norm6 c = 2 ∧ T = reflMat (gram6.mulVec c) c)) := by
  classical
  set N : Mat6 := T - 1 with hN
  have hT : T = N + 1 := by rw [hN, sub_add_cancel]
  have hNN : N * N = N := by rw [hN]; exact mat_sub_one_sq h2
  have hker : Fintype.card {v : Vec6 // N.mulVec v = 0} = 243 := by
    have hc : Fintype.card {v : Vec6 // N.mulVec v = 0}
        = Fintype.card {v : Vec6 // T.mulVec v = v} := by
      refine Fintype.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      show N.mulVec v = 0 ↔ T.mulVec v = v
      rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    rw [hc]
    omega
  obtain ⟨c, l, hc0, hNc, hNl⟩ := exists_vecMulVec_of_idem N hNN hker
  have hNm : ∀ u : Vec6, N.mulVec u = (l ⬝ᵥ u) • c := by
    intro u
    rw [hNl, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  have hTm : ∀ u : Vec6, T.mulVec u = u + (l ⬝ᵥ u) • c := by
    intro u
    rw [hT, Matrix.add_mulVec, Matrix.one_mulVec, hNm u, add_comm]
  have hlc : l ⬝ᵥ c = 1 := by
    have h : (l ⬝ᵥ c) • c = c := (hNm c).symm.trans hNc
    obtain ⟨i, hi⟩ : ∃ i : Fin 6, c i ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hc0 (funext fun i => h' i)
    have hi' := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at hi'
    exact zmod_mul_eq_self (l ⬝ᵥ c) (c i) hi' hi
  have hTc : T.mulVec c = -c := by
    rw [hTm c, hlc, one_smul]
    ext i
    simpa only [Pi.add_apply, Pi.neg_apply] using zmod_add_self (c i)
  have hkey : ∀ u : Vec6, bil6 u c = (l ⬝ᵥ u) * norm6 c := by
    intro u
    have h := isometry_bil6 hiso u c
    rw [hTm u, hTc, bil6_add_left, bil6_smul_left, bil6_neg_right, bil6_neg_right] at h
    exact zmod_key_aux (bil6 u c) (l ⬝ᵥ u) (bil6 c c) h
  have hnc_ne : norm6 c ≠ 0 := by
    intro h0
    have hgm : gram6.mulVec c = 0 := by
      funext i
      have hh := hkey (Pi.single i 1)
      rw [h0, mul_zero] at hh
      simpa only [bil6, single_one_dotProduct, Pi.zero_apply] using hh
    exact hc0 (gram6_mulVec_eq_zero c hgm)
  have hc5 : c 5 = 0 := by
    have h := congrFun hNc 5
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec] at h
    simp only [Pi.sub_apply] at h
    rw [h5 c] at h
    simp only [sub_self] at h
    exact h.symm
  refine ⟨c, hc5, ?_⟩
  rcases zmod_ne_zero_cases (norm6 c) hnc_ne with hnc | hnc
  · left
    refine ⟨hnc, ?_⟩
    rw [Matrix.ext_iff_mulVec]
    intro u
    rw [hTm u, reflNorm_mulVec]
    have h := hkey u
    rw [hnc, mul_one] at h
    rw [h]
  · right
    refine ⟨hnc, ?_⟩
    rw [Matrix.ext_iff_mulVec]
    intro u
    rw [hTm u, reflMat_gram_mulVec, sub_eq_add_neg, ← neg_smul]
    have h := hkey u
    rw [hnc] at h
    have hlu : l ⬝ᵥ u = -bil6 u c := zmod_solve_two (bil6 u c) (l ⬝ᵥ u) h
    rw [hlu]

end E6Dep

end CFSG.StandardType

end

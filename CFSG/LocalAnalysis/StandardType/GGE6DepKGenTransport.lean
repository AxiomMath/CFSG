module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKGlueDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeDefs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.StandardType

namespace E6Dep

open Matrix

private lemma zmod_refl_aux : ∀ a c d : ZMod 3, a - (2 * c) * d = a + c * d := by
  decide +kernel

private lemma zmod_sq_eq_one : ∀ x : ZMod 3, x * x = 1 → x = 1 ∨ x = -1 := by
  decide +kernel

private lemma zmod_three_self : ∀ x : ZMod 3, x + (x + x) = 0 := by
  decide +kernel

private lemma zmod_isometry_aux : ∀ z x y : ZMod 3, (z + y * x) + (x * y + x * y) = z := by
  decide +kernel

private lemma zmod_two_mul : ∀ x : ZMod 3, (2 : ZMod 3) * x = x + x := by
  decide +kernel

private lemma zmod_neg_eq_add : ∀ x : ZMod 3, -x = x + x := by
  decide +kernel

private lemma zmod_neg_one_mul : ∀ x : ZMod 3, (-1 : ZMod 3) * x = -x := by
  decide +kernel

private lemma two_smul_vec (v : Vec6) : (2 : ZMod 3) • v = v + v := by
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  exact zmod_two_mul (v i)

private lemma neg_eq_add_self (v : Vec6) : -v = v + v := by
  funext i
  simp only [Pi.neg_apply, Pi.add_apply]
  exact zmod_neg_eq_add (v i)

private lemma neg_one_smul_vec (v : Vec6) : (-1 : ZMod 3) • v = -v := by
  funext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact zmod_neg_one_mul (v i)

private lemma gram6_transpose : gram6.transpose = gram6 := by decide +kernel

private lemma reflNorm_mulVec (u v : Vec6) :
    (reflNorm v).mulVec u = u + bil6 u v • v := by
  simp only [reflNorm, reflMat, bil6, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  rw [smul_dotProduct, dotProduct_comm]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact zmod_refl_aux (u i) (u ⬝ᵥ Matrix.mulVec gram6 v) (v i)

private lemma bil6_add_left (u₁ u₂ w : Vec6) :
    bil6 (u₁ + u₂) w = bil6 u₁ w + bil6 u₂ w := by
  simp only [bil6, add_dotProduct]

private lemma bil6_smul_left (a : ZMod 3) (u w : Vec6) :
    bil6 (a • u) w = a * bil6 u w := by
  simp only [bil6, smul_dotProduct, smul_eq_mul]

private lemma bil6_smul_right (b : ZMod 3) (u w : Vec6) :
    bil6 u (b • w) = b * bil6 u w := by
  simp only [bil6, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma bil6_comm (u v : Vec6) : bil6 u v = bil6 v u := by
  have h : dotProduct u (Matrix.mulVec gram6 v) = dotProduct v (Matrix.mulVec gram6 u) := by
    have ht := Matrix.dotProduct_transpose_mulVec (A := gram6) u v
    rw [gram6_transpose] at ht
    exact ht
  simpa only [bil6] using h

private lemma bil6_add_right (u w₁ w₂ : Vec6) :
    bil6 u (w₁ + w₂) = bil6 u w₁ + bil6 u w₂ := by
  calc bil6 u (w₁ + w₂) = bil6 (w₁ + w₂) u := bil6_comm u (w₁ + w₂)
    _ = bil6 w₁ u + bil6 w₂ u := bil6_add_left w₁ w₂ u
    _ = bil6 u w₁ + bil6 u w₂ := by rw [bil6_comm w₁ u, bil6_comm w₂ u]

private lemma reflNorm_mulVec_inv {a : Vec6} (ha : norm6 a = 1) (x : Vec6) :
    (reflNorm a).mulVec ((reflNorm a).mulVec x) = x := by
  have ha' : bil6 a a = 1 := ha
  simp only [reflNorm_mulVec]
  rw [bil6_add_left, bil6_smul_left, ha', mul_one, add_assoc, ← add_smul,
    zmod_three_self (bil6 x a), zero_smul, add_zero]

private lemma isometry_bil6_reflNorm {a : Vec6} (ha : norm6 a = 1) (u w : Vec6) :
    bil6 ((reflNorm a).mulVec u) ((reflNorm a).mulVec w) = bil6 u w := by
  have ha' : bil6 a a = 1 := ha
  simp only [reflNorm_mulVec]
  rw [bil6_add_left, bil6_add_right, bil6_add_right, bil6_smul_left, bil6_smul_left,
    bil6_smul_right, bil6_smul_right, bil6_comm a w]
  simp only [ha', mul_one]
  exact zmod_isometry_aux (bil6 u w) (bil6 u a) (bil6 w a)

private lemma reflNorm_conj {a v : Vec6} (ha : norm6 a = 1) :
    reflNorm a * reflNorm v * reflNorm a = reflNorm ((reflNorm a).mulVec v) := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  simp only [← Matrix.mulVec_mulVec]
  set y : Vec6 := (reflNorm a).mulVec x with hy
  have hx : (reflNorm a).mulVec y = x := by rw [hy, reflNorm_mulVec_inv ha x]
  have hyv : v = (reflNorm a).mulVec ((reflNorm a).mulVec v) := (reflNorm_mulVec_inv ha v).symm
  have hiso : bil6 y v = bil6 x ((reflNorm a).mulVec v) := by
    rw [hy]
    conv_lhs => rw [hyv]
    exact isometry_bil6_reflNorm ha x ((reflNorm a).mulVec v)
  have hinner : (reflNorm v).mulVec y = y + bil6 y v • v := reflNorm_mulVec y v
  rw [hinner, Matrix.mulVec_add, Matrix.mulVec_smul, hx, hiso]
  exact (reflNorm_mulVec x ((reflNorm a).mulVec v)).symm

private lemma reflNorm_eq_centre {a b : Vec6} (ha : norm6 a = 1) (hb : norm6 b = 1)
    (h : reflNorm a = reflNorm b) : a = b ∨ a = -b := by
  have ha' : bil6 a a = 1 := ha
  have hb' : bil6 b b = 1 := hb
  have h1 : (reflNorm a).mulVec a = (reflNorm b).mulVec a := by rw [h]
  simp only [reflNorm_mulVec, ha', one_smul] at h1
  have hlam : a = bil6 a b • b := add_left_cancel h1
  have hsq : bil6 a b * bil6 a b = 1 := by
    calc bil6 a b * bil6 a b = bil6 ((bil6 a b) • b) ((bil6 a b) • b) := by
          rw [bil6_smul_left, bil6_smul_right, hb', mul_one]
      _ = bil6 a a := by conv_rhs => rw [hlam]
      _ = 1 := ha'
  rcases zmod_sq_eq_one (bil6 a b) hsq with h2 | h2
  · left; rw [hlam, h2, one_smul]
  · right; rw [hlam, h2]; exact neg_one_smul_vec b

private lemma bil6_mulVec_of_gram {M : Mat6} {c : ZMod 3}
    (hG : Mᵀ * gram6 * M = gbeta c) (u w : Vec6) :
    bil6 (M.mulVec u) (M.mulVec w) = bilK c u w := by
  simp only [bil6, bilK]
  rw [← hG]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

theorem kgen_of_conjGenerates {M : Mat6} {c : ZMod 3} {h : Vec6}
    (hMy : M.mulVec (kY c) = 0) (hMker : ∀ v, M.mulVec v = 0 → ∃ j : ZMod 3, v = j • kY c)
    (hM5 : ∀ v, M.mulVec v 5 = 0)
    (hG : Mᵀ * gram6 * M = gbeta c)
    {Λ : Type} [Fintype Λ] (k : Λ → Mat6)
    (hgen : ConjGenerates refl36 (Finset.univ.image k))
    (hcov : ∀ l, ∃ u, (u ∈ cS ∨ u = h) ∧ k l = reflNorm (M.mulVec u)) : KGen c h := by
  intro X hXsub hXrefl hXy hcSX hhX
  apply Finset.Subset.antisymm hXsub
  intro v hv
  classical
  have hnorm1 : ∀ u ∈ X, normK c u = 1 := by
    intro u hu
    have := hXsub hu
    simpa only [kNorm1, Finset.mem_filter, Finset.mem_univ, true_and] using this
  have hbil : ∀ u w : Vec6, bil6 (M.mulVec u) (M.mulVec w) = bilK c u w :=
    bil6_mulVec_of_gram hG
  have hnormM : ∀ u : Vec6, normK c u = 1 → norm6 (M.mulVec u) = 1 := by
    intro u hu
    change bil6 (M.mulVec u) (M.mulVec u) = 1
    rw [hbil u u]
    simpa only [normK] using hu
  have hv1 : normK c v = 1 := by
    simpa only [kNorm1, Finset.mem_filter, Finset.mem_univ, true_and] using hv
  set T' : Finset Mat6 := X.image (fun u => reflNorm (M.mulVec u)) with hT'def
  have hT'sub : T' ⊆ refl36 := by
    intro t ht
    rw [hT'def, Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    rw [refl36, Finset.mem_image]
    refine ⟨M.mulVec u, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hM5 u, hnormM u (hnorm1 u hu)⟩
  have hT'conj : ConjClosed T' := by
    intro a ha b hb
    rw [hT'def, Finset.mem_image] at ha hb
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨w, hw, rfl⟩ := hb
    have hnu : norm6 (M.mulVec u) = 1 := hnormM u (hnorm1 u hu)
    refine Finset.mem_image.mpr ⟨w + bilK c w u • u, hXrefl u hu w hw, ?_⟩
    rw [reflNorm_conj hnu]
    congr 1
    rw [reflNorm_mulVec, hbil w u, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hT'k : (Finset.univ.image k) ⊆ T' := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨l, _, rfl⟩ := ht
    obtain ⟨u, hu, hku⟩ := hcov l
    rw [hT'def, Finset.mem_image]
    refine ⟨u, ?_, hku.symm⟩
    rcases hu with hu | rfl
    · exact hcSX hu
    · exact hhX
  have hT'eq : T' = refl36 := hgen T' hT'sub hT'conj hT'k
  have hneg : ∀ w ∈ X, -w ∈ X := by
    intro w hw
    have hcl := hXrefl w hw w hw
    have hbw : bilK c w w = 1 := by simpa only [normK] using hnorm1 w hw
    rw [hbw, one_smul] at hcl
    rw [neg_eq_add_self]
    exact hcl
  have hj3 : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide +kernel
  have hXplus : ∀ j : ZMod 3, ∀ w ∈ X, w + j • kY c ∈ X := by
    intro j w hw
    rcases hj3 j with rfl | rfl | rfl
    · simpa using hw
    · simpa using hXy w hw
    · have h2 : (w + kY c) + kY c ∈ X := hXy (w + kY c) (hXy w hw)
      rwa [add_assoc, ← two_smul_vec] at h2
  have hMv : reflNorm (M.mulVec v) ∈ refl36 := by
    rw [refl36, Finset.mem_image]
    refine ⟨M.mulVec v, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hM5 v, hnormM v hv1⟩
  have hMvT : reflNorm (M.mulVec v) ∈ T' := by rw [hT'eq]; exact hMv
  rw [hT'def, Finset.mem_image] at hMvT
  obtain ⟨u, hu, hu_eq⟩ := hMvT
  have hnu : norm6 (M.mulVec u) = 1 := hnormM u (hnorm1 u hu)
  have hnv : norm6 (M.mulVec v) = 1 := hnormM v hv1
  have hcenter := reflNorm_eq_centre hnu hnv hu_eq
  have hex : ∃ u' ∈ X, M.mulVec u' = M.mulVec v := by
    rcases hcenter with h | h
    · exact ⟨u, hu, h⟩
    · refine ⟨-u, hneg u hu, ?_⟩
      rw [Matrix.mulVec_neg, h, neg_neg]
  obtain ⟨u', hu', hu'eq⟩ := hex
  have hzero : M.mulVec (v - u') = 0 := by
    rw [Matrix.mulVec_sub, hu'eq, sub_self]
  obtain ⟨j, hj⟩ := hMker (v - u') hzero
  have hv_eq : v = u' + j • kY c := by
    rw [← hj, add_comm, sub_add_cancel]
  rw [hv_eq]
  exact hXplus j u' hu'

theorem reflFix_xs_centre : ∀ g ∈ reflFix xs, ∃ u ∈ cS, g = reflNorm u := by
  have hsub : ∀ g ∈ reflFix xs, g ∈ cS.image reflNorm := by
    have hempty : (reflFix xs).filter (fun g => ¬ (g ∈ cS.image reflNorm)) = ∅ := by
      decide +kernel
    intro g hg
    by_contra hg'
    have hmem : g ∈ (reflFix xs).filter (fun g => ¬ (g ∈ cS.image reflNorm)) :=
      Finset.mem_filter.mpr ⟨hg, hg'⟩
    rw [hempty] at hmem
    simpa using hmem
  intro g hg
  obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp (hsub g hg)
  exact ⟨u, hu, hu_eq.symm⟩

end E6Dep

end CFSG.StandardType

end

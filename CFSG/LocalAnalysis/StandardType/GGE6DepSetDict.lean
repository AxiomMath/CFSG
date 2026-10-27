module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepStdFrame
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelForm
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelReflDict
public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootDefs

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private lemma zmod_refl_aux : ∀ a c d : ZMod 3, a - (2 * c) * d = a + c * d := by
  decide +kernel

private lemma reflNorm_mulVec (u v : Vec6) :
    (reflNorm v).mulVec u = u + bil6 u v • v := by
  simp only [reflNorm, reflMat, bil6, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  rw [smul_dotProduct, dotProduct_comm]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact zmod_refl_aux (u i) (u ⬝ᵥ Matrix.mulVec gram6 v) (v i)

private lemma zmod_two_mul : ∀ c : ZMod 3, (2 : ZMod 3) * c = -c := by
  decide +kernel

private lemma two_smul_neg (a : Vec6) : (2 : ZMod 3) • a = -a := by
  funext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact zmod_two_mul (a i)

private lemma zmod_cases (k : ZMod 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  revert k
  decide +kernel

private theorem gensL_isometry_gram : ∀ i : Fin 6,
    (gensL i).transpose * gram6 * gensL i = gram6 := by
  decide +kernel

private lemma actsAs_ext {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} {φ ψ : MulAut ↥Bs}
    {g : Mat6} (h₁ : ActsAs ι φ g) (h₂ : ActsAs ι ψ g) : φ = ψ := by
  refine MulEquiv.ext fun b => ?_
  apply Additive.ofMul.injective
  apply ι.injective
  rw [h₁ b, h₂ b]

theorem bil6_xx (v : Vec6) : bil6 v xx = v 5 := by
  have h : gram6.mulVec xx = xx := by decide +kernel
  have h2 : v ⬝ᵥ xx = v 5 := by
    simp [xx, dotProduct, Fin.sum_univ_six]
  simp only [bil6]
  rw [h, h2]

theorem bil6_isometry {m : Mat6} (hm : m.transpose * gram6 * m = gram6) (u v : Vec6) :
    bil6 (m.mulVec u) (m.mulVec v) = bil6 u v := by
  simp only [bil6]
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    ← Matrix.mul_assoc, hm, ← Matrix.dotProduct_mulVec]

theorem closureL_isometry {m : Mat6} (hm : m ∈ closureL) :
    m.transpose * gram6 * m = gram6 := by
  induction hm using Submonoid.closure_induction with
  | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact gensL_isometry_gram i
  | one => rw [Matrix.transpose_one, one_mul, mul_one]
  | mul g h _ _ ihg ihh =>
      calc
        (g * h).transpose * gram6 * (g * h)
            = h.transpose * (g.transpose * gram6 * g) * h := by
              rw [Matrix.transpose_mul]
              simp only [Matrix.mul_assoc]
        _ = h.transpose * gram6 * h := by rw [ihg]
        _ = gram6 := ihh

theorem evalWord_gensAll_isometry {t w : ZMod 3} (htw : t * w = 2) (word : List (Fin 7)) :
    (evalWord (gensAll 0 t 0 w) word).transpose * gram6 * evalWord (gensAll 0 t 0 w) word =
      gram6 := by
  induction word with
  | nil => simp [evalWord]
  | cons i l ih =>
      calc
        (evalWord (gensAll 0 t 0 w) (i :: l)).transpose * gram6 *
            evalWord (gensAll 0 t 0 w) (i :: l)
            = (evalWord (gensAll 0 t 0 w) l).transpose *
                ((gensAll 0 t 0 w i).transpose * gram6 * gensAll 0 t 0 w i) *
                evalWord (gensAll 0 t 0 w) l := by
              rw [show evalWord (gensAll 0 t 0 w) (i :: l)
                    = gensAll 0 t 0 w i * evalWord (gensAll 0 t 0 w) l from rfl,
                  Matrix.transpose_mul]
              simp only [Matrix.mul_assoc]
        _ = (evalWord (gensAll 0 t 0 w) l).transpose * gram6 *
                evalWord (gensAll 0 t 0 w) l := by
              rw [gensAll_isometry t w htw i]
        _ = gram6 := ih

theorem corootOrth_of_words {Bs L : Subgroup G} {x : G} {hxBs : x ∈ Bs}
    {ι : Additive ↥Bs ≃+ Vec6} (hι : GGE6DepCoord Bs L x hxBs ι) {a b : Vec6}
    (ha : norm6 a = 1) (hb : norm6 b = 1) (hab : a ≠ b) (hab' : a ≠ -b)
    (hwa : ∃ word : List (Fin 6), evalWord gensL word = reflNorm a)
    (hwb : ∃ word : List (Fin 6), evalWord gensL word = reflNorm b)
    (hcomm : reflNorm a * reflNorm b = reflNorm b * reflNorm a) :
    GGCorootOrth 3 (ggAutomizer L Bs) (Additive.toMul (ι.symm a)) (Additive.toMul (ι.symm b)) := by
  obtain ⟨wa, hwa'⟩ := hwa
  obtain ⟨wb, hwb'⟩ := hwb
  have hra : reflNorm a ∈ closureL := by
    rw [← hwa']; exact evalWord_gensL_mem wa
  have hrb : reflNorm b ∈ closureL := by
    rw [← hwb']; exact evalWord_gensL_mem wb
  obtain ⟨φ, hφA, hφ⟩ := hι.2.2.2 (reflNorm a) hra
  obtain ⟨ψ, hψA, hψ⟩ := hι.2.2.2 (reflNorm b) hrb
  obtain ⟨hφrefl, hφcen⟩ := actsAs_reflNorm ha hφ
  obtain ⟨hψrefl, hψcen⟩ := actsAs_reflNorm hb hψ
  have hcommφψ : φ * ψ = ψ * φ := by
    apply actsAs_ext (g := reflNorm a * reflNorm b)
    · exact hφ.mul hψ
    · rw [hcomm]; exact hψ.mul hφ
  refine ⟨?_, φ, hφA, ψ, hψA, hφrefl, hφcen, hψrefl, hψcen, hcommφψ⟩
  intro hsub
  have hBmem : Additive.toMul (ι.symm b) ∈
      Subgroup.zpowers (Additive.toMul (ι.symm a)) := by
    rw [hsub]
    exact Subgroup.mem_zpowers (Additive.toMul (ι.symm b))
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hBmem
  have hn' : n • a = b := by
    have h := congrArg (fun y : ↥Bs => ι (Additive.ofMul y)) hn
    rw [ofMul_zpow, map_zsmul, ofMul_toMul, AddEquiv.apply_symm_apply,
      ofMul_toMul, AddEquiv.apply_symm_apply] at h
    exact h
  have hna : (n : ZMod 3) • a = b := by
    rw [← hn']
    funext i
    change (n : ZMod 3) • a i = n • a i
    rw [zsmul_eq_mul, smul_eq_mul]
  rcases zmod_cases (n : ZMod 3) with h0 | h1 | h2
  · have hb0 : b = 0 := by rw [← hna, h0, zero_smul]
    rw [hb0] at hb
    have h00 : norm6 (0 : Vec6) = 0 := by decide +kernel
    rw [h00] at hb
    exact one_ne_zero hb.symm
  · have hba : b = a := by rw [← hna, h1, one_smul]
    exact hab hba.symm
  · have hba : b = -a := by rw [← hna, h2, two_smul_neg]
    exact hab' (by rw [hba]; simp)

theorem mem_fixedByCentres_of_perp {Bs L : Subgroup G} {x : G} {hxBs : x ∈ Bs}
    {ι : Additive ↥Bs ≃+ Vec6} (hι : GGE6DepCoord Bs L x hxBs ι) {S : Set ↥Bs} {u : ↥Bs}
    (hS : ∀ c ∈ S, norm6 (ι (Additive.ofMul c)) = 1 ∧
      bil6 (ι (Additive.ofMul u)) (ι (Additive.ofMul c)) = 0) :
    u ∈ ggFixedByCentres 3 (ggAutomizer L Bs) S := by
  show ∀ φ ∈ ggAutomizer L Bs, GGIsReflection 3 φ →
    (∃ c ∈ S, GGReflCentre φ c) → φ u = u
  intro φ hφA hr hc
  obtain ⟨c, hcS, hcen⟩ := hc
  obtain ⟨hcn, hcb⟩ := hS c hcS
  obtain ⟨T, hTmem, hT⟩ := hι.2.2.1 φ hφA
  have hiso : T.transpose * gram6 * T = gram6 := closureL_isometry hTmem
  have hTeq : T = reflNorm (ι (Additive.ofMul c)) :=
    actsAs_eq_reflNorm hT hiso hcn hr hcen
  have hfix : ι (Additive.ofMul (φ u)) = ι (Additive.ofMul u) := by
    rw [hT u, hTeq, reflNorm_mulVec, hcb, zero_smul, add_zero]
  exact Additive.ofMul.injective (ι.injective hfix)

end E6Dep

end CFSG.StandardType

end

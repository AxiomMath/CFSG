module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4GenEich
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem ofMat_add {K : Type} [Add K] (X Y : Matrix (Fin 2) (Fin 2) K) :
    ofMat (X + Y) = ofMat X + ofMat Y := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [ofMat]

private theorem ofVec_add (v v' : OmI → S.K) :
    S.ofVec (v + v') = S.ofVec v * S.ofVec v' := by
  simp [ofVec, ofAdd_add]

private theorem addMonoidHom_eq_mul_of_commute_sl
    (g : Matrix (Fin 2) (Fin 2) S.K →+ Matrix (Fin 2) (Fin 2) S.K)
    (hg : ∀ (p : SL(2, S.K) × SL(2, S.K)) (X : Matrix (Fin 2) (Fin 2) S.K),
      g ((p.1 : Matrix (Fin 2) (Fin 2) S.K) * X * (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ) =
        (p.1 : Matrix (Fin 2) (Fin 2) S.K) * g X *
          (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ) :
    ∀ X : Matrix (Fin 2) (Fin 2) S.K, g X = X * g 1 := by
  have hleft : ∀ (b : SL(2, S.K)) (X : Matrix (Fin 2) (Fin 2) S.K),
      g ((b : Matrix (Fin 2) (Fin 2) S.K) * X) =
        (b : Matrix (Fin 2) (Fin 2) S.K) * g X := by
    intro b X
    simpa using hg (b, 1) X
  let P : AddSubgroup (Matrix (Fin 2) (Fin 2) S.K) :=
    { carrier := {A | ∀ Y, g (A * Y) = A * g Y}
      zero_mem' := by intro Y; simp
      add_mem' := by
        intro A B hA hB Y
        rw [add_mul, map_add, hA Y, hB Y, add_mul]
      neg_mem' := by
        intro A hA Y
        rw [neg_mul, map_neg, hA Y, neg_mul] }
  have hone : (1 : Matrix (Fin 2) (Fin 2) S.K) ∈ P := by intro Y; simp
  have hmul : ∀ {A B : Matrix (Fin 2) (Fin 2) S.K}, A ∈ P → B ∈ P → A * B ∈ P := by
    intro A B hA hB Y
    rw [mul_assoc, hA (B * Y), hB Y, mul_assoc]
  have hSL : ∀ b : SL(2, S.K), (b : Matrix (Fin 2) (Fin 2) S.K) ∈ P := by
    intro b Y
    exact hleft b Y
  have hoff : ∀ (i j : Fin 2), i ≠ j → ∀ c : S.K,
      Matrix.single i j c ∈ P := by
    intro i j hij c
    have hb := hSL (⟨Matrix.transvection i j c,
      Matrix.det_transvection_of_ne i j hij c⟩ : SL(2, S.K))
    have hsub := P.sub_mem hb hone
    have he : (↑(⟨Matrix.transvection i j c,
        Matrix.det_transvection_of_ne i j hij c⟩ : SL(2, S.K)) :
          Matrix (Fin 2) (Fin 2) S.K) - 1 = Matrix.single i j c := by
      simp [Matrix.transvection]
    rwa [he] at hsub
  have hsingle : ∀ (i j : Fin 2) (c : S.K), Matrix.single i j c ∈ P := by
    intro i j c
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hk⟩ : ∃ k : Fin 2, k ≠ i := by
        by_cases h0 : i = 0
        · exact ⟨1, by rw [h0]; decide⟩
        · exact ⟨0, fun h => h0 h.symm⟩
      have e : Matrix.single i i c =
          Matrix.single i k c * Matrix.single k i (1 : S.K) := by
        rw [Matrix.single_mul_single_same]; simp
      rw [e]
      exact hmul (hoff i k hk.symm c) (hoff k i hk 1)
    · exact hoff i j hij c
  have hX : ∀ X : Matrix (Fin 2) (Fin 2) S.K, X ∈ P := by
    intro X
    rw [Matrix.matrix_eq_sum_single X]
    exact P.sum_mem fun i _ => P.sum_mem fun j _ => hsingle i j (X i j)
  intro X
  simpa using hX X 1

theorem exists_smul_of_commute_jHom (f : W →* W)
    (hf : ∀ (p : SL(2, S.K) × SL(2, S.K)) (w : W), f (S.jHom p w) = S.jHom p (f w)) :
    ∃ c : S.K, ∀ w : W, f w = S.smul c w := by
  let g : Matrix (Fin 2) (Fin 2) S.K →+ Matrix (Fin 2) (Fin 2) S.K :=
    AddMonoidHom.mk' (fun X => toMat (S.vec (f (S.ofVec (ofMat X))))) (fun X Y => by
      simp only [ofMat_add, ofVec_add, map_mul, vec_mul, toMat_add])
  have hgdef : ∀ X : Matrix (Fin 2) (Fin 2) S.K,
      g X = toMat (S.vec (f (S.ofVec (ofMat X)))) := fun X => rfl
  have hg : ∀ (p : SL(2, S.K) × SL(2, S.K)) (X : Matrix (Fin 2) (Fin 2) S.K),
      g ((p.1 : Matrix (Fin 2) (Fin 2) S.K) * X *
          (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ) =
        (p.1 : Matrix (Fin 2) (Fin 2) S.K) * g X *
          (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ := by
    intro p X
    have hw : S.jHom p (S.ofVec (ofMat X)) =
        S.ofVec (ofMat ((p.1 : Matrix (Fin 2) (Fin 2) S.K) * X *
          (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ)) := by
      apply S.vec_injective
      simp only [S.vec_jHom, S.vec_ofVec, toMat_ofMat]
    have h := hf p (S.ofVec (ofMat X))
    rw [hw] at h
    have h2 := congrArg S.vec h
    rw [S.vec_jHom] at h2
    have h3 := congrArg toMat h2
    simpa only [hgdef, toMat_ofMat] using h3
  have hleft : ∀ (b : SL(2, S.K)) (X : Matrix (Fin 2) (Fin 2) S.K),
      g ((b : Matrix (Fin 2) (Fin 2) S.K) * X) =
        (b : Matrix (Fin 2) (Fin 2) S.K) * g X := by
    intro b X
    simpa only [hgdef, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one,
      Matrix.mul_one] using hg (b, 1) X
  have hright : ∀ (a : SL(2, S.K)) (X : Matrix (Fin 2) (Fin 2) S.K),
      g (X * (a : Matrix (Fin 2) (Fin 2) S.K)) =
        g X * (a : Matrix (Fin 2) (Fin 2) S.K) := by
    intro a X
    have := hg (1, Matrix.SpecialLinearGroup.transpose a) X
    simpa [Matrix.SpecialLinearGroup.coe_transpose] using this
  have hmain := addMonoidHom_eq_mul_of_commute_sl S g hg
  have hcomm : ∀ a : SL(2, S.K),
      g 1 * (a : Matrix (Fin 2) (Fin 2) S.K) =
        (a : Matrix (Fin 2) (Fin 2) S.K) * g 1 := by
    intro a
    have h1 := hright a 1
    have h2 := hmain (a : Matrix (Fin 2) (Fin 2) S.K)
    rw [one_mul, h2] at h1
    exact h1.symm
  have hcommSingle : ∀ i j : Fin 2, i ≠ j →
      Commute (Matrix.single i j 1) (g 1) := by
    intro i j hij
    have hb := hcomm (⟨Matrix.transvection i j 1,
      Matrix.det_transvection_of_ne i j hij 1⟩ : SL(2, S.K))
    rw [show (↑(⟨Matrix.transvection i j 1,
        Matrix.det_transvection_of_ne i j hij 1⟩ : SL(2, S.K)) :
          Matrix (Fin 2) (Fin 2) S.K) = 1 + Matrix.single i j 1 by
        simp [Matrix.transvection],
      mul_add, add_mul, mul_one, one_mul] at hb
    exact (add_left_cancel hb).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := g 1) hcommSingle
  have hcsmul : Matrix.scalar (Fin 2) c = c • (1 : Matrix (Fin 2) (Fin 2) S.K) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hgsmul : ∀ X : Matrix (Fin 2) (Fin 2) S.K, g X = c • X := by
    intro X
    rw [hmain X, ← hc, hcsmul, Matrix.mul_smul, Matrix.mul_one]
  refine ⟨c, fun w => ?_⟩
  apply S.vec_injective
  rw [S.vec_smul]
  have hgl : g (toMat (S.vec w)) = toMat (S.vec (f w)) := by
    rw [hgdef (toMat (S.vec w)), ofMat_toMat, ofVec_vec]
  have hvec : toMat (S.vec (f w)) = c • toMat (S.vec w) := by
    have h := hgsmul (toMat (S.vec w))
    rwa [hgl] at h
  have h2 := congrArg ofMat hvec
  rw [ofMat_toMat, ofMat_smul, ofMat_toMat] at h2
  exact h2

theorem exists_smul_of_commute_omega0 (f : W →* W)
    (hf : ∀ h ∈ S.omega0, ∀ w : W, f (h w) = h (f w)) :
    ∃ c : S.K, ∀ w : W, f w = S.smul c w :=
  S.exists_smul_of_commute_jHom f fun p w => hf _ ⟨p, rfl⟩ w

theorem exists_jHom_eq_smul_of_Q_eq_zero {x : W} (hx : S.Q x = 0) {t : S.K} (ht : t ≠ 0) :
    ∃ p : SL(2, S.K) × SL(2, S.K), S.jHom p x = S.smul t x := by
  by_cases hX : toMat (S.vec x) = 0
  · have hx1 : x = 1 := by
      apply S.vec_injective
      rw [S.vec_one]
      have h := congrArg ofMat hX
      rw [ofMat_toMat] at h
      have h0 : ofMat (0 : Matrix (Fin 2) (Fin 2) S.K) = 0 := by
        funext i
        rcases i with i | i <;> fin_cases i <;> simp [ofMat]
      rwa [h0] at h
    refine ⟨1, ?_⟩
    rw [hx1]
    simp [S.smul_one_elem]
  · have hd : (toMat (S.vec x)).det = 0 := by rw [← S.Q_eq_det, hx]
    obtain ⟨p, q, hp, hq, hXp⟩ :=
      CFSG.ClassicalInvolution.RouteD.Exotic.exists_vecMulVec_of_det_eq_zero hX hd
    have htp : t • p ≠ 0 := by
      intro h
      exact hp ((smul_eq_zero.mp h).resolve_left ht)
    obtain ⟨b, hb⟩ :=
      CFSG.ClassicalInvolution.RouteD.Exotic.exists_sl2_mulVec_eq_of_ne_zero p (t • p) hp htp
    refine ⟨(b, 1), ?_⟩
    apply S.vec_injective
    rw [S.vec_jHom, S.vec_smul]
    have hcoe1 : ((1 : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K)ᵀ = 1 := by simp
    rw [hcoe1, Matrix.mul_one, hXp, Matrix.mul_vecMulVec, hb, Matrix.smul_vecMulVec,
      ofMat_smul, ← hXp, ofMat_toMat]

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

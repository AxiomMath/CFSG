module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeam
public import CFSG.LocalAnalysis.StandardType.PhanEResPsiAct
public import CFSG.LocalAnalysis.StandardType.PhanELocalGate

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix Module CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Universal.SpecialLinear

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} {d : List ℕ}

private theorem plo_cutTypes_next (hd : IsCut (m + 1) d) {k : Fin m} (hk : k ∈ cutTypes m d) :
    ∃ b, b + 1 < d.length ∧ d.getD b 0 ≤ k.val ∧ k.val + 1 < d.getD (b + 1) 0 := by
  let c := q2cFPt_nextCut hd k.castSucc
  have hc1 : 1 ≤ c := q2cFPt_nextCut_pos hd k.castSucc
  have hc : c < d.length := q2cFPt_nextCut_lt_length hd k.castSucc
  have hspec : k.val < d.getD c 0 := by simpa using q2cFPt_nextCut_spec hd k.castSucc
  have hmin : d.getD (c - 1) 0 ≤ k.val := by
    simpa using q2cFPt_nextCut_min hd k.castSucc (by omega)
  have hne : d.getD c 0 ≠ k.val + 1 := hk c hc
  exact ⟨c - 1, by rw [Nat.sub_add_cancel hc1]; exact hc, hmin, by
    rw [Nat.sub_add_cancel hc1]; omega⟩

private theorem plo_block_unique (hd : IsCut (m + 1) d) {b b' i : ℕ}
    (hb : b + 1 < d.length) (hb' : b' + 1 < d.length)
    (h1 : d.getD b 0 ≤ i) (h2 : i < d.getD (b + 1) 0)
    (h1' : d.getD b' 0 ≤ i) (h2' : i < d.getD (b' + 1) 0) : b = b' := by
  rcases lt_trichotomy b b' with h | h | h
  · have := q2cFPt_getD_le hd (show b + 1 ≤ b' by omega) (by omega)
    omega
  · exact h
  · have := q2cFPt_getD_le hd (show b' + 1 ≤ b by omega) (by omega)
    omega

private theorem plo_blockDiag_single (hd : IsCut (m + 1) d) {b : ℕ} (hb : b + 1 < d.length)
    {a bpos : Fin (m + 1)} (ha : d.getD b 0 ≤ a.val) (ha' : a.val < d.getD (b + 1) 0)
    (hb1 : d.getD b 0 ≤ bpos.val) (hb2 : bpos.val < d.getD (b + 1) 0) (c : K) :
    BlockDiag d (1 + Matrix.single a bpos c : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  intro b' hb' i j hij hnj
  have hne : i ≠ j := fun h => hnj (h ▸ hij)
  constructor
  · have hna : ¬ (a = i ∧ bpos = j) := by
      rintro ⟨rfl, rfl⟩
      have hblk : b' = b := plo_block_unique hd hb' hb hij.1 hij.2 ha ha'
      exact hnj ⟨by rw [hblk]; omega, by rw [hblk]; omega⟩
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply, if_neg hna, add_zero]
  · have hne' : j ≠ i := hne.symm
    have hna' : ¬ (a = j ∧ bpos = i) := by
      rintro ⟨rfl, rfl⟩
      have hblk : b' = b := plo_block_unique hd hb' hb hij.1 hij.2 hb1 hb2
      exact hnj ⟨by rw [hblk]; omega, by rw [hblk]; omega⟩
    rw [Matrix.add_apply, Matrix.one_apply_ne hne', Matrix.single_apply, if_neg hna', add_zero]

private theorem plo_blockDiag_tv (hd : IsCut (m + 1) d) {k : Fin m} (hk : k ∈ cutTypes m d)
    (c : K) :
    BlockDiag d ((tv K k.castSucc k.succ c : SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  obtain ⟨b, hb, h1, h2⟩ := plo_cutTypes_next hd hk
  have hpq : k.castSucc ≠ k.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  rw [tv_of_ne hpq, SpecialLinearGroup.transvection_coe]
  exact plo_blockDiag_single hd hb h1
    (by simp only [Fin.val_castSucc]; omega)
    (by simp only [Fin.val_succ]; omega)
    (by simp only [Fin.val_succ]; omega) c

private theorem plo_blockDiag_tv_inv (hd : IsCut (m + 1) d) {k : Fin m} (hk : k ∈ cutTypes m d)
    (c : K) :
    BlockDiag d ((tv K k.succ k.castSucc c : SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  obtain ⟨b, hb, h1, h2⟩ := plo_cutTypes_next hd hk
  have hpq : k.succ ≠ k.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  rw [tv_of_ne hpq, SpecialLinearGroup.transvection_coe]
  exact plo_blockDiag_single hd hb
    (by simp only [Fin.val_succ]; omega)
    (by simp only [Fin.val_succ]; omega)
    h1
    (by simp only [Fin.val_castSucc]; omega) c

theorem blockSL_blockDiag (hd : IsCut (m + 1) d) {A : SpecialLinearGroup (Fin (m + 1)) K}
    (hA : A ∈ blockSL K m d) : BlockDiag d (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  refine Subgroup.closure_induction
    (p := fun (A : SpecialLinearGroup (Fin (m + 1)) K) _ =>
      BlockDiag d (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) ?_ ?_ ?_ ?_ hA
  · rintro A ⟨k, hk, c, rfl | rfl⟩
    · exact plo_blockDiag_tv hd hk c
    · exact plo_blockDiag_tv_inv hd hk c
  · exact BlockDiag.one
  · intro x y hx hy hx' hy'
    exact BlockDiag.mul hx' hy'
  · intro x hx hx'
    have h1 := BlockDiag.inv (g := SpecialLinearGroup.toGL x) hx'
    have hval : (((SpecialLinearGroup.toGL x)⁻¹ : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K)⁻¹ :=
      by simpa using Units.val_inv_eq_inv_val (SpecialLinearGroup.toGL x)
    rw [hval] at h1
    have hxinv : (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K)⁻¹ =
        ((x⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
      rw [Matrix.inv_def, x.2, Ring.inverse_one, one_smul]
      rfl
    rwa [hxinv] at h1

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end

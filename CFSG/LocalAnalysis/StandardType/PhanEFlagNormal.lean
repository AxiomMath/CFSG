module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagNormBlkColl
public import CFSG.LocalAnalysis.StandardType.PhanEFlagNormBlkPol

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {d : List ℕ}

theorem exists_normalForm_flagPsi (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d)
    (pol : List Bool) {M : GL (Fin n) K} (hM : StabV n d M)
    (hinv : ∀ x ∈ refSet K n d,
      flagAct M (flagPsi hK hd pol (flagAct M (flagPsi hK hd pol x))) = x) :
    ∃ e : GL (Fin n) K, StabV n d e ∧ ∀ x ∈ refSet K n d,
      flagAct e (flagAct M (flagPsi hK hd pol (flagAct e⁻¹ x))) = flagPsi hK hd pol x := by
  classical
  let E : ∀ b, (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K) := fun b =>
    if hb : b + 1 < d.length then
      if hp : pol.getD b false = true then
        Classical.choose (exists_blockEquiv_pol hK hd pol hb hp hM hinv)
      else
        Classical.choose (exists_blockEquiv_coll hK hd pol hb
          (Bool.eq_false_iff.mpr hp) hM hinv)
    else LinearEquiv.refl K _
  have hgood : ∀ b (hb : b + 1 < d.length) (e : GL (Fin n) K), StabV n d e →
      (∀ w, glLin e (blkIn n d b w) = blkIn n d b (E b w)) →
      (if pol.getD b false then
        ∀ X : Submodule K (Fin n → K), Vsub n (d.getD b 0) ≤ X →
          X ≤ Vsub n (d.getD (b + 1) 0) →
          ((perpB K f n (d.getD b 0) (d.getD (b + 1) 0)
              (X.map (glLin e⁻¹).toLinearMap) ⊓ Vsub n (d.getD (b + 1) 0)).map
            (glLin M).toLinearMap).map (glLin e).toLinearMap =
            perpB K f n (d.getD b 0) (d.getD (b + 1) 0) X ⊓ Vsub n (d.getD (b + 1) 0)
      else
        ∀ X : Submodule K (Fin n → K), Vsub n (d.getD b 0) ≤ X →
          X ≤ Vsub n (d.getD (b + 1) 0) →
          ((sgS K f n (X.map (glLin e⁻¹).toLinearMap)).map (glLin M).toLinearMap).map
            (glLin e).toLinearMap = sgS K f n X) := by
    intro b hb e he hblock
    by_cases hp : pol.getD b false = true
    · have hEb : E b = Classical.choose (exists_blockEquiv_pol hK hd pol hb hp hM hinv) := by
        dsimp only [E]
        rw [dif_pos hb, dif_pos hp]
      rw [hEb] at hblock
      rw [if_pos hp]
      exact Classical.choose_spec (exists_blockEquiv_pol hK hd pol hb hp hM hinv) e he hblock
    · have hEb : E b = Classical.choose (exists_blockEquiv_coll hK hd pol hb
          (Bool.eq_false_iff.mpr hp) hM hinv) := by
        dsimp only [E]
        rw [dif_pos hb, dif_neg hp]
      rw [hEb] at hblock
      rw [if_neg hp]
      exact Classical.choose_spec (exists_blockEquiv_coll hK hd pol hb
        (Bool.eq_false_iff.mpr hp) hM hinv) e he hblock
  obtain ⟨e, he, hblock⟩ := exists_blockDiag hd E
  refine ⟨e, he, ?_⟩
  intro x hx
  have heinv : StabV n d e⁻¹ := StabV.inv he
  have hy : flagAct e⁻¹ x ∈ refSet K n d := StabV.flagAct_mem_refSet heinv hx
  have hyE : ∀ j, (flagAct e⁻¹ x).E j = (x.E j).map (glLin e⁻¹).toLinearMap := fun j =>
    flagMap_E (glLin e⁻¹) x j
  apply flagK_ext_of_blocks hd
  intro b s hb hs
  rw [flagAct, flagMap_E, flagAct, flagMap_E, flagPsi_E hK hd pol hy hb hs,
    flagPsi_E hK hd pol hx hb hs]
  rw [psiSub, psiSub]
  by_cases hp : pol.getD b false = true
  · rw [if_pos hp, if_pos hp]
    have hg := hgood b hb e he (hblock b hb)
    rw [if_pos hp] at hg
    rw [hyE (d.getD b 0 + (blockSize d b - s))]
    exact hg _ (refSet_E_mem_interval hd hx hb (Nat.sub_le (blockSize d b) s)).1
      (refSet_E_mem_interval hd hx hb (Nat.sub_le (blockSize d b) s)).2
  · rw [if_neg hp, if_neg hp]
    have hg := hgood b hb e he (hblock b hb)
    rw [if_neg hp] at hg
    rw [hyE (d.getD b 0 + s)]
    exact hg _ (refSet_E_mem_interval hd hx hb hs).1
      (refSet_E_mem_interval hd hx hb hs).2

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

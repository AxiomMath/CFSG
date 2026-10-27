module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Reversal
public import CFSG.LieType.SpecialLinear.BinaryDescent.ExteriorTwist
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.QuadraticDescent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem c2slout6e_ringEquiv_eq_refl {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) (τ : K ≃+* K) : τ = RingEquiv.refl K := by
  ext x
  obtain ⟨y, _hy, hyu⟩ := (Nat.card_eq_two_iff' (0 : K)).1 (by
    rw [Nat.card_eq_fintype_card, hK])
  have hy1 : y = 1 := (hyu 1 one_ne_zero).symm
  by_cases hx : x = 0
  · simp [hx]
  · have hxy : x = y := hyu x hx
    rw [hxy, hy1]
    simp

theorem c2slout6e_mulVec_cancel {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A G A' Φ : Matrix ι ι K) (v : ι → K) (hΦ : Φ = A * G * A')
    (h : A' * A = 1) : A *ᵥ (G *ᵥ v) = Φ *ᵥ (A *ᵥ v) := by
  rw [hΦ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [Matrix.mul_assoc, h, Matrix.mul_one]

theorem c2slout6e_slMap_id {K : Type} [Field K]
    (g : Matrix.SpecialLinearGroup (Fin 6) K) :
    ((Matrix.SpecialLinearGroup.map (RingHom.id K)) g : Matrix (Fin 6) (Fin 6) K) =
      (g : Matrix (Fin 6) (Fin 6) K) := by
  ext i j
  rfl

theorem c2slout6e_extTwist_zero_eq_minor {K : Type} [Field K] [CharP K 2]
    (g : Matrix.SpecialLinearGroup (Fin 6) K) :
    (extTwist 6 3 0 K g :
      Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K) =
      minor (g : Matrix (Fin 6) (Fin 6) K) := by
  ext s t
  change minor ((g : Matrix (Fin 6) (Fin 6) K).map (iterateFrobenius K 2 0)) s t =
    minor (g : Matrix (Fin 6) (Fin 6) K) s t
  rw [iterateFrobenius_zero]
  have hid : ⇑(RingHom.id K) = (id : K → K) := by funext x; rfl
  rw [hid, Matrix.map_id]

theorem c2slout6e_revMap_minor_id {K : Type} [Field K] (h2 : (2 : K) = 0)
    (g : Matrix.SpecialLinearGroup (Fin 6) K) (hn : 3 ≤ 6)
    (x : Set.powersetCard (Fin 6) 3 → K) :
    revMap (R := K) (n := 3) (m := 6) hn (minor (g : Matrix (Fin 6) (Fin 6) K) *ᵥ x) =
      (minor ((borelGraph 6 K g) : Matrix (Fin 6) (Fin 6) K) :
        Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K) *ᵥ
        revMap (R := K) (n := 3) (m := 6) hn x := by
  have hid : ⇑(RingHom.id K) = (id : K → K) := by funext x; rfl
  have h := revMap_minor (F := K) (R := K) h2 g (RingHom.id K) hn x
  rw [hid] at h
  simpa only [c2slout6e_slMap_id, Matrix.map_id] using h

theorem c2slout6e_minor_revMap_borelStd {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) (B : Matrix.GeneralLinearGroup (Fin 6) K) (τ : K ≃+* K)
    (hτ : τ = RingEquiv.refl K) (g : Matrix.SpecialLinearGroup (Fin 6) K)
    (v : Set.powersetCard (Fin 6) 3 → K) :
    (minor (B : Matrix (Fin 6) (Fin 6) K) :
        Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K) *ᵥ
        revMap (R := K) (n := 3) (m := 6) (by norm_num)
          (minor (g : Matrix (Fin 6) (Fin 6) K) *ᵥ v) =
      (minor (((borelStd 6 K B τ 1 g : Matrix.SpecialLinearGroup (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) :
        Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K) *ᵥ
        ((minor (B : Matrix (Fin 6) (Fin 6) K) :
            Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K) *ᵥ
          revMap (R := K) (n := 3) (m := 6) (by norm_num) v) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set A : Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K :=
    (minor (B : Matrix (Fin 6) (Fin 6) K) :
      Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K) with hA
  set A' : Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K :=
    (minor (((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
      Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K) with hA'
  set G : Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K :=
    (minor ((borelGraph 6 K g) : Matrix (Fin 6) (Fin 6) K) :
      Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K) with hG
  set Φ : Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K :=
    (minor (((borelStd 6 K B τ 1 g : Matrix.SpecialLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K)) :
      Matrix (Set.powersetCard (Fin 6) (6 - 3)) (Set.powersetCard (Fin 6) (6 - 3)) K) with hΦ
  have hmat : ((borelStd 6 K B τ 1 g : Matrix.SpecialLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) =
      (B : Matrix (Fin 6) (Fin 6) K) *
        ((borelGraph 6 K g) : Matrix (Fin 6) (Fin 6) K) *
        ((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    rw [borelStd_apply, pow_one, CFSG.QuasithinUnique.K1.coe_stdAut_zero, hτ]
    have hid : ⇑(RingEquiv.refl K) = (id : K → K) := by funext x; rfl
    rw [hid, Matrix.map_id]
  have hA'A : A' * A = 1 := by
    rw [hA', hA]
    change minorMatrix 3 (((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K)) *
      minorMatrix 3 (B : Matrix (Fin 6) (Fin 6) K) = 1
    have h1 : ((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (B : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
    rw [← minorMatrix_mul, h1, minorMatrix_one]
  have hΦ_eq : Φ = A * G * A' := by
    rw [hΦ, hA, hA', hG, hmat]
    change minorMatrix 3 ((B : Matrix (Fin 6) (Fin 6) K) *
        ((borelGraph 6 K g) : Matrix (Fin 6) (Fin 6) K) *
        ((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
      minorMatrix 3 (B : Matrix (Fin 6) (Fin 6) K) *
        minorMatrix 3 ((borelGraph 6 K g) : Matrix (Fin 6) (Fin 6) K) *
        minorMatrix 3 (((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K))
    rw [← minorMatrix_mul, ← minorMatrix_mul]
  have hrev : revMap (R := K) (n := 3) (m := 6) (by norm_num)
      (minor (g : Matrix (Fin 6) (Fin 6) K) *ᵥ v) =
      G *ᵥ revMap (R := K) (n := 3) (m := 6) (by norm_num) v := by
    rw [c2slout6e_revMap_minor_id h2 g (by norm_num) v, ← hG]
  rw [hrev]
  exact c2slout6e_mulVec_cancel A G A' Φ
    (revMap (R := K) (n := 3) (m := 6) (by norm_num) v) hΦ_eq hA'A

end CFSG.LocalAnalysis.WeakClosure81

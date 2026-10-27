module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.RankThree.PartOne.K133H.WeylKey
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

namespace ExcFrames

section Coord

variable {τ : Tag} {p : ℕ}

variable (τ p) in
@[expose] def frameCoord (s : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  fun i => ∑ j, ((τ.symmetrizedCartan i j : ℤ) : ZMod p) * s j

theorem frameCoord_add (s t : Fin τ.rank → ZMod p) :
    frameCoord τ p (s + t) = frameCoord τ p s + frameCoord τ p t := by
  funext i
  simp only [frameCoord, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem frameCoord_zero : frameCoord τ p 0 = 0 := by
  funext i
  simp [frameCoord]

theorem frameCoord_redMod (v : Fin τ.rank → ℤ) :
    frameCoord τ p (TableBExc.redMod τ p v) =
      TableBExc.redMod τ p (Matrix.mulVec τ.symmetrizedCartan v) := by
  funext i
  simp [frameCoord, TableBExc.redMod, Matrix.mulVec, dotProduct]

theorem adAct_redMod (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    TableBExc.E6Three.adAct τ p w (TableBExc.redMod τ p v) = TableBExc.redMod τ p
      (fun i => dotProduct (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) v) := by
  funext i
  simp [TableBExc.E6Three.adAct, TableBExc.redMod, dotProduct]

theorem frameCoord_injective [Fact p.Prime]
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) :
    Function.Injective (frameCoord τ p) := by
  have e : frameCoord τ p = (τ.symmetrizedCartan.map (Int.castRingHom (ZMod p))).mulVec := by
    funext s i
    simp [frameCoord, Matrix.mulVec, dotProduct]
  have hd : (τ.symmetrizedCartan.map (Int.castRingHom (ZMod p))).det =
      ((τ.symmetrizedCartan.det : ℤ) : ZMod p) := (RingHom.map_det _ _).symm
  rw [e, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hd]
  exact hdet


theorem adAct_frameCoord [NeZero p] (w : WeylGroup τ) (s : Fin τ.rank → ZMod p) :
    TableBExc.E6Three.adAct τ p w (frameCoord τ p s) =
      frameCoord τ p (TableBExc.torusAct τ p w s) := by
  set v := TableBExc.liftMod τ p s with hv
  have hs : s = TableBExc.redMod τ p v := (TableBExc.redMod_liftMod s).symm
  rw [TableBExc.torusAct, ← hv, hs, frameCoord_redMod, adAct_redMod, frameCoord_redMod]
  congr 1
  funext i
  rw [dotProduct_mulVec_eq_iform, ← iform_smul w, smul_inv_smul, ← dotProduct_mulVec_eq_iform]
  simp [Pi.single_apply, dotProduct]

end Coord

theorem det_symmetrizedCartan_F4 : Tag.F4.symmetrizedCartan.det = 4 := by
  rw [Tag.symmetrizedCartan, Matrix.det_mul, det_cartan_F4, mul_one]
  change (Matrix.diagonal ![(2 : ℤ), 2, 1, 1]).det = 4
  rw [Matrix.det_diagonal, Fin.prod_univ_four]
  rfl

theorem det_symmetrizedCartan_E7 : Tag.E7.symmetrizedCartan.det = 2 := by
  rw [Tag.symmetrizedCartan, Matrix.det_mul, det_cartan_E7]
  change (1 : Matrix (Fin 7) (Fin 7) ℤ).det * 2 = 2
  rw [Matrix.det_one, one_mul]

theorem det_symmetrizedCartan_E8 : Tag.E8.symmetrizedCartan.det = 1 := by
  rw [Tag.symmetrizedCartan, Matrix.det_mul, det_cartan_E8]
  change (1 : Matrix (Fin 8) (Fin 8) ℤ).det * 1 = 1
  rw [Matrix.det_one, one_mul]

theorem isUnit_two_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    IsUnit ((((2 ^ k : ℕ) : ℤ)) : ZMod p) := by
  rw [isUnit_iff_ne_zero, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
    ((Fact.out : p.Prime).dvd_of_dvd_pow h))

theorem isUnit_det_symmetrizedCartan {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p) := by
  rcases hτ with rfl | rfl | rfl
  · rw [det_symmetrizedCartan_F4]
    exact isUnit_two_pow hp2 2
  · rw [det_symmetrizedCartan_E7]
    exact isUnit_two_pow hp2 1
  · rw [det_symmetrizedCartan_E8]
    exact isUnit_two_pow hp2 0

end ExcFrames

end CFSG.StandardType

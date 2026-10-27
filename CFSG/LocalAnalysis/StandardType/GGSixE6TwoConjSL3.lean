module

public import CFSG.Assembly.Defs
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCommutant
public import Certificates.Certificate3007
public import Certificates.Certificate10005
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoSL3Core
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoF4Coord
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Group
public import CFSG.Certificates.CosetTableShort
public import CFSG.LieType.Multipliers.ProductKernel

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.StandardType.GGHalf Matrix

section Conj

private theorem f2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  by_cases hz : a = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq a hz).trans (huniq 1 one_ne_zero).symm)

theorem exists_conj_sl3four (J₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F2))
    (hq : CFSG.Assembly.IsQuasisimple ↥J₀)
    (hP : LieModel (↥J₀ ⧸ Subgroup.center ↥J₀) .PSL 3 2 2) :
    ∃ c : Matrix.SpecialLinearGroup (Fin 6) F2,
      J₀.map (MulAut.conj c).toMonoidHom = sl3four := by
  classical
  haveI : Finite ↥J₀ := inferInstance
  have hdim : Module.finrank (ZMod 2) (Fin 6 → F2) = 6 := by
    rw [Module.finrank_pi_fintype]
    simp [GaloisField.finrank (p := 2) (n := 1) (by norm_num)]
  let φ : ↥J₀ →* Matrix (Fin 6) (Fin 6) F2 :=
    { toFun := fun g => (g : Matrix (Fin 6) (Fin 6) F2)
      map_one' := by
        show ((1 : ↥J₀) : Matrix (Fin 6) (Fin 6) F2) = 1
        rw [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one]
      map_mul' := fun g h => by
        show (((g * h : ↥J₀) : Matrix (Fin 6) (Fin 6) F2)) =
          (g : Matrix (Fin 6) (Fin 6) F2) * (h : Matrix (Fin 6) (Fin 6) F2)
        rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] }
  let ρ : Representation (ZMod 2) ↥J₀ (Fin 6 → F2) :=
    { toFun := fun g => (Matrix.toLin' (φ g)).restrictScalars (ZMod 2)
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp }
  have hρ_apply : ∀ (g : ↥J₀) (v : Fin 6 → F2),
      ρ g v = (g : Matrix (Fin 6) (Fin 6) F2) *ᵥ v := by
    intro g v
    change (Matrix.toLin' (φ g)).restrictScalars (ZMod 2) v =
      (g : Matrix (Fin 6) (Fin 6) F2) *ᵥ v
    rw [LinearMap.coe_restrictScalars, Matrix.toLin'_apply', Matrix.mulVecLin_apply]
    rfl
  have hρ : Function.Injective ρ := by
    intro g h hgh
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← hρ_apply g v, ← hρ_apply h v, hgh]
  obtain ⟨θ, E, hE⟩ := sl3_four_core hq hP ρ hρ hdim
  obtain ⟨E', hE'⟩ := exists_block_coord
  let Φ : (Fin 6 → F2) ≃+ (Fin 6 → F2) := E.trans E'
  have hΦV : ∀ (a : Matrix.SpecialLinearGroup (Fin 3) F4) (v : Fin 6 → F2),
      Φ ((θ a : Matrix (Fin 6) (Fin 6) F2) *ᵥ v) =
        resMat 3 (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ Φ v := by
    intro a v
    have h1 : E (ρ (θ a) v) = (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ E v := hE a v
    have h2 : ρ (θ a) v = (θ a : Matrix (Fin 6) (Fin 6) F2) *ᵥ v := hρ_apply (θ a) v
    calc Φ ((θ a : Matrix (Fin 6) (Fin 6) F2) *ᵥ v)
        = Φ (ρ (θ a) v) := by rw [← h2]
      _ = E' (E (ρ (θ a) v)) := rfl
      _ = E' ((a : Matrix (Fin 3) (Fin 3) F4) *ᵥ E v) := by rw [h1]
      _ = resMat 3 (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ E' (E v) :=
            (hE' (a : Matrix (Fin 3) (Fin 3) F4) (E v)).symm
      _ = resMat 3 (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ Φ v := rfl
  let ΦF : (Fin 6 → F2) ≃ₗ[F2] (Fin 6 → F2) :=
    { toFun := Φ
      invFun := Φ.symm
      left_inv := fun x => Φ.left_inv x
      right_inv := fun x => Φ.right_inv x
      map_add' := Φ.map_add'
      map_smul' := by
        intro a v
        rcases f2_eq_zero_or_one a with h | h
        · rw [h]; simp
        · rw [h]; simp }
  let c₀ : Matrix (Fin 6) (Fin 6) F2 := LinearMap.toMatrix' ΦF.toLinearMap
  have hcomp1 : ΦF.toLinearMap * ΦF.symm.toLinearMap = 1 := by
    apply LinearMap.ext
    intro v
    simp [Module.End.mul_apply]
  have hcomp2 : ΦF.symm.toLinearMap * ΦF.toLinearMap = 1 := by
    apply LinearMap.ext
    intro v
    simp [Module.End.mul_apply]
  have hcunit : IsUnit c₀ := by
    refine ⟨⟨c₀, LinearMap.toMatrix' ΦF.symm.toLinearMap, ?_, ?_⟩, rfl⟩
    · change LinearMap.toMatrix' ΦF.toLinearMap *
        LinearMap.toMatrix' ΦF.symm.toLinearMap = 1
      rw [← LinearMap.toMatrix'_mul, hcomp1, LinearMap.toMatrix'_one]
    · change LinearMap.toMatrix' ΦF.symm.toLinearMap *
        LinearMap.toMatrix' ΦF.toLinearMap = 1
      rw [← LinearMap.toMatrix'_mul, hcomp2, LinearMap.toMatrix'_one]
  have hc₀_mulVec : ∀ v : Fin 6 → F2, c₀ *ᵥ v = Φ v := by
    intro v
    have h : Matrix.toLin' c₀ = ΦF.toLinearMap := Matrix.toLin'_toMatrix' ΦF.toLinearMap
    have h2 : (Matrix.toLin' c₀) v = Φ v := by
      rw [h]
      rfl
    simpa only [Matrix.toLin'_apply', Matrix.mulVecLin_apply] using h2
  have hdet : c₀.det = 1 := by
    have hu : IsUnit c₀.det := (Matrix.isUnit_iff_isUnit_det c₀).mp hcunit
    have hne : c₀.det ≠ 0 := hu.ne_zero
    rcases f2_eq_zero_or_one c₀.det with h | h
    · exact absurd h hne
    · exact h
  let c : Matrix.SpecialLinearGroup (Fin 6) F2 := ⟨c₀, hdet⟩
  have hrel : ∀ (a : Matrix.SpecialLinearGroup (Fin 3) F4) (v : Fin 6 → F2),
      c₀ *ᵥ ((θ a : Matrix (Fin 6) (Fin 6) F2) *ᵥ v) =
        resMat 3 (a : Matrix (Fin 3) (Fin 3) F4) *ᵥ (c₀ *ᵥ v) := by
    intro a v
    simp only [hc₀_mulVec, hΦV]
  have hmat : ∀ a : Matrix.SpecialLinearGroup (Fin 3) F4,
      (c : Matrix (Fin 6) (Fin 6) F2) * (θ a : Matrix (Fin 6) (Fin 6) F2) =
        resMat 3 (a : Matrix (Fin 3) (Fin 3) F4) * (c : Matrix (Fin 6) (Fin 6) F2) := by
    intro a
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hrel a v
  have hgroup : ∀ a : Matrix.SpecialLinearGroup (Fin 3) F4,
      c * (θ a : Matrix.SpecialLinearGroup (Fin 6) F2) = resSL 3 a * c := by
    intro a
    apply Subtype.ext
    simpa only [Matrix.SpecialLinearGroup.coe_mul, coe_resSL] using hmat a
  have hconj : ∀ a : Matrix.SpecialLinearGroup (Fin 3) F4,
      c * (θ a : Matrix.SpecialLinearGroup (Fin 6) F2) * c⁻¹ = resSL 3 a := by
    intro a
    rw [hgroup a]
    group
  refine ⟨c, ?_⟩
  change J₀.map (MulAut.conj c).toMonoidHom = (resSL 3).range
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨a, ha⟩ := θ.surjective ⟨y, hy⟩
    have hy' : (θ a : Matrix.SpecialLinearGroup (Fin 6) F2) = y := congrArg Subtype.val ha
    refine MonoidHom.mem_range.mpr ⟨a, ?_⟩
    rw [← hconj a, ← MulAut.conj_apply, hy']
    exact hyx
  · intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [Subgroup.mem_map]
    refine ⟨(θ a : Matrix.SpecialLinearGroup (Fin 6) F2), (θ a).2, ?_⟩
    show MulAut.conj c (θ a : Matrix.SpecialLinearGroup (Fin 6) F2) = resSL 3 a
    rw [MulAut.conj_apply, hconj a]

end Conj

end CFSG.StandardType.GGSixE6Two

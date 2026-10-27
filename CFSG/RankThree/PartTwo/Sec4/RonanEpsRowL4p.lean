module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsL4Diag
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHL4
import CFSG.RankThree.PartTwo.Sec4.RonanK432DiagThree
import CFSG.RankThree.PartTwo.Sec4.Item426A6Field

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.Assembly.RankThreeEven (projSL)
open Matrix

section SL4

variable {K : Type} [Field K]

theorem l4Eps_good_SL4 [Finite K] {ω : K} (hω2 : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0)
    (h4 : 4 ≤ Nat.card K)
    (hfin : ∀ (X : Type) [Group X] [Finite X],
      Nonempty (X ≃* ↥(GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker) → EpsQuot X → False)
    (A : (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    GoodEps (Subgroup.centralizer ({(A : GL (Fin 4) K)} : Set (GL (Fin 4) K)) ⊓
      (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker) := by
  have hω := RonanK432.isPrimitiveRoot_three_of_sq_add_add_one hω2 h3
  have hA3' : (A : GL (Fin 4) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hA3, Subgroup.coe_one]
  have hA1' : (A : GL (Fin 4) K) ≠ 1 := fun h => hA1 (Subtype.ext h)
  obtain ⟨g, a, hD⟩ := RonanK432.exists_conj_diagonal_of_pow_three hω2 h3 hA3'
  have hQ : IsQuasisimple (GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv SpecialLinearGroup.toGLKerEquiv
      (Item426.isQuasisimple_SL_three K).1
  have hQ₂ : IsQuasisimple (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv SpecialLinearGroup.toGLKerEquiv
      (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h4)
  have hGdet : ∀ x ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker,
      (x : Matrix (Fin 4) (Fin 4) K).det = 1 := fun x hx => l4_det_of_mem_ker hx
  have hGσ : ∀ (σ : Equiv.Perm (Fin 4)) (g : GL (Fin 4) K),
      g ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker ↔
        Sec21.Tables.reindexGL σ g ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := by
    intro σ g
    have e : ((Sec21.Tables.reindexGL σ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
        (g : Matrix (Fin 4) (Fin 4) K).det := by
      rw [Sec21.Tables.coe_reindexGL, det_submatrix_equiv_self]
    exact ⟨fun hg => l4_mem_ker_det (e.trans (l4_det_of_mem_ker hg)),
      fun hg => l4_mem_ker_det (e.symm.trans (l4_det_of_mem_ker hg))⟩
  have hE : ∀ B ∈ (GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker,
      l4BlkGL3 B ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := by
    intro B hB
    exact l4_mem_ker_det (by rw [coe_l4BlkGL3, det_l4Blk3]; exact l4_det_of_mem_ker hB)
  have hβ : ∀ M ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker, ∀ B : GL (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) =
        (M : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc Fin.castSucc →
      (∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) 3 = 0 ∧
        (M : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc i) = 0) →
      (B : Matrix (Fin 3) (Fin 3) K).det = 1 →
        B ∈ (GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker :=
    fun _ _ B _ _ hdet => l4_mem_ker_det hdet
  have hQ₂det : ∀ B ∈ (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker,
      (B : Matrix (Fin 2) (Fin 2) K).det = 1 := fun B hB => l4_det_of_mem_ker hB
  have hE₁ : ∀ B ∈ (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker,
      blkUp B ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := fun B hB =>
    l4_mem_ker_det (by rw [coe_blkUp, det_l4Up2]; exact l4_det_of_mem_ker hB)
  have hE₂ : ∀ B ∈ (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker,
      blkLow B ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := fun B hB =>
    l4_mem_ker_det (by rw [coe_blkLow, det_l4Low2]; exact l4_det_of_mem_ker hB)
  have hβ2 : ∀ M ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker,
      BlockDiag2 (M : Matrix (Fin 4) (Fin 4) K) →
      (∀ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) =
          (M : Matrix (Fin 4) (Fin 4) K).submatrix ![0, 1] ![0, 1] →
        (B : Matrix (Fin 2) (Fin 2) K).det = 1 →
          B ∈ (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker) ∧
      (∀ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) =
          (M : Matrix (Fin 4) (Fin 4) K).submatrix ![2, 3] ![2, 3] →
        (B : Matrix (Fin 2) (Fin 2) K).det = 1 →
          B ∈ (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker) :=
    fun _ _ _ => ⟨fun _ _ hdet => l4_mem_ker_det hdet, fun _ _ hdet => l4_mem_ker_det hdet⟩
  have hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈
      (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker → u ^ 3 = 1 → u = 1 := by
    intro u hu hu3
    calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
      _ = 1 := by rw [l4_pow_four_of_scalar_mem_ker hu, hu3, inv_one, one_mul]
  have hg : ∀ h : GL (Fin 4) K, h ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker ↔
      g * h * g⁻¹ ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := by
    intro h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      mul_comm (GeneralLinearGroup.det g), mul_inv_cancel_right]
  exact l4Eps_good_of_conj h3 hω hQ hGdet hGσ hE hβ hQ₂ hQ₂det hE₁ hE₂ hβ2 hfin hZ3 A.2 hA3'
    hA1' hg hD

theorem l4Eps_good_projSL [Finite K] {ω : K} (hω2 : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0)
    (h4 : 4 ≤ Nat.card K)
    (hfin : ∀ (X : Type) [Group X] [Finite X],
      Nonempty (X ≃* ↥(GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker) → EpsQuot X → False)
    (y : projSL 4 K) (hy : orderOf y = 3) :
    GoodEps (Subgroup.centralizer ({y} : Set (projSL 4 K))) :=
  l4Eps_good_proj (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker
    (fun _ hu => l4_pow_four_of_scalar_mem_ker hu)
    (fun A hA3 hA1 => l4Eps_good_SL4 hω2 h3 h4 hfin A hA3 hA1) y hy

end SL4

theorem l4Eps_fin_sl2 (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    ∀ (X : Type) [Group X] [Finite X],
      Nonempty (X ≃* ↥(GeneralLinearGroup.det : GL (Fin 2) (GaloisField p 1) →*
        (GaloisField p 1)ˣ).ker) → EpsQuot X → False := by
  intro X _ _ ⟨e⟩ hT
  have hcard : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  exact false_of_epsQuot_sl2 (Fact.out : Nat.Prime p) h5 hcard
    (e.trans SpecialLinearGroup.toGLKerEquiv.symm) hT

theorem rowSEpsOf_four_SL_mod_one : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 →
    RowSEpsOf (projSL 4 (GaloisField p 1)) := by
  intro p _ hp hp1
  obtain ⟨ω, hω2⟩ := l4_exists_cube_root p hp1
  have hcard : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have h4 : 4 ≤ Nat.card (GaloisField p 1) := by omega
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by
      intro h
      have hpr : Nat.Prime p := Fact.out
      rw [h] at hpr
      norm_num at hpr
    omega
  refine fun S _ _ hs hna ⟨e⟩ => ?_
  exact noCfgSEps_of_goodEps_model e (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e (l4_not_three_dvd_outer p))
    (fun x hx => l4Eps_good_projSL hω2 (l4_three_ne_zero p hp) h4 (l4Eps_fin_sl2 p hp5) x hx)

end CFSG.RankThree.PartTwo.Sec4.RonanEps

module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Bruhat
import CFSG.Quasithin.Vol2.Ch11SecC37N1
import CFSG.Quasithin.Background.HTriPermute
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open scoped Pointwise

theorem conjAut_mem_sup_of_isUpperTriangular {K : Type*} [Field K] {n : ℕ} {A : GL (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular) :
    conjAut n K A ∈ (TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
      (TauCeti.diagonalTorus K n).map (conjAut n K) := by
  let B : TauCeti.upperTriangularGroup (Fin n) K :=
    ⟨A, TauCeti.UpperTriangularGroup.mem_iff.mpr hA⟩
  let t : Fin n → Kˣ := TauCeti.UpperTriangularGroup.diag B
  let d : GL (Fin n) K := TauCeti.diagGL t
  have hd_mem : d ∈ TauCeti.diagonalTorus K n :=
    TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr ⟨t, rfl⟩
  let u : GL (Fin n) K := A * d⁻¹
  have hd_inv_coe : ((d⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => ((t i)⁻¹ : K)) := by
    have h : d⁻¹ = TauCeti.diagGL t⁻¹ := by
      dsimp only [d]
      exact (map_inv (TauCeti.diagGL (k := K) (ι := Fin n)) t).symm
    rw [h, TauCeti.diagGL_coe]
    simp
  have hd_inv_upper : ((d⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular := by
    rw [hd_inv_coe]
    exact Matrix.blockTriangular_diagonal _
  have hupper : u ∈ TauCeti.upperTriangularGroup (Fin n) K := by
    rw [TauCeti.UpperTriangularGroup.mem_iff]
    have hu_coe : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) *
          ((d⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
    rw [hu_coe]
    exact Matrix.BlockTriangular.mul hA hd_inv_upper
  have hdiag_u : TauCeti.UpperTriangularGroup.diag ⟨u, hupper⟩ = 1 := by
    funext i
    apply Units.ext
    change ((TauCeti.UpperTriangularGroup.diag ⟨u, hupper⟩ i : Kˣ) : K) = 1
    rw [TauCeti.UpperTriangularGroup.diag_apply_val]
    have hAii : (A : Matrix (Fin n) (Fin n) K) i i = (t i : K) := by
      have h := TauCeti.UpperTriangularGroup.diag_apply_val B i
      change ((t i : Kˣ) : K) = (A : Matrix (Fin n) (Fin n) K) i i at h
      exact h.symm
    have hu_coe : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) *
          ((d⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
    rw [hu_coe, Matrix.mul_apply_diag_of_isUpperTriangular hA hd_inv_upper i,
        hd_inv_coe, Matrix.diagonal_apply_eq, hAii]
    exact mul_inv_cancel₀ (Units.ne_zero (t i))
  have hu : u ∈ TauCeti.upperUnitriangularGroup (Fin n) K :=
    (TauCeti.UpperTriangularGroup.diag_eq_one_iff (g := ⟨u, hupper⟩)).mp hdiag_u
  have hAeq : A = u * d := by
    dsimp only [u]
    group
  rw [hAeq, map_mul]
  apply Subgroup.mul_mem
  · exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem (conjAut n K) hu)
  · exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem (conjAut n K) hd_mem)

theorem diagonalTorus_conj_mem_upperUnitriangularGroup {K : Type*} [Field K] (n : ℕ)
    {d : GL (Fin n) K} (hd : d ∈ TauCeti.diagonalTorus K n)
    {u : GL (Fin n) K} (hu : u ∈ TauCeti.upperUnitriangularGroup (Fin n) K) :
    d * u * d⁻¹ ∈ TauCeti.upperUnitriangularGroup (Fin n) K := by
  have hd_B : d ∈ TauCeti.upperTriangularGroup (Fin n) K :=
    TauCeti.UpperTriangularGroup.diagonalTorus_le hd
  have hu_B : u ∈ TauCeti.upperTriangularGroup (Fin n) K :=
    TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup hu
  have hN : ((TauCeti.upperUnitriangularGroup (Fin n) K).subgroupOf
      (TauCeti.upperTriangularGroup (Fin n) K)).Normal := by
    rw [← TauCeti.UpperTriangularGroup.ker_diag]
    exact MonoidHom.normal_ker _
  let d' : TauCeti.upperTriangularGroup (Fin n) K := ⟨d, hd_B⟩
  let u' : TauCeti.upperTriangularGroup (Fin n) K := ⟨u, hu_B⟩
  have hu'_N : u' ∈ (TauCeti.upperUnitriangularGroup (Fin n) K).subgroupOf
      (TauCeti.upperTriangularGroup (Fin n) K) := hu
  have hconj := hN.conj_mem u' hu'_N d'
  have hcoe : ((d' * u' * d'⁻¹ : TauCeti.upperTriangularGroup (Fin n) K) :
      GL (Fin n) K) = d * u * d⁻¹ := by simp [d', u']
  rw [← hcoe]
  simpa only [Subgroup.mem_subgroupOf] using hconj

theorem map_conjAut_diagonalTorus_le_normalizer {K : Type*} [Field K] (n : ℕ) :
    (TauCeti.diagonalTorus K n).map (conjAut n K) ≤
      Subgroup.normalizer
        ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) :
          Set (MulAut (projectiveSL n K))) := by
  have hconj : ∀ d ∈ TauCeti.diagonalTorus K n, ∀ y ∈
      (TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K),
      (conjAut n K) d * y * ((conjAut n K) d)⁻¹ ∈
        (TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) := by
    intro d hd y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [show (conjAut n K) d * (conjAut n K) u * ((conjAut n K) d)⁻¹
        = conjAut n K (d * u * d⁻¹) by rw [map_mul, map_mul, map_inv]]
    exact Subgroup.mem_map_of_mem (conjAut n K)
      (diagonalTorus_conj_mem_upperUnitriangularGroup n hd hu)
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hconj d hd y hy
  · intro hy
    have hmem := hconj d⁻¹ ((TauCeti.diagonalTorus K n).inv_mem hd) _ hy
    rw [map_inv] at hmem
    have heq : ((conjAut n K) d)⁻¹ * ((conjAut n K) d * y * ((conjAut n K) d)⁻¹) *
        (((conjAut n K) d)⁻¹)⁻¹ = y := by group
    rw [← heq]
    exact hmem

theorem isPGroup_upperUnitriangularGroup {K : Type*} [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    IsPGroup 2 (TauCeti.upperUnitriangularGroup (Fin n) K) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    exact IsPGroup.of_subsingleton 2 _
  · obtain ⟨P, hP_eq⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular (K := K) 2 hn
    have hP2 : IsPGroup 2 (P : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) := P.isPGroup'
    rw [hP_eq] at hP2
    have hU_eq : TauCeti.upperUnitriangularGroup (Fin n) K =
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n K).map
          (Matrix.SpecialLinearGroup.toGL) := by
      ext u
      constructor
      · intro hu
        have hu' : (u : Matrix (Fin n) (Fin n) K).IsUpperUnitriangular :=
          TauCeti.UpperUnitriangularGroup.mem_iff.mp hu
        have hdet : (u : Matrix (Fin n) (Fin n) K).det = 1 := hu'.det_eq_one
        refine ⟨⟨u, hdet⟩, ?_, ?_⟩
        · exact ⟨fun i j hij => hu'.isUpperTriangular hij, fun i => hu'.apply_diag i⟩
        · exact Units.ext rfl
      · rintro ⟨u', hu', rfl⟩
        rw [TauCeti.UpperUnitriangularGroup.mem_iff, Matrix.isUpperUnitriangular_def]
        exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular.mp hu')
    rw [hU_eq]
    exact IsPGroup.map hP2 (Matrix.SpecialLinearGroup.toGL)

theorem odd_natCard_diagonalTorus {K : Type*} [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    Odd (Nat.card (TauCeti.diagonalTorus K n)) := by
  rw [TauCeti.natCard_diagonalTorus K n]
  have hunits_odd : Odd (Nat.card K - 1) := by
    let _ : Fintype K := Fintype.ofFinite K
    obtain ⟨m, -, hKcard⟩ := FiniteField.card K 2
    have hKcard' : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hKcard]
    have hm_pos : 0 < (m : ℕ) := m.pos
    rw [hKcard']
    have h2m_even : Even (2 ^ (m : ℕ)) :=
      Even.pow_of_ne_zero (by norm_num : Even 2) (Nat.ne_of_gt hm_pos)
    exact Nat.Even.sub_odd (Nat.one_le_pow (m : ℕ) 2 (by norm_num)) h2m_even
      (Nat.odd_iff.2 rfl)
  exact hunits_odd.pow

theorem natCard_map_sup_eq_mul {K : Type*} [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    Nat.card ↥((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
      (TauCeti.diagonalTorus K n).map (conjAut n K)) =
    Nat.card ↥((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K)) *
      Nat.card ↥((TauCeti.diagonalTorus K n).map (conjAut n K)) := by
  have hU2 : IsPGroup 2 ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K)) :=
    (isPGroup_upperUnitriangularGroup n).map (conjAut n K)
  have hD_odd : Odd (Nat.card ((TauCeti.diagonalTorus K n).map (conjAut n K))) :=
    (odd_natCard_diagonalTorus n).of_dvd_nat
      (Subgroup.card_map_dvd (H := TauCeti.diagonalTorus K n) (conjAut n K))
  have hinf : (TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊓
      (TauCeti.diagonalTorus K n).map (conjAut n K) = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k
      (Nat.prime_two.coprime_iff_not_dvd.mpr hD_odd.not_two_dvd_nat)
  have hmul : ((TauCeti.diagonalTorus K n).map (conjAut n K) :
        Set (MulAut (projectiveSL n K))) *
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) :
        Set (MulAut (projectiveSL n K))) =
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) :
        Set (MulAut (projectiveSL n K))) *
      ((TauCeti.diagonalTorus K n).map (conjAut n K) :
        Set (MulAut (projectiveSL n K))) :=
    set_mul_normalizer_comm
      (((TauCeti.diagonalTorus K n).map (conjAut n K)) :
        Set (MulAut (projectiveSL n K)))
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K))
      (map_conjAut_diagonalTorus_le_normalizer n)
  exact CFSG.Quasithin.H.Tri.card_sup_eq_mul hmul.symm hinf

theorem isSylowTwoOf_map_upperUnitriangularGroup {K : Type*} [Field K] [Finite K] [CharP K 2]
    (n : ℕ) :
    QuasithinUnique.IsSylowTwoOf
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K))
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
        (TauCeti.diagonalTorus K n).map (conjAut n K)) := by
  have hU2 : IsPGroup 2 ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K)) :=
    (isPGroup_upperUnitriangularGroup n).map (conjAut n K)
  have hD_odd : Odd (Nat.card ((TauCeti.diagonalTorus K n).map (conjAut n K))) :=
    (odd_natCard_diagonalTorus n).of_dvd_nat
      (Subgroup.card_map_dvd (H := TauCeti.diagonalTorus K n) (conjAut n K))
  refine ⟨le_sup_left, hU2, ?_⟩
  have hindex : (((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K)).subgroupOf
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
        (TauCeti.diagonalTorus K n).map (conjAut n K))).index =
      Nat.card ((TauCeti.diagonalTorus K n).map (conjAut n K)) := by
    have h1 := Subgroup.card_mul_index
      (H := ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K)).subgroupOf
        ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
          (TauCeti.diagonalTorus K n).map (conjAut n K)))
    have h2 : Nat.card (((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K)).subgroupOf
        ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
          (TauCeti.diagonalTorus K n).map (conjAut n K))) =
        Nat.card ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    rw [h2, natCard_map_sup_eq_mul (K := K) n] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  rw [hindex]
  exact hD_odd.not_two_dvd_nat

theorem isHallTwoPrimeOf_map_diagonalTorus {K : Type*} [Field K] [Finite K] [CharP K 2]
    (n : ℕ) :
    QuasithinUnique.Lin2.IsHallTwoPrimeOf
      ((TauCeti.diagonalTorus K n).map (conjAut n K))
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
        (TauCeti.diagonalTorus K n).map (conjAut n K)) := by
  have hU2 : IsPGroup 2 ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K)) :=
    (isPGroup_upperUnitriangularGroup n).map (conjAut n K)
  have hD_odd : Odd (Nat.card ((TauCeti.diagonalTorus K n).map (conjAut n K))) :=
    (odd_natCard_diagonalTorus n).of_dvd_nat
      (Subgroup.card_map_dvd (H := TauCeti.diagonalTorus K n) (conjAut n K))
  refine ⟨le_sup_right, hD_odd, ?_⟩
  obtain ⟨k, hk⟩ := hU2.exists_card_eq
  refine ⟨k, ?_⟩
  have hindex : (((TauCeti.diagonalTorus K n).map (conjAut n K)).relIndex
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
        (TauCeti.diagonalTorus K n).map (conjAut n K))) =
      Nat.card ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K)) := by
    change (((TauCeti.diagonalTorus K n).map (conjAut n K)).subgroupOf
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
        (TauCeti.diagonalTorus K n).map (conjAut n K))).index =
      Nat.card ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K))
    have h1 := Subgroup.card_mul_index
      (H := ((TauCeti.diagonalTorus K n).map (conjAut n K)).subgroupOf
        ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
          (TauCeti.diagonalTorus K n).map (conjAut n K)))
    have h2 : Nat.card (((TauCeti.diagonalTorus K n).map (conjAut n K)).subgroupOf
        ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
          (TauCeti.diagonalTorus K n).map (conjAut n K))) =
        Nat.card ((TauCeti.diagonalTorus K n).map (conjAut n K)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    rw [h2, natCard_map_sup_eq_mul (K := K) n] at h1
    rw [mul_comm (Nat.card ((TauCeti.diagonalTorus K n).map (conjAut n K)))
      (((TauCeti.diagonalTorus K n).map (conjAut n K)).subgroupOf
        ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
          (TauCeti.diagonalTorus K n).map (conjAut n K))).index] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  rw [hindex, hk]

theorem exists_le_map_conj_map_diagonalTorus {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {E : Subgroup (MulAut (projectiveSL n K))}
    (hE : E ≤ (TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
      (TauCeti.diagonalTorus K n).map (conjAut n K))
    (hEo : Odd (Nat.card E)) :
    ∃ u ∈ TauCeti.upperUnitriangularGroup (Fin n) K,
      E ≤ ((TauCeti.diagonalTorus K n).map (conjAut n K)).map
        (MulAut.conj (conjAut n K u)).toMonoidHom := by
  have hP : QuasithinUnique.IsSylowTwoOf
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K))
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
        (TauCeti.diagonalTorus K n).map (conjAut n K)) :=
    isSylowTwoOf_map_upperUnitriangularGroup (K := K) n
  have hD_hall : QuasithinUnique.Lin2.IsHallTwoPrimeOf
      ((TauCeti.diagonalTorus K n).map (conjAut n K))
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
        (TauCeti.diagonalTorus K n).map (conjAut n K)) :=
    isHallTwoPrimeOf_map_diagonalTorus (K := K) n
  have hX_normalizes :
      ((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
        (TauCeti.diagonalTorus K n).map (conjAut n K)) ≤
        Subgroup.normalizer
          (((TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K)) :
            Set (MulAut (projectiveSL n K))) :=
    sup_le Subgroup.le_normalizer (map_conjAut_diagonalTorus_le_normalizer n)
  obtain ⟨p, hp, hEp⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecC.exists_conj_le_of_normal_sylow hP hX_normalizes hD_hall hE hEo
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hp
  exact ⟨u, hu, hEp⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

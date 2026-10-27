module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.Defs

import CFSG.RankThree.PartOne.KF.R9Levi
import CFSG.RankThree.PartOne.KF.R9Perm
import CFSG.RankThree.PartOne.KF.UnitaryDiag
import CFSG.RankThree.PartOne.KF.UnitaryTorus
import CFSG.RankThree.PartOne.S10.FiveSuccessorQuasisimple
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.Assembly.Subnormal
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.RankThree.PartOne.KF.R9Model
import CFSG.RankThree.PartOne.KF.R9Plane

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

open Matrix CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

theorem ggLieSU3Fixed_normal {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    {d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))} {α : K} (hα : α ≠ 1)
    (hd : ((d : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![α, α, α, 1])
    (Jh : Subgroup ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)))
    (hJsub : CFSG.Assembly.IsSubnormal Jh
      (Subgroup.centralizer ({d} : Set ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)))))
    (hJperf : ⁅Jh, Jh⁆ = Jh) (hJ1 : Jh ≠ ⊥) :
    ∃ t ∈ Jh, ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag ∧
      ∃ u ∈ Jh, t * u ≠ u * t := by
  classical
  have h : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  haveI := h.finite
  have hα0 : α ≠ 0 := by
    intro h0
    have hdetne : (Matrix.diagonal ![α, α, α, 1] : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← hd]
      exact Matrix.GeneralLinearGroup.det_ne_zero (d : GL (Fin 4) K)
    rw [Matrix.det_diagonal] at hdetne
    exact hdetne (Finset.prod_eq_zero (Finset.mem_univ 0) (by simp [h0]))
  set t₀ : Kˣ := Units.mk0 α hα0
  have hne : t₀ ≠ 1 := by
    intro h1
    exact hα (by simpa [t₀] using congrArg (fun x : Kˣ => (x : K)) h1)
  have hdU : (d : GL (Fin 4) K) = diagU (dvec9 t₀ 1) := by
    apply Units.ext
    rw [hd, diagU_val]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hb : diagU (dvec9 t₀ 1) ∈ unitarySU 2 n K 4 :=
    hdU ▸ (show (d : GL (Fin 4) K) ∈ unitarySU 2 n K 4 from d.2)
  have hd_eq : d = b9 hb := by
    apply Subtype.ext
    exact hdU
  have hJsub' : CFSG.Assembly.IsSubnormal Jh
      (Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 n K 4))) := by
    rw [← hd_eq]
    exact hJsub
  have hJleC : Jh ≤ Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 n K 4)) := hJsub'.le
  have hRC : (blk93 h).range ≤ Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 n K 4)) := by
    rintro _ ⟨X, rfl⟩
    exact blk93_mem_centralizer h hb X
  have hJleR : Jh ≤ (blk93 h).range := by
    rw [← hJperf]
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ hg₁ g₂ hg₂
    let g₁U : ↥(unitarySU 2 n K 4) := g₁
    let g₂U : ↥(unitarySU 2 n K 4) := g₂
    have hcommJ : ⁅g₁, g₂⁆ ∈ Jh := hJperf ▸ Subgroup.commutator_mem_commutator hg₁ hg₂
    have hcommC : ⁅g₁U, g₂U⁆ ∈
        Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 n K 4)) := hJleC hcommJ
    have hker : (⟨⁅g₁U, g₂U⁆, hcommC⟩ :
        ↥(Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 n K 4)))) ∈
        (phi9 h hne hb).ker := by
      rw [MonoidHom.mem_ker]
      have hkey : (⟨⁅g₁U, g₂U⁆, hcommC⟩ :
          ↥(Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 n K 4)))) =
          ⁅(⟨g₁, hJleC hg₁⟩ : ↥(Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 n K 4)))),
            (⟨g₂, hJleC hg₂⟩ : ↥(Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 n K 4))))⁆ :=
        Subtype.ext rfl
      rw [hkey, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact mul_comm _ _
    rw [ker_phi9 h hne hb] at hker
    exact (Subgroup.mem_subgroupOf).1 hker
  rcases eq_or_lt_of_le hn with hn1 | hn2
  ·
    subst n
    exfalso
    haveI : Group.IsSolvable ↥(unitarySU 2 1 K 3) :=
      SmallU.isSolvable_unitarySU_small (m := 3) h (by norm_num) le_rfl
    have hRsolv : Group.IsSolvable ↥((blk93 h).range) :=
      Group.isSolvable_of_surjective
        (f := (MonoidHom.ofInjective (blk93_injective h)).toMonoidHom)
        (MonoidHom.ofInjective (blk93_injective h)).surjective
    have hJsolv : Group.IsSolvable Jh := by
      haveI : Group.IsSolvable ↥((blk93 h).range) := hRsolv
      let f : ↥Jh →* ↥((blk93 h).range) :=
        Subgroup.inclusion (G := ↥(LargeEvenSUGroup (Fin 4) K (2 ^ 1))) hJleR
      exact Group.isSolvable_of_isSolvable_injective (f := f)
        (Subgroup.inclusion_injective (G := ↥(LargeEvenSUGroup (Fin 4) K (2 ^ 1))) hJleR)
    have hJbot : Jh = ⊥ := by
      by_contra hne'
      haveI : Nontrivial Jh := (Subgroup.nontrivial_iff_ne_bot Jh).mpr hne'
      haveI : Group.IsPerfect Jh := Subgroup.isPerfect_iff.mpr hJperf
      exact (Group.IsPerfect.not_isSolvable (G := Jh)) hJsolv
    exact hJ1 hJbot
  ·
    have hn2' : 2 ≤ n := hn2
    have hRq : CFSG.IsQuasisimple ↥((blk93 h).range) := by
      rw [← perfectResidual_centralizer_b9 h hn2' hne hb]
      exact isQuasisimple_perfectResidual_centralizer_b9 h hn2' hne hb
    have hJsub_inf : CFSG.Assembly.IsSubnormal (Jh ⊓ (blk93 h).range) (blk93 h).range :=
      hJsub'.inf_of_le hRC
    have hJeq : Jh ⊓ (blk93 h).range = Jh := inf_eq_left.mpr hJleR
    have hsn := (CFSG.Assembly.IsSubnormal.iff_subgroupOf hJleR).mp (hJeq ▸ hJsub_inf)
    haveI : Group.IsPerfect Jh := Subgroup.isPerfect_iff.mpr hJperf
    have hJeqR : Jh = (blk93 h).range :=
      CFSG.RankThree.PartOne.eq_of_isSubnormal_of_isPerfect_of_isQuasisimple
        hRq hJleR inferInstance hJ1 hsn
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot h Nat.prime_three h3
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
    have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
    have hζpow : ζ ^ (2 ^ n + 1) = 1 := by
      obtain ⟨k, hk⟩ := h3
      rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
    let dvec3 : Fin 3 → Kˣ :=
      ![Units.mk0 ζ hζ0, Units.mk0 (ζ ^ 2) (pow_ne_zero 2 hζ0), 1]
    let v : Fin 3 → K := ![ζ, ζ ^ 2, 1]
    let D : Fin 4 → K := ![ζ, ζ ^ 2, 1, 1]
    have hv : (fun i : Fin 3 => ((dvec3 i : Kˣ) : K)) = v := by
      funext i
      fin_cases i <;> simp [v, dvec3]
    have hXt_mem : diagU dvec3 ∈ unitarySU 2 n K 3 := by
      rw [mem_unitarySU_iff h]
      constructor
      · rw [diagU_val, hv, Matrix.det_diagonal, Fin.prod_univ_three]
        change ζ * ζ ^ 2 * 1 = 1
        rw [show ζ * ζ ^ 2 = ζ ^ 3 by ring, hζ.pow_eq_one, one_mul]
      · rw [diagU_val, hv, Matrix.diagonal_map h.bar.map_zero, Matrix.diagonal_transpose,
          Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        fin_cases i
        · change h.bar ζ * ζ = 1
          rw [h.bar_apply, ← pow_succ, hζpow]
        · change h.bar (ζ ^ 2) * ζ ^ 2 = 1
          rw [map_pow, ← mul_pow,
            show h.bar ζ * ζ = 1 by rw [h.bar_apply, ← pow_succ, hζpow], one_pow]
        · change h.bar 1 * 1 = 1
          simp
    let Xt : ↥(unitarySU 2 n K 3) := ⟨diagU dvec3, hXt_mem⟩
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let Xu : ↥(unitarySU 2 n K 3) := ⟨permGL σ, permGL_mem_unitarySU h σ⟩
    let t : ↥(unitarySU 2 n K 4) := blk93 h Xt
    let u : ↥(unitarySU 2 n K 4) := blk93 h Xu
    have ht_mem : t ∈ Jh := by
      rw [hJeqR]
      exact MonoidHom.mem_range.mpr ⟨Xt, rfl⟩
    have hu_mem : u ∈ Jh := by
      rw [hJeqR]
      exact MonoidHom.mem_range.mpr ⟨Xu, rfl⟩
    have hXtmat : ((Xt : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal v := by
      show ((diagU dvec3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal v
      rw [diagU_val, hv]
    have htmat : gu4 t = Matrix.diagonal D := by
      rw [show gu4 t = CFSG.RankThree.PartOne.KFU.blk3 ((Xt : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) from rfl, hXtmat]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CFSG.RankThree.PartOne.KFU.blk3, Matrix.diagonal_apply, D, v]
    have ht_diag : ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag := by
      rw [show ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal D from htmat]
      exact Matrix.isDiag_diagonal _
    have hP01 : ((Xu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 1 := by
      show ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 1
      rw [coe_permGL]
      rw [show σ⁻¹ = σ from by simp [σ]]
      rw [show (σ.permMatrix K) = σ.toPEquiv.toMatrix from rfl, PEquiv.toMatrix_toPEquiv_apply]
      simp [σ]
    have hu01 : gu4 u 0 1 = 1 := by
      rw [show gu4 u = CFSG.RankThree.PartOne.KFU.blk3 ((Xu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) from rfl]
      simp [CFSG.RankThree.PartOne.KFU.blk3, hP01]
    refine ⟨t, ht_mem, ht_diag, u, hu_mem, ?_⟩
    intro hcomm
    have h01 := congrFun (congrFun (congrArg
      (fun g : ↥(unitarySU 2 n K 4) => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
      hcomm) 0) 1
    change (gu4 t * gu4 u) 0 1 = (gu4 u * gu4 t) 0 1 at h01
    rw [htmat, Matrix.diagonal_mul, hu01, mul_one] at h01
    rw [Matrix.mul_diagonal, hu01, one_mul] at h01
    have hD0 : D 0 = ζ := rfl
    have hD1 : D 1 = ζ ^ 2 := rfl
    rw [hD0, hD1] at h01
    have hζeq : ζ = ζ * ζ := by rw [← pow_two]; exact h01
    exact hζ1 ((mul_left_cancel₀ hζ0 (by rw [mul_one]; exact hζeq)).symm)

end CFSG.StandardType

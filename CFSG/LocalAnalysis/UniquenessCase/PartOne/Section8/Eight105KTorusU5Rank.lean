module

public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU4Rank
public import CFSG.RankThree.PartOne.K1320X.U4Emb
import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTen
import CFSG.LocalAnalysis.StandardType.UnitaryCenterScalar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableRankMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open Matrix CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.RankThree.PartOne (suQ)
open CFSG.RankThree.PartOne.K1320X (su4Emb su4Emb_injective gu5_su4Emb embMat45_apply)
open CFSG.RankThree.PartOne.KFU (diagU dvec5 gu5 D8Mod d8Vec_mem_SU d8Comb_four)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD unitaryInvolution_rootsOfUnity)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem theta_injective (hK : Nat.card K = (2 ^ 2) ^ 2) :
    Function.Injective ((suQ 5 hK).comp (su4Emb (unitaryInvolution K 2 2))) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  let σ := unitaryInvolution K 2 2
  have hq : CFSG.RankThree.PartOne.KFU.IsCentralPQuot 3 (suQ 5 hK) :=
    CFSG.RankThree.PartOne.isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hK
  have hz : su4Emb σ y ∈ Subgroup.center ↥(SU σ 5) :=
    hq.central (MonoidHom.mem_ker.mpr hy)
  obtain ⟨c, hc, -, -⟩ :=
    CFSG.StandardType.UnitaryCenter.exists_scalar_of_mem_center hK (by norm_num)
      (by norm_num : 3 ≤ 5) hz
  have h22 : gu5 (su4Emb σ y) 2 2 = 1 := by
    rw [gu5_su4Emb, embMat45_apply]
    simp [CFSG.RankThree.PartOne.K1320X.eSum45, Matrix.fromBlocks]
  have hc22 : gu5 (su4Emb σ y) 2 2 = (c : K) := by
    change ((su4Emb σ y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 2 2 = (c : K)
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  have hc1 : (c : K) = 1 := by rw [← hc22, h22]
  have hc1' : c = 1 := Units.ext hc1
  have h1 : su4Emb σ y = 1 := by
    apply Subtype.ext
    rw [hc, hc1']
    simp
  apply su4Emb_injective σ
  rw [h1, map_one]

private theorem image_KOf_le (hK : Nat.card K = (2 ^ 2) ^ 2)
    {x : ↥(SU (unitaryInvolution K 2 2) 5)} {t : ↥(SU (unitaryInvolution K 2 2) 4)}
    (ht : su4Emb (unitaryInvolution K 2 2) t = x) :
    ((F08.KOf8103 (SU (unitaryInvolution K 2 2) 4) (zpowers (t : GL (Fin 4) K))).subgroupOf
      (SU (unitaryInvolution K 2 2) 4)).map
      ((suQ 5 hK).comp (su4Emb (unitaryInvolution K 2 2))) ≤
    F08.KOf8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) (zpowers (suQ 5 hK x)) := by
  let σ := unitaryInvolution K 2 2
  have ht' : su4Emb σ t = x := ht
  let θ := (suQ 5 hK).comp (su4Emb σ)
  let K' := F08.KOf8103 (SU σ 4) (zpowers (t : GL (Fin 4) K))
  have hK'perf : Group.IsPerfect ↥K' :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.isPerfect_derInf8
      (SU σ 4 ⊓ centralizer (zpowers (t : GL (Fin 4) K)))
  have hK'le : K' ≤ SU σ 4 := (Subgroup.map_subtype_le _).trans inf_le_left
  have hK'le_cent : K' ≤ centralizer (zpowers (t : GL (Fin 4) K)) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hKsub_perf : Group.IsPerfect ↥(K'.subgroupOf (SU σ 4)) := by
    have := hK'perf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK'le).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hmap_perf : Group.IsPerfect ↥((K'.subgroupOf (SU σ 4)).map θ) := by
    have := hKsub_perf
    exact Group.IsPerfect.ofSurjective (f := θ.subgroupMap (K'.subgroupOf (SU σ 4)))
      (θ.subgroupMap_surjective _)
  have hθt : θ t = suQ 5 hK x := by
    simp only [θ, MonoidHom.comp_apply, ht']
  have hmap_cent : (K'.subgroupOf (SU σ 4)).map θ ≤
      centralizer (zpowers (suQ 5 hK x) : Set (StatedProj (StatedSU 5 (2 ^ 2) K))) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hgK' : (g : GL (Fin 4) K) ∈ K' := Subgroup.mem_subgroupOf.mp hg
    have hcomm_gt : g * t = t * g := by
      have h : (g : GL (Fin 4) K) ∈ centralizer (zpowers (t : GL (Fin 4) K)) := hK'le_cent hgK'
      rw [Subgroup.mem_centralizer_iff] at h
      apply Subtype.ext
      exact (h (t : GL (Fin 4) K) (Subgroup.mem_zpowers (t : GL (Fin 4) K))).symm
    have hcomm_theta : θ g * θ t = θ t * θ g := by
      rw [← map_mul, ← map_mul, hcomm_gt]
    have hcomm_theta' : θ g * suQ 5 hK x = suQ 5 hK x * θ g := by
      rw [← hθt]
      exact hcomm_theta
    exact (((commute_iff_eq (θ g) (suQ 5 hK x)).mpr hcomm_theta').zpow_right n).eq.symm
  have hle : (K'.subgroupOf (SU σ 4)).map θ ≤
      (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
        centralizer (zpowers (suQ 5 hK x) :
          Set (StatedProj (StatedSU 5 (2 ^ 2) K))) :=
    le_inf le_top hmap_cent
  have hfinal := CFSG.RankThree.PartTwo.KFacts.le_inSubgroup_perfectResidual
    hmap_perf hle
  have hfinal' : (K'.subgroupOf (SU σ 4)).map θ ≤
      F08.DerInf8 (⊤ ⊓ centralizer (zpowers (suQ 5 hK x) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) := by
    simpa [F08.DerInf8, CFSG.inSubgroup, CFSG.perfectResidual, top_inf_eq] using hfinal
  change (K'.subgroupOf (SU σ 4)).map θ ≤
    F08.KOf8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) (zpowers (suQ 5 hK x))
  simpa [F08.KOf8103, top_inf_eq] using hfinal'

private theorem torusD_mem_SU (v : D8Mod 3 K) :
    (torusD v : GL (Fin 4) K) ∈ SU (unitaryInvolution K 2 2) 4 := by
  rw [CFSG.RankThree.PartTwo.Sec21.U4Lines.torusD_apply]
  exact d8Vec_mem_SU (Or.inl rfl) d8Comb_four _
    (fun u => CFSG.RankThree.PartTwo.Sec21.U4Lines.unitaryInvolution_rootsOfUnity even_two u) v

private theorem su4Emb_torusD_eq {ζ : Kˣ} (ω : rootsOfUnity 3 K) (hω : (ω : Kˣ) = ζ)
    {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹))
    (t3 t4 : ↥(SU (unitaryInvolution K 2 2) 4))
    (ht3 : (t3 : GL (Fin 4) K) = torusD ((ω, ω) : D8Mod 3 K))
    (ht4 : (t4 : GL (Fin 4) K) = torusD ((ω, ω⁻¹) : D8Mod 3 K)) :
    su4Emb (unitaryInvolution K 2 2) t3 = x₃ ∧
      su4Emb (unitaryInvolution K 2 2) t4 = x₄ := by
  have hx₃' : (x₃ : GL (Fin 5) K) = diagU (dvec5 (ω : Kˣ) (ω : Kˣ)) := by rw [hω]; exact hx₃
  have hx₄' : (x₄ : GL (Fin 5) K) = diagU (dvec5 (ω : Kˣ) ((ω : Kˣ)⁻¹)) := by
    rw [hω]; exact hx₄
  constructor
  · apply Subtype.ext
    apply Units.ext
    change gu5 (su4Emb (unitaryInvolution K 2 2) t3) =
      ((x₃ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
    rw [gu5_su4Emb, hx₃']
    rw [ht3, CFSG.RankThree.PartTwo.Sec21.U4Lines.torusD_apply,
      CFSG.RankThree.PartOne.KFU.d8Vec_four]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.RankThree.PartOne.K1320X.embMat45,
        CFSG.RankThree.PartOne.K1320X.eSum45, CFSG.RankThree.PartOne.KFU.diagU_val,
        CFSG.RankThree.PartOne.KFU.dvec5, CFSG.RankThree.PartOne.KFU.dvec4]
  · apply Subtype.ext
    apply Units.ext
    change gu5 (su4Emb (unitaryInvolution K 2 2) t4) =
      ((x₄ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
    rw [gu5_su4Emb, hx₄']
    rw [ht4, CFSG.RankThree.PartTwo.Sec21.U4Lines.torusD_apply,
      CFSG.RankThree.PartOne.KFU.d8Vec_four]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.RankThree.PartOne.K1320X.embMat45,
        CFSG.RankThree.PartOne.K1320X.eSum45, CFSG.RankThree.PartOne.KFU.diagU_val,
        CFSG.RankThree.PartOne.KFU.dvec5, CFSG.RankThree.PartOne.KFU.dvec4]

theorem u5_two_le_pRank (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹)) :
    2 ≤ Open.pRank 5
      (F08.KOf8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) (zpowers (suQ 5 hK x₃)) ⊔
        F08.KOf8103 ⊤ (zpowers (suQ 5 hK x₄))) := by
  let σ := unitaryInvolution K 2 2
  let ω : rootsOfUnity 3 K := ⟨ζ, (mem_rootsOfUnity 3 ζ).mpr h3⟩
  have hω : (ω : Kˣ) = ζ := rfl
  have hω1 : ω ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  let t3 : ↥(SU σ 4) := ⟨torusD ((ω, ω) : D8Mod 3 K), torusD_mem_SU _⟩
  let t4 : ↥(SU σ 4) := ⟨torusD ((ω, ω⁻¹) : D8Mod 3 K), torusD_mem_SU _⟩
  obtain ⟨ht3_eq, ht4_eq⟩ := su4Emb_torusD_eq ω hω hx₃ hx₄ t3 t4 rfl rfl
  have h4 := u4_two_le_pRank (F := K) (b := 2) (by norm_num) hK hω1
    Nat.prime_five (by norm_num)
  let θ := (suQ 5 hK).comp (su4Emb σ)
  let K3' := F08.KOf8103 (SU σ 4) (zpowers (t3 : GL (Fin 4) K))
  let K4' := F08.KOf8103 (SU σ 4) (zpowers (t4 : GL (Fin 4) K))
  have hK3'le : K3' ≤ SU σ 4 := (Subgroup.map_subtype_le _).trans inf_le_left
  have hK4'le : K4' ≤ SU σ 4 := (Subgroup.map_subtype_le _).trans inf_le_left
  have h3le := image_KOf_le (hK := hK) ht3_eq
  have h4le := image_KOf_le (hK := hK) ht4_eq
  have hle : ((K3' ⊔ K4').subgroupOf (SU σ 4)).map θ ≤
      F08.KOf8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)))
        (zpowers (suQ 5 hK x₃)) ⊔
      F08.KOf8103 ⊤ (zpowers (suQ 5 hK x₄)) := by
    rw [Subgroup.subgroupOf_sup hK3'le hK4'le, Subgroup.map_sup]
    exact sup_le_sup h3le h4le
  have hfH : ∀ x : ↥(SU σ 4), (x : GL (Fin 4) K) ∈ K3' ⊔ K4' → θ x ∈
      F08.KOf8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)))
        (zpowers (suQ 5 hK x₃)) ⊔
      F08.KOf8103 ⊤ (zpowers (suQ 5 hK x₄)) := by
    intro x hx
    exact hle ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hH : K3' ⊔ K4' ≤ SU σ 4 := sup_le hK3'le hK4'le
  have hrank := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15k_table_pRank_le_of_inj
    (p := 5) (by norm_num) θ (theta_injective hK) hH hfH
  change 2 ≤ Open.pRank 5 (K3' ⊔ K4') at h4
  exact h4.trans hrank

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

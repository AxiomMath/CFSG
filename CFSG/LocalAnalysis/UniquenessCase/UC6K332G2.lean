module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Syl
public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import Certificates.Certificate3951
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
import CFSG.GH74.GLS.IVK.Proofs2.Ivk47f
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QSU33
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Wreath
import CFSG.HardMathSupport.Lang.Proving.FieldCubeRoots
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LieType.Chevalley.ExactG2FiniteOrder
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Adapters.RankThreeOutcomesReverse
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Assembly.QuasithinDefs
import CFSG.Foundations
import CFSG.GH74.GLS.IVK.Defs
import CFSG.GH74.GLS.IVK.Defs2
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open scoped commutatorElement MatrixGroups
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree (isPGroup_closure_cycle)
open CFSG.Assembly.RankThreeEven (projSU statedClassicalModel_of_projSU)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

def K332CentreLeComm (A : Type*) [Group A] : Prop :=
  ∀ x ∈ Subgroup.center A, x ^ 3 = 1 → x ∈ commutator A

private theorem map_mem_commutator' {A B : Type*} [Group A] [Group B] (f : A →* B) {a : A}
    (ha : a ∈ commutator A) : f a ∈ commutator B := by
  have h : (commutator A).map f ≤ commutator B := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  exact h ⟨a, ha, rfl⟩

theorem K332_centreLeComm_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : K332CentreLeComm A) : K332CentreLeComm B := by
  intro x hxc hx3
  have hxc' : e.symm x ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff] at hxc ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hxc (e g)
  have hx3' : (e.symm x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have := map_mem_commutator' e.toMonoidHom (h _ hxc' hx3')
  simpa using this

theorem K332_sylowCLC_of_exists {G : Type} [Group G] [Finite G] (T₀ : Sylow 3 G)
    (h : K332CentreLeComm ↥(T₀ : Subgroup G)) : SylowCenterLeCommutator G := by
  haveI : Finite (Sylow 3 G) := Sylow.finite_of_finiteIndex T₀
  intro T
  exact K332_centreLeComm_of_mulEquiv (Sylow.equiv T₀ T) h

theorem K332_exists_sylow_mulEquiv {A G : Type} [Group A] [Group G] [Finite A] [Finite G]
    (ι : A →* G) (hι : Function.Injective ι)
    (hcard : (Nat.card G).factorization 3 = (Nat.card A).factorization 3) (P : Sylow 3 A) :
    ∃ Q : Sylow 3 G, Nonempty (↥(P : Subgroup A) ≃* ↥(Q : Subgroup G)) := by
  have hc : Nat.card ↥((P : Subgroup A).map ι) = 3 ^ (Nat.card G).factorization 3 := by
    rw [Subgroup.card_map_of_injective hι, Sylow.card_eq_multiplicity P, hcard]
  exact ⟨Sylow.ofCard _ hc, ⟨(Subgroup.equivMapOfInjective (P : Subgroup A) ι hι).trans
    (MulEquiv.subgroupCongr (Sylow.coe_ofCard _ hc).symm)⟩⟩

theorem K332_sylowCLC_up {A G : Type} [Group A] [Group G] [Finite A] [Finite G]
    (ι : A →* G) (hι : Function.Injective ι)
    (hcard : (Nat.card G).factorization 3 = (Nat.card A).factorization 3)
    (hA : SylowCenterLeCommutator A) : SylowCenterLeCommutator G := by
  obtain ⟨P⟩ : Nonempty (Sylow 3 A) := inferInstance
  obtain ⟨Q, ⟨e⟩⟩ := K332_exists_sylow_mulEquiv ι hι hcard P
  exact K332_sylowCLC_of_exists Q (K332_centreLeComm_of_mulEquiv e (hA P))

theorem K332_sylowCLC_down {A G : Type} [Group A] [Group G] [Finite A] [Finite G]
    (ι : A →* G) (hι : Function.Injective ι)
    (hcard : (Nat.card G).factorization 3 = (Nat.card A).factorization 3)
    (hG : SylowCenterLeCommutator G) : SylowCenterLeCommutator A := by
  intro P
  obtain ⟨Q, ⟨e⟩⟩ := K332_exists_sylow_mulEquiv ι hι hcard P
  exact K332_centreLeComm_of_mulEquiv e.symm (hG Q)

theorem K332_sylowCLC_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : SylowCenterLeCommutator A) : SylowCenterLeCommutator B :=
  K332_sylowCLC_up e.toMonoidHom e.injective (by rw [Nat.card_congr e.toEquiv]) h

theorem K332_sylowCLC_of_cycle {S : Type} [Group S] [Finite S] (D π c : S)
    (hc : c ∈ Subgroup.center S) (hD : D ^ 3 = 1) (hπ : π ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hrel : π * D * π⁻¹ = c * D)
    (hscal : ∀ x : S, x * D = D * x → x * π = π * x → ∃ i : ℕ, x = c ^ i) :
    SylowCenterLeCommutator S := by
  have hcg : ∀ g : S, g * c = c * g := Subgroup.mem_center_iff.mp hc
  have hcg2 : ∀ g : S, g * c ^ 2 = c ^ 2 * g := fun g =>
    Subgroup.mem_center_iff.mp ((Subgroup.center S).pow_mem hc 2) g
  have hcC : ∀ g : S, Commute c g := fun g => (hcg g).symm
  have hcC2 : ∀ g : S, Commute (c ^ 2) g := fun g => (hcg2 g).symm
  have hconj_c : π * c * π⁻¹ = c := by rw [hcg π, mul_assoc, mul_inv_cancel, mul_one]
  have hconj_c2 : π * c ^ 2 * π⁻¹ = c ^ 2 := by rw [hcg2 π, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : π * (c * D) * π⁻¹ = c ^ 2 * D := by
    calc π * (c * D) * π⁻¹ = (π * c * π⁻¹) * (π * D * π⁻¹) := by group
      _ = c * (c * D) := by rw [hconj_c, hrel]
      _ = c ^ 2 * D := by rw [pow_two, mul_assoc]
  have h3 : π * (c ^ 2 * D) * π⁻¹ = D := by
    calc π * (c ^ 2 * D) * π⁻¹ = (π * c ^ 2 * π⁻¹) * (π * D * π⁻¹) := by group
      _ = c ^ 2 * (c * D) := by rw [hconj_c2, hrel]
      _ = c ^ 3 * D := by group
      _ = D := by rw [hc3, one_mul]
  have huv : D * (c * D) = (c * D) * D := by rw [← mul_assoc, hcg D]
  have huw : D * (c ^ 2 * D) = (c ^ 2 * D) * D := by rw [← mul_assoc, hcg2 D]
  have hvw : (c * D) * (c ^ 2 * D) = (c ^ 2 * D) * (c * D) := by
    have h1 : Commute (c * D) (c ^ 2 * D) :=
      (hcC (c ^ 2 * D)).mul_left (((hcC2 D).symm).mul_right (Commute.refl D))
    exact h1.eq
  have hv3 : (c * D) ^ 3 = 1 := by rw [(hcC D).mul_pow, hc3, hD, one_mul]
  have hc23 : (c ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hc3, one_pow]
  have hw3 : (c ^ 2 * D) ^ 3 = 1 := by rw [(hcC2 D).mul_pow, hc23, hD, one_mul]
  have hQ := isPGroup_closure_cycle huv huw hvw hD hv3 hw3 hπ hrel h2 h3
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  have hDP : D ∈ (P : Subgroup S) := hP (Subgroup.subset_closure (by simp))
  have hvP : c * D ∈ (P : Subgroup S) := hP (Subgroup.subset_closure (by simp))
  have hπP : π ∈ (P : Subgroup S) := hP (Subgroup.subset_closure (by simp))
  have hcP : c ∈ (P : Subgroup S) := by
    have := mul_mem hvP (inv_mem hDP)
    simpa using this
  refine K332_sylowCLC_of_exists P ?_
  intro x hxc _
  have hxD : (x : S) * D = D * x :=
    (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hxc (⟨D, hDP⟩ : ↥(P : Subgroup S)))).symm
  have hxπ : (x : S) * π = π * x :=
    (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hxc (⟨π, hπP⟩ : ↥(P : Subgroup S)))).symm
  obtain ⟨i, hi⟩ := hscal x hxD hxπ
  have hcc : (⟨c, hcP⟩ : ↥(P : Subgroup S)) ∈ commutator ↥(P : Subgroup S) := by
    have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (⟨π, hπP⟩ : ↥(P : Subgroup S)))
      (Subgroup.mem_top (⟨D, hDP⟩ : ↥(P : Subgroup S)))
    have e : (⁅(⟨π, hπP⟩ : ↥(P : Subgroup S)), (⟨D, hDP⟩ : ↥(P : Subgroup S))⁆ :
        ↥(P : Subgroup S)) = (⟨c, hcP⟩ : ↥(P : Subgroup S)) := by
      apply Subtype.ext
      show π * D * π⁻¹ * D⁻¹ = c
      rw [hrel, mul_inv_cancel_right]
    rw [e] at h
    exact h
  have hx : x = (⟨c, hcP⟩ : ↥(P : Subgroup S)) ^ i := Subtype.ext (by rw [hi]; rfl)
  rw [hx]
  exact Subgroup.pow_mem _ hcc i

section SL3

variable {K : Type} [Field K]

theorem sl3_offDiag_eq_zero {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {X : Matrix (Fin 3) (Fin 3) K}
    (h : X * Matrix.diagonal ![1, ω, ω ^ 2] = Matrix.diagonal ![1, ω, ω ^ 2] * X) :
    ∀ i j, i ≠ j → X i j = 0 := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hω2 : ω ^ 2 ≠ 1 := fun h2 => hω1 (by linear_combination hω3 - ω * h2)
  have hω12 : ω ≠ ω ^ 2 := fun h2 => hω1 (by
    have : ω * (ω - 1) = 0 := by linear_combination -h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hω0))
  have hdist : ∀ a b : Fin 3, a ≠ b → (![1, ω, ω ^ 2] : Fin 3 → K) a ≠ ![1, ω, ω ^ 2] b := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | exact absurd rfl hab
        | exact hω1.symm
        | exact hω1
        | exact hω2.symm
        | exact hω2
        | exact hω12
        | exact hω12.symm
  intro i j hij
  have e := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  have key : X i j * ((![1, ω, ω ^ 2] : Fin 3 → K) j - ![1, ω, ω ^ 2] i) = 0 := by
    linear_combination e
  exact (mul_eq_zero.mp key).resolve_right (sub_ne_zero.mpr (hdist j i hij.symm))

theorem sl3_diag_eq_of_commute_perm {X : Matrix (Fin 3) (Fin 3) K}
    (h : X * !![0, 1, 0; 0, 0, 1; 1, 0, 0] = !![0, 1, 0; 0, 0, 1; 1, 0, 0] * X) :
    X 0 0 = X 1 1 ∧ X 1 1 = X 2 2 := by
  have e1 := congrFun (congrFun h 0) 1
  have e2 := congrFun (congrFun h 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e1 e2
  exact ⟨e1, e2⟩

theorem sl3_exists_cycle_data {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃ D π c : SL(3, K), c ∈ Subgroup.center SL(3, K) ∧ D ^ 3 = 1 ∧ π ^ 3 = 1 ∧ c ^ 3 = 1 ∧
      π * D * π⁻¹ = c * D ∧
      ∀ x : SL(3, K), x * D = D * x → x * π = π * x → ∃ i : ℕ, x = c ^ i := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hs : 1 + ω + ω ^ 2 = 0 := by
    have : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1)
  obtain ⟨D, hDc⟩ : ∃ D : SL(3, K), (D : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, ω, ω ^ 2] :=
    ⟨⟨Matrix.diagonal ![1, ω, ω ^ 2], by
      simp [Matrix.det_diagonal, Fin.prod_univ_three]
      linear_combination hω3⟩, rfl⟩
  obtain ⟨π, hπc⟩ : ∃ π : SL(3, K), (π : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; 0, 0, 1; 1, 0, 0] :=
    ⟨⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by simp [Matrix.det_fin_three]⟩, rfl⟩
  obtain ⟨c, hcc⟩ : ∃ c : SL(3, K), (c : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω :=
    ⟨⟨Matrix.scalar (Fin 3) ω, by
      rw [Matrix.scalar_apply, Matrix.det_diagonal]
      simp [hω3]⟩, rfl⟩
  have hD3 : D ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hDc, Matrix.diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hω3] <;> linear_combination (ω ^ 3 + 1) * hω3
  have hπ3 : π ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hπc, Matrix.SpecialLinearGroup.coe_one]
    simp [pow_succ, Matrix.mul_fin_three, Matrix.one_fin_three]
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hcc, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
      hω3, map_one]
  have hcz : c ∈ Subgroup.center SL(3, K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    exact ⟨ω, by simpa using hω3, hcc.symm⟩
  have hrel' : π * D = c * D * π := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hπc, hDc, hcc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.scalar_apply] <;>
      first | ring1 | linear_combination hω3 | linear_combination -hω3
  refine ⟨D, π, c, hcz, hD3, hπ3, hc3, ?_, ?_⟩
  · rw [hrel', mul_assoc, mul_inv_cancel, mul_one]
  · intro x hxD hxπ
    have hXD : (x : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal ![1, ω, ω ^ 2] =
        Matrix.diagonal ![1, ω, ω ^ 2] * (x : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) hxD
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hDc] using this
    have hXπ : (x : Matrix (Fin 3) (Fin 3) K) * !![0, 1, 0; 0, 0, 1; 1, 0, 0] =
        (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) *
          (x : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) hxπ
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hπc] using this
    have hoff := sl3_offDiag_eq_zero hω3 hω1 hXD
    obtain ⟨hd01, hd12⟩ := sl3_diag_eq_of_commute_perm hXπ
    obtain ⟨l, hl⟩ : ∃ l : K, l = (x : Matrix (Fin 3) (Fin 3) K) 0 0 := ⟨_, rfl⟩
    have hX : (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) l := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, hl]
        fin_cases i
        · rfl
        · exact hd01.symm
        · exact hd12.symm.trans hd01.symm
      · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
        exact hoff i j hij
    have hl3 : l ^ 3 = 1 := by
      have hdet := x.2
      rw [hX, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
      simpa using hdet
    have hprod : (l - 1) * (l - ω) * (l - ω ^ 2) = 0 := by
      linear_combination hl3 - (l ^ 2 - l) * hs + (l - 1) * hω3
    have hcpow : ∀ n : ℕ, ((c ^ n : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.scalar (Fin 3) (ω ^ n) := fun n => by
      rw [Matrix.SpecialLinearGroup.coe_pow, hcc, map_pow]
    rcases mul_eq_zero.mp hprod with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · refine ⟨0, Subtype.ext ?_⟩
        rw [hX, hcpow 0, pow_zero, sub_eq_zero.mp h1, map_one]
      · refine ⟨1, Subtype.ext ?_⟩
        rw [hX, hcpow 1, pow_one, sub_eq_zero.mp h2]
    · refine ⟨2, Subtype.ext ?_⟩
      rw [hX, hcpow 2, sub_eq_zero.mp h3]

theorem K332_sylowCLC_SL3 [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    SylowCenterLeCommutator SL(3, K) := by
  obtain ⟨ζ, hζ1, hζ3⟩ :=
    CFSG.HardMathSupport.Lang.Proving.exists_ne_one_pow_three_of_three_dvd K h3
  have hω3 : (ζ : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hω1 : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  obtain ⟨D, π, c, hc, hD, hπ, hc3, hrel, hscal⟩ := sl3_exists_cycle_data hω3 hω1
  exact K332_sylowCLC_of_cycle D π c hc hD hπ hc3 hrel hscal

end SL3

theorem K332_factorization_three_card_psu_three_three : (6048 : ℕ).factorization 3 = 3 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have h1 : 3 ^ 3 ∣ 6048 := by norm_num
  have h2 : ¬ 3 ^ (3 + 1) ∣ 6048 := by norm_num
  have h3 := (padicValNat_dvd_iff_le (p := 3) (by norm_num : (6048 : ℕ) ≠ 0)).1 h1
  have h4 : ¬ 3 + 1 ≤ padicValNat 3 6048 := fun h =>
    h2 ((padicValNat_dvd_iff_le (p := 3) (by norm_num : (6048 : ℕ) ≠ 0)).2 h)
  omega

theorem sylowCenterLeCommutator_projSU_three_three (X : Type) [Group X] [Finite X]
    (e : X ≃* projSU 3 3 1) : SylowCenterLeCommutator X := by
  have hadm : StatedLieAdmissible .PSU 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hcard : Nat.card X = 6048 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three
      (statedClassicalModel_of_projSU hadm e)
  obtain ⟨x, y, -, -, hxy, hP⟩ := CFSG.AGLEmbedding.KFactProofs.G2Q.exists_pair_projSU33 e
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  have hxT : x ∈ (T : Subgroup X) := hT (Subgroup.subset_closure (by simp))
  have hyT : y ∈ (T : Subgroup X) := hT (Subgroup.subset_closure (by simp))
  have hTcard : Nat.card ↥(T : Subgroup X) = 3 ^ 3 := by
    rw [Sylow.card_eq_multiplicity, hcard, K332_factorization_three_card_psu_three_three]
  have hnc : ¬ IsMulCommutative ↥(T : Subgroup X) := fun hc =>
    hxy (congrArg Subtype.val (hc.is_comm.comm (⟨x, hxT⟩ : ↥(T : Subgroup X)) ⟨y, hyT⟩))
  have hZ : Nat.card (Subgroup.center ↥(T : Subgroup X)) = 3 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.card_center_of_nonabelian_card_p_cube
      hTcard hnc
  refine K332_sylowCLC_of_exists T fun z hz _ => ?_
  exact center_le_commutator_of_card_center_eq_prime T.isPGroup' hnc hZ hz

theorem K332_factorization_three_g2_sq {q : ℕ} (hq : 2 ≤ q) (h1 : 3 ∣ q + 1) :
    ((q ^ 2) ^ 6 * ((q ^ 2) ^ 6 - 1) * ((q ^ 2) ^ 2 - 1)).factorization 3 =
      (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)).factorization 3 := by
  have hnq : ¬ 3 ∣ q := by omega
  have hq6 : q ^ 6 = (q ^ 2) ^ 3 := by rw [← pow_mul]
  rw [hq6]
  generalize hx : q ^ 2 = x
  have hx4 : 4 ≤ x := by rw [← hx]; nlinarith
  have hnx : ¬ 3 ∣ x := fun h => hnq (Nat.prime_three.dvd_of_dvd_pow (hx ▸ h))
  have hx1 : 3 ∣ x - 1 := by
    rw [← hx, show q ^ 2 - 1 = (q + 1) * (q - 1) by rw [← Nat.sq_sub_sq, one_pow]]
    exact h1.mul_right _
  have lte : ∀ m : ℕ, m ≠ 0 → padicValNat 3 (x ^ m - 1) =
      padicValNat 3 (x - 1) + padicValNat 3 m := fun m hm => by
    have := padicValNat.pow_sub_pow (p := 3) (by decide) (by omega : 1 < x) hx1 hnx hm
    rwa [one_pow] at this
  have key : ∀ k : ℕ, k ≠ 0 → ∀ y : ℕ, y ≠ 0 →
      (x ^ k * (x ^ k - 1) * y).factorization 3 = padicValNat 3 (x ^ k - 1) + padicValNat 3 y := by
    intro k hk y hy
    have hpos : x ^ k - 1 ≠ 0 := by
      have : 1 < x ^ k := Nat.one_lt_pow hk (by omega)
      omega
    have hxk : x ^ k ≠ 0 := pow_ne_zero _ (by omega)
    rw [Nat.factorization_def _ Nat.prime_three, padicValNat.mul (mul_ne_zero hxk hpos) hy,
      padicValNat.mul hxk hpos, padicValNat.eq_zero_of_not_dvd
        (fun h => hnx (Nat.prime_three.dvd_of_dvd_pow h)), zero_add]
  have hx2 : x ^ 2 - 1 ≠ 0 := by
    have : 1 < x ^ 2 := Nat.one_lt_pow two_ne_zero (by omega)
    omega
  have hx0 : x - 1 ≠ 0 := by omega
  have v2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have v3 : padicValNat 3 3 = 1 := padicValNat_self
  have v6 : padicValNat 3 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num), v3, v2]
  rw [key 6 (by norm_num) _ hx2, key 3 (by norm_num) _ hx0, lte 6 (by norm_num),
    lte 3 (by norm_num), lte 2 (by norm_num), v6, v3, v2]
  omega

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47 (Xa Xb Xr Xu Xv Xc Xa_mem Xb_mem Xr_mem Xu_mem Xv_mem Xc_mem
  rel_ab rel_ru mem_center_iff exists_mulEquiv_sylow_G2 charP_of_natCard_eq_pow)
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (exists_a2Hom_injective factorization_three_g2_eq_sl3)
open CFSG.AGLEmbedding.KFactProofs.G2Q (baseChangeAdjoint baseChangeAdjoint_injective)

section Certified

theorem K332_centreLeComm_posUnipotent {F : Type} [Field F] (h3 : (3 : F) = 0) :
    K332CentreLeComm ↥(posUnipotent .G2 F) := by
  intro z hz _
  obtain ⟨s, t, hst⟩ := (mem_center_iff h3 z).1 hz
  obtain ⟨e, he, hru⟩ := rel_ru (K := F) h3
  obtain ⟨e', he', hab⟩ := rel_ab (K := F)
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have hee' : e' * e' = 1 := by rcases he' with rfl | rfl <;> norm_num
  have hv : (⟨Xv s, Xv_mem s⟩ : ↥(posUnipotent .G2 F)) ∈ commutator ↥(posUnipotent .G2 F) := by
    have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (⟨Xr 1, Xr_mem 1⟩ : ↥(posUnipotent .G2 F)))
      (Subgroup.mem_top (⟨Xu (e * s), Xu_mem _⟩ : ↥(posUnipotent .G2 F)))
    have heq : (⁅(⟨Xr 1, Xr_mem 1⟩ : ↥(posUnipotent .G2 F)),
        (⟨Xu (e * s), Xu_mem _⟩ : ↥(posUnipotent .G2 F))⁆ : ↥(posUnipotent .G2 F)) =
          ⟨Xv s, Xv_mem s⟩ := by
      apply Subtype.ext
      show ⁅Xr (1 : F), Xu (e * s)⁆ = Xv s
      rw [hru, show e * (1 * (e * s)) = s by linear_combination s * hee]
    rw [heq] at h
    exact h
  have hc : (⟨Xc t, Xc_mem t⟩ : ↥(posUnipotent .G2 F)) ∈ commutator ↥(posUnipotent .G2 F) := by
    have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (⟨Xa (e' * t), Xa_mem _⟩ : ↥(posUnipotent .G2 F)))
      (Subgroup.mem_top (⟨Xb 1, Xb_mem 1⟩ : ↥(posUnipotent .G2 F)))
    have heq : (⁅(⟨Xa (e' * t), Xa_mem _⟩ : ↥(posUnipotent .G2 F)),
        (⟨Xb 1, Xb_mem 1⟩ : ↥(posUnipotent .G2 F))⁆ : ↥(posUnipotent .G2 F)) =
          ⟨Xc t, Xc_mem t⟩ := by
      apply Subtype.ext
      show ⁅Xa (e' * t), Xb (1 : F)⁆ = Xc t
      rw [hab, show e' * (e' * t * 1) = t by linear_combination t * hee']
    rw [heq] at h
    exact h
  have hz' : z = ⟨Xv s, Xv_mem s⟩ * ⟨Xc t, Xc_mem t⟩ := Subtype.ext hst
  rw [hz']
  exact mul_mem hv hc

theorem sylowCenterLeCommutator_g2_char3 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : UntwistedChevalleyModel X .G2 (3 ^ n)) : SylowCenterLeCommutator X := by
  intro T
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_sylow_G2 Nat.prime_three h T
  have hchar : CharP F 3 := charP_of_natCard_eq_pow Nat.prime_three hF
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  exact K332_centreLeComm_of_mulEquiv e.symm (K332_centreLeComm_posUnipotent h3)

theorem K332_exists_equiv_adjointG2 {X : Type} [Group X] {q : ℕ}
    (h : UntwistedChevalleyModel X .G2 q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
      Nonempty (X ≃* ↥(adjointGroup .G2 K)) := by
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨K, hK, hKfin, hcard,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩

theorem K332_sylowCLC_adjointG2_of_three_dvd_sub_one (K : Type) [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) (hq : 2 ≤ Nat.card K) :
    SylowCenterLeCommutator ↥(adjointGroup .G2 K) := by
  obtain ⟨ι, hι⟩ : ∃ ι : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup .G2 K),
      Function.Injective ι := by
    obtain ⟨ι, hι, -⟩ := exists_a2Hom_injective (K := K)
    exact ⟨ι, hι⟩
  obtain ⟨-, hC, -⟩ := exact_G2_finite_order K (q := Nat.card K) rfl
  have hS : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
      show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  refine K332_sylowCLC_up ι hι ?_ (K332_sylowCLC_SL3 h3)
  rw [hC, hS]
  exact factorization_three_g2_eq_sl3 h3 hq

theorem sylowCenterLeCommutator_g2_of_three_dvd_sub_one {X : Type} [Group X] [Finite X] {q : ℕ}
    (h : UntwistedChevalleyModel X .G2 q) (h3 : 3 ∣ q - 1) (hq : 3 ≤ q) :
    SylowCenterLeCommutator X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := K332_exists_equiv_adjointG2 h
  subst hK
  exact K332_sylowCLC_of_mulEquiv e.symm
    (K332_sylowCLC_adjointG2_of_three_dvd_sub_one K h3 (by omega))

theorem K332_sylowCLC_adjointG2_of_three_dvd_add_one (K : Type) [Field K] [Finite K]
    (h1 : 3 ∣ Nat.card K + 1) : SylowCenterLeCommutator ↥(adjointGroup .G2 K) := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨K₂, _, _, _, hK₂⟩ : ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : Algebra K K₂),
      Nat.card K₂ = Nat.card K ^ 2 := by
    have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
    haveI : Fact (ringChar K).Prime := ⟨hp⟩
    exact ⟨FiniteField.Extension K (ringChar K) 2, inferInstance, inferInstance, inferInstance,
      FiniteField.natCard_extension K (ringChar K) 2⟩
  have h₂ : 3 ∣ Nat.card K₂ - 1 := by
    rw [hK₂, show Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) by
      rw [← Nat.sq_sub_sq, one_pow]]
    exact h1.mul_right _
  have hq₂ : 2 ≤ Nat.card K₂ := Finite.one_lt_card
  obtain ⟨-, hN, -⟩ := exact_G2_finite_order K (q := Nat.card K) rfl
  obtain ⟨-, hN₂, -⟩ := exact_G2_finite_order K₂ hK₂
  refine K332_sylowCLC_down (baseChangeAdjoint (algebraMap K K₂))
    (baseChangeAdjoint_injective _) ?_ (K332_sylowCLC_adjointG2_of_three_dvd_sub_one K₂ h₂ hq₂)
  rw [hN, hN₂]
  exact K332_factorization_three_g2_sq hq h1

theorem g2SylowMinus :
    ∀ (X : Type) [Group X] [Finite X] (q : ℕ), UntwistedChevalleyModel X .G2 q → 3 ∣ q + 1 →
      SylowCenterLeCommutator X := by
  intro X _ _ q h h3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := K332_exists_equiv_adjointG2 h
  subst hK
  exact K332_sylowCLC_of_mulEquiv e.symm (K332_sylowCLC_adjointG2_of_three_dvd_add_one K h3)

theorem sylowCenterLeCommutator_of_isoGTwoPrime :
    ∀ (X : Type) [Group X] [Finite X], CFSG.RankThree.PartTwo.Sec4.IsoGTwoPrime X →
      SylowCenterLeCommutator X := by
  intro X _ _ h
  rcases h with ⟨p, f, ⟨hp, -, -, h3q⟩, hmodel⟩ | ⟨⟨e⟩⟩
  · by_cases hp3 : p = 3
    · subst hp3
      exact sylowCenterLeCommutator_g2_char3 hmodel
    · have hnd : ¬ 3 ∣ p ^ f := fun h =>
        hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
          (Nat.prime_three.dvd_of_dvd_pow h)).symm
      generalize p ^ f = q at hnd h3q hmodel
      by_cases hmod : q % 3 = 1
      · exact sylowCenterLeCommutator_g2_of_three_dvd_sub_one hmodel (by omega) h3q
      · exact g2SylowMinus X q hmodel (by omega)
  · exact sylowCenterLeCommutator_projSU_three_three X e

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

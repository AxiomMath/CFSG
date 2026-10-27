module

public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesOrders
import CFSG.RankThree.GF2n.Stroth80.Sec7Levi
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Assembly.QuasithinDefs
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoresForms
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactPiece
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.G11Stmts
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.Walter.JRFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KGenO6pProof

open CFSG.Open CFSG.RankThree.GF2n.Stroth80 Matrix
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

private noncomputable def kg6_permGL : Equiv.Perm (Fin 3 ⊕ Fin 3) →* GL (Fin 3 ⊕ Fin 3) K :=
  (Matrix.permMatrixHom (n := Fin 3 ⊕ Fin 3) (R := K)).toHomUnits

private theorem kg6_permGL_val (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    ((kg6_permGL σ : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      (σ⁻¹).permMatrix K := rfl

private def kg6_s0 : Equiv.Perm (Fin 3 ⊕ Fin 3) := Equiv.swap (Sum.inl 0) (Sum.inr 0)
private def kg6_g : Equiv.Perm (Fin 3 ⊕ Fin 3) :=
  Equiv.swap (Sum.inl 0) (Sum.inl 1) * Equiv.swap (Sum.inr 0) (Sum.inr 1)
private def kg6_pi : Equiv.Perm (Fin 3 ⊕ Fin 3) :=
  Equiv.swap (Sum.inl 0) (Sum.inr 0) * Equiv.swap (Sum.inl 1) (Sum.inr 1)

private theorem kg6_comm : ⁅kg6_s0, kg6_g⁆ = kg6_pi := by decide
private theorem kg6_pi_inv : kg6_pi⁻¹ = kg6_pi := by decide
private theorem kg6_s0_inv : kg6_s0⁻¹ = kg6_s0 := by decide
private theorem kg6_g_inv : kg6_g⁻¹ = kg6_g := by decide

private theorem kg6_w_eq : (kg6_permGL (K := K) kg6_pi : GL (Fin 3 ⊕ Fin 3) K) =
    ⁅kg6_permGL (K := K) kg6_s0, kg6_permGL (K := K) kg6_g⁆ := by
  rw [← map_commutatorElement, kg6_comm]

private theorem kg6_permGL_mulVec (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (v : Fin 3 ⊕ Fin 3 → K) :
    ((kg6_permGL σ : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v =
      v ∘ ⇑(σ⁻¹) := by
  rw [kg6_permGL_val, Matrix.permMatrix_mulVec]

private theorem kg6_s0_quad (v : Fin 3 ⊕ Fin 3 → K) :
    StatedQuadPlus 3 K (((kg6_permGL kg6_s0 : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v) = StatedQuadPlus 3 K v := by
  rw [kg6_permGL_mulVec, kg6_s0_inv, statedQuadPlus_three, statedQuadPlus_three]
  simp [kg6_s0, Equiv.swap_apply_def]
  ring

private theorem kg6_g_quad (v : Fin 3 ⊕ Fin 3 → K) :
    StatedQuadPlus 3 K (((kg6_permGL kg6_g : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v) = StatedQuadPlus 3 K v := by
  rw [kg6_permGL_mulVec, kg6_g_inv, statedQuadPlus_three, statedQuadPlus_three]
  simp [kg6_g, Equiv.swap_apply_def]
  ring

private def kg6_adjc (M : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![M 1 1, M 0 1; M 1 0, M 0 0]

private theorem kg6_pi_levi2Left (M : Matrix (Fin 2) (Fin 2) K) :
    ((kg6_permGL kg6_pi : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *
        levi2Left M =
      levi2Right (kg6_adjc M) *
        ((kg6_permGL kg6_pi : GL (Fin 3 ⊕ Fin 3) K) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) := by
  rw [kg6_permGL_val, kg6_pi_inv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [levi2Left, levi2Right, kg6_adjc, kg6_pi, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.swap_apply_def]

private noncomputable def kg6_w : GL (Fin 3 ⊕ Fin 3) K := kg6_permGL kg6_pi

private theorem kg6_w_mul_self : (kg6_w : GL (Fin 3 ⊕ Fin 3) K) * kg6_w = 1 := by
  rw [kg6_w, ← map_mul]
  have : kg6_pi * kg6_pi = 1 := by decide
  rw [this, map_one]

private theorem kg6_w_inv : (kg6_w : GL (Fin 3 ⊕ Fin 3) K)⁻¹ = kg6_w :=
  inv_eq_of_mul_eq_one_right kg6_w_mul_self

private theorem kg6_w_levi2Left (M : Matrix (Fin 2) (Fin 2) K) :
    ((kg6_w : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) * levi2Left M =
      levi2Right (kg6_adjc M) * ((kg6_w : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) :=
  kg6_pi_levi2Left M

private theorem kg6_w_levi2Left_w (M : Matrix (Fin 2) (Fin 2) K) :
    ((kg6_w : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) * levi2Left M *
        ((kg6_w : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) = levi2Right (kg6_adjc M) := by
  rw [kg6_w_levi2Left, Matrix.mul_assoc, ← Units.val_mul, kg6_w_mul_self, Units.val_one,
    Matrix.mul_one]

private theorem kg6_w_mem [CharP K 2] :
    (kg6_w : GL (Fin 3 ⊕ Fin 3) K) ∈ StatedOmega (StatedQuadPlus 3 K) := by
  have h : (kg6_w : GL (Fin 3 ⊕ Fin 3) K) = ⁅kg6_permGL kg6_s0, kg6_permGL kg6_g⁆ := kg6_w_eq
  rw [h]
  have h1 : (kg6_permGL kg6_s0 : GL (Fin 3 ⊕ Fin 3) K) ∈
      CFSG.MatrixModel.isometryCore (StatedQuadPlus 3 K) :=
    Subgroup.subset_closure (fun v => kg6_s0_quad v)
  have h2 : (kg6_permGL kg6_g : GL (Fin 3 ⊕ Fin 3) K) ∈
      CFSG.MatrixModel.isometryCore (StatedQuadPlus 3 K) :=
    Subgroup.subset_closure (fun v => kg6_g_quad v)
  exact Subgroup.commutator_mem_commutator h1 h2

private theorem kg6_levi_prod_eq_one [CharP K 2] {a : Matrix (Fin 2) (Fin 2) K}
    (h : levi2Left a * levi2Right (kg6_adjc a) = 1) : a = 1 := by
  have h11 := congrFun (congrFun h (Sum.inl 1)) (Sum.inl 1)
  have h12 := congrFun (congrFun h (Sum.inl 1)) (Sum.inl 2)
  have h21 := congrFun (congrFun h (Sum.inl 2)) (Sum.inl 1)
  have h22 := congrFun (congrFun h (Sum.inl 2)) (Sum.inl 2)
  simp [Matrix.mul_apply, levi2Left, levi2Right, kg6_adjc, Fintype.sum_sum_type,
    Fin.sum_univ_three] at h11 h12 h21 h22
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h00 : a 0 0 ≠ 0 := fun h0 => by rw [h0, zero_mul] at h11; exact zero_ne_one h11
  have h10 : a 1 0 = 0 := h12.resolve_left h00
  have h01 : a 0 1 = 0 := h21.resolve_left h00
  have hsq : (a 0 0 + 1) ^ 2 = 0 := by linear_combination h22 + (a 0 0 + 1) * h2
  have h00' : a 0 0 = 1 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.1 hsq
    linear_combination this - h2
  have h11' : a 1 1 = 1 := by
    rw [h00', one_mul] at h11
    exact h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00', h01, h10, h11']

private theorem kg6_perfect_range {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (f : G →* H) : ⁅f.range, f.range⁆ = f.range := by
  have h : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    rw [← commutator_def]; exact Group.IsPerfect.commutator_eq_top
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

private theorem kg6_perfect_map {G H : Type*} [Group G] [Group H] (f : G →* H) {A : Subgroup G}
    (hA : ⁅A, A⁆ = A) : ⁅A.map f, A.map f⁆ = A.map f := by
  rw [← Subgroup.map_commutator, hA]

private theorem kg6_perfect_sup {G : Type*} [Group G] {A B : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hB : ⁅B, B⁆ = B) : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂)
      (Subgroup.inv_mem _ hg₁)) (Subgroup.inv_mem _ hg₂)
  · refine sup_le ?_ ?_
    · calc A = ⁅A, A⁆ := hA.symm
        _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc B = ⁅B, B⁆ := hB.symm
        _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

private def kg6_vecStab (v : Fin 3 ⊕ Fin 3 → K) : Subgroup (GL (Fin 3 ⊕ Fin 3) K) where
  carrier := {g | (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, Units.val_mul, ← Matrix.mulVec_mulVec] at *
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hg]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem kg6_w_e0 :
    ((kg6_w : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) = Pi.single (Sum.inr 0) 1 := by
  rw [kg6_w, kg6_permGL_mulVec, kg6_pi_inv]
  funext j
  rcases j with j | j <;> fin_cases j <;>
    simp [kg6_pi, Equiv.swap_apply_def, Pi.single_apply]

private theorem kg6_w_f0 :
    ((kg6_w : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
      (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K) = Pi.single (Sum.inl 0) 1 := by
  rw [kg6_w, kg6_permGL_mulVec, kg6_pi_inv]
  funext j
  rcases j with j | j <;> fin_cases j <;>
    simp [kg6_pi, Equiv.swap_apply_def, Pi.single_apply]

theorem exists_genLine_witness [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K ^ 2 - 1) :
    ∃ (V : Subgroup (GL (Fin 3 ⊕ Fin 3) K)) (x w : GL (Fin 3 ⊕ Fin 3) K),
      V ≤ StatedOmega (StatedQuadPlus 3 K) ∧
      (∀ v ∈ V, (v : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
        (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) = Pi.single (Sum.inl 0) 1) ∧
      ⁅V, V⁆ = V ∧ x ∈ V ∧ x ^ p = 1 ∧ x ≠ 1 ∧ w ∈ StatedOmega (StatedQuadPlus 3 K) ∧
      (¬ ∃ c : K, (w : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
        (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) = c • Pi.single (Sum.inl 0) 1) ∧
      w * x * w⁻¹ ∈ Subgroup.zpowers x := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect SL(2, K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  obtain ⟨a, ha⟩ : ∃ a : SL(2, K), orderOf a = p := by
    apply exists_prime_orderOf_dvd_card' p
    rw [CFSG.SeitzReduction.F4Pilot.natCard_specialLinearGroup_eq_ordSL (by norm_num)]
    simp [CFSG.SeitzReduction.F4Pilot.ordSL]
    exact Dvd.dvd.mul_left hpq _
  have hσΓ : ∀ g : SL(2, K), (leviLeftHom g : GL (Fin 3 ⊕ Fin 3) K) ∈
      StatedOmega (StatedQuadPlus 3 K) := fun g =>
    mem_statedOmega_quadPlus_of_perfect leviLeftHom (fun x v => by
      rw [leviLeftHom_val]
      exact levi2Left_quad _ (Matrix.SpecialLinearGroup.det_coe x) v) g
  have hσe : ∀ g : SL(2, K),
      ((leviLeftHom g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
          (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) = Pi.single (Sum.inl 0) 1 ∧
        ((leviLeftHom g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
          (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K) = Pi.single (Sum.inr 0) 1 := fun g => by
    rw [leviLeftHom_val]
    exact levi2Left_mulVec_fix _
  have hwΓ := kg6_w_mem (K := K)
  have hconjc : ∀ g : SL(2, K),
      ((kg6_w * leviLeftHom g * kg6_w⁻¹ : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) =
        levi2Right (kg6_adjc (g : Matrix (Fin 2) (Fin 2) K)) := fun g => by
    rw [kg6_w_inv]
    simp only [Units.val_mul]
    rw [leviLeftHom_val]
    exact kg6_w_levi2Left_w _
  have hcomm : Commute (leviLeftHom a : GL (Fin 3 ⊕ Fin 3) K)
      (kg6_w * leviLeftHom a * kg6_w⁻¹) := by
    apply Units.ext
    rw [Units.val_mul (leviLeftHom a) (kg6_w * leviLeftHom a * kg6_w⁻¹),
      Units.val_mul (kg6_w * leviLeftHom a * kg6_w⁻¹) (leviLeftHom a), hconjc a, leviLeftHom_val]
    exact levi2Left_mul_levi2Right _ _
  have hpow : (leviLeftHom a : GL (Fin 3 ⊕ Fin 3) K) ^ p = 1 := by
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  refine ⟨leviLeftHom.range ⊔ (leviLeftHom.range).map (MulAut.conj kg6_w).toMonoidHom,
    leviLeftHom a * (kg6_w * leviLeftHom a * kg6_w⁻¹), kg6_w, ?_, ?_, ?_, ?_, ?_, ?_, hwΓ, ?_, ?_⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact hσΓ g
    · rintro _ ⟨y, ⟨g, rfl⟩, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwΓ (hσΓ g)) (Subgroup.inv_mem _ hwΓ)
  · have hle : (leviLeftHom.range ⊔ (leviLeftHom.range).map (MulAut.conj kg6_w).toMonoidHom) ≤
        kg6_vecStab (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨g, rfl⟩
        exact (hσe g).1
      · rintro _ ⟨y, ⟨g, rfl⟩, rfl⟩
        change (((kg6_w * leviLeftHom g * kg6_w⁻¹ : GL (Fin 3 ⊕ Fin 3) K)) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
            (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) = Pi.single (Sum.inl 0) 1
        rw [kg6_w_inv]
        simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
        rw [kg6_w_e0, (hσe g).2, kg6_w_f0]
    intro v hv
    exact hle hv
  · exact kg6_perfect_sup (kg6_perfect_range _) (kg6_perfect_map _ (kg6_perfect_range _))
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, rfl⟩)
      (Subgroup.mem_sup_right ⟨leviLeftHom a, ⟨a, rfl⟩, rfl⟩)
  · rw [hcomm.mul_pow, conj_pow, hpow]
    simp
  · intro h1
    have h1' : ((leviLeftHom a * (kg6_w * leviLeftHom a * kg6_w⁻¹) : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1 := by
      rw [h1]; rfl
    rw [Units.val_mul (leviLeftHom a) (kg6_w * leviLeftHom a * kg6_w⁻¹), hconjc a,
      leviLeftHom_val] at h1'
    have ha1 : (a : Matrix (Fin 2) (Fin 2) K) = 1 := kg6_levi_prod_eq_one h1'
    have : a = 1 := Subtype.ext (by rw [ha1]; rfl)
    rw [this, orderOf_one] at ha
    exact hp.one_lt.ne ha
  · rintro ⟨c, hc⟩
    rw [kg6_w_e0] at hc
    have := congrFun hc (Sum.inr 0)
    simp at this
  · have e1 : kg6_w * (leviLeftHom a * (kg6_w * leviLeftHom a * kg6_w⁻¹)) * kg6_w⁻¹ =
        (kg6_w * leviLeftHom a * kg6_w⁻¹) * leviLeftHom a := by
      simp only [kg6_w_inv]
      calc kg6_w * (leviLeftHom a * (kg6_w * leviLeftHom a * kg6_w)) * kg6_w
          = (kg6_w * leviLeftHom a * kg6_w) * leviLeftHom a * (kg6_w * kg6_w) := by group
        _ = (kg6_w * leviLeftHom a * kg6_w) * leviLeftHom a := by
          rw [kg6_w_mul_self, mul_one]
    rw [e1, ← hcomm.eq]
    exact Subgroup.mem_zpowers _

end CFSG.LocalAnalysis.UniquenessCase.UC22.KGenO6pProof

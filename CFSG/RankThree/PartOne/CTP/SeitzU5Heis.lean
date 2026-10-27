module

public import CFSG.RankThree.PartOne.CTP.SeitzFineU5Five
public import CFSG.RankThree.PartOne.CTP.SeitzU5Gen
public import CFSG.RankThree.PartOne.CTP.SeitzU5Eigen
public import CFSG.RankThree.PartOne.CTP.SeitzU5Four
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.CTP.SeitzFineU5
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.RankThree.PartOne.CTP.U5Heis

open Matrix CFSG CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCEvenUnitaryFive
  CFSG.RankThree.PartOne.CTP
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr SUid SUid_eq_statedSU)
open CFSG.RankThree.PartOne.CTP.U5Alg (kMat kMat_eq_smul)

section Transport

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem closure_fixUnion_of_centralizers (γ0 : MulAut (primeFormP h (idGram K 5)))
    (A : Subgroup (MulAut (primeFormP h (idGram K 5))))
    (Sx : Set (primeFormUnitary h (idGram K 5)))
    (hSx : ∀ x ∈ Sx, primeFormConjHom h (idGram K 5) x ∈ A.map (MulAut.conj γ0).toMonoidHom ∧
      primeFormConjHom h (idGram K 5) x ≠ 1)
    (hmain : Subgroup.closure {g : unitarySU 2 f K 5 | ∃ x ∈ Sx,
      (g : GL (Fin 5) K) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (g : GL (Fin 5) K)} = ⊤) :
    Subgroup.closure {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
        ∀ φ ∈ F, φ k = k} = ⊤ := by
  classical
  set ρ := primeFormConjHom h (idGram K 5) with hρ
  let φ : MulAut (MulAut (primeFormP h (idGram K 5))) := MulAut.conj γ0
  let eg : unitarySU 2 f K 5 ≃* gramSU h (idGram K 5) :=
    MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 5)
  let π' : unitarySU 2 f K 5 →* primeFormP h (idGram K 5) :=
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 5)) 5)).comp eg.toMonoidHom
  have hπ' : Function.Surjective π' := (QuotientGroup.mk'_surjective _).comp eg.surjective
  have hfix : ∀ (g : unitarySU 2 f K 5) (x : primeFormUnitary h (idGram K 5)), x ∈ Sx →
      (g : GL (Fin 5) K) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (g : GL (Fin 5) K) →
      π' g ∈ {k : primeFormP h (idGram K 5) | ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))),
        F ≤ A.map φ.toMonoidHom ∧ F ≠ ⊥ ∧ ∀ ψ ∈ F, ψ k = k} := by
    intro g x hx hgx
    refine ⟨Subgroup.zpowers (ρ x), Subgroup.zpowers_le.2 (hSx x hx).1, ?_, ?_⟩
    · intro hbot
      exact (hSx x hx).2 (Subgroup.zpowers_eq_bot.1 hbot)
    · have hfix1 : ρ x (π' g) = π' g := by
        show primeFormConjHom h (idGram K 5) x
          (((eg g : gramSU h (idGram K 5)) : primeFormP h (idGram K 5))) = _
        rw [primeFormConjHom_mk]
        congr 1
        apply Subtype.ext
        show (x : GL (Fin 5) K) * (g : GL (Fin 5) K) * (x : GL (Fin 5) K)⁻¹ = (g : GL (Fin 5) K)
        rw [mul_inv_eq_iff_eq_mul]
        exact hgx.symm
      intro ψ hψ
      have hmem : ρ x ∈ MulAction.stabilizer (MulAut (primeFormP h (idGram K 5))) (π' g) := by
        rw [MulAction.mem_stabilizer_iff]
        exact hfix1
      have := Subgroup.zpowers_le.2 hmem hψ
      rw [MulAction.mem_stabilizer_iff] at this
      exact this
  have hle : (Subgroup.closure {g : unitarySU 2 f K 5 | ∃ x ∈ Sx,
      (g : GL (Fin 5) K) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (g : GL (Fin 5) K)}).map π' ≤
      Subgroup.closure {k : primeFormP h (idGram K 5) |
        ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A.map φ.toMonoidHom ∧ F ≠ ⊥ ∧
          ∀ ψ ∈ F, ψ k = k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨x, hx, hgx⟩, rfl⟩
    exact Subgroup.subset_closure (hfix g x hx hgx)
  rw [hmain, Subgroup.map_top_of_surjective π' hπ'] at hle
  have hback : ∀ k' ∈ {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A.map φ.toMonoidHom ∧ F ≠ ⊥ ∧
        ∀ ψ ∈ F, ψ k = k}, γ0⁻¹ k' ∈ {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
        ∀ ψ ∈ F, ψ k = k} := by
    rintro k' ⟨F', hF'A, hF'ne, hF'fix⟩
    refine ⟨F'.map φ.symm.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨ψ', hψ', rfl⟩
      obtain ⟨a, haA, rfl⟩ := hF'A hψ'
      simpa using haA
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ φ.symm.injective]
    · rintro _ ⟨ψ', hψ', rfl⟩
      have h1 := hF'fix ψ' hψ'
      show (φ.symm ψ') (γ0⁻¹ k') = γ0⁻¹ k'
      have h2 : φ.symm ψ' = γ0⁻¹ * ψ' * γ0 := by
        change (MulAut.conj γ0).symm ψ' = _
        rw [MulAut.conj_symm_apply]
      rw [h2]
      simp [MulAut.mul_apply, h1]
  rw [eq_top_iff]
  have hle2 : (Subgroup.closure {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A.map φ.toMonoidHom ∧ F ≠ ⊥ ∧
        ∀ ψ ∈ F, ψ k = k}).map (γ0⁻¹).toMonoidHom ≤
      Subgroup.closure {k : primeFormP h (idGram K 5) |
        ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
          ∀ ψ ∈ F, ψ k = k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k', hk', rfl⟩
    exact Subgroup.subset_closure (hback k' hk')
  rw [eq_top_iff.mpr hle,
    Subgroup.map_top_of_surjective (γ0⁻¹).toMonoidHom (γ0⁻¹).surjective] at hle2
  exact hle2

end Transport

section Pair

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem commute_of_mem_ker (hq3 : 3 < 2 ^ f) {z : primeFormUnitary h (idGram K 5)}
    (hz : z ∈ (primeFormConjHom h (idGram K 5)).ker) (w : primeFormUnitary h (idGram K 5)) :
    Commute z w := by
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff (by norm_num) hq3 z).mp
    (MonoidHom.mem_ker.mp hz)
  refine Subtype.ext ?_
  show (z : GL (Fin 5) K) * (w : GL (Fin 5) K) = (w : GL (Fin 5) K) * (z : GL (Fin 5) K)
  rw [hc]
  exact (commute_scalar c (w : GL (Fin 5) K)).symm.eq

theorem pow_comm_left' {E F : Matrix (Fin 5) (Fin 5) K} {ζ : K} (hEF : E * F = ζ • (F * E))
    (k : ℕ) : E ^ k * F = ζ ^ k • (F * E ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ]
    rw [Matrix.mul_assoc, hEF, Matrix.mul_smul, ← Matrix.mul_assoc, ih, Matrix.smul_mul,
      smul_smul, Matrix.mul_assoc, mul_comm ζ]

theorem eq_one_of_smul_eq {ζ : K} (M : GL (Fin 5) K)
    (hM : ζ • (M : Matrix (Fin 5) (Fin 5) K) = M) : ζ = 1 := by
  have h1 : (M : Matrix (Fin 5) (Fin 5) K) * ((M⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ζ • (1 : Matrix (Fin 5) (Fin 5) K) = 1 := by
    calc ζ • (1 : Matrix (Fin 5) (Fin 5) K)
        = ζ • ((M : Matrix (Fin 5) (Fin 5) K) *
          ((M⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) := by rw [h1]
      _ = (ζ • (M : Matrix (Fin 5) (Fin 5) K)) *
          ((M⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by rw [Matrix.smul_mul]
      _ = 1 := by rw [hM, h1]
  have h3 := congrFun (congrFun h2 0) 0
  simpa using h3

theorem exists_heis_pair (hq3 : 3 < 2 ^ f)
    (A : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hAel : IsElementaryAbelian 5 A)
    (hnab : ¬ ∀ x y : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
        x * y = y * x)
    (hshape : ∀ x : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A →
        ∃ z ∈ (primeFormConjHom h (idGram K 5)).ker, x ^ 5 = z ^ 5) :
    ∃ (e g : primeFormUnitary h (idGram K 5)) (ζ : K),
      primeFormConjHom h (idGram K 5) e ∈ A ∧ primeFormConjHom h (idGram K 5) g ∈ A ∧
      e ^ 5 = 1 ∧ g ^ 5 = 1 ∧ ζ ^ 5 = 1 ∧ ζ ≠ 1 ∧
      ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * ((g : GL (Fin 5) K) : Matrix _ _ K) =
        ζ • (((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((e : GL (Fin 5) K) : Matrix _ _ K)) := by
  classical
  set ρ := primeFormConjHom h (idGram K 5) with hρ
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have hc : IsMulCommutative A := hAel.toIsMulCommutative
    exact congrArg Subtype.val (hc.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  push Not at hnab
  obtain ⟨x, y, hx, hy, hxy⟩ := hnab
  obtain ⟨z₁, hz₁, hx5⟩ := hshape x hx
  obtain ⟨z₂, hz₂, hy5⟩ := hshape y hy
  have hz1c := commute_of_mem_ker h hq3 hz₁
  have hz2c := commute_of_mem_ker h hq3 hz₂
  set e := x * z₁⁻¹ with he
  set g := y * z₂⁻¹ with hg
  have hρe : ρ e = ρ x := by
    rw [he, map_mul, map_inv, MonoidHom.mem_ker.mp hz₁, inv_one, mul_one]
  have hρg : ρ g = ρ y := by
    rw [hg, map_mul, map_inv, MonoidHom.mem_ker.mp hz₂, inv_one, mul_one]
  have he5 : e ^ 5 = 1 := by
    rw [he, ((hz1c x).symm.inv_right).mul_pow, hx5, inv_pow, mul_inv_cancel]
  have hg5 : g ^ 5 = 1 := by
    rw [hg, ((hz2c y).symm.inv_right).mul_pow, hy5, inv_pow, mul_inv_cancel]
  have hκ : e * g * e⁻¹ * g⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hρe, hρg,
      hcomm _ hx _ hy]
    group
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff (by norm_num) hq3 _).mp
    (MonoidHom.mem_ker.mp hκ)
  have hmat : ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      ((g : GL (Fin 5) K) : Matrix _ _ K) =
      (c : K) • (((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((e : GL (Fin 5) K) : Matrix _ _ K)) := by
    have h1 : (e : GL (Fin 5) K) * g = ((e * g * e⁻¹ * g⁻¹ : primeFormUnitary h (idGram K 5)) :
        GL (Fin 5) K) * g * e := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hc] at h1
    have h2 := congrArg (fun m : GL (Fin 5) K => (m : Matrix (Fin 5) (Fin 5) K)) h1
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_assoc] at h2
    exact h2.trans (Matrix.smul_eq_diagonal_mul _ _).symm
  have hE5 : ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 = 1 := by
    have h3 := congrArg (fun m : primeFormUnitary h (idGram K 5) =>
      ((m : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) he5
    simpa using h3
  have hζ5 : (c : K) ^ 5 = 1 := by
    have h3 := pow_comm_left' hmat 5
    rw [hE5, Matrix.one_mul, Matrix.mul_one] at h3
    have hinv : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        (((g : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h4 : (1 : Matrix (Fin 5) (Fin 5) K) = (c : K) ^ 5 • 1 := by
      calc (1 : Matrix (Fin 5) (Fin 5) K)
          = ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
            (((g : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := hinv.symm
        _ = ((c : K) ^ 5 • ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) *
            (((g : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
          rw [← h3]
        _ = (c : K) ^ 5 • 1 := by rw [Matrix.smul_mul, hinv]
    have h5 := congrFun (congrFun h4 0) 0
    simpa using h5.symm
  have hζ1 : (c : K) ≠ 1 := by
    intro hc1
    apply hxy
    rw [hc1, one_smul] at hmat
    have hEG : Commute e g := Subtype.ext (Units.ext hmat)
    have hx' : x = e * z₁ := by rw [he]; group
    have hy' : y = g * z₂ := by rw [hg]; group
    have hcx : Commute (e * z₁) (g * z₂) :=
      (hEG.mul_right (hz2c e).symm).mul_left ((hz1c g).mul_right (hz1c z₂))
    rw [hx', hy']
    exact hcx.eq
  exact ⟨e, g, c, by rw [hρe]; exact hx, by rw [hρg]; exact hy, he5, hg5, hζ5, hζ1, hmat⟩

end Pair

section Bridge

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem bar_apply_eq (c : K) : h.bar c = unitaryInvolution K 2 f c := by
  rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]

theorem conjTr_mul_of_mem {g : GL (Fin 5) K} (hg : g ∈ primeFormUnitary h (idGram K 5)) :
    conjTr (unitaryInvolution K 2 f) (g : Matrix (Fin 5) (Fin 5) K) *
      (g : Matrix (Fin 5) (Fin 5) K) = 1 := by
  have := mem_primeFormUnitary.mp hg
  simp only [idGram, Units.val_one, Matrix.mul_one] at this
  rw [conjTr]
  convert this using 3
  ext i j
  simp [bar_apply_eq h]

theorem mem_of_conjTr_mul {g : GL (Fin 5) K}
    (hg : conjTr (unitaryInvolution K 2 f) (g : Matrix (Fin 5) (Fin 5) K) *
      (g : Matrix (Fin 5) (Fin 5) K) = 1) : g ∈ primeFormUnitary h (idGram K 5) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  rw [conjTr] at hg
  convert hg using 3
  ext i j
  simp [bar_apply_eq h]

@[expose] noncomputable def unitaryOfMatrix (P : Matrix (Fin 5) (Fin 5) K)
    (hP : conjTr (unitaryInvolution K 2 f) P * P = 1) : primeFormUnitary h (idGram K 5) :=
  ⟨⟨P, conjTr (unitaryInvolution K 2 f) P, mul_eq_one_comm.mp hP, hP⟩,
    mem_of_conjTr_mul h (g := ⟨P, conjTr (unitaryInvolution K 2 f) P,
      mul_eq_one_comm.mp hP, hP⟩) hP⟩

theorem coe_unitaryOfMatrix (P : Matrix (Fin 5) (Fin 5) K)
    (hP : conjTr (unitaryInvolution K 2 f) P * P = 1) :
    (((unitaryOfMatrix h P hP : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = P := rfl

theorem coe_unitaryOfMatrix_inv (P : Matrix (Fin 5) (Fin 5) K)
    (hP : conjTr (unitaryInvolution K 2 f) P * P = 1) :
    ((((unitaryOfMatrix h P hP)⁻¹ : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = conjTr (unitaryInvolution K 2 f) P := rfl

theorem isIsom_of_mem {g : GL (Fin 5) K} (hg : g ∈ primeFormUnitary h (idGram K 5)) :
    U5Eigen.IsIsom (unitaryInvolution K 2 f) (g : Matrix (Fin 5) (Fin 5) K) :=
  U5Eigen.isIsom_of_conjTr _ (conjTr_mul_of_mem h hg)

theorem norm_one_of_pow_five (h5 : 5 ∣ 2 ^ f + 1) {x : K} (hx : x ^ 5 = 1) :
    unitaryInvolution K 2 f x * x = 1 := by
  obtain ⟨m, hm⟩ := h5
  rw [unitaryInvolution_apply, ← pow_succ, hm, pow_mul, hx, one_pow]

end Bridge

section Shift

theorem shiftMat_eq {K : Type} [Field K] : (U5Eigen.shiftMat : Matrix (Fin 5) (Fin 5) K) =
    !![0, 0, 0, 0, 1; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U5Eigen.shiftMat_apply] <;> decide

theorem kMat_comm_shift {K : Type} [Field K] (h2 : (2 : K) = 0) (η ρ : K) :
    kMat η ρ * U5Eigen.shiftMat = U5Eigen.shiftMat * kMat η ρ := by
  have hJ : vecMulVec (fun _ : Fin 5 => (1 : K)) (fun _ => 1) * U5Eigen.shiftMat =
      U5Eigen.shiftMat * vecMulVec (fun _ : Fin 5 => (1 : K)) (fun _ => 1) := by
    rw [shiftMat_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [vecMulVec, Matrix.mul_apply, Fin.sum_univ_five]
  rw [kMat_eq_smul h2, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hJ]

end Shift

section Main

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem closure_fixUnion_of_shape48 [Finite K] [CharP K 2] (hq3 : 3 < 2 ^ f)
    (h5 : 5 ∣ 2 ^ f + 1)
    (hgen : ∀ M : Subgroup (SUid (unitaryInvolution K 2 f) 5),
      (∀ (t : Fin 5 → K) (ht : ∀ i, unitaryInvolution K 2 f (t i) * t i = 1)
        (hdet : ∏ i, t i = 1), U5Gen.dgSU (unitaryInvolution K 2 f) t ht hdet ∈ M) →
      (∀ g : SUid (unitaryInvolution K 2 f) 5,
        U5Gen.mat (unitaryInvolution K 2 f) g * U5Eigen.shiftMat =
          U5Eigen.shiftMat * U5Gen.mat (unitaryInvolution K 2 f) g → g ∈ M) →
      (∀ x ∈ M, U5Gen.shiftSU (unitaryInvolution K 2 f) * x *
        (U5Gen.shiftSU (unitaryInvolution K 2 f))⁻¹ ∈ M) → M = ⊤)
    (A : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hAel : IsElementaryAbelian 5 A)
    (hnab : ¬ ∀ x y : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
        x * y = y * x)
    (hshape : ∀ x : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A →
        ∃ z ∈ (primeFormConjHom h (idGram K 5)).ker, x ^ 5 = z ^ 5) :
    Subgroup.closure {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
        ∀ φ ∈ F, φ k = k} = ⊤ := by
  classical
  have hK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  have hσi := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
    (p := 2) (f := f) hK
  have h2 : (2 : K) = 0 := U5Gen.two_eq_zero
  obtain ⟨e, g, ζ, heA, hgA, he5, hg5, hζ5, hζ1, hEF⟩ :=
    exists_heis_pair h hq3 A hAel hnab hshape
  set ρ := primeFormConjHom h (idGram K 5) with hρ
  have hEisom := isIsom_of_mem h e.2
  have hFisom := isIsom_of_mem h g.2
  have hE5 : ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 = 1 := by
    have h3 := congrArg (fun m : primeFormUnitary h (idGram K 5) =>
      ((m : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) he5
    simpa using h3
  have hF5 : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 = 1 := by
    have h3 := congrArg (fun m : primeFormUnitary h (idGram K 5) =>
      ((m : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) hg5
    simpa using h3
  obtain ⟨P, lam, hPP, hlam5, hEP, hFP⟩ := U5Eigen.exists_frame (unitaryInvolution K 2 f) hσi h2
    (fun x hx => norm_one_of_pow_five h5 hx) hζ5 hζ1 hEisom hFisom hE5 hF5 hEF
  set Pu := unitaryOfMatrix h P hPP with hPu
  set D₀ : primeFormUnitary h (idGram K 5) := Pu⁻¹ * e * Pu with hD₀
  set S₀ : primeFormUnitary h (idGram K 5) := Pu⁻¹ * g * Pu with hS₀
  have hD₀mat : ((D₀ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.diagonal (fun j : Fin 5 => lam * ζ ^ (j : ℕ)) := by
    simp only [hD₀, Subgroup.coe_mul, Units.val_mul, hPu, coe_unitaryOfMatrix_inv,
      coe_unitaryOfMatrix]
    rw [Matrix.mul_assoc, hEP, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hS₀mat : ((S₀ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = U5Eigen.shiftMat := by
    simp only [hS₀, Subgroup.coe_mul, Units.val_mul, hPu, coe_unitaryOfMatrix_inv,
      coe_unitaryOfMatrix]
    rw [Matrix.mul_assoc, hFP, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have hc : IsMulCommutative A := hAel.toIsMulCommutative
    exact congrArg Subtype.val (hc.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  set γ0 : MulAut (primeFormP h (idGram K 5)) := (ρ Pu)⁻¹ with hγ0
  have hconj : ∀ x : primeFormUnitary h (idGram K 5),
      ρ (Pu⁻¹ * x * Pu) = (MulAut.conj γ0) (ρ x) := by
    intro x
    rw [map_mul, map_mul, map_inv, MulAut.conj_apply, hγ0, inv_inv]
  set A' := A.map (MulAut.conj γ0).toMonoidHom with hA'
  have hcommA' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show (MulAut.conj γ0) a * (MulAut.conj γ0) b = (MulAut.conj γ0) b * (MulAut.conj γ0) a
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hnec : ¬ Commute e g := by
    intro hc
    have hmat : ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
      congrArg (fun m : primeFormUnitary h (idGram K 5) =>
        ((m : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) hc.eq
    have h3 : ζ • (((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) =
        ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
      rw [← hEF]; exact hmat
    exact hζ1 (eq_one_of_smul_eq ((g : GL (Fin 5) K) * (e : GL (Fin 5) K)) (by
      simpa only [Units.val_mul] using h3))
  have hρe1 : ρ e ≠ 1 := fun h1 =>
    hnec (commute_of_mem_ker h hq3 (MonoidHom.mem_ker.mpr h1) g)
  have hρg1 : ρ g ≠ 1 := fun h1 =>
    hnec (commute_of_mem_ker h hq3 (MonoidHom.mem_ker.mpr h1) e).symm
  let Sx : Set (primeFormUnitary h (idGram K 5)) := {x | ρ x ∈ A' ∧ ρ x ≠ 1}
  have hD₀Sx : D₀ ∈ Sx := by
    refine ⟨⟨ρ e, heA, (hconj e).symm⟩, ?_⟩
    rw [hD₀, hconj]
    exact fun h1 => hρe1 ((map_eq_one_iff _ (MulAut.conj γ0).injective).mp h1)
  have hS₀Sx : S₀ ∈ Sx := by
    refine ⟨⟨ρ g, hgA, (hconj g).symm⟩, ?_⟩
    rw [hS₀, hconj]
    exact fun h1 => hρg1 ((map_eq_one_iff _ (MulAut.conj γ0).injective).mp h1)
  have hstab : ∀ x ∈ Sx, S₀ * x * S₀⁻¹ ∈ Sx := by
    intro x hx
    have h1 : ρ (S₀ * x * S₀⁻¹) = ρ x := by
      rw [map_mul, map_mul, map_inv, hcommA' _ hS₀Sx.1 _ hx.1]
      group
    exact ⟨by rw [h1]; exact hx.1, by rw [h1]; exact hx.2⟩
  let 𝒢 : Set (SUid (unitaryInvolution K 2 f) 5) := {g | ∃ x ∈ Sx,
    ((g : GL (Fin 5) K)) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (g : GL (Fin 5) K)}
  set M₀ : Subgroup (SUid (unitaryInvolution K 2 f) 5) := Subgroup.closure 𝒢 with hM₀
  have hD : ∀ (t : Fin 5 → K) (ht : ∀ i, unitaryInvolution K 2 f (t i) * t i = 1)
      (hdet : ∏ i, t i = 1), U5Gen.dgSU (unitaryInvolution K 2 f) t ht hdet ∈ M₀ := by
    intro t ht hdet
    refine Subgroup.subset_closure ⟨D₀, hD₀Sx, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD₀mat]
    show Matrix.diagonal t * _ = _ * Matrix.diagonal t
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hC : ∀ g : SUid (unitaryInvolution K 2 f) 5,
      U5Gen.mat (unitaryInvolution K 2 f) g * U5Eigen.shiftMat =
        U5Eigen.shiftMat * U5Gen.mat (unitaryInvolution K 2 f) g → g ∈ M₀ := by
    intro g hg
    refine Subgroup.subset_closure ⟨S₀, hS₀Sx, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hS₀mat]
    exact hg
  have hsGL : ((U5Gen.shiftSU (unitaryInvolution K 2 f) : SUid (unitaryInvolution K 2 f) 5) :
      GL (Fin 5) K) = (S₀ : GL (Fin 5) K) := by
    apply Units.ext
    rw [hS₀mat]
    rfl
  have hS : ∀ x ∈ M₀, U5Gen.shiftSU (unitaryInvolution K 2 f) * x *
      (U5Gen.shiftSU (unitaryInvolution K 2 f))⁻¹ ∈ M₀ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨z, hz, hyz⟩ := hy
      refine Subgroup.subset_closure ⟨S₀ * z * S₀⁻¹, hstab z hz, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsGL]
      calc (S₀ : GL (Fin 5) K) * (y : GL (Fin 5) K) * (S₀ : GL (Fin 5) K)⁻¹ *
            ((S₀ : GL (Fin 5) K) * (z : GL (Fin 5) K) * (S₀ : GL (Fin 5) K)⁻¹)
          = (S₀ : GL (Fin 5) K) * ((y : GL (Fin 5) K) * (z : GL (Fin 5) K)) *
            (S₀ : GL (Fin 5) K)⁻¹ := by group
        _ = (S₀ : GL (Fin 5) K) * ((z : GL (Fin 5) K) * (y : GL (Fin 5) K)) *
            (S₀ : GL (Fin 5) K)⁻¹ := by rw [hyz]
        _ = _ := by group
    | one => simp
    | mul a b _ _ ha hb =>
      have : U5Gen.shiftSU (unitaryInvolution K 2 f) * (a * b) *
          (U5Gen.shiftSU (unitaryInvolution K 2 f))⁻¹ =
          (U5Gen.shiftSU (unitaryInvolution K 2 f) * a *
            (U5Gen.shiftSU (unitaryInvolution K 2 f))⁻¹) *
          (U5Gen.shiftSU (unitaryInvolution K 2 f) * b *
            (U5Gen.shiftSU (unitaryInvolution K 2 f))⁻¹) := by group
      rw [this]
      exact M₀.mul_mem ha hb
    | inv a _ ha =>
      have : U5Gen.shiftSU (unitaryInvolution K 2 f) * a⁻¹ *
          (U5Gen.shiftSU (unitaryInvolution K 2 f))⁻¹ =
          (U5Gen.shiftSU (unitaryInvolution K 2 f) * a *
            (U5Gen.shiftSU (unitaryInvolution K 2 f))⁻¹)⁻¹ := by group
      rw [this]
      exact M₀.inv_mem ha
  have hM : M₀ = ⊤ := hgen M₀ hD hC hS
  have hmain : Subgroup.closure {g : unitarySU 2 f K 5 | ∃ x ∈ Sx,
      (g : GL (Fin 5) K) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (g : GL (Fin 5) K)} = ⊤ := by
    let ε : Su K 2 f 5 ≃* unitarySU 2 f K 5 := MulEquiv.subgroupCongr (SUid_eq_statedSU hK 5)
    have himg : (ε.toMonoidHom '' 𝒢) = {g : unitarySU 2 f K 5 | ∃ x ∈ Sx,
        (g : GL (Fin 5) K) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (g : GL (Fin 5) K)} := by
      ext g'
      constructor
      · rintro ⟨g, ⟨x, hx, hgx⟩, rfl⟩
        exact ⟨x, hx, hgx⟩
      · rintro ⟨x, hx, hgx⟩
        have hεs : ((ε.symm g' : SUid (unitaryInvolution K 2 f) 5) : GL (Fin 5) K) =
            (g' : GL (Fin 5) K) := rfl
        exact ⟨ε.symm g', ⟨x, hx, by rw [hεs]; exact hgx⟩, by simp⟩
    rw [← himg, ← MonoidHom.map_closure, ← hM₀, hM, Subgroup.map_top_of_surjective _ ε.surjective]
  exact closure_fixUnion_of_centralizers h γ0 A Sx (fun x hx => hx) hmain

end Main

end CFSG.RankThree.PartOne.CTP.U5Heis

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCEvenUnitaryFive

theorem psu5DiagPlane48 : PSU5DiagPlane48 := by
  intro f K _ h h5 A hAel hAcard hAD hnab hshape
  have := h.finite
  have := h.charP
  have hK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  by_cases hf : f = 2
  · subst hf
    exact U5Heis.closure_fixUnion_of_shape48 h (by norm_num) h5
      (fun M hD hC hS => U5Four.eq_top_of_four hK M hD hC hS) A hAel hnab hshape
  · have h1 := h.one_le
    have hf6 : 6 ≤ f := by
      by_contra hlt
      push Not at hlt
      interval_cases f <;> omega
    have hq3 : 3 < 2 ^ f := by
      have : 2 ^ 6 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf6
      omega
    exact U5Heis.closure_fixUnion_of_shape48 h hq3 h5
      (fun M hD hC hS => U5Gen.eq_top_of_diag_circ_shift hK hf6 h5 M hD
        (fun η hη => hC _ (U5Heis.kMat_comm_shift U5Gen.two_eq_zero η _)) hS) A hAel hnab hshape

end CFSG.RankThree.PartOne.CTP

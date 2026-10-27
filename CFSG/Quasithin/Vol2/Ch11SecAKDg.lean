module

public import CFSG.Quasithin.Vol2.Ch11SecAKDf
public import CFSG.Quasithin.Background.HSL3Bridge
public import CFSG.Quasithin.Background.HSp4Rel
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Quasithin.H CFSG.Assembly.LowTwoRank

section Nat

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem exists_model_nat {W : Type} [CommGroup W] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hR : (FFModel.nat Γ).Realizes H ⊤ ⊥) :
    ∃ (π : ↥Γ ≃* ↥H) (e : W ≃* StdMod ι K),
      ∀ γ w, e (((π γ : ↥H) : MulAut W) w) = natAut Γ γ (e w) := by
  obtain ⟨π₀, hπ₀⟩ := hR
  let π : ↥Γ →* ↥H := π₀
  have hπ : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π := hπ₀
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia Γ hπ
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro (γ : ↥Γ) hγ
    have h1 : natAut Γ γ = 1 := by
      refine MulEquiv.ext fun m => ?_
      have h2 := he γ (e.symm m)
      rw [hγ, MulEquiv.apply_symm_apply] at h2
      rw [natAut_apply, ← h2]
      exact MulEquiv.apply_symm_apply e m
    exact natAut_injective Γ (h1.trans (map_one _).symm)
  exact ⟨MulEquiv.ofBijective π ⟨hinj, hπ.1⟩, e, fun γ w => he γ w⟩

theorem matAut_semilinear (A g : GL ι K) (σ : K ≃+* K) (g' : GL ι K)
    (hg' : (g' : Matrix ι ι K) = (A : Matrix ι ι K) * (g : Matrix ι ι K).map σ *
      ((A⁻¹ : GL ι K) : Matrix ι ι K)) :
    matAut g' = (matAut A * fieldMap σ) * matAut g * (matAut A * fieldMap σ)⁻¹ := by
  refine toAddMap_injective fun v => ?_
  have h1 : (matAut A * fieldMap σ) * matAut g * (matAut A * fieldMap σ)⁻¹ =
      matAut A * (fieldMap σ * matAut g * (fieldMap σ)⁻¹) * matAut A⁻¹ := by
    have : matAut A⁻¹ = (matAut A)⁻¹ := by
      show matHom A⁻¹ = (matHom A)⁻¹
      rw [map_inv]
    rw [this]
    group
  rw [h1, toAddMap_mul, toAddMap_mul, toAddMap_matAut, toAddMap_matAut, toAddMap_fieldMap_conj,
    toAddMap_matAut, hg', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Nat

section SL3

variable {K : Type} [Field K]

theorem stdAut_zero_mem_indM (A : GL (Fin 3) K) (σ : K ≃+* K) :
    MulAut.congr (SL3Pair.slEquiv K) (CFSG.QuasithinUnique.K1.stdAut A σ 0) ∈
      indM (natAut (StatedSL 3 K)) := by
  refine ⟨matAut A * fieldMap σ, fun γ => ?_⟩
  show matAut _ = _
  apply matAut_semilinear A (γ : GL (Fin 3) K) σ
  change ((CFSG.QuasithinUnique.K1.stdAut A σ 0 ((SL3Pair.slEquiv K).symm γ) :
    Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
  rw [CFSG.QuasithinUnique.K1.coe_stdAut_zero]
  conv_rhs => rw [← MulEquiv.apply_symm_apply (SL3Pair.slEquiv K) γ, SL3Pair.coe_slEquiv]

variable [Finite K]

theorem cover_sl3 :
    ∃ τ : MulAut ↥(StatedSL 3 K), ∀ θ, θ ∈ indM (natAut (StatedSL 3 K)) ∨
      θ * τ⁻¹ ∈ indM (natAut (StatedSL 3 K)) := by
  refine ⟨MulAut.congr (SL3Pair.slEquiv K)
    (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 K), fun θ => ?_⟩
  obtain ⟨A, σ, ε, hε, hθ⟩ := SL3Pair.exists_eq_stdAut (MulAut.congr (SL3Pair.slEquiv K).symm θ)
  have hθ' : θ = MulAut.congr (SL3Pair.slEquiv K) (CFSG.QuasithinUnique.K1.stdAut A σ ε) := by
    rw [← hθ]
    refine MulEquiv.ext fun γ => ?_
    simp [MulAut.congr_apply]
  interval_cases ε
  · exact Or.inl (hθ' ▸ stdAut_zero_mem_indM A σ)
  · right
    rw [hθ', ← map_inv, ← map_mul]
    convert stdAut_zero_mem_indM A σ using 2
    simp [CFSG.QuasithinUnique.K1.stdAut]

end SL3

section Sp4

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjSp fieldSp coe_conjSp
  coe_fieldSp)

variable {K : Type} [Field K]

theorem semilinear_mem_indM_sp4 (A : gsp 2 K) (σ : K ≃+* K) {θ : MulAut ↥(StatedSp 2 K)}
    (hθ : ∀ g, θ g = conjSp 2 K A (fieldSp 2 K σ g)) :
    θ ∈ indM (natAut (StatedSp 2 K)) := by
  refine ⟨matAut (A : GL (Fin 2 ⊕ Fin 2) K) * fieldMap σ, fun γ => ?_⟩
  show matAut _ = _
  apply matAut_semilinear (A : GL (Fin 2 ⊕ Fin 2) K) (γ : GL (Fin 2 ⊕ Fin 2) K) σ
  rw [Subgroup.subtype_apply, hθ γ, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]

variable [Finite K] [CharP K 2]

theorem cover_sp4 :
    ∃ τ : MulAut ↥(StatedSp 2 K), ∀ θ, θ ∈ indM (natAut (StatedSp 2 K)) ∨
      θ * τ⁻¹ ∈ indM (natAut (StatedSp 2 K)) := by
  refine ⟨CFSG.QuasithinUnique.Lin2.Five.tauEquiv, fun θ => ?_⟩
  obtain ⟨A, σ, h | h⟩ := Sp4.exists_aut_eq θ
  · exact Or.inl (semilinear_mem_indM_sp4 A σ h)
  · right
    refine semilinear_mem_indM_sp4 A σ fun g => ?_
    rw [MulAut.mul_apply, h]
    congr 2
    exact CFSG.QuasithinUnique.Lin2.Five.tauEquiv.apply_symm_apply g

end Sp4

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

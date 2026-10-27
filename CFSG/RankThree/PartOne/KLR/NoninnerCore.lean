module

public import CFSG.RankThree.PartOne.KLR.NoninnerAux
public import CFSG.RankThree.PartOne.RF4.Descent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.RankThree.Chevalley.SteinbergBNComponentLocalCoreReduction
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.ReeStabilizer
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldGlue
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.RankThree.Chevalley.SteinbergCFPrimeFieldG2LocalCores
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalFormStabilizer
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.Open
  CFSG.RankThree.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge CFSG.RankThree.LocalRank
  CFSG.ComponentClassification.UnbalancedCatalog

section Noninner

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

local notation "Γ₀" => ReeTag.F4.reeGamma K a

theorem localCoreTrivialOn_noninner (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) :
    LocalCoreTrivialOn p fun α : MulAut Γ₀ => α ∉ (MulAut.conj : Γ₀ →* MulAut Γ₀).range := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  refine localCoreTrivialOn_of_forall hp ?_
  intro B hB α hαn hαp
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form
      a ha K hK
  have hZ := ReeTag.large_Ree_fixed_group_center_trivial a K hK
  let Θ : MulAut Γ₀ →* (K ≃+* K) := SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘ : ∀ (x : Γ₀) (β : K ≃+* K),
      Θ (MulAut.conj x * ReeTag.F4.reeGammaFieldAut K a β) = β := fun x β => by
    rw [← hΨ x β]
    change SemidirectProduct.rightHom (Ψ.symm (Ψ ⟨x, β⟩)) = β
    rw [MulEquiv.symm_apply_apply]
    rfl
  set α' : MulAut Γ₀ := (α : MulAut Γ₀) with hα'
  have hα'ord : orderOf α' = p := by rw [hα', Subgroup.orderOf_coe, hαp]
  have hα'p : α' ^ p = 1 := by
    rw [← hα'ord]
    exact pow_orderOf_eq_one α'
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α'
  have hΘα : Θ α' = σ := by
    rw [hxσ]
    exact hΘ x σ
  have hσp : σ ^ p = 1 := by
    rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 :=
    map_one (ReeTag.F4.reeGammaFieldAutHom K a)
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hαn
    have hαx : α' = MulAut.conj x := by
      rw [hxσ]
      change MulAut.conj x * ReeTag.F4.reeGammaFieldAut K a σ = _
      rw [h, hone, mul_one]
    exact ⟨x, hαx.symm⟩
  have hσ : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp σ hσ α' hα'p
    ⟨x, hxσ⟩
  set δ : MulAut Γ₀ := ReeTag.F4.reeGammaFieldAut K a σ with hδ
  have hhom : ∀ u v : K ≃+* K, ReeTag.F4.reeGammaFieldAut K a u * ReeTag.F4.reeGammaFieldAut K a v =
      ReeTag.F4.reeGammaFieldAut K a (u * v) := fun u v =>
    (map_mul (ReeTag.F4.reeGammaFieldAutHom K a) u v).symm
  have hcommσ : ∀ τ : K ≃+* K, ReeTag.F4.reeGammaFieldAut K a τ * δ =
      δ * ReeTag.F4.reeGammaFieldAut K a τ := fun τ => by
    rw [hδ, hhom, hhom, ringAut_commute τ σ]
  have hinjφ : Function.Injective (ReeTag.F4.reeGammaFieldAutHom K a) := fun s t h => by
    have h1 := hΘ 1 s
    have h2 := hΘ 1 t
    rw [map_one, one_mul] at h1 h2
    exact h1.symm.trans ((congrArg Θ h).trans h2)
  have hδord : orderOf δ = p := by
    have := orderOf_injective _ hinjφ σ
    rwa [hσ] at this
  obtain ⟨b, hkcard, hfixed⟩ := largeRee_fixed_data ha hK hp hp3 σ hσ
  have hFS := largeReeFixedSimple a ha K hK p hp hp3 σ hσ
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hinner : ∀ ρ : fixSubfield σ ≃+* fixSubfield σ,
      ReeTag.F4.reeGammaFieldAut (fixSubfield σ) b ρ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner
          (ReeTag.F4.reeGamma (fixSubfield σ) b) → ρ = 1 := by
    intro ρ hρ
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      exact ringEquiv_eq_one_of_card_eq_prime Nat.prime_two (by simpa using hkcard) ρ
    · obtain ⟨-, hNFk, -⟩ :=
        large_Ree_full_inner_field_automorphism_normal_form
          b hb1 (fixSubfield σ) hkcard
      obtain ⟨y, hy⟩ := hρ
      obtain ⟨q, -, huniq⟩ := hNFk (ReeTag.F4.reeGammaFieldAut (fixSubfield σ) b ρ)
      have hone' : ReeTag.F4.reeGammaFieldAut (fixSubfield σ) b 1 = 1 :=
        map_one (ReeTag.F4.reeGammaFieldAutHom (fixSubfield σ) b)
      have h1 := huniq (1, ρ) (by simp)
      have h2 := huniq (y, 1) (by
        change ReeTag.F4.reeGammaFieldAut (fixSubfield σ) b ρ =
          MulAut.conj y * ReeTag.F4.reeGammaFieldAut (fixSubfield σ) b 1
        rw [hone', mul_one]
        exact hy.symm)
      exact congrArg Prod.snd (h1.trans h2.symm)
  have hS : IsSimpleGroup (CFSG.generalizedFitting ↥(signalizerFixedSubgroup δ)) := by
    have := hFS.1
    rw [CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514.signalizerGeneralizedFitting_eq] at this
    exact this
  have hnc : ¬ IsMulCommutative (CFSG.generalizedFitting ↥(signalizerFixedSubgroup δ)) := by
    rw [isMulCommutative_iff]
    push Not
    have := hFS.2
    rw [CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514.signalizerGeneralizedFitting_eq] at this
    exact this
  exact aschbacherSolvableCore_eq_bot_of_fieldActor hp hZ (fun u v => ringAut_commute u v)
    (ReeTag.F4.reeGammaFieldAutHom K a)
    (fun β => by
      obtain ⟨⟨x, τ⟩, h, -⟩ := hNF β
      exact ⟨x, τ, h⟩) σ hS hnc
    (fun x τ hx hfix => ree_zpowers_of_inner_on_subfield σ hfixed hinner x τ hx hfix) hB α g hg
    hαp

end Noninner

end CFSG.RankThree.PartOne.KLR

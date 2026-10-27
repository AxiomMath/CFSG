module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RawFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6A3StepUnitary
public import CFSG.LocalAnalysis.StandardType.GGTwE6A3PairLayer
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp

public section

namespace CFSG.StandardType.KGL.TwLayer

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.KGL
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.StandardType.TwE6EltSmall
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE CFSG.StandardType.LayerSixE
  CFSG.StandardType.LayerExc CFSG.RankThree.PartOne.KE8F
open scoped MatrixGroups commutatorElement


variable {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem rootSL2_WSL_mem_Γ_raw (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) :
    rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ WSL ∈
      (LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0).Γ := by
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h₁ := ennola_step_pinnedX (rawTwLang (σ := σ) Fr hFr v g0 hg0C hg0) hv hK hγ 1
  have h₂ := ennola_step_pinnedX (rawTwLang (σ := σ) Fr hFr v g0 hg0C hg0) hv hK
    (IsRoot.neg hγ) 1
  rw [map_one] at h₁ h₂
  rw [neg_neg] at h₂
  exact mem_Γ_of_mem_model_of_mul_self Nat.prime_two hn hK hσ hFr _ rfl
    (LangRat.rootSL2_WSL_mem_model _ hγ h₁ h₂) (LangRat.rootSL2_WSL_mul_self γ)

theorem a3_E0_data (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (hαβ : iform α β = 0) :
    ∃ E0 : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)), CFSG.IsQuasisimple E0 ∧
      E0 ≤ (LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0).Γ ∧
      E0 ≤ Subgroup.centralizer
        {rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α + kgExpVec β))} ∧
      ∀ μ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 μ → iform μ α = 0 → iform μ β = 0 →
        rootSL2 Tag.E6 (AlgebraicClosure K) μ WSL ∈ E0 := by
  classical
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := AlgebraicClosure K with hL
  set D := LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0 with hD
  obtain ⟨u, hUeq, hlayer⟩ := ggLayerOf_pair_A3 ζ hζ hζo hα hβ hαβ
  have hstep : ∀ γ, IsRoot Tag.E6 γ → ∀ c,
      D.step (pinnedX Tag.E6 L γ c) = pinnedX Tag.E6 L (-γ) (Fr c) := fun γ hγ c =>
    ennola_step_pinnedX (rawTwLang (σ := σ) Fr hFr v g0 hg0C hg0) hv hK hγ c
  let σ' : L ≃+* L := twFrobEquiv Fr hFr
  have hσ'1 : σ'.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hσ' : ∀ c, σ' c = c ^ 2 ^ n := hFr
  have hfixq : CFSG.IsQuasisimple (fixSubgroup (stdUnitaryEquiv (ν := 4) σ')) :=
    (stdUnitary_fixSubgroup (ν := 4) Nat.prime_two (f := n) hn σ' hσ' (by norm_num)).2.1
      (by simp)
  set U := rootSpan Tag.E6 L
    (famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)}) with hU
  set E0 := U ⊓ D.step.eqLocus (MonoidHom.id _) with hE0
  have hE0eq : E0 = (fixSubgroup (stdUnitaryEquiv (ν := 4) σ')).map (rhoSigmaE6A3 L u) := by
    rw [hE0, hUeq]
    exact inf_eqLocus_eq_map_fix Fr D.step hstep u σ' hσ'1
  have hE0q : CFSG.IsQuasisimple E0 := by
    rw [hE0eq]
    exact (CFSG.IsQuasisimple.congr (Subgroup.equivMapOfInjective _ _
      (rhoSigmaE6A3_injective u))).mp hfixq
  have hE0model : E0 ≤ D.model := fun x hx =>
    D.mem_model.2 ⟨rootSpan_le_adjointGroup L _ hx.1, hx.2⟩
  have hE0Γ : E0 ≤ D.Γ := by
    have h1 : ⁅E0, E0⁆ = E0 := Subgroup.isPerfect_iff.mp hE0q.1
    have h2 := Subgroup.commutator_mono hE0model hE0model
    rw [h1] at h2
    exact h2
  have hΓmodel : D.Γ ≤ D.model := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact D.model.mul_mem (D.model.mul_mem (D.model.mul_mem ha hb) (D.model.inv_mem ha))
      (D.model.inv_mem hb)
  have hΓfix : D.Γ ≤ D.step.eqLocus (MonoidHom.id _) := fun x hx => (D.mem_model.1 (hΓmodel hx)).2
  refine ⟨E0, hE0q, hE0Γ, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := hlayer.1 hx.1
    have hg' := mem_famCentralizer.1 hg
    have hA := hg' (zetaVec ζ hζ (kgExpVec α)) (Set.mem_insert _ _)
    have hB := hg' (zetaVec ζ hζ (kgExpVec β)) (Set.mem_insert_of_mem _ rfl)
    have hA' := mul_inv_eq_iff_eq_mul.1 hA
    have hB' := mul_inv_eq_iff_eq_mul.1 hB
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [CFSG.StandardType.ExcFrames.zetaVec_add, rootDiagUnit_mul]
    calc rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) *
          rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec β)) * (g : ModGL Tag.E6 L) =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) *
          (rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec β)) * (g : ModGL Tag.E6 L)) :=
          mul_assoc _ _ _
      _ = rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) *
          ((g : ModGL Tag.E6 L) * rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec β))) := by
          rw [hB']
      _ = (rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) * (g : ModGL Tag.E6 L)) *
          rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec β)) := (mul_assoc _ _ _).symm
      _ = ((g : ModGL Tag.E6 L) * rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α))) *
          rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec β)) := by rw [hA']
      _ = (g : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) *
          rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec β))) := mul_assoc _ _ _
  · intro μ hμ hμα hμβ
    have hS := famKernel_kgExpVec_pair hζo hζ hα hβ
    have hμS : μ ∈ famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} := by
      rw [hS]
      exact ⟨hμ, hμα, hμβ⟩
    have hnα : iform (τ := Tag.E6) (-μ) α = 0 := by
      rw [iform_neg_left (τ := Tag.E6) μ α, hμα, neg_zero]
    have hnβ : iform (τ := Tag.E6) (-μ) β = 0 := by
      rw [iform_neg_left (τ := Tag.E6) μ β, hμβ, neg_zero]
    have hnμS : -μ ∈ famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} := by
      rw [hS]
      exact ⟨IsRoot.neg hμ, hnα, hnβ⟩
    have hmemU : rootSL2 Tag.E6 L μ WSL ∈ U :=
      rootRankOneGroup_le_rootSpan hμ hμS hnμS (MonoidHom.mem_range.2 ⟨WSL, rfl⟩)
    have hmemΓ : rootSL2 Tag.E6 L μ WSL ∈ D.Γ :=
      rootSL2_WSL_mem_Γ_raw hn hK hσ Fr hFr v hv g0 hg0C hg0 hμ
    exact ⟨hmemU, hΓfix hmemΓ⟩

end CFSG.StandardType.KGL.TwLayer

end

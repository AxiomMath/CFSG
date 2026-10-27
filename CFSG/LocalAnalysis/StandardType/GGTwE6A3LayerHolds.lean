module

public import CFSG.LocalAnalysis.StandardType.GGTwE6A3StepUnitary
public import CFSG.LocalAnalysis.StandardType.GGTwE6SUFixEquiv
public import CFSG.LocalAnalysis.StandardType.GGTwE6A3PairLayer
public import CFSG.LocalAnalysis.StandardType.GGTwE6RawFrame

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.KGL
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.StandardType.TwE6EltSmall
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE CFSG.StandardType.LayerSixE
  CFSG.StandardType.LayerExc CFSG.RankThree.PartOne.KE8F CFSG.StandardType.KGL.TwLayer
open scoped MatrixGroups commutatorElement


theorem ggTwE6A3LayerInput_holds : GGTwE6A3LayerInput := by
  intro n hn h3 K _ _ σ hK hσ Fr hFr v hv g0 hg0C hg0 α β hα hβ hαβ ζ hζ hζ1 ta hta tb htb hta' htb'
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ hζ1
  set L := AlgebraicClosure K with hL
  set D := LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0 with hD
  have hα' : IsRoot Tag.E6 α := hα
  have hβ' : IsRoot Tag.E6 β := hβ
  obtain ⟨u, hUeq, hlayer⟩ := ggLayerOf_pair_A3 ζ hζ hζo hα' hβ' hαβ
  have hstep : ∀ γ, IsRoot Tag.E6 γ → ∀ c,
      D.step (pinnedX Tag.E6 L γ c) = pinnedX Tag.E6 L (-γ) (Fr c) := fun γ hγ c =>
    ennola_step_pinnedX (rawTwLang (σ := σ) Fr hFr v g0 hg0C hg0) hv hK hγ c
  let σ' : L ≃+* L := twFrobEquiv Fr hFr
  have hσ'1 : σ'.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hσ' : ∀ c, σ' c = c ^ 2 ^ n := hFr
  have hfixq : CFSG.IsQuasisimple (fixSubgroup (stdUnitaryEquiv (ν := 4) σ')) :=
    (stdUnitary_fixSubgroup (ν := 4) Nat.prime_two (f := n) hn σ' hσ' (by norm_num)).2.1
      (by simp)
  set X' := (famCentralizer {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)}).map
    (adjointGroup Tag.E6 L).subtype with hX'
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
  have hlayerΓ : GGLayerOf (D.Γ ⊓ X') E0 :=
    ggLayerOf_inf_eqLocus D.step hlayer hΓfix hE0Γ hE0q
  set C0 := twistedE6RootGroup K σ with hC0
  let Θ : ↥C0 →* ModGL TwistTag.E6.tag L := (twThetaHom g0).comp C0.subtype
  have hΘinj : Function.Injective Θ :=
    (twThetaHom_injective g0).comp (Subgroup.subtype_injective _)
  have hrange : Θ.range = D.Γ := range_twThetaHom_eq_Γ hn hK hσ Fr hFr v g0 hg0C hg0
  have hdα : rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (kgExpVec α)) = twThetaHom g0 ta := by
    rw [twThetaHom_apply, hta', corootTuple_eq_zetaVec_kg ζ hζ α] <;> rfl
  have hdβ : rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (kgExpVec β)) = twThetaHom g0 tb := by
    rw [twThetaHom_apply, htb', corootTuple_eq_zetaVec_kg ζ hζ β] <;> rfl
  have key : ∀ (t : ModGL TwistTag.E6.tag K) (a : Fin Tag.E6.rank → Lˣ),
      rootDiagUnit TwistTag.E6.tag a = twThetaHom g0 t → ∀ c : ModGL TwistTag.E6.tag K,
        (rootDiagUnit TwistTag.E6.tag a * twThetaHom g0 c * (rootDiagUnit TwistTag.E6.tag a)⁻¹ =
          twThetaHom g0 c ↔ t * c = c * t) := by
    intro t a hta c
    rw [hta, ← map_inv, ← map_mul, ← map_mul, (twThetaHom_injective g0).eq_iff]
    constructor
    · intro h
      calc t * c = (t * c * t⁻¹) * t := by group
        _ = c * t := by rw [h]
    · intro h
      rw [h]
      group
  have hmap : ((Subgroup.centralizer ({ta, tb} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
      C0).map Θ = D.Γ ⊓ X' := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcΓ : Θ c ∈ D.Γ := by
        rw [← hrange]
        exact ⟨c, rfl⟩
      refine ⟨hcΓ, ⟨⟨Θ c, (D.mem_model.1 (hΓmodel hcΓ)).1⟩, ?_, rfl⟩⟩
      intro a ha
      have hc' : ∀ h ∈ ({ta, tb} : Set (ModGL TwistTag.E6.tag K)),
          h * (c : ModGL TwistTag.E6.tag K) = (c : ModGL TwistTag.E6.tag K) * h :=
        Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hc)
      rcases ha with rfl | ha
      · exact (key ta _ hdα c).2 (hc' ta (Set.mem_insert _ _))
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        exact (key tb _ hdβ c).2 (hc' tb (Set.mem_insert_of_mem _ rfl))
    · rintro ⟨hyΓ, g, hgF, rfl⟩
      rw [← hrange] at hyΓ
      obtain ⟨c, hc⟩ := hyΓ
      refine ⟨c, Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_iff.2 ?_), hc⟩
      intro h hh
      have hgF' := mem_famCentralizer.1 hgF
      have hΘc : twThetaHom g0 (c : ModGL TwistTag.E6.tag K) =
          ((g : ↥(adjointGroup Tag.E6 L)) : ModGL Tag.E6 L) := hc
      have hA := hgF' (zetaVec ζ hζ (kgExpVec α)) (Set.mem_insert _ _)
      have hB := hgF' (zetaVec ζ hζ (kgExpVec β)) (Set.mem_insert_of_mem _ rfl)
      rw [← hΘc] at hA hB
      rcases hh with hh | hh
      · rw [hh]
        exact (key ta (zetaVec ζ hζ (kgExpVec α)) hdα c).1 hA
      · rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (key tb (zetaVec ζ hζ (kgExpVec β)) hdβ c).1 hB
  have hlayerC : GGLayerOf
      ((Subgroup.centralizer ({ta, tb} : Set (ModGL TwistTag.E6.tag K))).subgroupOf C0)
      (E0.comap Θ) :=
    ggLayerOf_comap Θ hΘinj (by rw [hmap]; exact hlayerΓ)
  have key3 : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → iform γ α = 0 → iform γ β = 0 →
      ∀ tc ∈ twistedE6InndiagGL K σ,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) tc * g0 =
            rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) →
          tc ∈ (E0.comap Θ).map C0.subtype := by
    intro γ hγ hγα hγβ tc htc hθ
    have hθ' : twThetaHom g0 tc =
        rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) := by
      rw [twThetaHom_apply]
      exact hθ
    have hS := famKernel_kgExpVec_pair hζo hζ hα' hβ'
    have hγS : γ ∈ famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} := by
      rw [hS]
      exact ⟨hγ, hγα, hγβ⟩
    have hnα : iform (τ := Tag.E6) (-γ) α = 0 := by
      rw [iform_neg_left (τ := Tag.E6) γ α, hγα, neg_zero]
    have hnβ : iform (τ := Tag.E6) (-γ) β = 0 := by
      rw [iform_neg_left (τ := Tag.E6) γ β, hγβ, neg_zero]
    have hnγS : -γ ∈ famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} := by
      rw [hS]
      exact ⟨IsRoot.neg hγ, hnα, hnβ⟩
    have hmemU : twThetaHom g0 tc ∈ U := by
      rw [hθ', ← rootSL2_HSL_eq_rootDiagUnit_corootTuple hγ ζ]
      exact rootRankOneGroup_le_rootSpan hγ hγS hnγS (MonoidHom.mem_range.2 ⟨HSL ζ, rfl⟩)
    have hmemE0 : twThetaHom g0 tc ∈ E0 :=
      ⟨hmemU, (D.mem_model.1 (twThetaHom_mem_model hσ Fr hFr v g0 hg0C hg0 htc)).2⟩
    have hmemΓ : twThetaHom g0 tc ∈ D.Γ := hE0Γ hmemE0
    rw [← hrange] at hmemΓ
    obtain ⟨c, hc⟩ := hmemΓ
    have hct : (c : ModGL TwistTag.E6.tag K) = tc := twThetaHom_injective g0 hc
    refine ⟨c, ?_, hct⟩
    show Θ c ∈ E0
    rw [show Θ c = twThetaHom g0 tc from hc]
    exact hmemE0
  refine ⟨E0.comap Θ, hlayerC, ?_, ?_⟩
  · obtain ⟨e⟩ := nonempty_statedSU_equiv_fixSubgroup (ν := 4) (L := L)
      Nat.prime_two hn σ' hσ' (by norm_num) K hK
    have h1 : (E0.comap Θ).map Θ = E0 := Subgroup.map_comap_eq_self (hrange ▸ hE0Γ)
    let f1 : ↥(E0.comap Θ) ≃* ↥((E0.comap Θ).map Θ) := Subgroup.equivMapOfInjective _ Θ hΘinj
    let f2 : ↥((E0.comap Θ).map Θ) ≃* ↥E0 := MulEquiv.subgroupCongr h1
    let f3 : ↥E0 ≃* ↥((fixSubgroup (stdUnitaryEquiv (ν := 4) σ')).map (rhoSigmaE6A3 L u)) :=
      MulEquiv.subgroupCongr hE0eq
    let f4 : ↥(fixSubgroup (stdUnitaryEquiv (ν := 4) σ')) ≃*
        ↥((fixSubgroup (stdUnitaryEquiv (ν := 4) σ')).map (rhoSigmaE6A3 L u)) :=
      Subgroup.equivMapOfInjective _ _ (rhoSigmaE6A3_injective u)
    exact ⟨f1.trans (f2.trans (f3.trans (f4.symm.trans e.symm)))⟩
  · exact key3

end CFSG.StandardType.KGL

end

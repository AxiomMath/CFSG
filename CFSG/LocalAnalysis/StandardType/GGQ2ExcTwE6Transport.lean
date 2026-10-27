module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Datum
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreCompNormal
import CFSG.LocalAnalysis.StandardType.GGQ2ModelFrameMap
import CFSG.LocalAnalysis.StandardType.GGQ2HeartJLang
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenFrame
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusAut
import CFSG.LocalAnalysis.StandardType.GGTwE6D4RootFacts
import CFSG.LieType.Chevalley.TwistedE6RootGroupPerfect
import CFSG.LieType.SeitzGeneration.ExcTorusCount
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A5

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
  CFSG.RankThree.PartOne.KE CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.TwE6ThreeRootGen
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.HardMathSupport.Lang.E6Descent

noncomputable section

private theorem twTr_zetaDiag_mem_twistedTorus
    {K : Type} [Field K] [Finite K]
    (hK1 : Nat.card K = (2 ^ 1) ^ 2)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) (x : Fin Tag.E6.rank → ZMod 3) :
    rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
        (twistHom TwistTag.E6 (AlgebraicClosure K) Fr) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2) (by rw [hK1]; norm_num)
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have h : rootDiagUnit Tag.E6 (zetaVec ζ hζ x) ∈
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.twE6EnnolaDatum (ℓ := 2) (Ω := AlgebraicClosure K)
        (K := K) Nat.prime_two le_rfl hK1 hFr).torus := by
    refine (CFSG.LocalAnalysis.GLTheoremA.Y10F.twE6EnnolaDatum_torus (ℓ := 2)
      (Ω := AlgebraicClosure K) (K := K) Nat.prime_two le_rfl hK1 hFr).2 (fun i => ?_)
    have h3 := CFSG.StandardType.KGL.TwLayer.zetaVec_apply_pow_three hζ x i
    simpa using h3
  exact h

private theorem twTr_compNormal_congr {M : Type} [Group M] {H₁ H₂ E₁ E₂ : Subgroup M}
    {R : RawFrameData} (hH : H₁ = H₂) (hE : E₁ = E₂) {mf : ModelFrame H₁ E₁ R}
    (hmf : mf.CompNormal) : (hH ▸ hE ▸ mf : ModelFrame H₂ E₂ R).CompNormal := by
  subst hH
  subst hE
  exact hmf

theorem excTwE6ModelFrame_of_core
    (hO2 : ExcCoreOccurs 2 .E6) (hM2 : ExcCoreMarked 2 .E6) (hC2 : ExcCoreCent 2 .E6)
    (hI2 : ExcCoreInside 2 .E6) (hN2 : ExcCoreNormalizer 2 .E6) (hA2 : ExcCoreAmbient 2 .E6)
    (hO3 : ExcCoreOccurs 3 .E6) (hM3 : ExcCoreMarked 3 .E6) (hC3 : ExcCoreCent 3 .E6)
    (hI3 : ExcCoreInside 3 .E6) (hN3 : ExcCoreNormalizer 3 .E6) (hA3 : ExcCoreAmbient 3 .E6) :
    ExcTwE6ModelFrame := by
  classical
  intro K _ _ σ hK4 hσ2 A hA hAΓ h5 hsc
  have hK1 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK4]; norm_num
  have hσ1 : ∀ c, σ c = c ^ 2 ^ 1 := by simpa using hσ2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2) (by rw [hK4]; norm_num)
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have : ExpChar (AlgebraicClosure K) 2 := ExpChar.prime Nat.prime_two
  obtain ⟨ζ, hζp⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) Nat.prime_two Nat.prime_three (by norm_num)
  have hζ : ζ ^ 3 = 1 := hζp.pow_eq_one
  have hζo : orderOf ζ = 3 := hζp.eq_orderOf.symm
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 1
  have hFr : ∀ c, Fr c = c ^ 2 ^ 1 :=
    fun c => iterateFrobenius_def (R := AlgebraicClosure K) 2 1 c
  let A' : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) :=
    (A.subgroupOf (RecipeExcLang.twInndiagGroup K σ)).map (RecipeExcLang.twConj K σ)
  have hA' : CFSG.Open.IsElemAbelian 3 A' := (hA.subgroupOf _).map _
  have hAH' : ∀ a ∈ A', ∃ φ ∈ (RecipeExcLang.twConj K σ).range,
      ∀ l : ↥(twistedE6RootGroup K σ), φ l = a l := by
    rintro a ha
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨_, ⟨w, rfl⟩, fun l => rfl⟩
  have h5' : 3 ^ 5 ≤ Nat.card A' := by
    rw [show Nat.card A' = Nat.card ↥(A.subgroupOf (RecipeExcLang.twInndiagGroup K σ)) from
      Subgroup.card_map_of_injective
        (NoOffTwE6Three.twConj_injective (n := 1) le_rfl hK1 σ hσ1)]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAΓ).toEquiv]
    exact h5
  have hsc' : GGTorusSelfCent 3 A' := by
    intro n hn hn3
    have hn3' : (n : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
      have h := congrArg Subtype.val hn3
      simpa using h
    have hncomm : ∀ a ∈ A,
        a * (n : ModGL TwistTag.E6.tag K) = (n : ModGL TwistTag.E6.tag K) * a := by
      intro a ha
      have hmem : RecipeExcLang.twConj K σ ⟨a, hAΓ ha⟩ ∈ A' :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
      have h1 := hn _ hmem
      have h2 : ((RecipeExcLang.twConj K σ ⟨a, hAΓ ha⟩) n : ModGL TwistTag.E6.tag K) =
          (n : ModGL TwistTag.E6.tag K) := congrArg Subtype.val h1
      rw [RecipeExcLang.coe_twConj] at h2
      calc a * (n : ModGL TwistTag.E6.tag K)
          = (a * (n : ModGL TwistTag.E6.tag K) * a⁻¹) * a := by group
        _ = (n : ModGL TwistTag.E6.tag K) * a := by rw [h2]
    have hnA : (n : ModGL TwistTag.E6.tag K) ∈ A := hsc _ n.2 hncomm hn3'
    refine Subgroup.mem_map.mpr ⟨⟨(n : ModGL TwistTag.E6.tag K), hAΓ hnA⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hnA
    · refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [RecipeExcLang.coe_twConj, MulAut.conj_apply]
      rfl
  have hperf : commutator ↥(twistedE6RootGroup K σ) = ⊤ :=
    CFSG.LieType.Chevalley.commutator_twistedE6RootGroup_eq_top Nat.prime_two le_rfl hK1 σ hσ1
  obtain ⟨g, κ, t, -, hg, hgF, hκinj, hκrange, ht, hconj, -, -, -, -⟩ :=
    exists_frame_torus (n := 1) le_rfl hK1 σ hσ1 (by norm_num) hFr hζ hζo
      (L' := ↥(twistedE6RootGroup K σ)) (ψ₀ := MonoidHom.id _)
      (fun x => ⟨x, rfl⟩) bot_le hperf hA' hAH' h5' hsc'
  let n₀ : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0
  have hgF' : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g = g * n₀ := hgF
  have htx_adjoint : ∀ x : Fin 6 → ZMod 3,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) ∈
        adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    intro x
    rw [ht x]
    have hd : rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) ∈
        adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
      CFSG.StandardType.ExcFrames.rootDiagUnit_mem_adjointGroup _
    exact (adjointGroup TwistTag.E6.tag (AlgebraicClosure K)).mul_mem
      ((adjointGroup TwistTag.E6.tag (AlgebraicClosure K)).mul_mem hg hd)
      ((adjointGroup TwistTag.E6.tag (AlgebraicClosure K)).inv_mem hg)
  have htx_fixed : ∀ x : Fin 6 → ZMod 3,
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x)) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) := by
    intro x
    have hdt := twTr_zetaDiag_mem_twistedTorus (K := K) hK1 hζ hFr x
    have hdfix : twistHom TwistTag.E6 (AlgebraicClosure K) Fr
        (rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x)) =
        n₀⁻¹ * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) * n₀ := by
      have h := (mem_twistedTorusOf (n := n₀)
        (Φ := twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).1 hdt |>.2
      calc twistHom TwistTag.E6 (AlgebraicClosure K) Fr
            (rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x))
          = n₀⁻¹ * (n₀ * twistHom TwistTag.E6 (AlgebraicClosure K) Fr
              (rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x)) * n₀⁻¹) * n₀ := by group
        _ = n₀⁻¹ * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) * n₀ := by rw [h]
    calc twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x))
        = twistHom TwistTag.E6 (AlgebraicClosure K) Fr
            (g * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) * g⁻¹) := by
          rw [ht x]; rfl
      _ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr g *
            twistHom TwistTag.E6 (AlgebraicClosure K) Fr
              (rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x)) *
            (twistHom TwistTag.E6 (AlgebraicClosure K) Fr g)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = (g * n₀) * (n₀⁻¹ * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) * n₀) * (g * n₀)⁻¹ := by
          rw [hgF', hdfix]
      _ = g * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) * g⁻¹ := by group
      _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) := (ht x).symm
  have htx_mem : ∀ x : Fin 6 → ZMod 3, t x ∈ RecipeExcLang.twInndiagGroup K σ := by
    intro x
    obtain ⟨w, hw, hwv⟩ := RecipeExcLang.exists_mem_twInndiag_of_twist_fixed (n := 1) le_rfl
      hK1 hσ1 (Fr := Fr) hFr (htx_adjoint x) (htx_fixed x)
    have hwt : w = t x :=
      CFSG.LieType.Chevalley.baseChangeGL_injective
        (algebraMap K (AlgebraicClosure K)) hwv
    rwa [hwt] at hw
  let κA : ↥A → Multiplicative (Fin 6 → ZMod 3) := fun a =>
    κ ⟨RecipeExcLang.twConj K σ ⟨(a : ModGL TwistTag.E6.tag K), hAΓ a.2⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr a.2)⟩
  have ha_eq : ∀ a : ↥A,
      (a : ModGL TwistTag.E6.tag K) = t (Multiplicative.toAdd (κA a)) := by
    intro a
    let a' : A' := ⟨RecipeExcLang.twConj K σ ⟨(a : ModGL TwistTag.E6.tag K), hAΓ a.2⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr a.2)⟩
    have heq : RecipeExcLang.twConj K σ ⟨(a : ModGL TwistTag.E6.tag K), hAΓ a.2⟩ =
        RecipeExcLang.twConj K σ ⟨t (Multiplicative.toAdd (κA a)), htx_mem _⟩ := by
      refine MulEquiv.ext fun l => Subtype.ext ?_
      have h1 := hconj a' l
      change (((a' : MulAut ↥(twistedE6RootGroup K σ)) l : ↥(twistedE6RootGroup K σ)) :
          ModGL TwistTag.E6.tag K) =
        ((RecipeExcLang.twConj K σ ⟨t (Multiplicative.toAdd (κA a)), htx_mem _⟩) l :
          ModGL TwistTag.E6.tag K)
      rw [RecipeExcLang.coe_twConj]
      exact h1
    have heq' : (⟨(a : ModGL TwistTag.E6.tag K), hAΓ a.2⟩ :
        ↥(RecipeExcLang.twInndiagGroup K σ)) =
        ⟨t (Multiplicative.toAdd (κA a)), htx_mem _⟩ :=
      NoOffTwE6Three.twConj_injective (n := 1) le_rfl hK1 σ hσ1 heq
    exact congrArg Subtype.val heq'
  obtain ⟨S, e, he, hρ, hq, hAlg, htor⟩ :=
    CFSG.StandardType.ggQ2HeartJ_langSetup (K := K) (σ := σ) (n := 1) le_rfl hK1 hσ1 Fr hFr
      g hg hgF
  have hS : NegLangTwo S := ⟨by simpa using hq, hAlg, fun γ _ => hρ γ⟩
  let φ : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K (AlgebraicClosure K)))
  have hφ_apply : ∀ y, φ y = g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) y * g := by
    intro y
    change MulAut.conj g⁻¹ (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) y * g
    rw [MulAut.conj_apply, inv_inv]
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * g =
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) y * g := by
      rw [← hφ_apply x, ← hφ_apply y]
      exact hxy
    exact CFSG.LieType.Chevalley.baseChangeGL_injective
      (algebraMap K (AlgebraicClosure K)) (mul_left_cancel (mul_right_cancel h1))
  have hC₀map : (twistedE6RootGroup K σ).map φ = S.Γ := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      have hφx : φ x = (e ⟨x, hx⟩ : ModGL Tag.E6 (AlgebraicClosure K)) := by
        rw [hφ_apply]
        exact (he ⟨x, hx⟩).symm
      rw [hφx]
      exact (e ⟨x, hx⟩).2
    · intro y hy
      refine ⟨((e.symm ⟨y, hy⟩ : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K),
        (e.symm ⟨y, hy⟩).2, ?_⟩
      have hφx : φ ((e.symm ⟨y, hy⟩ : ↥(twistedE6RootGroup K σ)) :
          ModGL TwistTag.E6.tag K) =
          (e (e.symm ⟨y, hy⟩) : ModGL Tag.E6 (AlgebraicClosure K)) := by
        rw [hφ_apply]
        exact (he (e.symm ⟨y, hy⟩)).symm
      rw [hφx]
      simp
  have hφ_diag : ∀ a : ↥A,
      φ (a : ModGL TwistTag.E6.tag K) =
        rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (Multiplicative.toAdd (κA a))) := by
    intro a
    rw [hφ_apply, ha_eq a, ht]
    group; rfl
  have hκA_range : ∀ a : ↥A,
      Multiplicative.ofAdd (Multiplicative.toAdd (κA a)) ∈ κ.range := by
    intro a
    exact MonoidHom.mem_range.mpr
      ⟨⟨RecipeExcLang.twConj K σ ⟨(a : ModGL TwistTag.E6.tag K), hAΓ a.2⟩,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr a.2)⟩, rfl⟩
  have hT_of : ∀ U : AddSubgroup (Fin Tag.E6.rank → ZMod 3),
      zetaTorus ζ hζ U ≤ fullThreeTorus S := by
    intro U y hy
    obtain ⟨x, -, rfl⟩ := (mem_zetaTorus (ζ := ζ) (hζ := hζ) (U := U)).1 hy
    refine ⟨(htor (zetaVec ζ hζ x)).2 (fun i => ?_), ?_⟩
    · have h3 := CFSG.StandardType.KGL.TwLayer.zetaVec_apply_pow_three hζ x i
      simpa using h3
    · have hcube : (zetaVec ζ hζ x) ^ 3 = 1 :=
        funext fun i => CFSG.StandardType.KGL.TwLayer.zetaVec_apply_pow_three hζ x i
      rw [rootDiagUnit_pow, hcube, rootDiagUnit_one]
  rcases hκrange with htop | hhyp
  · have hAmap : A.map φ = zetaTorus ζ hζ ⊤ := by
      refine le_antisymm ?_ ?_
      · rintro y ⟨a, ha, rfl⟩
        exact (mem_zetaTorus (ζ := ζ) (hζ := hζ) (U := ⊤)).2
          ⟨Multiplicative.toAdd (κA ⟨a, ha⟩), AddSubgroup.mem_top _,
            (hφ_diag ⟨a, ha⟩).symm⟩
      · rintro y hy
        obtain ⟨x, -, rfl⟩ := (mem_zetaTorus (ζ := ζ) (hζ := hζ) (U := ⊤)).1 hy
        have hx : Multiplicative.ofAdd x ∈ κ.range := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨a', ha'⟩ := MonoidHom.mem_range.mp hx
        obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp a'.2
        refine Subgroup.mem_map.mpr ⟨(w : ModGL TwistTag.E6.tag K),
          Subgroup.mem_subgroupOf.mp hw, ?_⟩
        have hκw : κA ⟨(w : ModGL TwistTag.E6.tag K), Subgroup.mem_subgroupOf.mp hw⟩ =
            Multiplicative.ofAdd x := by
          have h1 : κA ⟨(w : ModGL TwistTag.E6.tag K), Subgroup.mem_subgroupOf.mp hw⟩ = κ a' :=
            congrArg κ (Subtype.ext hweq)
          rw [h1]
          exact ha'
        rw [hφ_diag ⟨(w : ModGL TwistTag.E6.tag K), Subgroup.mem_subgroupOf.mp hw⟩, hκw]
        rfl
    obtain ⟨d⟩ := nonempty_excCoordDatum_two S hζ hζo (hT_of ⊤)
    obtain ⟨mf, hmfN⟩ := exists_compNormal_modelFrame_of_core hO2 hM2 hC2 hI2 hN2 hA2 S hS d
    have hmf' : (hC₀map.symm ▸ hAmap.symm ▸ mf : ModelFrame
        ((twistedE6RootGroup K σ).map φ) (A.map φ) (excRaw 2)).CompNormal :=
      twTr_compNormal_congr hC₀map.symm hAmap.symm hmfN
    exact Or.inl (exists_compNormal_modelFrame_of_map hφinj _ hmf')
  · have hAmap : A.map φ = zetaTorus ζ hζ hypE6 := by
      refine le_antisymm ?_ ?_
      · rintro y ⟨a, ha, rfl⟩
        exact (mem_zetaTorus (ζ := ζ) (hζ := hζ) (U := hypE6)).2
          ⟨Multiplicative.toAdd (κA ⟨a, ha⟩), (hhyp _).1 (hκA_range ⟨a, ha⟩),
            (hφ_diag ⟨a, ha⟩).symm⟩
      · rintro y hy
        obtain ⟨x, hx, rfl⟩ := (mem_zetaTorus (ζ := ζ) (hζ := hζ) (U := hypE6)).1 hy
        have hxr : Multiplicative.ofAdd x ∈ κ.range := (hhyp x).2 hx
        obtain ⟨a', ha'⟩ := MonoidHom.mem_range.mp hxr
        obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp a'.2
        refine Subgroup.mem_map.mpr ⟨(w : ModGL TwistTag.E6.tag K),
          Subgroup.mem_subgroupOf.mp hw, ?_⟩
        have hκw : κA ⟨(w : ModGL TwistTag.E6.tag K), Subgroup.mem_subgroupOf.mp hw⟩ =
            Multiplicative.ofAdd x := by
          have h1 : κA ⟨(w : ModGL TwistTag.E6.tag K), Subgroup.mem_subgroupOf.mp hw⟩ = κ a' :=
            congrArg κ (Subtype.ext hweq)
          rw [h1]
          exact ha'
        rw [hφ_diag ⟨(w : ModGL TwistTag.E6.tag K), Subgroup.mem_subgroupOf.mp hw⟩, hκw]
        rfl
    obtain ⟨d⟩ := nonempty_excCoordDatum_three S hζ hζo (hT_of hypE6)
    obtain ⟨mf, hmfN⟩ := exists_compNormal_modelFrame_of_core hO3 hM3 hC3 hI3 hN3 hA3 S hS d
    have hmf' : (hC₀map.symm ▸ hAmap.symm ▸ mf : ModelFrame
        ((twistedE6RootGroup K σ).map φ) (A.map φ) (excRaw 3)).CompNormal :=
      twTr_compNormal_congr hC₀map.symm hAmap.symm hmfN
    exact Or.inr (exists_compNormal_modelFrame_of_map hφinj _ hmf')

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end

module

public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamF4Orbit
public import CFSG.LocalAnalysis.StandardType.GGFamF4Shapes
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeModelsPart1
import CFSG.LocalAnalysis.StandardType.GGFamInnerCover
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart1
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3AlgebraicPart3
import CFSG.LieType.Chevalley.WeylRootTransport
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.F4ExplicitPos CFSG.StandardType.F4ExplicitPos.C3Range
  CFSG.StandardType.F4ExplicitPos.SelectedLiteral CFSG.SeitzReduction.F4Pilot

private noncomputable def l10lH4_conjRootSpanEquiv (K : Type) [CommRing K]
    (v : WeylGroup Tag.F4) (S : Set (Fin Tag.F4.rank → ℤ))
    (hS : ∀ α ∈ S, IsRoot Tag.F4 α) :
    ↥(rootSpan Tag.F4 K S) ≃* ↥(rootSpan Tag.F4 K ((fun α => v • α) '' S)) :=
  (Subgroup.equivMapOfInjective (rootSpan Tag.F4 K S)
    (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K v)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K v)).injective).trans
  (MulEquiv.subgroupCongr ((canonical_weyl_root_transport Tag.F4 K).1 v S hS))

private noncomputable def l10lH4_c3Equiv (K : Type) [Field K] [Finite K] [CharP K 2] :
    ↥(StatedSp 3 K) ≃* ↥(rootSpan Tag.F4 K C3Range.c3RootSet) := by
  let fC : ↥(StatedSp 3 K) →* ModGL Tag.F4 K :=
    (adjointGroup Tag.F4 K).subtype.comp (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOf K)
  have hfC : Function.Injective fC :=
    (Subgroup.subtype_injective (adjointGroup Tag.F4 K)).comp
      (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOf_injective K)
  exact (MonoidHom.ofInjective hfC).trans
    (MulEquiv.subgroupCongr
      (CFSG.StandardType.F4ExplicitPos.C3Algebraic.range_eq_rootSpan_alg
        (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOf K)
        (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOf_x K)))

private noncomputable def l10lH4_c3EquivV (K : Type) [Field K] [Finite K] [CharP K 2]
    (v : WeylGroup Tag.F4) :
    ↥(StatedSp 3 K) ≃* ↥(rootSpan Tag.F4 K ((fun α => v • α) '' C3Range.c3RootSet)) :=
  (l10lH4_c3Equiv K).trans
    (l10lH4_conjRootSpanEquiv K v C3Range.c3RootSet
      (fun _ hα => C3Range.isRoot_of_mem_c3RootSet hα))

private noncomputable def l10lH4_b3Equiv (K : Type) [Field K] [Finite K] [CharP K 2]
    [Algebra (ZMod 2) K] [Algebra.IsAlgebraic (ZMod 2) K] :
    ↥(StatedSp 3 K) ≃* ↥(rootSpan Tag.F4 K CFSG.SeitzReduction.F4Pilot.b3LeviRoots) := by
  let fB : ↥(StatedSp 3 K) →* ModGL Tag.F4 K :=
    (adjointGroup Tag.F4 K).subtype.comp (CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ K)
  have hfB : Function.Injective fB :=
    (Subgroup.subtype_injective (adjointGroup Tag.F4 K)).comp
      (CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ_injective K)
  exact (MonoidHom.ofInjective hfB).trans
    (MulEquiv.subgroupCongr
      (CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ_map_range K))

private noncomputable def l10lH4_b3EquivV (K : Type) [Field K] [Finite K] [CharP K 2]
    [Algebra (ZMod 2) K] [Algebra.IsAlgebraic (ZMod 2) K] (v : WeylGroup Tag.F4) :
    ↥(StatedSp 3 K) ≃* ↥(rootSpan Tag.F4 K
      ((fun α => v • α) '' CFSG.SeitzReduction.F4Pilot.b3LeviRoots)) :=
  (l10lH4_b3Equiv K).trans
    (l10lH4_conjRootSpanEquiv K v CFSG.SeitzReduction.F4Pilot.b3LeviRoots
      (fun _ hα => hα.1))

private theorem l10lH4_lieModel_of_spEquiv {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : ℕ} (he : 1 ≤ e) (hcard : Nat.card K = 2 ^ e) {X : Subgroup (ModGL Tag.F4 K)}
    (ee : ↥(StatedSp 3 K) ≃* ↥X) :
    CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) StatedLieTag.PSp 3 2 e := by
  have hadm : StatedLieAdmissible StatedLieTag.PSp 3 2 e := by
    refine ⟨Nat.prime_two, he, by norm_num, ?_⟩
    intro hcon
    have h2 : 2 ^ e = 2 := congrArg Prod.snd hcon
    have h3 : 3 = 2 := congrArg Prod.fst hcon
    omega
  have hclass : StatedClassicalModel (↥(StatedSp 3 K) ⧸
      Subgroup.center ↥(StatedSp 3 K)) StatedLieTag.PSp 3 2 e :=
    CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient 3 K hadm hcard
  exact CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv ee
    (Or.inl ⟨by decide, hclass⟩)

theorem famF4_rankThree_lieModel
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hr3 : FamF4B3Shape (componentRoots (famCharHom a) i) ∨
      FamF4C3Shape (componentRoots (famCharHom a) i)) :
    CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ∧
      ∃ e : ℕ, 1 ≤ e ∧ S.D.q = 2 ^ e ∧
        CFSG.Blueprint.LieModel (↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i))
          StatedLieTag.PSp 3 2 e := by
  classical
  have hL2 : CharP L 2 := inferInstance
  obtain ⟨hρ, horb⟩ :
      (∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a)) ∧
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
          componentRoots (famCharHom a) i = componentRoots (famCharHom a) i ∧
        componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1) :=
    ⟨fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ, famF4_orbit S hp hp2 hT hap i⟩
  have hshapeOr :
      (∃ v : WeylGroup Tag.F4,
          componentRoots (famCharHom a) i = (fun α => v • α) '' b3LeviRoots) ∨
      (∃ v : WeylGroup Tag.F4,
          componentRoots (famCharHom a) i =
            (fun α => v • α) '' C3Range.c3RootSet) := by
    rcases hr3 with ⟨v, hv⟩ | ⟨v, hv⟩
    · left
      exact ⟨v, by rw [hv, parabolicRoots_f4LeviB3_eq_b3LeviRoots]⟩
    · right
      exact ⟨v, by rw [hv, parabolicRoots_f4LeviC3_eq_c3RootSet]⟩
  have h3 : compRank (componentRoots (famCharHom a) i) = 3 := by
    rcases hr3 with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [hv, compRank_image]
      exact compRank_parabolicRoots_f4LeviB3
    · rw [hv, compRank_image]
      exact compRank_parabolicRoots_f4LeviC3
  have h18 : (componentRoots (famCharHom a) i).ncard = 18 := by
    rcases hr3 with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [hv, ncard_image_smul]
      exact ncard_parabolicRoots_f4LeviB3
    · rw [hv, ncard_image_smul]
      exact ncard_parabolicRoots_f4LeviC3
  have hinner : twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]) := by
    rw [horb.2]
    open CFSG.StandardType.F4ExplicitPos in
    simpa using
      RankThreeModels.twistInner_of_compRank_three_ncard_eighteen_generic
        (Ω := L) (χ := famCharHom a) S.frob i h3 h18 horb.1
  obtain ⟨σ, hfinK, hcardK, f, hf1, hfker, hf2⟩ :=
    fam_exists_inner_cover (τ := Tag.F4) S hρ i hinner
  let K := ↥(fixSubfield σ)
  let : Finite K := hfinK
  let : CharP K 2 := Subfield.charP (fixSubfield σ) 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra.IsAlgebraic (ZMod 2) K := Algebra.IsAlgebraic.of_finite (ZMod 2) K
  obtain ⟨r, e₀, hr, hchar, he₀, hqr⟩ := exists_char_pow (τ := Tag.F4) S
  have hr2 : r = 2 := CharP.eq L hchar hL2
  have hq2 : S.D.q = 2 ^ e₀ := by rw [hqr, hr2]
  have hcard2 : Nat.card K = 2 ^ e₀ := by rw [hcardK, horb.2, pow_one, hq2]
  have he2 : 1 ≤ e₀ := he₀
  have hex : Nonempty (↥(StatedSp 3 K) ≃* ↥(componentRootSpan K (famCharHom a) i)) := by
    rcases hshapeOr with ⟨v, hv⟩ | ⟨v, hv⟩
    · refine ⟨?_⟩
      have hCe : componentRootSpan K (famCharHom a) i =
          rootSpan Tag.F4 K ((fun α => v • α) '' b3LeviRoots) := by
        rw [show componentRootSpan K (famCharHom a) i =
          rootSpan Tag.F4 K (componentRoots (famCharHom a) i) from rfl, hv]
      rw [hCe]
      exact l10lH4_b3EquivV K v
    · refine ⟨?_⟩
      have hCe : componentRootSpan K (famCharHom a) i =
          rootSpan Tag.F4 K ((fun α => v • α) '' C3Range.c3RootSet) := by
        rw [show componentRootSpan K (famCharHom a) i =
          rootSpan Tag.F4 K (componentRoots (famCharHom a) i) from rfl, hv]
      rw [hCe]
      exact l10lH4_c3EquivV K v
  let eC : ↥(StatedSp 3 K) ≃* ↥(componentRootSpan K (famCharHom a) i) :=
    Classical.choice hex
  have hF : (Infinite K ∨ 4 ≤ Nat.card K) ∨ Nat.card K = 3 ∧ 2 ≤ 3 ∨
      Nat.card K = 2 ∧ 3 ≤ 3 := by
    rcases lt_or_ge e₀ 2 with h | h
    · have he1 : e₀ = 1 := by omega
      exact Or.inr (Or.inr ⟨by rw [hcard2, he1]; norm_num, by norm_num⟩)
    · have h4 : 4 ≤ Nat.card K := by
        rw [hcard2]
        exact Nat.pow_le_pow_right (n := 2) (by norm_num) h
      exact Or.inl (Or.inr h4)
  have hsp : CFSG.IsQuasisimple ↥(StatedSp 3 K) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num) hF
  have hCq : CFSG.IsQuasisimple ↥(componentRootSpan K (famCharHom a) i) :=
    CFSG.IsQuasisimple.of_mulEquiv eC.symm hsp
  have hCperf : ⁅componentRootSpan K (famCharHom a) i,
      componentRootSpan K (famCharHom a) i⁆ = componentRootSpan K (famCharHom a) i :=
    (Subgroup.isPerfect_iff (H := componentRootSpan K (famCharHom a) i)).mp hCq.1
  have hR_eq : f.range = rationalComponentM S.ρ S.Γ (famCharHom a) i :=
    le_antisymm (hf2 hCperf) hf1
  have hLieC : CFSG.Blueprint.LieModel
      (↥(componentRootSpan K (famCharHom a) i) ⧸
        Subgroup.center ↥(componentRootSpan K (famCharHom a) i))
      StatedLieTag.PSp 3 2 e₀ :=
    l10lH4_lieModel_of_spEquiv he2 hcard2 eC
  let g : ↥(componentRootSpan K (famCharHom a) i) →*
      ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
    f.codRestrict _ (fun x => hR_eq.symm ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hgker : g.ker ≤ Subgroup.center ↥(componentRootSpan K (famCharHom a) i) := by
    rw [MonoidHom.ker_codRestrict]
    exact hfker
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : ModGL Tag.F4 L) ∈ f.range := hR_eq.symm ▸ y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨eQR⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      (Group.isPerfect_def.mp hCq.1) g hgsurj hgker
  have hLieR : CFSG.Blueprint.LieModel
      (↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i))
      StatedLieTag.PSp 3 2 e₀ :=
    CFSG.Blueprint.LieModel.of_mulEquiv eQR hLieC
  have hQ : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
    hR_eq ▸ CFSG.HardMathSupport.Timmesfeld.LangTorus.isQuasisimple_range_of_ker_le_center
      hCq f hfker
  exact ⟨hQ, e₀, he2, hq2, hLieR⟩

theorem famF4_laneRankThree
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hr3 : FamF4B3Shape (componentRoots (famCharHom a) i) ∨
      FamF4C3Shape (componentRoots (famCharHom a) i))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    CFSG.StandardType.GGCompFieldAt
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  obtain ⟨-, e₀, -, hq2, hLieR⟩ :=
    famF4_rankThree_lieModel S hp hp2 hT hap i hr3
  rw [(famF4_orbit S hp hp2 hT hap i).2, pow_one, hq2]
  exact ggCompFieldAt_of_lieModel (ggStrongRecog_open_isQuasisimple hq) hLieR (by decide)

end CFSG.StandardType.TableCRes

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExc
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aBridge
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aFrame
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aComponent
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aRootSub
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCStdEnvelope
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairA1
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairSL
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairD
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairTwoD
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE6
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE7
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE8
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwE6
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairTriD4
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourKac
import CFSG.LieType.AlgebraicGroups.KernelRootGroup
import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
import CFSG.LieType.Chevalley.SignKernelComponentBorel
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag)
open scoped commutatorElement

section Cert


theorem ExcLangFrame.q_facts {t : StatedLieTag} {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (F : ExcLangFrame t n f p ψ G₀ B₁ D x) :
    (IsPrimePow F.Δ.q ∧ ((F.Δ.q : ℕ) : GGL) = 0) ∧ ¬ 5 ∣ F.Δ.q := by
  have hf : f ≠ 0 := Nat.ne_of_gt F.one_le_f
  rw [F.q_eq]
  refine ⟨⟨Nat.prime_two.isPrimePow.pow hf, ?_⟩, fun h5 => ?_⟩
  · exact (CharP.cast_eq_zero_iff GGL 2 _).2 (dvd_pow_self 2 hf)
  · have := Nat.prime_five.dvd_of_dvd_pow h5
    omega

@[expose] noncomputable def ExcLangFrame.setup {t : StatedLieTag} {X : Type} [Group X]
    {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (F : ExcLangFrame t n f p ψ G₀ B₁ D x) : LangSetup (langTag t) GGL 5 :=
  F.Δ.toSetup 5 F.ρ F.frob Nat.prime_five (Or.inl le_rfl) F.q_facts.1 F.q_facts.2 F.finite

theorem ExcLangFrame.exists_class_of_noncentral_of_ne_G2 {t : StatedLieTag}
    (hτG2 : langTag t ≠ .G2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X} {G₀ L : Subgroup X} {x : X}
    (hN : Subgroup.zpowers x ≤ Subgroup.normalizer (G₀ : Set X))
    (F : ExcLangFrame t n f p ψ G₀ (Subgroup.zpowers x) (Subgroup.zpowers x) x)
    (hLG0 : L ≤ G₀) (hLc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer {x}))
    (hnc : x ∉ Subgroup.centralizer (G₀ : Set X)) :
    rootDiagUnit (langTag t) (F.coord x) ∈ F.setup.D.torus ∧ (∀ j, F.coord x j ^ p = 1) ∧
      rootDiagUnit (langTag t) (F.coord x) ≠ 1 ∧
      ∃ i : KernelComponent (rootCharHom (F.coord x)),
        CFSG.IsQuasisimple ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i) ∧
        (L.subgroupOf G₀).map F.η =
          rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i := by
  have hxD : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  have hT : rootDiagUnit (langTag t) (F.coord x) ∈ F.setup.D.torus := F.coord_torus x hxD
  have hap : ∀ j, F.coord x j ^ p = 1 := F.coord_pow x hxD
  have h1 : rootDiagUnit (langTag t) (F.coord x) ≠ 1 := by
    intro h
    apply hnc
    refine (F.Θ_eq_one ⟨x, hxD⟩).1 ?_
    rw [F.Θ_eq_coord ⟨x, hxD⟩ hxD, h]
  have hKc : CFSG.Open.IsComponentOf ((L.subgroupOf G₀).map F.η)
      (F.setup.Γ ⊓ Subgroup.centralizer {rootDiagUnit (langTag t) (F.coord x)}) :=
    CFSG.Assembly.isComponentOf_iff_open.1 (attach_nbr_of hN le_rfl F x hxD L hLG0 hLc)
  obtain ⟨i, hqs, hKeq⟩ := LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
    F.setup hτG2 hp (RCKRP.rck_natCast_ne_zero_GGL hp hp2) hT hap h1 hKc
  exact ⟨hT, hap, h1, i, hqs, hKeq⟩

theorem ExcLangFrame.exists_class_of_noncentral {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X} {G₀ L : Subgroup X} {x : X}
    (hN : Subgroup.zpowers x ≤ Subgroup.normalizer (G₀ : Set X))
    (F : ExcLangFrame t n f p ψ G₀ (Subgroup.zpowers x) (Subgroup.zpowers x) x)
    (hLG0 : L ≤ G₀) (hLc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer {x}))
    (hnc : x ∉ Subgroup.centralizer (G₀ : Set X)) :
    rootDiagUnit (langTag t) (F.coord x) ∈ F.setup.D.torus ∧ (∀ j, F.coord x j ^ p = 1) ∧
      rootDiagUnit (langTag t) (F.coord x) ≠ 1 ∧
      ∃ i : KernelComponent (rootCharHom (F.coord x)),
        CFSG.IsQuasisimple ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i) ∧
        (L.subgroupOf G₀).map F.η =
          rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i := by
  have hτG2 : langTag t ≠ .G2 := by
    rcases ht with rfl | rfl | rfl <;> simp [langTag]
  exact ExcLangFrame.exists_class_of_noncentral_of_ne_G2
    hτG2 hp hp2 hN F hLG0 hLc hnc


@[expose] def CarrierModel {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (M : LieUniversal) (g : ℕ) : Prop :=
  (compRank (componentRoots (rootCharHom a) i) = 1 ∧ M = ggU .PSL 2 g) ∨
    (twistKind S.ρ (rootCharHom a) i = .inner ∧
      2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1) ∧
      M = ggU .PSL (compRank (componentRoots (rootCharHom a) i) + 1) g) ∨
    (twistKind S.ρ (rootCharHom a) i = .suN ∧
      M = ggU .PSU (compRank (componentRoots (rootCharHom a) i) + 1) g) ∨
    (twistKind S.ρ (rootCharHom a) i = .inner ∧
      4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1) ∧
      M = ggU .POmegaPlus (compRank (componentRoots (rootCharHom a) i)) g) ∨
    (twistKind S.ρ (rootCharHom a) i = .twoD ∧
      M = ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) g) ∨
    (twistKind S.ρ (rootCharHom a) i = .inner ∧
      ((compRank (componentRoots (rootCharHom a) i) = 6 ∧
          (componentRoots (rootCharHom a) i).ncard = 72 ∧ M = ggU .E6 0 g) ∨
        (compRank (componentRoots (rootCharHom a) i) = 7 ∧
          (componentRoots (rootCharHom a) i).ncard = 126 ∧ M = ggU .E7 0 g) ∨
        (compRank (componentRoots (rootCharHom a) i) = 8 ∧
          (componentRoots (rootCharHom a) i).ncard = 240 ∧ M = ggU .E8 0 g))) ∨
    (twistKind S.ρ (rootCharHom a) i = .exc ∧
      ((compRank (componentRoots (rootCharHom a) i) = 6 ∧ M = ggU .twistedE6 0 g) ∨
        (compRank (componentRoots (rootCharHom a) i) = 4 ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
            TriField F σ g ∧ M = triD4Universal F σ)))

theorem rckCarrierPairADE_holds : RCKRP.RCKCarrierPairADE :=
  RCKRP.rckCarrierPairADE_of_shapes RCKRP.rckPairA1_holds RCKRP.rckPairSLInner_holds
    RCKRP.rckPairSU_holds RCKRP.rckPairDInner_holds RCKRP.rckPairTwoD_holds RCKRP.rckPairE6_holds
    RCKRP.rckPairE7_holds RCKRP.rckPairE8_holds RCKRP.rckPairTwE6_holds RCKRP.rckPairTriD4_holds

theorem inf_eqLocus_step_eq_inf_model {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    {V : Subgroup (ModGL τ L)} (hV : V ≤ adjointGroup τ L) :
    V ⊓ D.step.eqLocus (MonoidHom.id _) = V ⊓ D.model := by
  rw [LangDatum.model, ← inf_assoc, inf_eq_left.2 hV]

private theorem commutatorElement_mul_mul_of_mem_center {H : Type*} [Group H] {a b z w : H}
    (hz : z ∈ Subgroup.center H) (hw : w ∈ Subgroup.center H) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : z * b = b * z := (Subgroup.mem_center_iff.1 hz b).symm
  have h2 : z * w = w * z := (Subgroup.mem_center_iff.1 hz w).symm
  have h3 : w * a⁻¹ = a⁻¹ * w := (Subgroup.mem_center_iff.1 hw a⁻¹).symm
  calc ⁅a * z, b * w⁆ = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (z * w) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [h1]; group
    _ = a * b * w * (z * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [h2]; group
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = ⁅a, b⁆ := by rw [h3, commutatorElement_def]; group

@[expose] def ExcLangFrame.RootStep {t : StatedLieTag} {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (F : ExcLangFrame t n f p ψ G₀ B₁ D x) : Prop :=
  ∀ ⦃α : Fin (langTag t).rank → ℤ⦄ ⦃w : ModGL (langTag t) GGL⦄, IsRoot (langTag t) α →
    w ∈ adjointGroup (langTag t) GGL →
    (excCurve α w).map F.Δ.step = excCurve α w →
    (excCurve (-α) w).map F.Δ.step = excCurve (-α) w →
    ∃ (β : Fin (ggU t n f).D.rank → ℤ) (k : (ggU t n f).K), β ∈ (ggU t n f).D.roots ∧
      GGLongRoot (ggU t n f).D β ∧
      ((ggRootSub (ggU t n f).D ψ β k).subgroupOf G₀).map F.η = excCurve α w ⊓ F.Δ.model ∧
      ((ggRootSub (ggU t n f).D ψ (-β) k).subgroupOf G₀).map F.η = excCurve (-α) w ⊓ F.Δ.model

theorem ExcLangFrame.rootStep_of_exc {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    {X : Type} [Group X] {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (hψ : ψ.range = G₀) (F : ExcLangFrame t n f p ψ G₀ B₁ D x) : F.RootStep := by
  intro α w hα hw hV hVm
  obtain ⟨β, k, hβ, hlong, hR, hRm, -, -⟩ := ExcLangFrame.exists_rootSub ht hψ F hα hw hV hVm
  exact ⟨β, k, hβ, hlong, hR, hRm⟩

theorem ExcLangFrame.exists_member_of_orbit_one_of_rootStep {t : StatedLieTag}
    (hτ : langTag t = .D4 ∨ langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X} {G₀ L : Subgroup X} {x : X}
    (hψ : ψ.range = G₀) (hZ : Odd (Nat.card (Subgroup.center ↥G₀)))
    (hLperf : commutator ↥L = ⊤)
    (F : ExcLangFrame t n f p ψ G₀ (Subgroup.zpowers x) (Subgroup.zpowers x) x)
    (hstep : F.RootStep) (hLG0 : L ≤ G₀)
    (hT : rootDiagUnit (langTag t) (F.coord x) ∈ F.setup.D.torus)
    (hap : ∀ j, F.coord x j ^ p = 1) (h1 : rootDiagUnit (langTag t) (F.coord x) ≠ 1)
    (i : KernelComponent (rootCharHom (F.coord x)))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i))
    (hL : (L.subgroupOf G₀).map F.η =
      rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i)
    (horb : componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1) :
    ∃ (M : LieUniversal) (α : M.K →* X),
      CarrierModel F.setup (F.coord x) i M f ∧ RCKRP.RCKADEModel M f ∧ α.range = L ∧
        α.ker ≤ Subgroup.center M.K ∧ Finite M.K ∧ Group.IsPerfect M.K ∧
        ∀ β ∈ M.D.roots, GGLongRoot M.D β → ∃ β' ∈ (ggU t n f).D.roots,
          GGLongRoot (ggU t n f).D β' ∧ ∃ k : (ggU t n f).K,
            (M.D.rootGroup β).map α ⊔ (Subgroup.center ↥G₀).map G₀.subtype =
                ggRootSub (ggU t n f).D ψ β' k ⊔ (Subgroup.center ↥G₀).map G₀.subtype ∧
              (M.D.rootGroup (-β)).map α ⊔ (Subgroup.center ↥G₀).map G₀.subtype =
                ggRootSub (ggU t n f).D ψ (-β') k ⊔ (Subgroup.center ↥G₀).map G₀.subtype := by
  classical
  have hap1 : rootDiagUnit (langTag t) (F.coord x) ^ p = 1 := by
    rw [rootDiagUnit_pow]
    have h3 : F.coord x ^ p = 1 := funext fun j => by simpa using hap j
    rw [h3, rootDiagUnit_one]
  have hstd : RCKRP.RCKADEShape F.setup.ρ (rootCharHom (F.coord x)) i :=
    RCKRP.rckStdEnvelope_holds (langTag t) hτ F.setup p hp hp2 (F.coord x) hT h1 hap i hqs
  obtain ⟨M, φ, hMod, hADE, hrange, hker, hfin, hperf, hsplit, hpairc⟩ :=
    rckCarrierPairADE_holds (langTag t) 5 F.setup (F.coord x) hT p hp hp2 hap1 i f F.q_eq hstd hqs
  simp only [horb, mul_one] at hMod hADE
  let ηL : ↥L →* ModGL (langTag t) GGL := F.η.comp (Subgroup.inclusion hLG0)
  have hηLrange : ηL.range = (L.subgroupOf G₀).map F.η := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hLG0 l,
        Subgroup.mem_subgroupOf.2 l.2, rfl⟩
    · rintro hy
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨g, Subgroup.mem_subgroupOf.1 hg⟩, rfl⟩
  have hφmem : ∀ m, φ m ∈ ηL.range := fun m => by
    rw [hηLrange, hL, ← hrange]
    exact ⟨m, rfl⟩
  have hηLker : ∀ l : ↥L, ηL l = 1 → Subgroup.inclusion hLG0 l ∈ Subgroup.center ↥G₀ := by
    intro l hl
    rw [← F.ker_η]
    exact hl
  have hηLcen : ∀ l : ↥L, ηL l = 1 → l ∈ Subgroup.center ↥L := by
    intro l hl
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subgroup.inclusion_injective hLG0 (by
      simpa only [map_mul] using
        Subgroup.mem_center_iff.1 (hηLker l hl) (Subgroup.inclusion hLG0 y))
  let P : Subgroup (M.K × ↥L) :=
    (φ.comp (MonoidHom.fst M.K ↥L)).eqLocus (ηL.comp (MonoidHom.snd M.K ↥L))
  let π : ↥P →* M.K := (MonoidHom.fst M.K ↥L).comp P.subtype
  have hπsurj : Function.Surjective π := by
    intro m
    obtain ⟨l, hl⟩ := hφmem m
    exact ⟨⟨(m, l), hl.symm⟩, rfl⟩
  have hπ1 : ∀ e : ↥P, π e = 1 → ηL (e : M.K × ↥L).2 = 1 := by
    intro e he
    have h : φ (e : M.K × ↥L).1 = ηL (e : M.K × ↥L).2 := e.2
    have he1 : (e : M.K × ↥L).1 = 1 := he
    rw [he1, map_one] at h
    exact h.symm
  have hπker : π.ker ≤ Subgroup.center ↥P := by
    intro e he
    rw [Subgroup.mem_center_iff]
    intro e'
    have he1 : (e : M.K × ↥L).1 = 1 := he
    have hc := Subgroup.mem_center_iff.1 (hηLcen _ (hπ1 e he)) (e' : M.K × ↥L).2
    apply Subtype.ext
    apply Prod.ext
    · change (e' : M.K × ↥L).1 * (e : M.K × ↥L).1 = (e : M.K × ↥L).1 * (e' : M.K × ↥L).1
      rw [he1, mul_one, one_mul]
    · exact hc
  have hπodd : Odd (Nat.card π.ker) := by
    let j : π.ker →* ↥(Subgroup.center ↥G₀) :=
      { toFun := fun e => ⟨Subgroup.inclusion hLG0 ((e : ↥P) : M.K × ↥L).2,
          hηLker _ (hπ1 e e.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := by
      intro e e' hee'
      have h2 : ((e : ↥P) : M.K × ↥L).2 = ((e' : ↥P) : M.K × ↥L).2 :=
        Subgroup.inclusion_injective hLG0 (congrArg Subtype.val hee')
      have ha : ((e : ↥P) : M.K × ↥L).1 = 1 := e.2
      have hb : ((e' : ↥P) : M.K × ↥L).1 = 1 := e'.2
      exact Subtype.ext (Subtype.ext (Prod.ext (ha.trans hb.symm) h2))
    exact Odd.of_dvd_nat hZ (Subgroup.card_dvd_of_injective j hj)
  obtain ⟨s, hs⟩ := hsplit ↥P π hπsurj hπker hπodd
  let α' : M.K →* ↥L := (MonoidHom.snd M.K ↥L).comp (P.subtype.comp s)
  have hα' : ∀ m, ηL (α' m) = φ m := fun m => by
    have h : φ ((s m : ↥P) : M.K × ↥L).1 = ηL ((s m : ↥P) : M.K × ↥L).2 := (s m).2
    have h1 : ((s m : ↥P) : M.K × ↥L).1 = m := hs m
    rw [h1] at h
    exact h.symm
  have hcomp : ηL.comp α' = φ := MonoidHom.ext hα'
  have hα'sup : ∀ l : ↥L, ∃ m : M.K, ∃ z : ↥L, z ∈ Subgroup.center ↥L ∧ l = α' m * z := by
    intro l
    have hl : ηL l ∈ φ.range := by
      rw [hrange, ← hL, ← hηLrange]
      exact ⟨l, rfl⟩
    obtain ⟨m, hm⟩ := hl
    refine ⟨m, (α' m)⁻¹ * l, hηLcen _ ?_, by group⟩
    rw [map_mul, map_inv, hα' m, hm, inv_mul_cancel]
  have hα'surj : Function.Surjective α' := by
    have hcomm : commutator ↥L ≤ α'.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨m, z, hz, rfl⟩ := hα'sup a
      obtain ⟨m', z', hz', rfl⟩ := hα'sup b
      rw [commutatorElement_mul_mul_of_mem_center hz hz', ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro l
    have hl : l ∈ commutator ↥L := by
      rw [hLperf]
      exact Subgroup.mem_top l
    exact hcomm hl
  have hrangeα : (L.subtype.comp α').range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hα'surj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hkerα : (L.subtype.comp α').ker ≤ Subgroup.center M.K := fun m hm => hker (by
    have h1 : α' m = 1 := Subtype.ext (MonoidHom.mem_ker.1 hm)
    rw [MonoidHom.mem_ker, ← hα', h1, map_one])
  have hpull : ∀ (A : Subgroup ↥L) (R : Subgroup X), R ≤ G₀ →
      A.map ηL = (R.subgroupOf G₀).map F.η →
        A.map L.subtype ⊔ (Subgroup.center ↥G₀).map G₀.subtype =
          R ⊔ (Subgroup.center ↥G₀).map G₀.subtype := by
    intro A R hR hAR
    have h1 : A.map (Subgroup.inclusion hLG0) ⊔ Subgroup.center ↥G₀ =
        R.subgroupOf G₀ ⊔ Subgroup.center ↥G₀ := by
      rw [← F.ker_η, ← Subgroup.map_eq_map_iff, Subgroup.map_map]
      exact hAR
    have h2 := congrArg (Subgroup.map G₀.subtype) h1
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hR] at h2
    exact h2
  have hRle : ∀ (γ : Fin (ggU t n f).D.rank → ℤ) (k : (ggU t n f).K),
      ggRootSub (ggU t n f).D ψ γ k ≤ G₀ := fun γ k => by
    rw [← hψ]
    exact Subgroup.map_le_range _ _
  refine ⟨M, L.subtype.comp α', hMod, hADE, hrangeα, hkerα, hfin, hperf, ?_⟩
  intro β hβ hlong
  obtain ⟨γ, hγ, z, hz, hUst, hVst, hφβ, hφβ'⟩ := hpairc horb β hβ hlong
  have hγroot : IsRoot (langTag t) γ := isRoot_of_mem_componentRoots hγ
  have hzA : z ∈ adjointGroup (langTag t) GGL := torus_sup_rootSpan_le_adjointGroup _ hz
  have hcurve : ∀ δ, excCurve δ z ≤ adjointGroup (langTag t) GGL :=
    fun δ => (Subgroup.map_mono (rootSubgroup_le_adjointGroup δ)).trans
      (Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hzA)).le
  obtain ⟨β', k, hβ', hlong', hR, hRm⟩ := hstep hγroot hzA hUst hVst
  refine ⟨β', hβ', hlong', k, ?_, ?_⟩
  · rw [← Subgroup.map_map]
    apply hpull _ _ (hRle β' k)
    rw [hR, Subgroup.map_map, hcomp, hφβ]
    exact inf_eqLocus_step_eq_inf_model F.Δ (hcurve γ)
  · rw [← Subgroup.map_map]
    apply hpull _ _ (hRle (-β') k)
    rw [hRm, Subgroup.map_map, hcomp, hφβ']
    exact inf_eqLocus_step_eq_inf_model F.Δ (hcurve (-γ))


theorem ExcLangFrame.exists_member_of_orbit_one {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X} {G₀ L : Subgroup X} {x : X}
    (hψ : ψ.range = G₀) (hZ : Odd (Nat.card (Subgroup.center ↥G₀)))
    (hLperf : commutator ↥L = ⊤)
    (F : ExcLangFrame t n f p ψ G₀ (Subgroup.zpowers x) (Subgroup.zpowers x) x)
    (hLG0 : L ≤ G₀) (hT : rootDiagUnit (langTag t) (F.coord x) ∈ F.setup.D.torus)
    (hap : ∀ j, F.coord x j ^ p = 1) (h1 : rootDiagUnit (langTag t) (F.coord x) ≠ 1)
    (i : KernelComponent (rootCharHom (F.coord x)))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i))
    (hL : (L.subgroupOf G₀).map F.η =
      rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i)
    (horb : componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1) :
    ∃ (M : LieUniversal) (α : M.K →* X),
      CarrierModel F.setup (F.coord x) i M f ∧ RCKRP.RCKADEModel M f ∧ α.range = L ∧
        α.ker ≤ Subgroup.center M.K ∧ Finite M.K ∧ Group.IsPerfect M.K ∧
        ∀ β ∈ M.D.roots, GGLongRoot M.D β → ∃ β' ∈ (ggU t n f).D.roots,
          GGLongRoot (ggU t n f).D β' ∧ ∃ k : (ggU t n f).K,
            (M.D.rootGroup β).map α ⊔ (Subgroup.center ↥G₀).map G₀.subtype =
                ggRootSub (ggU t n f).D ψ β' k ⊔ (Subgroup.center ↥G₀).map G₀.subtype ∧
              (M.D.rootGroup (-β)).map α ⊔ (Subgroup.center ↥G₀).map G₀.subtype =
                ggRootSub (ggU t n f).D ψ (-β') k ⊔ (Subgroup.center ↥G₀).map G₀.subtype := by
  have hτ : langTag t = .D4 ∨ langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
    rcases ht with rfl | rfl | rfl <;> simp [langTag]
  exact F.exists_member_of_orbit_one_of_rootStep hτ hp hp2 hψ hZ hLperf
    (F.rootStep_of_exc ht hψ) hLG0 hT hap h1 i hqs hL horb

end Cert

end CFSG.StandardType.LieKnownR2.ExcPos

namespace CFSG.StandardType

namespace FieldTwoExc

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.StandardType.LieKnownR2.ExcPos CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem ggl_isAlgebraic_zmod : letI := ZMod.algebra GGL 2; Algebra.IsAlgebraic (ZMod 2) GGL := by
  have h : ZMod.algebra GGL 2 = (inferInstance : Algebra (ZMod 2) GGL) := Subsingleton.elim _ _
  rw [h]
  exact AlgebraicClosure.isAlgebraic (ZMod 2)

theorem injective_and_center_eq_bot {U X : Type*} [Group U] [Group X] {ψ : U →* X}
    {G₀ : Subgroup X} (hψ : ψ.range = G₀) (hker : ψ.ker ≤ Subgroup.center U)
    (hZ : Subgroup.center U = ⊥) :
    Function.Injective ψ ∧ Subgroup.center ↥G₀ = ⊥ := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hker
  refine ⟨hinj, ?_⟩
  rw [eq_bot_iff]
  intro g hg
  have hgψ : (g : X) ∈ ψ.range := by
    rw [hψ]
    exact g.2
  obtain ⟨u, hu⟩ := hgψ
  have huZ : u ∈ Subgroup.center U := by
    rw [Subgroup.mem_center_iff]
    intro v
    apply hinj
    have hv : ψ v ∈ G₀ := by
      rw [← hψ]
      exact ⟨v, rfl⟩
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hg ⟨ψ v, hv⟩)
    rw [map_mul, map_mul, hu]
    exact hc
  rw [hZ, Subgroup.mem_bot] at huZ
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hu, huZ, map_one]
  rfl

section Cert


theorem monomialToralAt_langTag {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt (langTag t) p :=
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
    (by rcases ht with rfl | rfl | rfl <;> simp [langTag]) hp hp2

theorem nonempty_excLangFrame_zpowers_of_normalizer {t : StatedLieTag}
    (hexc : GGExcFive t)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X] {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ : Subgroup X} {x : X}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    (hdiag : GGPsiInnerDiag (ggU t n f).D ψ x) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (G₀ : Set X))
    (hmono : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt (langTag t) p) :
    Nonempty (ExcLangFrame t n f p ψ G₀ (Subgroup.zpowers x) (Subgroup.zpowers x) x) := by
  have hN : Subgroup.zpowers x ≤ Subgroup.normalizer (G₀ : Set X) :=
    Subgroup.zpowers_le.mpr hxN
  have hxN' : x ∈ Subgroup.normalizer (ψ.range : Set X) := by
    rw [hpres.2.1.1]
    exact hxN
  obtain ⟨hf, θ, lam, hθker, hθrange, hθι, -, hlam, hpart, hlam1⟩ :=
    excU1a_bridge_of hexc hpres hN (hdiag.forall_mem_zpowers hxN')
  have hDel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers hxp
  let x0 : ↥(Subgroup.zpowers x) := ⟨x, Subgroup.mem_zpowers x⟩
  have hpow : lam x0 ^ p = 1 := by
    have h3 : x0 ^ p = 1 := Subtype.ext (by simpa [x0] using hxp)
    rw [← map_pow, h3, map_one]
  obtain ⟨g, hg, hgt⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_conj_torusGroup_of_pow_eq_one
      (ℓ := 2) hp hmono (Ne.symm hp2)
      ggl_isAlgebraic_zmod (hlam x0).1 hpow
  have hT : IsToralSubgroup (langTag t) GGL
      (((Subgroup.zpowers x).subgroupOf (Subgroup.zpowers x)).map lam) := by
    refine ⟨g, hg, ?_⟩
    rintro y hy
    obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
    have hb : b = x0 ^ k := Subtype.ext (by simp [x0, hk])
    have e := map_zpow (MulAut.conj g⁻¹) (lam x0) k
    simp only [MulAut.conj_apply, inv_inv] at e
    rw [hb, map_zpow, e]
    exact zpow_mem hgt k
  have hclosure : Subgroup.closure ({x, x} : Set X) = Subgroup.zpowers x := by
    rw [Set.pair_eq_singleton, Subgroup.zpowers_eq_closure]
  exact nonempty_excLangFrame_of_toral_of hexc hp hp2 hDel le_rfl hf
    hθker hθrange hθι hlam hpart hlam1 hT (Subgroup.mem_zpowers x) hclosure

theorem nonempty_excLangFrame_zpowers {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X] {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ : Subgroup X} {x : X}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    (hdiag : GGPsiInnerDiag (ggU t n f).D ψ x) (hxp : x ^ p = 1) :
    Nonempty (ExcLangFrame t n f p ψ G₀ (Subgroup.zpowers x) (Subgroup.zpowers x) x) := by
  have ht4 : GGExcFour t := by rcases ht with rfl | rfl | rfl <;> simp [GGExcFour]
  have hexc : GGExcFive t := by rcases ht with rfl | rfl | rfl <;> simp [GGExcFive]
  exact nonempty_excLangFrame_zpowers_of_normalizer hexc hp hp2 hpres hdiag hxp
    (ggPsiInnerDiag_mem_normalizer_exc ht4 hpres hdiag) (monomialToralAt_langTag ht hp hp2)

theorem center_ggU_exc_eq_bot {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (n : ℕ) :
    Subgroup.center (ggU t n 1).K = ⊥ := by
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  rcases ht with rfl | rfl | rfl
  · show Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 2 1)) = ⊥
    apply Subgroup.eq_bot_of_card_eq
    have h := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
      (k := GaloisField 2 1)).1
    rw [hcard] at h
    simpa using h
  · show Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup
      (GaloisField 2 1)) = ⊥
    apply Subgroup.eq_bot_of_card_eq
    have h := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e7
      (k := GaloisField 2 1)).1
    rw [hcard] at h
    simpa using h
  · exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot

section ComponentFieldReduction

theorem exists_member_of_ggConfig_exc {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (ψ : (ggU t n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ)
    (hdiag : GGPsiInnerDiag (ggU t n f).D ψ x)
    (hnc : x ∉ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) :
    f = 1 ∧ Function.Injective ψ ∧
      ∃ (F : ExcLangFrame t n f 3 ψ (ggG0 3 B x L D J) (Subgroup.zpowers x)
          (Subgroup.zpowers x) x) (i : KernelComponent (rootCharHom (F.coord x))),
        rootDiagUnit (langTag t) (F.coord x) ∈ F.setup.D.torus ∧ (∀ j, F.coord x j ^ 3 = 1) ∧
        rootDiagUnit (langTag t) (F.coord x) ≠ 1 ∧
        CFSG.IsQuasisimple
          ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i) ∧
        (L.subgroupOf (ggG0 3 B x L D J)).map F.η =
          rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i ∧
        RCKRP.RCKADEShape F.setup.ρ (rootCharHom (F.coord x)) i ∧
        (componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1 →
          ∃ (M : LieUniversal) (α : M.K →* G),
            CarrierModel F.setup (F.coord x) i M f ∧ RCKRP.RCKADEModel M f ∧ α.range = L ∧
              α.ker ≤ Subgroup.center M.K ∧ Finite M.K ∧ Group.IsPerfect M.K ∧
              ∀ β ∈ M.D.roots, GGLongRoot M.D β → ∃ β' ∈ (ggU t n f).D.roots,
                GGLongRoot (ggU t n f).D β' ∧ ∃ k : (ggU t n f).K,
                  (M.D.rootGroup β).map α = ggRootSub (ggU t n f).D ψ β' k ∧
                    (M.D.rootGroup (-β)).map α = ggRootSub (ggU t n f).D ψ (-β') k) := by
  have ht4 : GGExcFour t := by rcases ht with rfl | rfl | rfl <;> simp [GGExcFour]
  have hf := ggConfig_field_one_of_exc_qTwo ht4 hC hq ψ hpres hdiag
  subst hf
  obtain ⟨hinj, hZ⟩ :=
    injective_and_center_eq_bot hpres.2.1.1 hpres.2.1.2 (center_ggU_exc_eq_bot ht n)
  have hsstar := hC.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hsstar.1.1.2 x hsstar.2.1
  obtain ⟨F⟩ := nonempty_excLangFrame_zpowers ht Nat.prime_three (by norm_num) hpres hdiag hx3
  have hN : Subgroup.zpowers x ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    Subgroup.zpowers_le.mpr (ggPsiInnerDiag_mem_normalizer_exc ht4 hpres hdiag)
  have hLG0 : L ≤ ggG0 3 B x L D J := le_ggG0_left 3 B x L D J
  obtain ⟨hT, hap, h1, i, hqs, hL⟩ :=
    F.exists_class_of_noncentral ht Nat.prime_three (by norm_num) hN hLG0 hsstar.2.2.2.1 hnc
  have hτ : langTag t = .D4 ∨ langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
    rcases ht with rfl | rfl | rfl <;> simp [langTag]
  refine ⟨rfl, hinj, F, i, hT, hap, h1, hqs, hL,
    RCKRP.rckStdEnvelope_holds (langTag t) hτ F.setup 3 Nat.prime_three (by norm_num)
      (F.coord x) hT h1 hap i hqs, fun horb => ?_⟩
  have hZodd : Odd (Nat.card (Subgroup.center ↥(ggG0 3 B x L D J))) := by
    rw [hZ]
    simp
  obtain ⟨M, α, hMod, hADE, hrange, hker, hfin, hperf, hpair⟩ :=
    F.exists_member_of_orbit_one ht Nat.prime_three (by norm_num) hpres.2.1.1 hZodd
      hsstar.2.2.2.1.2.2.1 hLG0 hT hap h1 i hqs hL horb
  have hZc : (Subgroup.center ↥(ggG0 3 B x L D J)).map (ggG0 3 B x L D J).subtype = ⊥ := by
    rw [hZ, Subgroup.map_bot]
  refine ⟨M, α, hMod, hADE, hrange, hker, hfin, hperf, fun β hβ hlong => ?_⟩
  obtain ⟨β', hβ', hlong', k, hk₁, hk₂⟩ := hpair β hβ hlong
  rw [hZc, sup_bot_eq, sup_bot_eq] at hk₁ hk₂
  exact ⟨β', hβ', hlong', k, hk₁, hk₂⟩

end ComponentFieldReduction

end Cert

end FieldTwoExc

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PairDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTwE6
import CFSG.Quasithin.Background.A3ComponentsQuotient

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def TwE6PairDict : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    ∀ B : ExcBase .E6 f p G₀ B₁ D J x, TwE6BaseCompat n f p ψ B → B.b = 1 →
    (J.subgroupOf G₀).map B.η = LieCore.ratComp B.ρ B.Δ.Γ B.rootsJ

@[expose] def TwE6StablePairStmt : Prop :=
  ∀ {f : ℕ} (_hf : 1 ≤ f) (Δ : LangDatum Tag.E6 GGL) (_hq : Δ.q = 2 ^ f)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (_hρ : FrobRootMap Δ ρ) (_hfin : Finite Δ.model)
    {p : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    {a₁ a₂ : Fin Tag.E6.rank → GGLˣ} (_ha₁ : rootDiagUnit Tag.E6 a₁ ∈ Δ.torus)
    (_ha₂ : rootDiagUnit Tag.E6 a₂ ∈ Δ.torus) (_hap₁ : ∀ j, a₁ j ^ p = 1) (_hap₂ : ∀ j, a₂ j ^ p = 1)
    (_hne : rootDiagUnit Tag.E6 a₁ ≠ 1 ∨ rootDiagUnit Tag.E6 a₂ ≠ 1)
    (iJ : KernelComponent (LieCore.jointChar a₁ a₂))
    (_hb : componentOrbitLength ρ (componentRoots (LieCore.jointChar a₁ a₂) iJ) = 1)
    (_hqs : CFSG.Assembly.IsQuasisimple
      ↥(LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ))),
    ∃ (α : Fin Tag.E6.rank → ℤ) (w : ModGL Tag.E6 GGL),
      α ∈ componentRoots (LieCore.jointChar a₁ a₂) iJ ∧
      w ∈ torusGroup Tag.E6 GGL ⊔ rootSpan Tag.E6 GGL (kernelRoots (LieCore.jointChar a₁ a₂)) ∧
      (excCurve α w).map Δ.step = excCurve α w ∧
      (excCurve (-α) w).map Δ.step = excCurve (-α) w ∧
      excCurve α w ⊓ Δ.model ≤
        LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ) ∧
      excCurve (-α) w ⊓ Δ.model ≤
        LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ)

@[expose] def TwE6RootTransport : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    ∀ B : ExcBase .E6 f p G₀ B₁ D J x, TwE6BaseCompat n f p ψ B → B.b = 1 →
    ∀ (α : Fin Tag.E6.rank → ℤ) (w : ModGL Tag.E6 GGL), α ∈ B.rootsJ →
      w ∈ torusGroup Tag.E6 GGL ⊔
        rootSpan Tag.E6 GGL (kernelRoots (LieCore.jointChar (B.coord x) (B.coord B.d))) →
      (excCurve α w).map B.Δ.step = excCurve α w →
      (excCurve (-α) w).map B.Δ.step = excCurve (-α) w →
      ∃ (β : Fin (ggU .twistedE6 n f).D.rank → ℤ) (u : (ggU .twistedE6 n f).K),
        β ∈ (ggU .twistedE6 n f).D.roots ∧ (-β) ∈ (ggU .twistedE6 n f).D.roots ∧
        GGLongRoot (ggU .twistedE6 n f).D β ∧
        Nat.card (((ggRootSub (ggU .twistedE6 n f).D ψ β u).subgroupOf G₀).map B.η) =
          Nat.card (GaloisField 2 f) ∧
        ((ggRootSub (ggU .twistedE6 n f).D ψ β u).subgroupOf G₀).map B.η =
          excCurve α w ⊓ B.Δ.model ∧
        Nat.card (((ggRootSub (ggU .twistedE6 n f).D ψ (-β) u).subgroupOf G₀).map B.η) =
          Nat.card (GaloisField 2 f) ∧
        ((ggRootSub (ggU .twistedE6 n f).D ψ (-β) u).subgroupOf G₀).map B.η =
          excCurve (-α) w ⊓ B.Δ.model

@[expose] def ExcRLeJStmt : Prop :=
  ∀ {G H : Type} [Group G] [Finite G] [Group H] (η : G →* H), η.ker ≤ Subgroup.center G →
    Odd (Nat.card η.ker) → ∀ {R J : Subgroup G}, IsPGroup 2 R → R.map η ≤ J.map η → R ≤ J

theorem odd_card_ker_eta {X : Type} [Group X] [Finite X] {G₀ : Subgroup X} {τ : Tag}
    {K : Type} [Field K] (η : ↥G₀ →* ModGL τ K) (hker : η.ker ≤ Subgroup.center ↥G₀)
    (hodd : Odd (Nat.card (Subgroup.centralizer (G₀ : Set X)))) : Odd (Nat.card η.ker) := by
  have hle : η.ker.map G₀.subtype ≤ Subgroup.centralizer (G₀ : Set X) := by
    rintro _ ⟨k, hk, rfl⟩ g hg
    have := Subgroup.mem_center_iff.1 (hker hk) ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hcard : Nat.card (η.ker.map G₀.subtype) = Nat.card η.ker :=
    Subgroup.card_map_of_injective G₀.subtype_injective
  exact Odd.of_dvd_nat hodd (hcard ▸ Subgroup.card_dvd_of_le hle)

theorem isQuasisimple_map_eta {X : Type} [Group X] {G₀ J : Subgroup X} {τ : Tag} {K : Type}
    [Field K] (η : ↥G₀ →* ModGL τ K) (hker : η.ker ≤ Subgroup.center ↥G₀)
    (hJG : J ≤ G₀) (hJq : CFSG.Assembly.IsQuasisimple ↥J) :
    CFSG.Assembly.IsQuasisimple ↥((J.subgroupOf G₀).map η) := by
  have hJ' : CFSG.Assembly.IsQuasisimple ↥(J.subgroupOf G₀) :=
    (CFSG.Assembly.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hJG)).2 hJq
  have hKf : ¬ J.subgroupOf G₀ ≤ η.ker := by
    intro hle
    have hcen : ∀ a : ↥(J.subgroupOf G₀), a ∈ Subgroup.center ↥(J.subgroupOf G₀) := by
      intro a
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (Subgroup.mem_center_iff.1 (hker (hle a.2)) b.1)
    haveI : Nontrivial (↥(J.subgroupOf G₀) ⧸ Subgroup.center ↥(J.subgroupOf G₀)) :=
      hJ'.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne
      (↥(J.subgroupOf G₀) ⧸ Subgroup.center ↥(J.subgroupOf G₀))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (((QuotientGroup.eq_one_iff a).2 (hcen a)).trans
      ((QuotientGroup.eq_one_iff b).2 (hcen b)).symm)
  have h := CFSG.LocalCores.isQuasisimple_map (K := J.subgroupOf G₀)
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hJ') η hKf
  exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp h

theorem ggRootSub_le_range {X : Type} [Group X] {U : Type} [Group U] (Δ : UniversalRootDatum U)
    (ψ : U →* X) (γ : Fin Δ.rank → ℤ) (u : U) : ggRootSub Δ ψ γ u ≤ ψ.range := by
  rw [CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map]
  exact Subgroup.map_le_range _ _

theorem twE6_coord_ne_one {X : Type} [Group X] {f p : ℕ} {G₀ B₁ D J L : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hDB1 : D ≤ B₁) (hLG0 : L ≤ G₀)
    (hDnotc : ¬ D ≤ Subgroup.centralizer (L : Set X)) (hx : x ∈ D) :
    rootDiagUnit Tag.E6 (B.coord x) ≠ 1 ∨ rootDiagUnit Tag.E6 (B.coord B.d) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨htx, htd⟩ := hcon
  apply hDnotc
  rw [← B.closure_eq]
  refine (Subgroup.closure_le _).2 ?_
  rintro y (hy | hy)
  · rw [hy]
    have hxG0 : x ∈ Subgroup.centralizer (G₀ : Set X) := by
      rw [← B.Θ_eq_one ⟨x, hDB1 hx⟩]
      rw [B.Θ_eq_coord ⟨x, hDB1 hx⟩ hx]
      exact htx
    exact Subgroup.centralizer_le hLG0 hxG0
  · rw [hy]
    have hdG0 : B.d ∈ Subgroup.centralizer (G₀ : Set X) := by
      rw [← B.Θ_eq_one ⟨B.d, hDB1 B.d_mem⟩]
      rw [B.Θ_eq_coord ⟨B.d, hDB1 B.d_mem⟩ B.d_mem]
      exact htd
    exact Subgroup.centralizer_le hLG0 hdG0

theorem twE6PairOne_of_pieces (hdict : TwE6PairDict) (hstab : TwE6StablePairStmt)
    (htrans : TwE6RootTransport) (hRJ : ExcRLeJStmt) : TwE6PairOne := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos B hB hb
  have hpos' := hpos
  obtain ⟨hψr, -, -, hodd, hp, hp2, -, -, -, -, hDB1, -, -, -, hJc, -, hx, -, hLG0, -, -, hDnotc,
    -, -, -, -, -, -, -, -, -⟩ := hpos
  have hdict' := hdict X n f ψ p G₀ B₁ D J L x hpos' B hB hb
  have hf : 1 ≤ f := B.one_le_f
  have hb1 : componentOrbitLength B.ρ
      (componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) B.iJ) = 1 := hb
  have hJG : J ≤ G₀ := hJc.1.trans inf_le_left
  have hqs : CFSG.Assembly.IsQuasisimple ↥(LieCore.ratComp B.ρ B.Δ.Γ
      (componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) B.iJ)) := by
    have h := isQuasisimple_map_eta B.η B.ker_η hJG hJc.2.2
    rw [hdict'] at h
    exact h
  have hq : B.Δ.q = 2 ^ f := by
    rw [B.hq]
    exact GaloisField.card 2 f (by omega)
  obtain ⟨α, w, hα, hw, hV, hVm, hle, hlem⟩ := hstab hf B.Δ hq B.frob B.finite hp hp2
    (B.coord_torus x hx) (B.coord_torus B.d B.d_mem) (B.coord_pow x hx) (B.coord_pow B.d B.d_mem)
    (twE6_coord_ne_one B hDB1 hLG0 hDnotc hx) B.iJ hb1 hqs
  obtain ⟨β, u, hβ, hβn, hlong, hcard, hle1, hcardm, hle2⟩ :=
    htrans X n f ψ p G₀ B₁ D J L x hpos' B hB hb α w hα hw hV hVm
  have hΓmodel : B.Δ.Γ ≤ B.Δ.model :=
    Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
        (Subgroup.inv_mem _ h₂)
  have hmodel : ∀ S : Subgroup ↥G₀, S.map B.η ≤ B.Δ.model := fun S =>
    (Subgroup.map_le_range B.η S).trans (B.range_η ▸ hΓmodel)
  have hoddker := odd_card_ker_eta B.η B.ker_η hodd
  have key : ∀ (γ : Fin (ggU .twistedE6 n f).D.rank → ℤ) (V : Subgroup (ModGL Tag.E6 GGL)),
      γ ∈ (ggU .twistedE6 n f).D.roots →
      ((ggRootSub (ggU .twistedE6 n f).D ψ γ u).subgroupOf G₀).map B.η ≤ V →
      V ⊓ B.Δ.model ≤ LieCore.ratComp B.ρ B.Δ.Γ B.rootsJ →
      ggRootSub (ggU .twistedE6 n f).D ψ γ u ≤ J := by
    intro γ V hγ hVle hVJ r hr
    have hRG : ggRootSub (ggU .twistedE6 n f).D ψ γ u ≤ G₀ :=
      hψr ▸ ggRootSub_le_range _ ψ γ u
    have hRp : IsPGroup 2 ↥(ggRootSub (ggU .twistedE6 n f).D ψ γ u) := by
      have h0 := CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_twistedE6 hγ u rfl
      rw [CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map]
      exact h0.of_surjective (ψ.subgroupMap _) (ψ.subgroupMap_surjective _)
    have hRp' : IsPGroup 2 ↥((ggRootSub (ggU .twistedE6 n f).D ψ γ u).subgroupOf G₀) :=
      hRp.of_injective (Subgroup.subgroupOfEquivOfLe hRG).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hRG).injective
    have hmap : ((ggRootSub (ggU .twistedE6 n f).D ψ γ u).subgroupOf G₀).map B.η ≤
        (J.subgroupOf G₀).map B.η := by
      rw [hdict']
      exact (le_inf hVle (hmodel _)).trans hVJ
    have hr' := hRJ B.η B.ker_η hoddker hRp' hmap
      (Subgroup.mem_subgroupOf.2 hr : (⟨r, hRG hr⟩ : ↥G₀) ∈
        (ggRootSub (ggU .twistedE6 n f).D ψ γ u).subgroupOf G₀)
    exact Subgroup.mem_subgroupOf.1 hr'
  refine ⟨ggRootSub (ggU .twistedE6 n f).D ψ β u, ggRootSub (ggU .twistedE6 n f).D ψ (-β) u,
    key β _ hβ (hle1.trans_le inf_le_left) hle,
    key (-β) _ hβn (hle2.trans_le inf_le_left) hlem, ⟨β, hβ, Or.inl hlong, u, rfl, rfl⟩, ?_⟩
  exact ⟨{ α := α, α_mem := hα, wD := w, wD_mem := hw,
           pair_one := fun _ => ⟨hcard, hle1, hcardm, hle2, hV, hVm⟩,
           pair_two := fun h2 => absurd (hb1.symm.trans h2) (by norm_num) }⟩

end CFSG.StandardType.LieKnownR2.ExcPos

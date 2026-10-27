module

public import CFSG.LocalAnalysis.StandardType.GGExcCorootComponent
public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGLatOrth
public import CFSG.LocalAnalysis.StandardType.GGExcRootGroupsCommute
public import CFSG.LocalAnalysis.StandardType.GGSixExceptionalTagSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section FusionWitness

private theorem neg_mem_roots_lat {U' : Type} [Group U'] (Δ : UniversalRootDatum U')
    {α : Fin Δ.rank → ℤ} (hα : α ∈ Δ.roots) : -α ∈ Δ.roots := by
  rcases hα with h | h
  · rcases h with ⟨w, i, rfl⟩
    refine Or.inl ⟨w * (coxeterMatrix Δ.isFiniteType).toCoxeterSystem.simple i, i, ?_⟩
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg]
  · rcases h with ⟨w, i, hi, rfl⟩
    refine Or.inr ⟨w * (coxeterMatrix Δ.isFiniteType).toCoxeterSystem.simple i, i, hi, ?_⟩
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg, smul_neg]

private theorem commute_rankOne_iSup (hcomm : GGRootGroupsCommute) (t : StatedLieTag)
    (n f : ℕ) (ht : GGExcFive t) {α : Fin (ggU t n f).D.rank → ℤ}
    (hα : α ∈ (ggU t n f).D.roots) (Z : Set (Fin (ggU t n f).D.rank → ℤ))
    (hZsub : ∀ β ∈ Z, β ∈ (ggU t n f).D.roots)
    (horth : ∀ β ∈ Z, StronglyOrth (ggU t n f).D α β)
    {G : Type} [Group G] (ψ : (ggU t n f).K →* G) {x' : G}
    (hx' : x' ∈ ((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)).map ψ)
    {t₀ : G} (ht₀ : t₀ ∈ ⨆ β ∈ Z, ((ggU t n f).D.rootGroup β).map ψ) :
    x' * t₀ = t₀ * x' := by
  have hlocal : ∀ β ∈ Z,
      ((ggU t n f).D.rootGroup β).map ψ ≤
        Subgroup.centralizer
          (((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)).map ψ : Set G) := by
    intro β hβ
    have hcommα : ∀ a ∈ (ggU t n f).D.rootGroup α,
        ∀ b ∈ (ggU t n f).D.rootGroup β, a * b = b * a :=
      hcomm t n f ht α hα β (hZsub β hβ) (horth β hβ)
    have hnegα : (-α) ∈ (ggU t n f).D.roots := neg_mem_roots_lat (ggU t n f).D hα
    have hcommneg : ∀ a ∈ (ggU t n f).D.rootGroup (-α),
        ∀ b ∈ (ggU t n f).D.rootGroup β, a * b = b * a :=
      hcomm t n f ht (-α) hnegα β (hZsub β hβ)
        (stronglyOrth_neg (ggU t n f).D (horth β hβ))
    have hsup : ((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)) ≤
        Subgroup.centralizer ((ggU t n f).D.rootGroup β : Set (ggU t n f).K) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        exact fun b hb => (hcommα a ha b hb).symm
      · rw [Subgroup.mem_centralizer_iff]
        exact fun b hb => (hcommneg a ha b hb).symm
    rintro x ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hsup ha) b hb]
  have hjoin : (⨆ β ∈ Z, ((ggU t n f).D.rootGroup β).map ψ) ≤
      Subgroup.centralizer
        (((ggU t n f).D.rootGroup α ⊔ (ggU t n f).D.rootGroup (-α)).map ψ : Set G) :=
    iSup_le fun β => iSup_le fun hβ => hlocal β hβ
  exact Subgroup.mem_centralizer_iff.mp (hjoin ht₀) x' hx'

theorem sixRootFusionWitnessOn_exc_of_stdForm (hreg : GGExcRegimeInput)
    (hstd : GGSixExcStandardFormInput) (hcoroot : GGLatCorootExc)
    (hW1 : GGExcKGInvolutions ggASClass) (horth : GGLatOrthExc ggASClass)
    (hcomm : GGRootGroupsCommute) (t : StatedLieTag) (ht : GGExcFive t) :
    GGSixRootFusionWitnessOn fun t' _ _ _ => t' = t := by
  intro G _ _ p B Bs x L D J t' n f ψ ht' hctx s1 s2 E r hchoice hCr hodd s hs hs2ord
  subst t'
  have hp := hctx.prime
  have hp2 := hctx.ne_two
  obtain ⟨S, π, F, hS, hπ, -, -, -, hF3, hF5⟩ :=
    hstd G p B Bs x L D J t n f ψ ht hctx s1
      (hreg G p B Bs x L D J t n f ψ ht hctx s1)
  have hks : GGKnownSetting t n f ψ := ggKnownSetting_of_ctx hctx s1
  have hsψ : s ∈ ψ.range := by rw [hctx.range_eq]; exact hs
  obtain ⟨g, hgψ, Z, hZ, ht₀Z⟩ := hW1 t n f ht G ψ hks s hsψ hs2ord
  obtain ⟨α, hα, hαcls, hortho⟩ := horth t n f ht Z hZ
  have hZsub : ∀ β ∈ Z, β ∈ (ggU t n f).D.roots :=
    fun β hβ => ggASClass_subset_roots t n f ht Z hZ hβ
  obtain ⟨⟨x', hx'rank, hx'ord⟩, hF5all⟩ := hF5 α hα hαcls
  obtain ⟨h, hhG0, αB, hαB, hαBπ, k, hk, b, hb, hbcoord⟩ := hF5all x' hx'rank hx'ord
  have hx't₀ : x' * (g * s * g⁻¹) = (g * s * g⁻¹) * x' :=
    commute_rankOne_iSup hcomm t n f ht hα Z hZsub hortho ψ hx'rank ht₀Z
  set y : G := g⁻¹ * x' * g with hydef
  set m : G := h * g with hmdef
  have hy : y * s = s * y := by
    have h2 : g⁻¹ * (x' * (g * s * g⁻¹)) * g = g⁻¹ * ((g * s * g⁻¹) * x') * g := by
      rw [hx't₀]
    calc y * s = g⁻¹ * (x' * (g * s * g⁻¹)) * g := by rw [hydef]; group
      _ = g⁻¹ * ((g * s * g⁻¹) * x') * g := h2
      _ = s * y := by rw [hydef]; group
  have hgG0 : g ∈ ggG0 p B x L D J := hctx.range_eq ▸ hgψ
  have hmG0 : m ∈ ggG0 p B x L D J := by
    rw [hmdef]; exact Subgroup.mul_mem _ hhG0 hgG0
  have hmM : m ∈ ggM p B x L D J := Subgroup.le_normalizer hmG0
  have hmym : m * y * m⁻¹ = (b : G) := by
    rw [hmdef, hydef]
    calc (h * g) * (g⁻¹ * x' * g) * (h * g)⁻¹ = h * x' * h⁻¹ := by group
      _ = (b : G) := hb.symm
  obtain ⟨hb1, L₂, hL₂, hcard⟩ :=
    exists_component_of_coroot hcoroot t f ht p hp hp2 Bs (ggG0 p B x L D J) S π hS hπ F αB
      hαB hαBπ k hk b hbcoord
  have hb1' : (b : G) ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  refine Or.inr (Or.inl ⟨y, hy, m, hmM, ?_⟩)
  rw [hmym]
  exact ⟨hb1', Or.inr (Or.inr ⟨b.2, L₂, hL₂, Or.inl hcard⟩)⟩

theorem sixRootFusionWitnessExc_of_stdForm (hreg : GGExcRegimeInput)
    (hstd : GGSixExcStandardFormInput) (hcoroot : GGLatCorootExc)
    (hW1 : GGExcKGInvolutions ggASClass) (horth : GGLatOrthExc ggASClass)
    (hcomm : GGRootGroupsCommute) : GGSixRootFusionWitnessExcTags :=
  ⟨sixRootFusionWitnessOn_exc_of_stdForm hreg hstd hcoroot hW1 horth hcomm .F4 (Or.inl rfl),
    sixRootFusionWitnessOn_exc_of_stdForm hreg hstd hcoroot hW1 horth hcomm .E6
      (Or.inr (Or.inl rfl)),
    sixRootFusionWitnessOn_exc_of_stdForm hreg hstd hcoroot hW1 horth hcomm .E7
      (Or.inr (Or.inr (Or.inl rfl))),
    sixRootFusionWitnessOn_exc_of_stdForm hreg hstd hcoroot hW1 horth hcomm .E8
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    sixRootFusionWitnessOn_exc_of_stdForm hreg hstd hcoroot hW1 horth hcomm .twistedE6
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

end FusionWitness

end CFSG.StandardType

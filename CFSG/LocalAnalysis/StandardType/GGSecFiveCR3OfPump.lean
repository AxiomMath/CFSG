module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDichotomy
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Subgroup

@[expose] def GGWeylReflTripleInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs)),
    p.Prime → p ≠ 2 → IsElemAbelian p Bs → (∀ a ∈ A, ¬ GGIsTransvection p a) →
      GGWeylReflectionGroup p A → ¬ GGWeylOfType p CoxeterMatrix.G₂ A →
        ∀ r₁ ∈ A, ∀ r₂ ∈ A, ∀ s ∈ A, GGIsReflection p r₁ → GGIsReflection p r₂ →
          GGIsReflection p s → orderOf (r₁ * r₂) = 3 →
            Nat.card (closure ({r₁, r₂, s} : Set (MulAut ↥Bs))) ∣ 48

@[expose] def GGSecFiveCR3Input
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ r₁ ∈ ggAutomizer J Bs, ∀ r₂ ∈ ggAutomizer J Bs, GGIsReflection p r₁ →
        GGIsReflection p r₂ → orderOf (r₁ * r₂) = 3 →
        ∀ g ∈ ggInduced ⊤ Bs, ∀ t' : MulAut ↥Bs, GGIsReflection p t' → GGRealized p Bs t' →
          ¬ (Commute t' (g * r₁ * g⁻¹) ∧ Commute t' (g * r₂ * g⁻¹)) →
            Nat.card (closure ({g * r₁ * g⁻¹, g * r₂ * g⁻¹, t'} : Set (MulAut ↥Bs))) ∣ 48

private theorem cr3_conj_back {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} {g : MulAut ↥Bs} (hg : g ∈ ggInduced ⊤ Bs) {t' : MulAut ↥Bs}
    (ht'r : GGIsReflection p t') (ht'R : GGRealized p Bs t') (r₁ r₂ : MulAut ↥Bs) :
    GGRealized p Bs (g⁻¹ * t' * g) ∧ GGIsReflection p (g⁻¹ * t' * g) ∧
      Nat.card (closure ({g * r₁ * g⁻¹, g * r₂ * g⁻¹, t'} : Set (MulAut ↥Bs))) =
        Nat.card (closure ({r₁, r₂, g⁻¹ * t' * g} : Set (MulAut ↥Bs))) := by
  obtain ⟨n, -, hnN, hn⟩ := hg
  have hgn : g = ggConjAut Bs hnN := MulEquiv.ext fun b => Subtype.ext (hn b)
  have hninv : n⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hnN
  have hinv : ggConjAut Bs hninv = g⁻¹ := by
    rw [hgn]
    refine eq_inv_of_mul_eq_one_left (MulEquiv.ext fun b => Subtype.ext ?_)
    show n⁻¹ * (n * (b : G) * n⁻¹) * n⁻¹⁻¹ = b
    group
  have hsR : GGRealized p Bs (ggConjAut Bs hninv * t' * (ggConjAut Bs hninv)⁻¹) :=
    GGRealized.conj hp ht'R hninv
  rw [hinv, inv_inv] at hsR
  refine ⟨hsR, by simpa using ht'r.conj g⁻¹, ?_⟩
  have himg : (MulAut.conj g).toMonoidHom '' ({r₁, r₂, g⁻¹ * t' * g} : Set (MulAut ↥Bs)) =
      {g * r₁ * g⁻¹, g * r₂ * g⁻¹, t'} := by
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    congr 2
    group
  rw [← himg, ← MonoidHom.map_closure]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_closure_conj_dvd_48_of_weyl (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRT : GGWeylReflTripleInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hconf : GGConfig p B Bs x L D J)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNT : GGNoTransvection p Bs)
    (hWL : GGWeylReflectionGroup p (ggAutomizer L Bs) ∧
      ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer L Bs))
    (hWK : ∀ (d : G) (K : Subgroup G), GGNbr p B x D J d K →
      GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
        ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs))
    {r₁ r₂ : MulAut ↥Bs} (hr₁J : r₁ ∈ ggAutomizer J Bs) (hr₂J : r₂ ∈ ggAutomizer J Bs)
    (hr₁ : GGIsReflection p r₁) (hr₂ : GGIsReflection p r₂) (hord : orderOf (r₁ * r₂) = 3)
    {g : MulAut ↥Bs} (hg : g ∈ ggInduced ⊤ Bs) {t' : MulAut ↥Bs} (ht'r : GGIsReflection p t')
    (ht'R : GGRealized p Bs t')
    (hnc : ¬ (Commute t' (g * r₁ * g⁻¹) ∧ Commute t' (g * r₂ * g⁻¹))) :
    Nat.card (closure ({g * r₁ * g⁻¹, g * r₂ * g⁻¹, t'} : Set (MulAut ↥Bs))) ∣ 48 := by
  obtain ⟨hp, -, -, -, -⟩ := hconf.tableB_facts
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have hBsab : IsElemAbelian p Bs := hconf.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hNoTv : ∀ X : Subgroup G, ∀ a ∈ ggAutomizer X Bs, ¬ GGIsTransvection p a := by
    intro X a ha
    obtain ⟨m, -, hmN, hm⟩ := mem_ggAutomizer_iff.mp ha
    exact hNT a ⟨m, Subgroup.mem_top m, hmN, hm⟩
  obtain ⟨hsR, hsr, hcard⟩ := cr3_conj_back hp hg ht'r ht'R r₁ r₂
  set s := g⁻¹ * t' * g with hs
  rw [hcard]
  obtain ⟨Js, hind, hJC, hpc⟩ := hsR
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hconf.1 hconf.2.2
  rcases ggDichotomy_refined hL hP hconf hInn hsr hind hJC hpc with hJsL | ⟨d, K, hnb, hJK, hJsK⟩ |
    hcomm
  ·
    obtain ⟨hJL, -, -⟩ := eq_of_le_of_stdSub hconf.1 hconf.2.2 hpJ
    obtain ⟨m, hm, hmN, hm'⟩ := hind
    obtain ⟨hW, hG2⟩ := hWL
    exact hRT G p Bs (ggAutomizer L Bs) hp hp2 hBsab (hNoTv L) hW hG2 r₁
      (ggAutomizer_mono Bs hJL hr₁J) r₂ (ggAutomizer_mono Bs hJL hr₂J) s
      (Subgroup.subset_closure ⟨m, hJsL hm, hmN, hm'⟩) hr₁ hr₂ hsr hord
  ·
    obtain ⟨m, hm, hmN, hm'⟩ := hind
    obtain ⟨hW, hG2⟩ := hWK d K hnb
    exact hRT G p Bs (ggAutomizer K Bs) hp hp2 hBsab (hNoTv K) hW hG2 r₁
      (ggAutomizer_mono Bs hJK hr₁J) r₂ (ggAutomizer_mono Bs hJK hr₂J) s
      (Subgroup.subset_closure ⟨m, hJsK hm, hmN, hm'⟩) hr₁ hr₂ hsr hord
  ·
    exfalso
    apply hnc
    have hc₁ : Commute s r₁ := hcomm r₁ (mem_ggAutomizer_iff.mp hr₁J)
    have hc₂ : Commute s r₂ := hcomm r₂ (mem_ggAutomizer_iff.mp hr₂J)
    have ht' : t' = g * s * g⁻¹ := by rw [hs]; group
    rw [ht']
    exact ⟨(hc₁.conj g), (hc₂.conj g)⟩

theorem ggSecFiveCR3Input_of_pump
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    (hRT : GGWeylReflTripleInput) :
    GGSecFiveCR3Input := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit r₁ hr₁J r₂ hr₂J hr₁ hr₂ hord g hg t' ht'r ht'R hnc
  exact card_closure_conj_dvd_48_of_weyl hL hP hRT hcfg.1.1 hcfg.1.2.2.1 hcfg.1.2.2.2.1
    (hPump.1 G p B Bs x L D J 𝒦 hcfg hsplit)
    (fun d K hnb => hPump.2 G p B Bs x L D J 𝒦 hcfg hsplit d K hnb)
    hr₁J hr₂J hr₁ hr₂ hord hg ht'r ht'R hnc

end CFSG.StandardType

end

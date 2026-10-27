module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneRestCX

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Defs

variable {G : Type} [Group G]

@[expose] def GGNbrClauseFiveMarking (p : ℕ) (x : G) (K : Subgroup G) : Prop :=
  LargeEvenMarking K (fun lab _ _ I F θ =>
    LargeEvenHalfSplit p lab (Subgroup.center K = ⊥) ∨
      LargeEvenPrimeField p lab I F (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x))

end Defs

section Inputs

@[expose] def GGNonsplitCompLiftInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ 2 ^ f + 1 →
    ∀ x y : G, x ^ p = 1 → y ^ p = 1 → x * y = y * x →
      x ∈ Subgroup.normalizer (G₀ : Set G) → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ x → GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ K : Subgroup G, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {x}) → ¬ p ∣ Nat.card K →
        ∃ K' : Subgroup G, IsComponentOf K' (G₀ ⊓ Subgroup.centralizer {y}) ∧ K ≤ K'

@[expose] def GGNonsplitNbrMarkingInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ 2 ^ f + 1 →
    ∀ x y : G, x ^ p = 1 → y ^ p = 1 → x * y = y * x →
      x ∈ Subgroup.normalizer (G₀ : Set G) → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ x → GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ K K' : Subgroup G, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {x}) →
        ¬ p ∣ Nat.card K → IsComponentOf K' (G₀ ⊓ Subgroup.centralizer {y}) → K ≤ K' →
        x ∈ Subgroup.normalizer (K' : Set G) → ¬ GGNbrClauseFiveMarking p x K'

end Inputs

section Config

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem exists_ggNbr_not_le_centralizer {K : Subgroup G}
    (hK : CFSG.Assembly.IsQuasisimple K) (hKG : K ≤ ggG0 p B x L D J)
    (hKL : K ≤ Subgroup.centralizer (L : Set G)) :
    ∃ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' ∧
      ¬ K' ≤ Subgroup.centralizer (K : Set G) := by
  by_contra hall
  push Not at hall
  apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hK
  have hG0 : ggG0 p B x L D J ≤ Subgroup.centralizer (K : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mp hKL)
      (iSup_le fun y => iSup_le fun K' => iSup_le fun h => hall y K' h)
  exact hKG.trans hG0

theorem GGSixCtxV2.bstar_facts (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {y : G}
    (hy : y ∈ Bs) :
    x * y = y * x ∧ y ^ p = 1 ∧ y ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
      GGPsiInnerDiag Δ ψ y := by
  have hxBs : x ∈ Bs := h.d_le_bstar h.x_mem_d
  exact ⟨congrArg Subtype.val (h.bstar.2.1.1.is_comm.comm (⟨x, hxBs⟩ : ↥Bs) ⟨y, hy⟩),
    h.bstar.2.1.2 y hy, h.bstar_le_normalizer hy, h.2.2.2.2.2.2.1.2 y hy⟩

theorem GGSixCtxV2.isComponentOf_inf_of_ggNbr (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {y : G}
    {K' : Subgroup G} (hnbr : GGNbr p B x D J y K') :
    IsComponentOf K' (ggG0 p B x L D J ⊓ Subgroup.centralizer {y}) := by
  have hc := (isComponentOf_of_isNeighborOf h.stdType (isNeighborOf_of_ggNbr h.stdSub hnbr)).1
  exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hc
    (le_inf (le_ggG0_of_ggNbr hnbr) hc.1) inf_le_right

theorem GGSixCtxV2.exists_ggNbr_le (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {K : Subgroup G}
    (hK : IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}))
    (hKL : K ≤ Subgroup.centralizer (L : Set G))
    (hlift : ∀ y ∈ Bs, ∃ K' : Subgroup G,
      IsComponentOf K' (ggG0 p B x L D J ⊓ Subgroup.centralizer {y}) ∧ K ≤ K') :
    ∃ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' ∧ y ∈ Bs ∧
      IsComponentOf K' (ggG0 p B x L D J ⊓ Subgroup.centralizer {y}) ∧ K ≤ K' := by
  obtain ⟨y, K', hnbr, hKK'⟩ :=
    exists_ggNbr_not_le_centralizer (B := B) (D := D) (J := J) hK.2.2 (hK.1.trans inf_le_left)
      hKL
  have hyBs : y ∈ Bs := h.bstar.1 hnbr.1.2.1
  have hK'c := h.isComponentOf_inf_of_ggNbr hnbr
  obtain ⟨Ky, hKy, hKKy⟩ := hlift y hyBs
  refine ⟨y, K', hnbr, hyBs, hK'c, ?_⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hKy hK'c with heq | hcomm
  · exact heq ▸ hKKy
  · exfalso
    apply hKK'
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
    exact hcomm.trans (Subgroup.centralizer_le hKKy)

end Config

section Main

theorem ggSixLayerCXNonsplitInput_of_kg (hlift : GGNonsplitCompLiftInput)
    (hmark : GGNonsplitNbrMarkingInput) : GGSixLayerCXNonsplitInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hq1 hq2 K hK hKL
  by_contra hpK
  have hpres := hctx.presents
  have hxBs : x ∈ Bs := hctx.d_le_bstar hctx.x_mem_d
  obtain ⟨-, hxp, hxN, hxD⟩ := hctx.bstar_facts hxBs
  obtain ⟨y, K', hnbr, hyBs, hK'c, hKK'⟩ := hctx.exists_ggNbr_le hK hKL fun y hy => by
    obtain ⟨hxy, hyp, hyN, hyD⟩ := hctx.bstar_facts hy
    exact hlift G t n f ψ _ hpres p hctx.prime hctx.ne_two hq1 hq2 x y hxp hyp hxy hxN hyN
      hxD hyD K hK hpK
  obtain ⟨hxy, hyp, hyN, hyD⟩ := hctx.bstar_facts hyBs
  have h5 := hctx.stdType.2.2.1 y K' (isNeighborOf_of_ggNbr hctx.stdSub hnbr)
  exact hmark G t n f ψ _ hpres p hctx.prime hctx.ne_two hq1 hq2 x y hxp hyp hxy hxN hyN hxD hyD
    K K' hK hpK hK'c hKK' (h5.1 (hctx.stdSub.1.1 hctx.x_mem_d)) h5.2

theorem ggSixLayerCXInput_of_nonsplitKG (hKG : GGLayerPDivInput)
    (hlift : GGNonsplitCompLiftInput) (hmark : GGNonsplitNbrMarkingInput) : GGSixLayerCXInput :=
  ggSixLayerCXInput_of_split hKG (ggSixLayerCXNonsplitInput_of_kg hlift hmark)

end Main

section Tags

@[expose] def GGNonsplitCompLiftTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ 2 ^ f + 1 →
    ∀ x y : G, x ^ p = 1 → y ^ p = 1 → x * y = y * x →
      x ∈ Subgroup.normalizer (G₀ : Set G) → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ x → GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ K : Subgroup G, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {x}) → ¬ p ∣ Nat.card K →
        ∃ K' : Subgroup G, IsComponentOf K' (G₀ ⊓ Subgroup.centralizer {y}) ∧ K ≤ K'

@[expose] def GGNonsplitNbrMarkingTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ 2 ^ f + 1 →
    ∀ x y : G, x ^ p = 1 → y ^ p = 1 → x * y = y * x →
      x ∈ Subgroup.normalizer (G₀ : Set G) → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ x → GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ K K' : Subgroup G, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {x}) →
        ¬ p ∣ Nat.card K → IsComponentOf K' (G₀ ⊓ Subgroup.centralizer {y}) → K ≤ K' →
        x ∈ Subgroup.normalizer (K' : Set G) → ¬ GGNbrClauseFiveMarking p x K'

theorem ggNonsplitCompLiftInput_of_tags (h : ∀ t, GGNonsplitCompLiftTag t) :
    GGNonsplitCompLiftInput := by
  intro G _ _ t
  exact h t G

theorem ggNonsplitNbrMarkingInput_of_tags (h : ∀ t, GGNonsplitNbrMarkingTag t) :
    GGNonsplitNbrMarkingInput := by
  intro G _ _ t
  exact h t G

theorem not_ggPresentsG0_of_placeholder {G : Type} [Group G] (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) {n f : ℕ} {ψ : (ggU t n f).K →* G} {G₀ : Subgroup G} :
    ¬ GGPresentsG0 G₀ (ggU t n f).D t n f ψ := by
  intro hpres
  have hrk := hpres.1.2
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem not_ggPresentsG0_POmegaOdd {G : Type} [Group G] {n f : ℕ}
    {ψ : (ggU .POmegaOdd n f).K →* G} {G₀ : Subgroup G} :
    ¬ GGPresentsG0 G₀ (ggU .POmegaOdd n f).D .POmegaOdd n f ψ :=
  fun hpres => absurd rfl hpres.1.1.2.2.2

theorem ggNonsplitCompLiftTag_of_vacuous (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits ∨ t = .POmegaOdd) : GGNonsplitCompLiftTag t := by
  intro G _ _ n f ψ G₀ hpres
  rcases ht with h | h | h | h | h | h | rfl
  all_goals first
    | exact absurd hpres not_ggPresentsG0_POmegaOdd
    | exact absurd hpres (not_ggPresentsG0_of_placeholder t (by simp [h]))

theorem ggNonsplitNbrMarkingTag_of_vacuous (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits ∨ t = .POmegaOdd) : GGNonsplitNbrMarkingTag t := by
  intro G _ _ n f ψ G₀ hpres
  rcases ht with h | h | h | h | h | h | rfl
  all_goals first
    | exact absurd hpres not_ggPresentsG0_POmegaOdd
    | exact absurd hpres (not_ggPresentsG0_of_placeholder t (by simp [h]))

@[expose] def GGNonsplitTag (t : StatedLieTag) : Prop :=
  GGNonsplitCompLiftTag t ∧ GGNonsplitNbrMarkingTag t

theorem ggNonsplitTag_all (hPSL : GGNonsplitTag .PSL) (hPSU : GGNonsplitTag .PSU)
    (hPSp : GGNonsplitTag .PSp) (hPlus : GGNonsplitTag .POmegaPlus)
    (hMinus : GGNonsplitTag .POmegaMinus) (hF4 : GGNonsplitTag .F4) (hE6 : GGNonsplitTag .E6)
    (hE7 : GGNonsplitTag .E7) (hE8 : GGNonsplitTag .E8) (hTwE6 : GGNonsplitTag .twistedE6) :
    ∀ t, GGNonsplitTag t := by
  intro t
  cases t with
  | PSL => exact hPSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTwE6
  | _ =>
    exact ⟨ggNonsplitCompLiftTag_of_vacuous _ (by simp),
      ggNonsplitNbrMarkingTag_of_vacuous _ (by simp)⟩

theorem ggSixLayerCXNonsplitInput_of_tags (hPSL : GGNonsplitTag .PSL) (hPSU : GGNonsplitTag .PSU)
    (hPSp : GGNonsplitTag .PSp) (hPlus : GGNonsplitTag .POmegaPlus)
    (hMinus : GGNonsplitTag .POmegaMinus) (hF4 : GGNonsplitTag .F4) (hE6 : GGNonsplitTag .E6)
    (hE7 : GGNonsplitTag .E7) (hE8 : GGNonsplitTag .E8) (hTwE6 : GGNonsplitTag .twistedE6) :
    GGSixLayerCXNonsplitInput :=
  have h := ggNonsplitTag_all hPSL hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6
  ggSixLayerCXNonsplitInput_of_kg (ggNonsplitCompLiftInput_of_tags fun t => (h t).1)
    (ggNonsplitNbrMarkingInput_of_tags fun t => (h t).2)

end Tags

end CFSG.StandardType

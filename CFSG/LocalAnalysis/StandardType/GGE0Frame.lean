module

public import CFSG.LocalAnalysis.StandardType.GGOTwoStarFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatKGDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

@[expose] def GGE0Concl {G : Type} [Group G] (E₀ C₀ : Subgroup G) : Prop :=
  E₀ ≤ Subgroup.normalizer (C₀ : Set G) ∧
    (LargeEvenMarking ↥C₀ (fun _ _ _ _ _ _ => True) →
      LargeEvenMarking ↥C₀ (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ ε ∈ E₀, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = ε⁻¹ * l * ε) φ))

theorem ggE0Concl_mono {G : Type} [Group G] {E₁ E₂ C₀ : Subgroup G} (h : E₁ ≤ E₂)
    (hc : GGE0Concl E₂ C₀) : GGE0Concl E₁ C₀ := by
  refine ⟨h.trans hc.1, fun hm => ?_⟩
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1, fun ε hε => hP.2 ε (h hε)⟩)
    (hc.2 hm)

@[expose] def GGE0At
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G), b ∈ Bs → b ≠ 1 →
        ∀ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} →
          ∀ C₀ : Subgroup G, IsComponentOf C₀ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
            GGE0Concl (D.map (MulAut.conj m⁻¹).toMonoidHom) C₀

theorem ggE0InnerDiagInput_of_at
    (h : ∀ t, GGE0At t) : GGE0InnerDiagInput :=
  fun G _ _ p B Bs x L D J t n f ψ => h t G p B Bs x L D J n f ψ

theorem ggE0At_of_small
    {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGE0At t := by
  intro G _ _ p B Bs x L D J n f ψ hctx
  have hrank : (ggU t n f).D.rank = 0 := lieUniversal_rank_eq_zero t n 2 f Nat.prime_two ht
  have h2 := hctx.2.2.2.1.2
  rw [hrank] at h2
  exact absurd h2 (by norm_num)

theorem ggE0At_POmegaOdd
    : GGE0At .POmegaOdd := by
  intro G _ _ p B Bs x L D J n f ψ hctx
  exact (hctx.2.2.2.1.1.2.2.2 rfl).elim

@[expose] def GGE0Rest
    : Prop :=
  GGE0At .PSL ∧ GGE0At .PSU ∧ GGE0At .PSp ∧ GGE0At .POmegaPlus ∧ GGE0At .POmegaMinus ∧
    GGE0At .F4 ∧ GGE0At .E6 ∧ GGE0At .E7 ∧ GGE0At .E8 ∧ GGE0At .twistedE6

theorem ggE0InnerDiagInput_of_rest
    (h : GGE0Rest) : GGE0InnerDiagInput := by
  obtain ⟨hL, hU, hSp, hP, hM, hF4, hE6, hE7, hE8, h2E6⟩ := h
  refine ggE0InnerDiagInput_of_at fun t => ?_
  cases t with
  | PSL => exact hL
  | PSU => exact hU
  | PSp => exact hSp
  | POmegaOdd => exact ggE0At_POmegaOdd
  | POmegaPlus => exact hP
  | POmegaMinus => exact hM
  | G2 => exact ggE0At_of_small (Or.inl rfl)
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact h2E6
  | trialityD4 => exact ggE0At_of_small (Or.inr (Or.inl rfl))
  | twistedB2 => exact ggE0At_of_small (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 => exact ggE0At_of_small (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 => exact ggE0At_of_small (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits => exact ggE0At_of_small (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem ggE0_le_ggG0_inf_centralizer_of_diagInner {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (h : GGPsiDiagInnerAt t)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {b m : G} (hm : m ∈ ggM p B x L D J)
    (hEC : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b}) :
    D.map (MulAut.conj m⁻¹).toMonoidHom ≤ ggG0 p B x L D J ⊓ Subgroup.centralizer {b} := by
  intro z hz
  refine Subgroup.mem_inf.mpr ⟨?_, hEC hz⟩
  obtain ⟨d, hd, rfl⟩ := hz
  have hdBs : d ∈ Bs := hctx.bstar.1 (hctx.stdSub.1.1 hd)
  have hdG1 : d ∈ ggG1 ψ := ggBs_le_ggG1 hctx hdBs
  have hdG0 : d ∈ ggG0 p B x L D J := ggG1_le_ggG0_of_diagInner h hctx s1 hdG1
  have hm' : m⁻¹ ∈ ggM p B x L D J := Subgroup.inv_mem _ hm
  have hconj : m⁻¹ * d * m ∈ ggG0 p B x L D J := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hm' d).mp hdG0
  change MulAut.conj m⁻¹ d ∈ ggG0 p B x L D J
  simpa only [MulAut.conj_apply, inv_inv] using hconj

@[expose] def GGCentInnerDiagAt
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G), b ∈ Bs → b ≠ 1 →
        ∀ C₀ : Subgroup G, IsComponentOf C₀ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
          GGE0Concl (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) C₀

theorem ggE0At_of_centInnerDiag
    {t : StatedLieTag} (hd : GGPsiDiagInnerAt t) (h : GGCentInnerDiagAt t) : GGE0At t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b hb hb1 m hm hEC C₀ hC₀
  exact ggE0Concl_mono (ggE0_le_ggG0_inf_centralizer_of_diagInner hd hctx s1 hm hEC)
    (h G p B Bs x L D J n f ψ hctx s1 b hb hb1 C₀ hC₀)

end CFSG.StandardType

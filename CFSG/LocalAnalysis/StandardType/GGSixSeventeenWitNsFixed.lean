module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitNsWit
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLTag

public section

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

namespace WitNs

section General

variable {G : Type} [Group G]

theorem mem_normalizer_inf_centralizer {G₀ : Subgroup G} {x b : G}
    (hb : b ∈ Subgroup.normalizer (G₀ : Set G)) (hxb : x * b = b * x) :
    b ∈ Subgroup.normalizer ((G₀ ⊓ Subgroup.centralizer {x} : Subgroup G) : Set G) := by
  have hbx : b ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxb.symm
  have hbG := Subgroup.mem_normalizer_iff.mp hb
  have hbC := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hbx)
  exact Subgroup.mem_normalizer_iff.mpr fun h =>
    ⟨fun h' => ⟨(hbG h).mp h'.1, (hbC h).mp h'.2⟩, fun h' => ⟨(hbG h).mpr h'.1, (hbC h).mpr h'.2⟩⟩

variable [Finite G]

theorem mem_normalizer_of_le_isComponentOf {H K J : Subgroup G} {y : G}
    (hK : IsComponentOf K H) (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hJK : J ≤ K)
    (hyH : y ∈ Subgroup.normalizer (H : Set G))
    (hyJ : y ∈ Subgroup.centralizer (J : Set G)) : y ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hn
  have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hK y
  have e : H.map (MulAut.conj y).toMonoidHom = H :=
    CFSG.LocalAnalysis.ComponentInitial.conjSub_eq_of_mem_normalizer hyH
  rw [e] at h1
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute h1 hK with h | h
  · exact hn (mem_normalizer_of_map_conj_eq h)
  · apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hJ
    have hJK' : J ≤ K.map (MulAut.conj y).toMonoidHom := by
      intro j hj
      refine ⟨j, hJK hj, ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hyJ j hj
      change y * j * y⁻¹ = j
      rw [← this]
      group
    exact (hJK'.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)).trans
      (Subgroup.centralizer_le hJK)

end General

section Tag

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}

theorem dvd_card_of_le_centralizer_of_tag (hT : GGNonsplitTag t)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (hq1 : ¬ p ∣ 2 ^ f - 1)
    (hq2 : ¬ p ∣ 2 ^ f + 1) {K : Subgroup G}
    (hK : IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}))
    (hKL : K ≤ Subgroup.centralizer (L : Set G)) : p ∣ Nat.card K := by
  by_contra hpK
  have hpres := hctx.presents
  have hxBs : x ∈ Bs := hctx.d_le_bstar hctx.x_mem_d
  obtain ⟨-, hxp, hxN, hxD⟩ := hctx.bstar_facts hxBs
  obtain ⟨y, K', hnbr, hyBs, hK'c, hKK'⟩ := hctx.exists_ggNbr_le hK hKL fun y hy => by
    obtain ⟨hxy, hyp, hyN, hyD⟩ := hctx.bstar_facts hy
    exact hT.1 G n f ψ _ hpres p hctx.prime hctx.ne_two hq1 hq2 x y hxp hyp hxy hxN hyN hxD hyD K
      hK hpK
  obtain ⟨hxy, hyp, hyN, hyD⟩ := hctx.bstar_facts hyBs
  have h5 := hctx.stdType.2.2.1 y K' (isNeighborOf_of_ggNbr hctx.stdSub hnbr)
  exact hT.2 G n f ψ _ hpres p hctx.prime hctx.ne_two hq1 hq2 x y hxp hyp hxy hxN hyN hxD hyD K K'
    hK hpK hK'c hKK' (h5.1 (hctx.stdSub.1.1 hctx.x_mem_d)) h5.2

theorem dvd_card_of_isComponentOf_of_tag (hT : GGNonsplitTag t) (hP : GGLayerPDivTag t)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) {b : G} (hb : b ∈ Bs)
    {L₁ : Subgroup G} (hL₁ : IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b})) :
    p ∣ Nat.card L₁ := by
  have hpres := hctx.presents
  obtain ⟨hxb, hbp, hbN, hbD⟩ := hctx.bstar_facts hb
  by_cases hq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1
  · exact hP G n f ψ _ hpres p hctx.prime hctx.ne_two hq b hbp hbN hbD L₁ hL₁
  push Not at hq
  obtain ⟨hq1, hq2⟩ := hq
  by_contra hpL
  obtain ⟨-, hxp, hxN, hxD⟩ := hctx.bstar_facts (hctx.d_le_bstar hctx.x_mem_d)
  obtain ⟨K, hK, hLK⟩ := hT.1 G n f ψ _ hpres p hctx.prime hctx.ne_two hq1 hq2 b x hbp hxp
    hxb.symm hbN hxN hbD hxD L₁ hL₁ hpL
  by_cases hKL : K = L
  ·
    subst hKL
    have hbL₁ : b ∈ Subgroup.centralizer (L₁ : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun l hl => Subgroup.mem_centralizer_singleton_iff.mp (hL₁.1 hl).2
    have hbK := mem_normalizer_of_le_isComponentOf hK hL₁.2.2 hLK
      (mem_normalizer_inf_centralizer hbN hxb) hbL₁
    exact hT.2 G n f ψ _ hpres p hctx.prime hctx.ne_two hq1 hq2 b x hbp hxp hxb.symm hbN hxN hbD
      hxD L₁ K hL₁ hpL hK hLK hbK
      (largeEvenMarking_mono (fun lab R _ I F θ h => Or.inl (Or.inl h.1)) hctx.stdType.1)
  ·
    have hKc := hctx.le_centralizer_of_isComponentOf_ne hK hKL
    exact hctx.not_dvd_card_of_isComponentOf_le hK hKc
      (dvd_card_of_le_centralizer_of_tag hT hctx hq1 hq2 hK hKc)

end Tag

section PSL

theorem dvd_card_of_isComponentOf_PSL {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU .PSL n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSL n f).D .PSL n f ψ) {b : G} (hb : b ∈ Bs)
    {L₁ : Subgroup G} (hL₁ : IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b})) :
    p ∣ Nat.card L₁ :=
  dvd_card_of_isComponentOf_of_tag ggNonsplitTag_PSL ggLayerPDivTag_PSL hctx hb hL₁

end PSL

end WitNs

end CFSG.StandardType

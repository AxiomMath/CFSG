module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalf

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
  ExcFrames ExcFramesHalf

section KG


@[expose] def GGExcHalfTwoLocalInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    p ∣ Nat.card K + 1 → (p = 3 ∨ p = 5) →
      ∃ E U : Subgroup (adjointGroup τ K), IsElemAbelian p E ∧ Nat.card E = p ^ (τ.rank - 1) ∧
        U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set (adjointGroup τ K))

@[expose] def GGExcHalfMaxElemInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    p ∣ Nat.card K + 1 → (p = 3 ∨ p = 5) →
      ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → p ^ (τ.rank - 1) ≤ Nat.card E →
        (∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E) →
          p ^ τ.rank ≤ Nat.card E

theorem pow_le_card_of_kg {τ : Tag} {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    {G : Type} [Group G] [Finite G] (χ : adjointGroup τ K →* G) (hχ : Function.Injective χ)
    {B Bs : Subgroup G} (hBsR : Bs ≤ χ.range) (hB : GGBstar p B Bs)
    (hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G)
    (h1 : ∃ E U : Subgroup (adjointGroup τ K), IsElemAbelian p E ∧
      Nat.card E = p ^ (τ.rank - 1) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        E ≤ Subgroup.normalizer (U : Set (adjointGroup τ K)))
    (h2 : ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E →
      p ^ (τ.rank - 1) ≤ Nat.card E →
        (∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E) →
          p ^ τ.rank ≤ Nat.card E) :
    p ^ τ.rank ≤ Nat.card Bs := by
  obtain ⟨E, U, hE, hEc, hU, hU2, hEU⟩ := h1
  have hrk : τ.rank - 1 ≤ LargeEvenTwoLocalRank p G := by
    have hUne : U.map χ ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hχ]
      exact hU
    have hTL : IsTwoLocal (Subgroup.normalizer ((U.map χ : Subgroup G) : Set G)) :=
      ⟨_, hUne, hU2.map _, rfl⟩
    have hle : E.map χ ≤ Subgroup.normalizer ((U.map χ : Subgroup G) : Set G) := by
      rintro _ ⟨e, he, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hn := Subgroup.mem_normalizer_iff.mp (hEU he)
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨e * u * e⁻¹, (hn u).mp hu, by simp only [map_mul, map_inv]⟩
      · rintro ⟨u', hu', hyu⟩
        have hy : y = χ (e⁻¹ * u' * e) := by
          simp only [map_mul, map_inv, hyu]
          group
        refine ⟨_, ?_, hy.symm⟩
        have h3 := (hn (e⁻¹ * u' * e)).mpr (by
          rw [show e * (e⁻¹ * u' * e) * e⁻¹ = u' by group]
          exact hu')
        exact h3
    refine TableB.le_twoLocalRank hp.one_lt hTL (TableB.le_pRank_of_le hp.one_lt hle
      (isElemAbelian_map_frame χ hE) ?_)
    rw [Subgroup.card_map_of_injective hχ, hEc]
  have hEs := isElemAbelian_comap_frame χ hχ hB.2.1
  have hcard : Nat.card (Bs.comap χ) = Nat.card Bs := card_comap_of_le_range χ hχ hBsR
  have hge : p ^ (τ.rank - 1) ≤ Nat.card (Bs.comap χ) := by
    rw [hcard]
    calc p ^ (τ.rank - 1) ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos hrk
      _ = Nat.card B := hBc.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hB.1
  have hmax : ∀ x ∈ Subgroup.centralizer ((Bs.comap χ : Subgroup _) : Set (adjointGroup τ K)),
      x ^ p = 1 → x ∈ Bs.comap χ := by
    intro x hx hxp
    refine hB.2.2.2 (χ x) ?_ (by rw [← map_pow, hxp, map_one])
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨y, rfl⟩ := hBsR hb
    have hy := Subgroup.mem_centralizer_iff.mp hx y hb
    rw [← map_mul, ← map_mul, hy]
  rw [← hcard]
  exact h2 _ hEs hge hmax

end KG

section Tags


theorem ggExcHalfBstarRankOn_E8Small_of_kg (h1 : GGExcHalfTwoLocalInput .E8)
    (h2 : GGExcHalfMaxElemInput .E8) : GGExcHalfBstarRankOn .E8 GGExcE8HalfSmallLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq, hs⟩ := hP
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpK : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK]; exact hpq
  obtain ⟨hinj, hBsR⟩ := halfE8_inj_le_range hctx hC
  exact pow_le_card_of_kg hp ψ hinj hBsR hctx.2.1 hctx.1.2.2.2.2.2.2.1.1.2.1
    (h1 _ p hp hp2 hpK hs) (h2 _ p hp hp2 hpK hs)

theorem ggExcHalfBstarRankOn_E7Small_of_kg
    (h1 : GGExcHalfTwoLocalInput .E7) (h2 : GGExcHalfMaxElemInput .E7) :
    GGExcHalfBstarRankOn .E7 GGExcE7HalfSmallLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq, hs⟩ := hP
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpK : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK]; exact hpq
  obtain ⟨χ, hχ, -, hBsR⟩ := halfE7_chi hctx hC
  exact pow_le_card_of_kg hp χ hχ hBsR hctx.2.1 hctx.1.2.2.2.2.2.2.1.1.2.1
    (h1 _ p hp hp2 hpK hs) (h2 _ p hp hp2 hpK hs)

@[expose] def GGSixBstarExcFramesRestHalfKG : Prop :=
  GGExcNonsplitRankInput .F4 ∧
    (GGExcHalfTwoLocalInput .E7 ∧ GGExcHalfMaxElemInput .E7) ∧ GGExcNonsplitRankInput .E7 ∧
      (GGExcHalfTwoLocalInput .E8 ∧ GGExcHalfMaxElemInput .E8) ∧
        GGSixBstarExcFrameOn .E8 GGExcE8RestLabel ∧
          GGSixBstarExcFrameOn .E6 GGExcE6SplitLabel ∧
            GGSixBstarExcFrameOn .F4 GGExcE6NonsplitLabel ∧
              GGSixBstarExcFrameOn .E6 GGExcTwE6SplitLabel ∧
                GGSixBstarExcFrameOn .F4 GGExcTwE6NonsplitLabel

theorem ggSixBstarExcFramesRestHalf_of_kg
    (h : GGSixBstarExcFramesRestHalfKG) : GGSixBstarExcFramesRestHalf := by
  obtain ⟨hF4N, ⟨hE7a, hE7b⟩, hE7N, ⟨hE8a, hE8b⟩, hE8N, hE6S, hE6N, hTwS, hTwN⟩ := h
  exact ⟨hF4N, ggExcHalfBstarRankOn_E7Small_of_kg hE7a hE7b, hE7N,
    ggExcHalfBstarRankOn_E8Small_of_kg hE8a hE8b, hE8N, hE6S, hE6N, hTwS, hTwN⟩

end Tags

end CFSG.StandardType

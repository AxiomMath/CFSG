module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesAutTrivial
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE8RestTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTags
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Minuscule CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration ExcFrames

section TagE8Rest


theorem ggSixBstarExcFrameOn_E8Rest_of_innerDiag
    (hVI : ∀ (G : Type) [Group G] (n f : ℕ) (ψ : (ggU .E8 n f).K →* G),
      ψ.ker ≤ Subgroup.center (ggU .E8 n f).K → ∀ c : G,
        GGPsiInnerDiag (ggU .E8 n f).D ψ c →
          ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G)) :
    GGSixBstarExcFrameOn .E8 GGExcE8RestLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hq1, hq2, hp5⟩ := hP
  right
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have := Fact.mk hp
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center (adjointGroup .E8 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  have hBsR : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := hVI G n f ψ hker b (hctx.2.2.2.2.2.2.1.2 b hb)
    have hbg' : b * g ∈ Subgroup.centralizer (ψ.range : Set G) := hbg
    have hg' : g ∈ ψ.range := hg
    rw [hCψ, Subgroup.mem_bot] at hbg'
    rw [eq_inv_of_mul_eq_one_left hbg']
    exact ψ.range.inv_mem hg'
  have hcfg : GGConfig p B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  obtain ⟨-, hBs, -, -, h4⟩ := hcfg.tableB_facts
  have hp7 : 7 ≤ p := by
    by_contra hlt
    have h2' := hp.two_le
    have h6 : p ≤ 6 := by omega
    interval_cases p
    · exact hp2 rfl
    · have hx : ¬ 3 ∣ 2 ^ f := fun hd =>
        absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
          (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
      have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    · exact absurd hp (by norm_num)
    · exact hp5 rfl
    · exact absurd hp (by norm_num)
  have hpq : ¬ p ∣ Nat.card (GaloisField 2 f) := by
    rw [hK]
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have h1 : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hq1
  have h2 : ¬ p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK]; exact hq2
  have hAel : IsElemAbelian p (Bs.comap ψ) := isElemAbelian_comap_frame ψ hinj hBs
  have hAc : p ^ 4 ≤ Nat.card (Bs.comap ψ) := by
    rw [card_comap_of_le_range ψ hinj hBsR]
    exact h4
  have hdata : ∀ (K₀ : Type) [Field K₀] [Finite K₀],
      ((Nat.card K₀ : ℕ) : ZMod p) = ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) →
        SylowTorus (adjointGroup .E8 K₀) p 4 := fun K₀ _ _ hres =>
    sylowTorus_E8_rest_of_four_le_card (GaloisField 2 f) hp hp7 hpq h1 h2 hAel hAc K₀ hres
  have hNF : ∀ α : MulAut (adjointGroup .E8 (GaloisField 2 f)), α ^ p = 1 →
      ∃ (x : ModGL .E8 (GaloisField 2 f)) (σ : GaloisField 2 f ≃+* GaloisField 2 f),
        x ∈ adjointGroup .E8 (GaloisField 2 f) ⊔ ⊥ ∧ σ ^ p = 1 ∧
          ∀ h : adjointGroup .E8 (GaloisField 2 f), (α h : ModGL .E8 (GaloisField 2 f)) =
            x * Units.map (entrywiseHom σ.toRingHom) (h : ModGL .E8 (GaloisField 2 f)) * x⁻¹ := by
    intro α hαp
    obtain ⟨hex, Θ, hΘ, -, -, -⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hf (GaloisField 2 f) hK .E8
        (Or.inr rfl)
    obtain ⟨⟨g₀, σ⟩, hgσ, -⟩ := hex α
    refine ⟨(g₀ : ModGL .E8 (GaloisField 2 f)), σ,
      Subgroup.mem_sup_left g₀.2, ?_, hgσ⟩
    have h1 : (Θ α) ^ p = 1 := by rw [← map_pow, hαp, map_one]
    rwa [hΘ α g₀ σ hgσ] at h1
  intro g hgM hgB hgp
  have hgN : g ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hgM
  refine centralizes_of_induced (k := 1) ⊥ bot_le hp.not_dvd_one (fun d hd => ?_) hdata hNF ψ hinj
    hBsR hBs h4 hgN hgB hgp
  rw [Subgroup.mem_bot.1 hd, pow_one]
  exact Subgroup.one_mem _

end TagE8Rest

section TagE8RestVI


theorem ggSixBstarExcFrameOn_E8Rest : GGSixBstarExcFrameOn .E8 GGExcE8RestLabel :=
  ggSixBstarExcFrameOn_E8Rest_of_innerDiag fun _ _ _ f ψ hker _ hc =>
    PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ hker hc

end TagE8RestVI

end CFSG.StandardType

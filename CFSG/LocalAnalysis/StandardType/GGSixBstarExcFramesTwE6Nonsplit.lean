module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFrames
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesAutTrivial
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesIsogenyTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesResidualLabels
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTags
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6NonsplitThree
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedCentralize
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg.Exceptional CFSG.Assembly.LowTwoRank
  CFSG.LieType.SeitzGeneration ExcFrames

section TagTwE6Nonsplit

theorem ggSixBstarExcFrameOn_TwE6NonsplitGeFive :
    GGSixBstarExcFrameOn .F4 (fun t _ f p => t = .twistedE6 ∧ ¬ p ∣ 2 ^ f + 1 ∧ p ≠ 3) := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq1, hp3⟩ := hP
  right
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have := Fact.mk hp
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hperf : commutator ↥ψ.range = ⊤ := by rw [hrange]; exact hctx.2.2.2.2.2.1.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  obtain ⟨χ, hχinj, hχrange⟩ := exists_injective_factor_twistedE6 hf ψ hker hCψ
  have hBs : IsElemAbelian p Bs := hctx.2.1.2.1
  have hBsR : Bs ≤ χ.range := by
    rw [hχrange]
    intro b hb
    refine mem_range_of_innerDiag_twistedE6 hp hp2 hf (fun h => hp3 h.1) ψ hker hperf hCψ ?_
      (hBs.2 b hb) (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hrange]
    exact hctx.2.2.2.2.2.2.1.1 hb
  have hcfg : GGConfig p B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  obtain ⟨-, -, -, -, h4⟩ := hcfg.tableB_facts
  have hp3' : 3 < p := by
    by_contra hlt
    have h2' := hp.two_le
    have h3 : p ≤ 3 := by omega
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
  have h5 : 5 ≤ p := by
    by_contra h
    have h4' : p = 4 := by omega
    rw [h4'] at hp
    exact absurd hp (by norm_num)
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hpq : ¬ p ∣ 2 ^ f := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  set σ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) :=
    iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : σ.toRingHom = frobQ 2 f := RingHom.ext fun c => by
    change σ c = frobQ 2 f c
    rw [hσ, frobQ_apply]
  have hAel : IsElemAbelian p (Bs.comap χ) := isElemAbelian_comap_frame χ hχinj hBs
  have hAc : p ^ 4 ≤ Nat.card (Bs.comap χ) := by
    rw [card_comap_of_le_range χ hχinj hBsR]
    exact h4
  have he1 : orderOf (((2 ^ f : ℕ)) : ZMod p) = 1 :=
    orderOf_eq_one_of_four_le_card_graphFixed Nat.prime_two hf (GaloisField 2 (2 * f)) hK σ hσ
      hσθ hp h5 hpq hpq1 hAel hAc
  have hdata := sylowData_twistedE6_one hp h5 he1
  intro g hgM hgB hgp
  have hgN : g ∈ Subgroup.normalizer (χ.range : Set G) := by
    rw [show (χ.range : Set G) = (ψ.range : Set G) by rw [hχrange], hrange]
    exact hgM
  exact centralizes_twistedE6 hf hK σ hσ hσθ hp2 hp3 hdata χ hχinj hBsR hBs h4 hgN hgB hgp

theorem ggSixBstarExcFrameOn_TwE6NonsplitThree (hU : TwistedE6ThreeSCUnique)
    (hE : TwistedE6ThreeRefFrame) :
    GGSixBstarExcFrameOn .F4 GGExcTwE6NonsplitThreeLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, rfl, h3⟩ := hP
  left
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have := Fact.mk hp
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hperf : commutator ↥ψ.range = ⊤ := by rw [hrange]; exact hctx.2.2.2.2.2.1.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  obtain ⟨χ, hχinj, hχrange⟩ := exists_injective_factor_twistedE6 hf ψ hker hCψ
  have hBs : IsElemAbelian 3 Bs := hctx.2.1.2.1
  have hBsR : Bs ≤ χ.range := by
    rw [hχrange]
    intro b hb
    refine mem_range_of_innerDiag_twistedE6 hp (by norm_num) hf (fun h => h3 h.2) ψ hker hperf
      hCψ ?_ (hBs.2 b hb) (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hrange]
    exact hctx.2.2.2.2.2.2.1.1 hb
  have hcfg : GGConfig 3 B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  obtain ⟨-, -, -, -, h4⟩ := hcfg.tableB_facts
  have hAel : IsElemAbelian 3 (Bs.comap χ) := isElemAbelian_comap_frame χ hχinj hBs
  have hAc : 3 ^ 4 ≤ Nat.card (Bs.comap χ) := by
    rw [card_comap_of_le_range χ hχinj hBsR]
    exact h4
  have hSC : ∀ c ∈ Subgroup.centralizer ((Bs.comap χ : Subgroup
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) : Set
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
      c ^ 3 = 1 → c ∈ Bs.comap χ := by
    intro c hc hc3
    refine (Subgroup.mem_comap.2 (hcfg.2.1.2.2.2 (χ c) ?_ ?_))
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨a, rfl⟩ := hBsR hb
      have hac : a * c = c * a :=
        Subgroup.mem_centralizer_iff.1 hc a (Subgroup.mem_comap.2 hb)
      rw [← map_mul, ← map_mul, hac]
    · rw [← map_pow, hc3, map_one]
  obtain ⟨ι, hιinj, hιrange, hact⟩ :=
    exists_weylFrame_aut_twistedE6_three hU hE hf h3 hAel hAc hSC
  refine ⟨χ.comp ι, hχinj.comp hιinj, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hιrange]
    exact Subgroup.map_comap_eq_self hBsR
  · intro g hgM hgB hgp
    have hgN : g ∈ Subgroup.normalizer (χ.range : Set G) := by
      rw [show (χ.range : Set G) = (ψ.range : Set G) by rw [hχrange], hrange]
      exact hgM
    obtain ⟨α, hα⟩ := exists_inducedAut χ hχinj hgN
    have hαp : α ^ 3 = 1 := inducedAut_pow_eq_one χ hχinj hα hgp
    have hstab : ∀ a ∈ Bs.comap χ, α a ∈ Bs.comap χ := by
      intro a ha
      have ha' : χ a ∈ Bs := ha
      show χ (α a) ∈ Bs
      rw [hα a]
      exact (Subgroup.mem_normalizer_iff.1 hgB (χ a)).1 ha'
    obtain ⟨w, hw⟩ := hact α hαp hstab
    refine ⟨w, fun s => ?_⟩
    have h1 := hα (ι (Multiplicative.ofAdd s))
    rw [hw s] at h1
    exact h1.symm

theorem ggSixBstarExcFrameOn_TwE6Nonsplit_of_three
    (h3 : GGSixBstarExcFrameOn .F4 GGExcTwE6NonsplitThreeLabel) :
    GGSixBstarExcFrameOn .F4 GGExcTwE6NonsplitLabel :=
  GGSixBstarExcFrameOn.of_or ggSixBstarExcFrameOn_TwE6NonsplitGeFive h3 fun t _ f p ⟨ht, h⟩ => by
    by_cases hp3 : p = 3
    · exact Or.inr ⟨ht, hp3, hp3 ▸ h⟩
    · exact Or.inl ⟨ht, h, hp3⟩

end TagTwE6Nonsplit

end CFSG.StandardType

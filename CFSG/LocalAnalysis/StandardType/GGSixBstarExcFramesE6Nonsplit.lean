module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesAutTrivial
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitThree
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NormalForm
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesIsogenyE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesResidualLabels
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Minuscule CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration ExcFrames

section TagE6Nonsplit

theorem ggSixBstarExcFrameOn_E6NonsplitGeFive :
    GGSixBstarExcFrameOn .F4 (fun t _ f p => t = .E6 ∧ ¬ p ∣ 2 ^ f - 1 ∧ p ≠ 3) := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq1, hp3⟩ := hP
  right
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have := Fact.mk hp
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hperf : commutator ↥ψ.range = ⊤ := by rw [hrange]; exact hctx.2.2.2.2.2.1.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  obtain ⟨χ, hχinj, hχrange⟩ := exists_injective_factor_E6 ψ hker hCψ
  have hBs : IsElemAbelian p Bs := hctx.2.1.2.1
  have hBsR : Bs ≤ χ.range := by
    rw [hχrange]
    intro b hb
    refine mem_range_of_innerDiag_E6 hp (Or.inl hp3) ψ hker hperf hCψ ?_ (hBs.2 b hb)
      (hctx.2.2.2.2.2.2.1.2 b hb)
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
  have hpq : ¬ p ∣ Nat.card (GaloisField 2 f) := by
    rw [hK]
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have h1 : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq1
  have hAel : IsElemAbelian p (Bs.comap χ) := isElemAbelian_comap_frame χ hχinj hBs
  have hAc : p ^ 4 ≤ Nat.card (Bs.comap χ) := by
    rw [card_comap_of_le_range χ hχinj hBsR]
    exact h4
  have hdata : ∀ (K₀ : Type) [Field K₀] [Finite K₀],
      ((Nat.card K₀ : ℕ) : ZMod p) = ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) →
        SylowTorus (adjointGroup .E6 K₀) p 4 := fun K₀ _ _ hres =>
    sylowTorus_E6_nonsplit_of_four_le_card (GaloisField 2 f) hp hp3' hpq h1 hAel hAc K₀ hres
  intro g hgM hgB hgp
  have hgN : g ∈ Subgroup.normalizer (χ.range : Set G) := by
    rw [show (χ.range : Set G) = (ψ.range : Set G) by rw [hχrange], hrange]
    exact hgM
  exact centralizes_of_induced_exists (k := 3)
    (fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd)) hdata
    (fun α hα => exists_normalForm_E6 hp2 α hα) χ hχinj hBsR hBs h4 hgN hgB hgp

theorem ggSixBstarExcFrameOn_E6NonsplitThree (hU : E6ThreeSCUnique) (hE : E6ThreeRefFrame) :
    GGSixBstarExcFrameOn .F4 GGExcE6NonsplitThreeLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, rfl, h3⟩ := hP
  left
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have := Fact.mk hp
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hperf : commutator ↥ψ.range = ⊤ := by rw [hrange]; exact hctx.2.2.2.2.2.1.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  obtain ⟨χ, hχinj, hχrange⟩ := exists_injective_factor_E6 ψ hker hCψ
  have hBs : IsElemAbelian 3 Bs := hctx.2.1.2.1
  have h3q : ¬ 3 ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact h3
  have hBsR : Bs ≤ χ.range := by
    rw [hχrange]
    intro b hb
    refine mem_range_of_innerDiag_E6 hp (Or.inr h3q) ψ hker hperf hCψ ?_ (hBs.2 b hb)
      (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hrange]
    exact hctx.2.2.2.2.2.2.1.1 hb
  have hcfg : GGConfig 3 B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  obtain ⟨-, -, -, -, h4⟩ := hcfg.tableB_facts
  have hq : 3 ∣ Nat.card (GaloisField 2 f) + 1 := by
    rw [hK]
    have h0 : ¬ 3 ∣ 2 ^ f := fun hd =>
      absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  haveI : Finite (adjointGroup .E6 (GaloisField 2 f)) := generated_group_finite .E6 _
  have hAel : IsElemAbelian 3 (Bs.comap χ) := isElemAbelian_comap_frame χ hχinj hBs
  have hAc : 3 ^ 4 ≤ Nat.card (Bs.comap χ) := by
    rw [card_comap_of_le_range χ hχinj hBsR]
    exact h4
  have hSC : ∀ c ∈ Subgroup.centralizer ((Bs.comap χ : Subgroup _) : Set (adjointGroup .E6 (GaloisField 2 f))),
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
    exists_weylFrame_aut_E6_three hU hE (K := GaloisField 2 f) hq hAel hAc hSC
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

theorem ggSixBstarExcFrameOn_E6Nonsplit_of_three
    (h3 : GGSixBstarExcFrameOn .F4 GGExcE6NonsplitThreeLabel) :
    GGSixBstarExcFrameOn .F4 GGExcE6NonsplitLabel :=
  GGSixBstarExcFrameOn.of_or ggSixBstarExcFrameOn_E6NonsplitGeFive h3 fun t _ f p ⟨ht, h⟩ => by
    by_cases hp3 : p = 3
    · exact Or.inr ⟨ht, hp3, hp3 ▸ h⟩
    · exact Or.inl ⟨ht, h, hp3⟩

end TagE6Nonsplit

end CFSG.StandardType

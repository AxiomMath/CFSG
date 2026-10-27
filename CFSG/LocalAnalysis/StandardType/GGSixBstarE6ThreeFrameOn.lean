module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeAutFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAut
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAutTwoLocal
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAutInduces
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesIsogenyE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProof
public import CFSG.LocalAnalysis.StandardType.GGSixBstarModelFrameTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section FrameOn

open TableBExc.E6Three


theorem exists_injective_factor_E6_comp {G : Type} [Group G] {n f : ℕ}
    (ψ : (ggU .E6 n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .E6 n f).K)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ∃ χ : adjointGroup .E6 (GaloisField 2 f) →* G, Function.Injective χ ∧ χ.range = ψ.range ∧
      ∀ y, χ (e6Isogeny (GaloisField 2 f) y) = ψ y := by
  have hkerEq : ψ.ker = Subgroup.center (ggU .E6 n f).K := by
    refine le_antisymm hker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have h : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hC, Subgroup.mem_bot] at h
    exact h
  obtain ⟨χ, hχ, hval⟩ :=
    ExcNonsplit.exists_factor_e6Isogeny (k := GaloisField 2 f) (ψ := ψ) hkerEq
  refine ⟨χ, hχ, ?_, hval⟩
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨y, rfl⟩ := e6Isogeny_surjective (GaloisField 2 f) c
    exact ⟨y, (hval y).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e6Isogeny (GaloisField 2 f) y, hval y⟩

theorem ggSixBstarE6ThreeFrameOn_E6 : GGSixBstarE6ThreeFrameOn GGExcE6ThreeLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, rfl, h3f⟩ := hP
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h3 : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact h3f
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  obtain ⟨χ, hχinj, hχrange, hval⟩ := exists_injective_factor_E6_comp ψ hker hCψ
  have hχG0 : χ.range = ggG0 3 B x L D J := hχrange.trans hrange
  have hCχ : Subgroup.centralizer (χ.range : Set G) = ⊥ := by rw [hχrange]; exact hCψ
  have hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := hctx.2.2.2.2.2.2.1.1
  have hBsM : Bs ≤ ggM 3 B x L D J := hBsN
  have hBsdiag : ∀ b ∈ Bs, GGPsiInnerDiag (ggU .E6 n f).D ψ b := hctx.2.2.2.2.2.2.1.2
  have hBs : IsElemAbelian 3 Bs := hctx.2.1.2.1
  have hMeq : (χ.range : Set G) = (ggG0 3 B x L D J : Set G) := by rw [hχG0]
  have hM : ggM 3 B x L D J ≤ Subgroup.normalizer (χ.range : Set G) := by rw [hMeq]
  have hχM : χ.range ≤ ggM 3 B x L D J := by
    rw [hχG0]
    exact Subgroup.le_normalizer
  set Φ := NormalizerAut.normAutOn χ hχinj hM with hΦ
  have hΦinj : Function.Injective Φ := NormalizerAut.normAutOn_injective χ hχinj hM hCχ
  set S : Subgroup (MulAut (adjointGroup .E6 (GaloisField 2 f))) :=
    (Bs.subgroupOf (ggM 3 B x L D J)).map Φ with hS
  have hcardS : Nat.card S = Nat.card Bs := by
    rw [hS, Subgroup.card_map_of_injective (K := Bs.subgroupOf (ggM 3 B x L D J)) hΦinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsM).toEquiv
  have hcfg : GGConfig 3 B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  have hperf : commutator ↥(ggG0 3 B x L D J) = ⊤ := hctx.2.2.2.2.2.1.1
  obtain ⟨θ⟩ := NormalizerAut.nonempty_quotient_center_mulEquiv χ hχinj
    (center_adjointGroup_eq_bot (τ := .E6) (K := GaloisField 2 f)) hχG0
  have h5Bs : 3 ^ 5 ≤ Nat.card Bs :=
    pow_le_card_bstar_of_torusLift hcfg hperf θ (TableBExc.ggTorusLift_adjoint_E6_three h3)
  have hSI : S ≤ (hatAut .E6 (GaloisField 2 f)).range := by
    rintro _ ⟨⟨b, hbM⟩, hb, rfl⟩
    have hbBs : b ∈ Bs := hb
    have hbN : b ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hBsN hbBs
    obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_E6 ψ hker hbN (hBsdiag b hbBs)
    have hind := NormalizerAut.ggInduces_normAutOn (π := e6Isogeny (GaloisField 2 f)) (ψ := ψ) χ
      hχinj hval hM ⟨b, hbM⟩
    have huniq := LayerSixE.GGInduces.unique (e6Isogeny_surjective (GaloisField 2 f)) hbN hind hα
    rw [huniq, hatAut_range_eq_sup]
    exact hαD
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hctx.1.2.2.2.2.2.2.1.1.2.1
  have hBB : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1
  have hM2 : ∀ X : Subgroup (MulAut (adjointGroup .E6 (GaloisField 2 f))), X ≤ Φ.range →
      IsElemAbelian 3 X → (∃ U : Subgroup (adjointGroup .E6 (GaloisField 2 f)), U ≠ ⊥ ∧
        IsPGroup 2 U ∧ ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U) → Nat.card X ≤ Nat.card S := by
    rintro X hX hXel ⟨U, hU, hU2, hXU⟩
    have h1 := NormalizerAut.card_le_pow_twoLocalRank Nat.prime_three χ hχinj hM hCχ hX hXel hU hU2
      hXU
    rw [hcardS]
    exact h1.trans (hBc ▸ hBB)
  have hF := exists_autFrame_E6 h3 (M' := Φ.range) (S := S) (Subgroup.map_le_range Φ _)
    (NormalizerAut.conj_range_le_range_normAutOn χ hχinj hM hχM)
    (CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hBs _) Φ) hSI
    (hcardS ▸ h5Bs) hM2
  rcases hF with hF | hF
  · exact Or.inl (GGBstarModelFrame.of_injective_hom hBsM Φ hΦinj hF)
  · exact Or.inr (GGBstarModelFrame.of_injective_hom hBsM Φ hΦinj hF)

end FrameOn

end NoOffE6Three

end CFSG.StandardType

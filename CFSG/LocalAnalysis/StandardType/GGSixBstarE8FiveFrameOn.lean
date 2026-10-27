module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveAutFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAut
public import CFSG.LocalAnalysis.StandardType.GGSixBstarModelFrameTransfer
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProof
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTags
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE8Five

section FrameOn


theorem five_dvd_sq_add_one_of_not_dvd {q : ℕ} (hq : ∃ f : ℕ, q = 2 ^ f) (h1 : ¬ 5 ∣ q - 1)
    (h2 : ¬ 5 ∣ q + 1) : 5 ∣ q * q + 1 := by
  obtain ⟨f, rfl⟩ := hq
  have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h0 : ¬ 5 ∣ 2 ^ f := fun hd =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow hd)) (by norm_num)
  have h : 2 ^ f % 5 = 2 ∨ 2 ^ f % 5 = 3 := by omega
  rcases h with h | h <;> exact Nat.dvd_of_mod_eq_zero (by simp [Nat.add_mod, Nat.mul_mod, h])

theorem ggSixBstarE8FiveFrameOn_E8_of_innerDiag
    (hVI : ∀ (G : Type) [Group G] (n f : ℕ) (ψ : (ggU .E8 n f).K →* G),
      ψ.ker ≤ Subgroup.center (ggU .E8 n f).K → ∀ c : G,
        GGPsiInnerDiag (ggU .E8 n f).D ψ c →
          ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G)) :
    GGSixBstarE8FiveFrameOn GGExcE8QuarticFiveLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, rfl, hq1, hq2⟩ := hP
  right
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
  have hcfg : GGConfig 5 B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  obtain ⟨-, hBs, -, -, h4⟩ := hcfg.tableB_facts
  have hBsN : Bs ≤ Subgroup.normalizer (ggG0 5 B x L D J : Set G) := hctx.2.2.2.2.2.2.1.1
  have hBsM : Bs ≤ ggM 5 B x L D J := hBsN
  let χ : adjointGroup Tag.E8 (GaloisField 2 f) →* G := ψ
  have hχinj : Function.Injective χ := hinj
  have hχrange : χ.range = ggG0 5 B x L D J := hrange
  have hCχ : Subgroup.centralizer (χ.range : Set G) = ⊥ := hCψ
  have hBsRχ : Bs ≤ χ.range := hBsR
  have hMeq : (χ.range : Set G) = (ggG0 5 B x L D J : Set G) := by rw [hχrange]
  have hM : ggM 5 B x L D J ≤ Subgroup.normalizer (χ.range : Set G) := by rw [hMeq]
  set Φ := NormalizerAut.normAutOn χ hχinj hM with hΦ
  have hΦinj : Function.Injective Φ := NormalizerAut.normAutOn_injective χ hχinj hM hCχ
  set S : Subgroup (MulAut (adjointGroup Tag.E8 (GaloisField 2 f))) :=
    (Bs.subgroupOf (ggM 5 B x L D J)).map Φ with hS
  have hcardS : Nat.card S = Nat.card Bs := by
    rw [hS, Subgroup.card_map_of_injective (K := Bs.subgroupOf (ggM 5 B x L D J)) hΦinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsM).toEquiv
  have hSI : S ≤ (MulAut.conj : adjointGroup Tag.E8 (GaloisField 2 f) →*
      MulAut (adjointGroup Tag.E8 (GaloisField 2 f))).range := by
    rintro _ ⟨⟨b, hbM⟩, hb, rfl⟩
    have hbBs : b ∈ Bs := hb
    obtain ⟨y, hy⟩ := hBsRχ hbBs
    subst hy
    exact ⟨y, (NormalizerAut.normAutOn_chi χ hχinj hM y hbM).symm⟩
  have h5 : 5 ∣ Nat.card (GaloisField 2 f) * Nat.card (GaloisField 2 f) + 1 := by
    rw [hK]
    exact five_dvd_sq_add_one_of_not_dvd ⟨f, rfl⟩ hq1 hq2
  have hF := exists_autFrame_E8 (K := GaloisField 2 f) (M' := Φ.range) hf hK h5 hSI
    (CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hBs _) Φ)
    (hcardS ▸ h4)
  exact GGBstarModelFrame.of_injective_hom hBsM Φ hΦinj hF

end FrameOn

section FrameOnVI


theorem ggSixBstarE8FiveFrameOn_E8 : GGSixBstarE8FiveFrameOn GGExcE8QuarticFiveLabel :=
  ggSixBstarE8FiveFrameOn_E8_of_innerDiag fun _ _ _ f ψ hker _ hc =>
    PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ hker hc

end FrameOnVI

end NoOffE8Five

end CFSG.StandardType

module

public import CFSG.RankThree.PartOne.K133Spor.HSPair
public import CFSG.RankThree.PartOne.S11c.HNInvQ6
public import CFSG.RankThree.PartOne.KS.HSMcL
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneKit
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientGraph
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S11c.OuterInner
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartOne.K133Spor

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.HNRed Subgroup
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem hnClassA (D : Subgroup JH) (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hD5 : ∀ d ∈ D, d ^ 5 = 1) (hDc : Nat.card D = 25) (hDC : D ≤ C6) {t' : JH} (ht'C : t' ∈ C6)
    (ht'2 : t' ^ 2 = 1) (ht'1 : t' ≠ 1) (ht'a : t' ≠ aJ) (hcomm : ∀ d ∈ D, d * t' = t' * d)
    (hcheck : HSPairFreeCheck) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨q, hq⟩ := exists_q6
  have hAut := hs_autModel
  let θ : Carrier .HS ≃* hs100P := hs100Equiv
  let ι : MulAut (Carrier .HS) →* Equiv.Perm (Fin 100) :=
    hAut.hom.comp (MulAut.congr θ).toMonoidHom
  have hι : Function.Injective ι := hAut.hom_injective.comp (MulAut.congr θ).injective
  have hιR : ∀ α, ι α ∈ hs100R := fun α => hAut.elt_mem _
  let ψ : C6 →* Equiv.Perm (Fin 100) := ι.comp q
  have hψker : ∀ y : C6, ψ y = 1 → (y : JH) = 1 ∨ (y : JH) = aJ := fun y hy =>
    hq y (hι (by rw [map_one]; exact hy))
  have hD1 : ∃ x ∈ D, x ≠ 1 := by
    by_contra h
    push Not at h
    have : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr h
    rw [this, Subgroup.card_bot] at hDc
    omega
  obtain ⟨x, hxD, hx1⟩ := hD1
  have hxord : orderOf x = 5 := orderOf_eq_prime (hD5 x hxD) hx1
  have hf : ∃ f ∈ D, f ∉ zpowers x := by
    by_contra h
    push Not at h
    have hle : D ≤ zpowers x := h
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hxord, hDc] at this
    omega
  obtain ⟨f, hfD, hfx⟩ := hf
  have hf1 : f ≠ 1 := fun h => hfx (h ▸ one_mem _)
  have hford : orderOf f = 5 := orderOf_eq_prime (hD5 f hfD) hf1
  have haJ : ∀ y ∈ D, y ≠ 1 → y ≠ aJ := by
    intro y hy hy1 hya
    have h5 := hD5 y hy
    rw [hya] at h5
    have h2 : aJ ^ 2 = 1 := aJ_sq
    have : aJ = 1 := by
      calc aJ = aJ ^ 5 * (aJ ^ 2)⁻¹ ^ 2 := by group
        _ = 1 := by rw [h5, h2]; group
    exact aJ_ne_one this
  have hker_D : ∀ y : C6, (y : JH) ∈ D → ψ y = 1 → (y : JH) = 1 := by
    intro y hy hψ
    rcases hψker y hψ with h | h
    · exact h
    · by_cases h1 : (y : JH) = 1
      · exact h1
      · exact absurd h (haJ _ hy h1)
  let xC : C6 := ⟨x, hDC hxD⟩
  let fC : C6 := ⟨f, hDC hfD⟩
  let tC : C6 := ⟨t', ht'C⟩
  have hψx5 : ψ xC ^ 5 = 1 := by rw [← map_pow]; exact (by
    have : xC ^ 5 = 1 := Subtype.ext (hD5 x hxD)
    rw [this, map_one])
  have hψx1 : ψ xC ≠ 1 := fun h => hx1 (hker_D xC hxD h)
  have hψxord : orderOf (ψ xC) = 5 := orderOf_eq_prime hψx5 hψx1
  have hψf5 : ψ fC ^ 5 = 1 := by rw [← map_pow]; exact (by
    have : fC ^ 5 = 1 := Subtype.ext (hD5 f hfD)
    rw [this, map_one])
  have hψf1 : ψ fC ≠ 1 := fun h => hf1 (hker_D fC hfD h)
  have hψford : orderOf (ψ fC) = 5 := orderOf_eq_prime hψf5 hψf1
  have hψt2 : ψ tC ^ 2 = 1 := by
    rw [← map_pow]
    have : tC ^ 2 = 1 := Subtype.ext ht'2
    rw [this, map_one]
  have hψt1 : ψ tC ≠ 1 := by
    intro h
    rcases hψker tC h with h1 | h1
    · exact ht'1 h1
    · exact ht'a h1
  have hψtord : orderOf (ψ tC) = 2 := orderOf_eq_prime hψt2 hψt1
  have hψfx : ψ fC ∉ zpowers (ψ xC) := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    apply hfx
    have hmemD : f * x ^ (-k) ∈ D := D.mul_mem hfD (D.zpow_mem (D.inv_mem hxD) k |> fun h' => by
      simpa [zpow_neg] using h')
    let yC : C6 := fC * xC ^ (-k)
    have hyD : (yC : JH) ∈ D := hmemD
    have hψy : ψ yC = 1 := by
      show ψ (fC * xC ^ (-k)) = 1
      rw [map_mul, map_zpow, zpow_neg, hk]
      group
    have := hker_D yC hyD hψy
    have h' : f * x ^ (-k) = 1 := this
    exact ⟨k, by
      have : f = x ^ k := by
        calc f = (f * x ^ (-k)) * x ^ k := by simp [zpow_neg]
          _ = x ^ k := by rw [h']; group
      exact this.symm⟩
  have hψxf : ψ xC * ψ fC = ψ fC * ψ xC := by
    have e : xC * fC = fC * xC := Subtype.ext (hDab x hxD f hfD)
    rw [← map_mul, ← map_mul, e]
  have hψtx : ψ tC * ψ xC = ψ xC * ψ tC := by
    have e : tC * xC = xC * tC := Subtype.ext (hcomm x hxD).symm
    rw [← map_mul, ← map_mul, e]
  have hψtf : ψ tC * ψ fC = ψ fC * ψ tC := by
    have e : tC * fC = fC * tC := Subtype.ext (hcomm f hfD).symm
    rw [← map_mul, ← map_mul, e]
  have hxP : ψ xC ∈ hs100P :=
    mem_of_pow_eq_one_of_autModel hAut hs_card_le Nat.prime_five (by norm_num) (hιR _) hψx5
  exact hsPairFree hcheck hxP hψxord (hιR _) hψford hψxf hψfx (hιR _) hψtord hψtx hψtf

end CFSG.RankThree.PartOne.K133Spor

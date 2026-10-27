module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormFrame
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Twisted
public import CFSG.LocalAnalysis.StandardType.GGTorusE6RelativeAut
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Split
public import CFSG.LocalAnalysis.StandardType.GGTorusE6RelativeLangAut

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.TwistedE6Cover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem ggTorusWNormSC_recipe_twE6_relative {K : Type} [Field K] [Finite K]
    {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) :
    GGTorusWNormSC p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  classical
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨σ, hσ, -, ζ0, -, -, hζp, hζσ, ψ0, Λ0,
    hψ0, hk0, hΛ0, hΛψ0, hZ, hζo, hAout⟩ :=
    exists_aligned_splitFrame_twE6_relative (r := 3) hn hK hp hp5 hpn ψ A
      ⟨hψ, hker, hperf, hA, hAI, h3, h3, hsc⟩
  let ζ : Kˣ := fixUnit σ.toRingHom ζ0
  let C0 := ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
  let t := E6RelativeWeyl.stdFrame (K := K) (σ := σ.toRingHom)
    (hp := hp) (hζ := hζp) (hζσ := hζσ)
  let E0 : Subgroup C0 := t.range
  have ht : Function.Injective t :=
    ExcFrames.twE6SplitFrameHom_injective σ.toRingHom hp5 hζo hζp hζσ
  obtain ⟨hnN, -, eW, heW⟩ := E6RelativeWeyl.exists_markedWeyl_standard
    (K := K) (σ := σ.toRingHom) (hp := hp) (hp5 := hp5)
    (hζo := hζo) (hζ := hζp) (hζσ := hζσ)
  have hAut : ∀ β : MulAut C0, (∀ x, β x ∈ E0 ↔ x ∈ E0) →
      ∃ (c : (ZMod p)ˣ) (u : WeylGroup Tag.F4), ∀ v,
        β (t (Multiplicative.ofAdd v)) =
          t (Multiplicative.ofAdd ((c : ZMod p) • TableBExc.torusAct Tag.F4 p u v)) := by
    intro β hβ
    have hmap : E0.map β.toMonoidHom = E0 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hβ y).mpr hy
      · intro hx
        obtain ⟨y, rfl⟩ := β.surjective x
        exact ⟨y, (hβ y).mp hx, rfl⟩
    exact E6RelativeWeyl.exists_scalar_weyl_of_map_stdFrame_eq
      σ hp hζp hζσ hn hK hσ hp5 hζo β hmap
  intro _ Γ _ _ M C V _ _ ι φ h α _ _ _ _ hgen s hs
  exact ggWNormConcl_of_centralCover_weylFrame ψ0 hψ0
    (by rw [hk0]; exact hker) hZ Λ0 hΛ0 hΛψ0 E0 A hAout t ht rfl
    (fun i => E6RelativeWeyl.nNative (K := K) (σ := σ.toRingHom) i) hnN
    (fun i v => E6RelativeWeyl.nNative_conj (K := K) (σ := σ.toRingHom)
      (hp := hp) (hζo := hζo) (hζ := hζp) (hζσ := hζσ) i v)
    (fun g hg => E6RelativeWeyl.normalizer_action (K := K) (σ := σ.toRingHom)
      (hp := hp) (hp5 := hp5) (hζo := hζo) (hζ := hζp) (hζσ := hζσ) g hg)
    hAut (by decide) (ExcFrames.isUnit_det_symmetrizedCartan (Or.inl rfl) (by omega))
    ι φ h α hgen hs

theorem largeEvenLabelAll_wnorm_twE6_relative {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twE6)
    (hpq : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I :=
  TwE6Delta.labelAll htag fun _K _ _ hK =>
    ggTorusWNormSC_recipe_twE6_relative hlab.1 hK hp hp5 hpq

theorem ggTorusWNormSC_recipe_E6_relative {K : Type} [Field K] [Finite K] [CharP K 2]
    {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) :
    GGTorusWNormSC p (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  classical
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ψ0, Λ0, E, F, hψ0, hk0, hΛ0, hΛψ0, hEA, hlong⟩ :=
    exists_aligned_LangFrame_E6_relative (r := 3) hn hK hp (by omega) (by omega) hpq ψ A
      ⟨hψ, hker, hperf, hA, hAI, h3, h3, hsc⟩
  have hpq0 : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  obtain ⟨_nn, ζ, hζo, hζ, _hformula, _hnW, _eW, _heW⟩ :=
    E6RelativeLangWeyl.exists_markedWeyl_qplusLang F hp hp5 hpq0 hlong
  let t := E6RelativeLangWeyl.pFrame F hp ζ hζo hζ hpq0 hlong
  have ht : Function.Injective t :=
    E6RelativeLangWeyl.pFrame_injective F hp hp5 ζ hζo hζ hpq0 hlong
  have htr : t.range = E := E6RelativeLangWeyl.pFrame_range F hp hp5 ζ hζo hζ hpq0 hlong
  let nn := E6RelativeLangWeyl.nNative F hlong
  have hns : ∀ i v, nn i * t (Multiplicative.ofAdd v) * (nn i)⁻¹ =
      t (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 p (simple Tag.F4 i) v)) :=
    E6RelativeLangWeyl.nNative_frameConj F hp hp5 ζ hζo hζ hpq0 hlong
  have hN : ∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E6 K)),
      ∃ u : WeylGroup Tag.F4, ∀ v, g * t (Multiplicative.ofAdd v) * g⁻¹ =
        t (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 p u v)) :=
    E6RelativeLangWeyl.normalizer_frame_action F hp hp5 ζ hζo hζ hpq0 hlong
  obtain ⟨hnN, -, _e, _he⟩ := exists_markedWeyl_ggAutomizer (τ := Tag.F4)
    (hp.odd_of_ne_two (by omega)) E t ht htr nn hns hN
  intro _ Γ _ _ M C V _ _ ι φ h α _ _ _ _ hgen s hs
  exact ggWNormConcl_of_centralCover_weylFrame ψ0 hψ0
    (by rw [hk0]; exact hker) center_adjointGroup_eq_bot Λ0 hΛ0 hΛψ0 E A hEA
    t ht htr nn hnN hns hN
    (E6RelativeLangWeyl.automorphism_frame_action F hp hp5 ζ hζo hζ hpq0 hlong)
    (by decide) (ExcFrames.isUnit_det_symmetrizedCartan (Or.inl rfl) (by omega))
    ι φ h α hgen hs

theorem largeEvenLabelAll_wnorm_E6_relative {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E6)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨tag, rank, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hn hpq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  exact ⟨K, i1, i2, hK, hQK, ggTorusWNormSC_recipe_E6_relative hn hK hp hp5 hpq⟩

end CFSG.StandardType

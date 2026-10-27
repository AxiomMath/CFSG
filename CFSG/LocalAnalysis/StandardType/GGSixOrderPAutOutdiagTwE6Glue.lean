module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagExcPpd
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagTwE6Model

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.ComponentInitial

section TwE6

@[expose] def GGTwE6FrameNoPpdInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → 3 ∣ 2 ^ f + 1 →
    ∀ M' S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))),
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range
          ≤ M' →
      S ≤ M' → S ≤ LayerSixE.twInndiagAut f → IsElemAbelian 3 S →
      (∀ X : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))), X ≤ M' → IsElemAbelian 3 X → Nat.card X ≤ Nat.card S) →
      ∀ α ∈ S, α ≠ 1 → ∀ r, (∃ e ∈ ggOutdiagExpsTwE6, IsTwoPowPpd f e r) →
        ∀ z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
          orderOf z = r → α z ≠ z

@[expose] def GGTwE6FrameFixPpdInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → 3 ∣ 2 ^ f + 1 →
    ∀ M' S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))),
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range
          ≤ M' →
      S ≤ M' → S ≤ LayerSixE.twInndiagAut f → IsElemAbelian 3 S →
      (∀ X : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))), X ≤ M' → IsElemAbelian 3 X → Nat.card X ≤ Nat.card S) →
      ∀ α ∈ M', α ∈ LayerSixE.twInndiagAut f → α ^ 3 = 1 → (∀ m ∈ M', m⁻¹ * α * m ∉ S) →
        ∃ r, (∃ e ∈ ggOutdiagExpsTwE6, IsTwoPowPpd f e r) ∧
          ∃ z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
            orderOf z = r ∧ α z = z

theorem GGOutdiagPrimeConfig.of_twistedE6 {p n f : ℕ}
    (h : GGOutdiagPrimeConfig p .twistedE6 n f) : p = 3 ∧ 3 ∣ 2 ^ f + 1 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hp, h3⟩
  · exact nomatch h
  · exact nomatch h
  · exact nomatch h
  · exact ⟨hp, h3⟩

namespace OutdiagTwE6

theorem exists_frame_setup {G : Type} [Group G] [Finite G] {Bs G₀ : Subgroup G} {n f : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* G}
    (hS : GGSixFusionSetting 3 Bs G₀ (ggU .twistedE6 n f).D .twistedE6 n f ψ) :
    ∃ χ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G,
      Function.Injective χ ∧ χ.range = G₀ ∧
      (∀ c ∈ Subgroup.normalizer (G₀ : Set G), GGPsiInnerDiag (ggU .twistedE6 n f).D ψ c →
        ∃ α ∈ LayerSixE.twInndiagAut f, OutdiagModel.Induces χ c α) ∧
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range
          ≤ OutdiagModel.inducedSub χ (Subgroup.normalizer (G₀ : Set G)) ∧
      OutdiagModel.inducedSub χ Bs ≤ OutdiagModel.inducedSub χ (Subgroup.normalizer (G₀ : Set G)) ∧
      OutdiagModel.inducedSub χ Bs ≤ LayerSixE.twInndiagAut f ∧
      IsElemAbelian 3 (OutdiagModel.inducedSub χ Bs) ∧
      (∀ X : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))), X ≤ OutdiagModel.inducedSub χ (Subgroup.normalizer (G₀ : Set G)) →
        IsElemAbelian 3 X → Nat.card X ≤ Nat.card (OutdiagModel.inducedSub χ Bs)) := by
  obtain ⟨χ, hχ, hrange, hind⟩ := exists_model hS
  have hC : Subgroup.centralizer (χ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G) := hS.2.2.2.1.1
  have hBsel : IsElemAbelian 3 Bs := hS.2.2.2.1.2.1
  have hBsN' : Bs ≤ Subgroup.normalizer (χ.range : Set G) := by
    rw [hrange]
    exact hBsN
  have hχN : χ.range ≤ Subgroup.normalizer (G₀ : Set G) := by
    rw [hrange]
    exact Subgroup.le_normalizer
  refine ⟨χ, hχ, hrange, hind, OutdiagModel.innerAut_le_inducedSub hχN,
    fun α ⟨b, hb, h⟩ => ⟨b, hBsN hb, h⟩, ?_, OutdiagModel.isElemAbelian_inducedSub hχ hBsel, ?_⟩
  · rintro α ⟨b, hb, hbα⟩
    obtain ⟨α', hα'D, hα'⟩ := hind b (hBsN hb) (hS.innerDiag b hb)
    rw [OutdiagModel.Induces.unique hχ hbα hα']
    exact hα'D
  · intro X hXM hXel
    have hXtop : X ≤ OutdiagModel.inducedSub χ ⊤ :=
      hXM.trans (fun α ⟨b, _, h⟩ => ⟨b, Subgroup.mem_top _, h⟩)
    rw [OutdiagModel.card_inducedSub hχ hC hBsN']
    exact (OutdiagModel.card_le_liftSub hχ hXtop).trans
      (hS.card_le_card_bstar (OutdiagModel.isElemAbelian_liftSub hC hXel))

end OutdiagTwE6

theorem ggOutdiagTwistedPpdAt_twistedE6_of_input (hF2 : GGTwE6FrameFixPpdInput) :
    GGOutdiagTwistedPpdAt .twistedE6 ggOutdiagExpsTwE6 := by
  intro G _ _ p Bs G₀ n f ψ hS h4 hcfg y hyN hyo hyi hnc
  obtain ⟨rfl, h3⟩ := GGOutdiagPrimeConfig.of_twistedE6 hcfg
  obtain ⟨χ, hχ, hrange, hind, hInn, hSM, hSI, hSel, hM2⟩ := OutdiagTwE6.exists_frame_setup hS
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  have hC : Subgroup.centralizer (χ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hχN : χ.range ≤ Subgroup.normalizer (G₀ : Set G) := by
    rw [hrange]
    exact Subgroup.le_normalizer
  have hy3 : y ^ 3 = 1 := by
    rw [← hyo]
    exact pow_orderOf_eq_one y
  obtain ⟨α, hαD, hα⟩ := hind y hyN hyi
  have hα3 : α ^ 3 = 1 := by
    have h1 := hα.pow 3
    rw [hy3] at h1
    exact OutdiagModel.Induces.unique hχ h1 OutdiagModel.Induces.one
  have hαM : α ∈ OutdiagModel.inducedSub χ (Subgroup.normalizer (G₀ : Set G)) := ⟨y, hyN, hα⟩
  have hnc' : ∀ m ∈ OutdiagModel.inducedSub χ (Subgroup.normalizer (G₀ : Set G)),
      m⁻¹ * α * m ∉ OutdiagModel.inducedSub χ Bs := by
    intro m hm hmS
    obtain ⟨e, he, hem⟩ := hm
    exact hnc e he (OutdiagModel.mem_of_conj_induces hC hα hem hmS)
  obtain ⟨r, hr, z, hzo, hαz⟩ := hF2 f hf h3 _ _ hInn hSM hSI hSel hM2 α hαM hαD hα3 hnc'
  refine ⟨r, hr, χ z, ⟨hχN ⟨z, rfl⟩, ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff.mp hh]
    calc y * χ z = (y * χ z * y⁻¹) * y := by group
      _ = χ (α z) * y := by rw [hα z]
      _ = χ z * y := by rw [hαz]
  · rw [orderOf_injective χ hχ z, hzo]

theorem ggOutdiagToralNoPpdAt_twistedE6_of_input (hF1 : GGTwE6FrameNoPpdInput) :
    GGOutdiagToralNoPpdAt .twistedE6 ggOutdiagExpsTwE6 := by
  intro G _ _ p Bs G₀ n f ψ hS h4 hcfg b hb hb1 r hr z hz hzr
  obtain ⟨rfl, h3⟩ := GGOutdiagPrimeConfig.of_twistedE6 hcfg
  obtain ⟨χ, hχ, hrange, hind, hInn, hSM, hSI, hSel, hM2⟩ := OutdiagTwE6.exists_frame_setup hS
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  have hC : Subgroup.centralizer (χ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  obtain ⟨e, he, hppd⟩ := hr
  have he' : e = 12 ∨ e = 18 := by
    simpa [ggOutdiagExpsTwE6] using he
  have hef : 3 ≤ e * f := by
    rcases he' with rfl | rfl <;> omega
  have hrp : r.Prime := hppd.1
  have hr2 : r ≠ 2 := hppd.ne_two (by omega)
  have hr3 : r ≠ 3 := hppd.ne_three hef
  have hrf : ¬ r ∣ f := hppd.not_dvd (by rcases he' with rfl | rfl <;> omega) hf
  have hzr1 : z ^ r = 1 := by
    rw [← hzr]
    exact pow_orderOf_eq_one z
  have hzN : z ∈ Subgroup.normalizer (χ.range : Set G) := by
    rw [hrange]
    exact hz.1
  obtain ⟨z', rfl⟩ := OutdiagTwE6.mem_range_of_pow_eq_one hf hrp hr2 hr3 hrf hχ hC hzN hzr1
  have hbN : b ∈ Subgroup.normalizer (χ.range : Set G) := by
    rw [hrange]
    exact hS.2.2.2.1.1 hb
  obtain ⟨α, hbα⟩ := OutdiagModel.exists_induces hχ hbN
  have hα1 : α ≠ 1 := by
    intro h
    rw [h] at hbα
    exact hb1 (OutdiagModel.Induces.inj hC hbα OutdiagModel.Induces.one)
  have hfix : α z' = z' := by
    refine hχ ?_
    rw [← hbα z']
    have hcomm := Subgroup.mem_centralizer_iff.mp hz.2 b (Set.mem_singleton b)
    calc b * χ z' * b⁻¹ = (χ z' * b) * b⁻¹ := by rw [← hcomm]
      _ = χ z' := by group
  have hord : orderOf z' = r := by
    rw [← orderOf_injective χ hχ z']
    exact hzr
  exact hF1 f hf h3 _ _ hInn hSM hSI hSel hM2 α ⟨b, hb, hbα⟩ hα1 r ⟨e, he, hppd⟩ z' hord hfix

end TwE6

end CFSG.StandardType

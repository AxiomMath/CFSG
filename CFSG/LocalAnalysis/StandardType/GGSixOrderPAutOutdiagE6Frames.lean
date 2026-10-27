module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Model
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Toral

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule

section E6

namespace OutdiagE6

open NoOffE6Three TableBExc.E6Three

theorem exists_frame_data {G : Type} [Group G] [Finite G] {Bs G₀ : Subgroup G} {n f : ℕ}
    {ψ : (ggU .E6 n f).K →* G}
    (hS : GGSixFusionSetting 3 Bs G₀ (ggU .E6 n f).D .E6 n f ψ) (h3 : 3 ∣ 2 ^ f - 1) :
    ∃ χ : adjointGroup .E6 (GaloisField 2 f) →* G, Function.Injective χ ∧ χ.range = G₀ ∧
      (∀ c ∈ Subgroup.normalizer (G₀ : Set G), GGPsiInnerDiag (ggU .E6 n f).D ψ c →
        ∃ α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f), OutdiagModel.Induces χ c α) ∧
      (∀ b ∈ Bs, ∀ α, OutdiagModel.Induces χ b α →
        LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α)) ∧
      (∀ y ∈ Subgroup.normalizer (G₀ : Set G), y ^ 3 = 1 → ∀ α, OutdiagModel.Induces χ y α →
        α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f) →
        LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α) →
        ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Bs) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨χ, hχ, hrange, hind⟩ := exists_model hS
  have hC : Subgroup.centralizer (χ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h3K : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [hK]
    exact h3
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := GaloisField 2 f) h3K
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G) := hS.2.2.2.1.1
  have hBsel : IsElemAbelian 3 Bs := hS.2.2.2.1.2.1
  have hBsN' : Bs ≤ Subgroup.normalizer (χ.range : Set G) := by
    rw [hrange]
    exact hBsN
  have hχN : χ.range ≤ Subgroup.normalizer (G₀ : Set G) := by
    rw [hrange]
    exact Subgroup.le_normalizer
  set M' := OutdiagModel.inducedSub χ (Subgroup.normalizer (G₀ : Set G)) with hM'
  set S := OutdiagModel.inducedSub χ Bs with hSdef
  have hSM : S ≤ M' := fun α ⟨b, hb, h⟩ => ⟨b, hBsN hb, h⟩
  have hInn : (MulAut.conj : adjointGroup .E6 (GaloisField 2 f) →*
      MulAut (adjointGroup .E6 (GaloisField 2 f))).range ≤ M' :=
    OutdiagModel.innerAut_le_inducedSub hχN
  have hSel : IsElemAbelian 3 S := OutdiagModel.isElemAbelian_inducedSub hχ hBsel
  have hcardS : Nat.card S = Nat.card Bs := OutdiagModel.card_inducedSub hχ hC hBsN'
  have hSI : S ≤ (hatAut .E6 (GaloisField 2 f)).range := by
    rintro α ⟨b, hb, hbα⟩
    obtain ⟨α', hα'D, hα'⟩ := hind b (hBsN hb) (hS.innerDiag b hb)
    rw [OutdiagModel.Induces.unique hχ hbα hα', hatAut_range_eq_sup]
    exact hα'D
  have hvH : vHyp (K := GaloisField 2 f) ζ hζ ≤ OutdiagModel.inducedSub χ ⊤ := by
    intro φ hφ
    obtain ⟨g, rfl⟩ := vHyp_le_innerAut ζ hζ hφ
    exact ⟨χ g, Subgroup.mem_top _, OutdiagModel.Induces.conj g⟩
  have h5 : 3 ^ 5 ≤ Nat.card S := by
    rw [hcardS, ← card_vHyp hζo hζ]
    exact (OutdiagModel.card_le_liftSub hχ hvH).trans
      (hS.card_le_card_bstar (OutdiagModel.isElemAbelian_liftSub hC (isElemAbelian_vHyp ζ hζ)))
  have hM2 : ∀ X : Subgroup (MulAut (adjointGroup .E6 (GaloisField 2 f))), X ≤ M' →
      IsElemAbelian 3 X → Nat.card X ≤ Nat.card S := by
    intro X hXM hXel
    have hXtop : X ≤ OutdiagModel.inducedSub χ ⊤ :=
      hXM.trans (fun α ⟨b, _, h⟩ => ⟨b, Subgroup.mem_top _, h⟩)
    rw [hcardS]
    exact (OutdiagModel.card_le_liftSub hχ hXtop).trans
      (hS.card_le_card_bstar (OutdiagModel.isElemAbelian_liftSub hC hXel))
  refine ⟨χ, hχ, hrange, hind, ?_, ?_⟩
  ·
    intro b hb α hbα
    obtain ⟨c, hc⟩ := OutdiagE6.ggInndiagToral_of_frame_E6 h3K hSM hInn hSel hSI h5 hM2
    have hαS : α ∈ S := ⟨b, hb, hbα⟩
    exact ⟨c, fun a ha => hc a (Subgroup.zpowers_le.mpr hαS ha)⟩
  ·
    intro y hy hy3 α hα hαD hαT
    have hαM : α ∈ M' := ⟨y, hy, hα⟩
    have hα3 : α ^ 3 = 1 := by
      have h1 := hα.pow 3
      rw [hy3] at h1
      exact OutdiagModel.Induces.unique hχ h1 OutdiagModel.Induces.one
    have hαI : α ∈ (hatAut .E6 (GaloisField 2 f)).range := by
      rw [hatAut_range_eq_sup]
      exact hαD
    obtain ⟨g, hg⟩ := exists_inner_conj_mem_E6 h3K hSM hInn hSel hSI h5 hM2 hαM hαI hα3 hαT
    refine ⟨χ g⁻¹, hχN ⟨g⁻¹, rfl⟩, ?_⟩
    have hm : OutdiagModel.Induces χ (χ g⁻¹) (MulAut.conj g)⁻¹ := by
      have h1 := OutdiagModel.Induces.conj (χ := χ) g⁻¹
      have h2 : (MulAut.conj g⁻¹ : MulAut (adjointGroup .E6 (GaloisField 2 f))) =
          (MulAut.conj g)⁻¹ := map_inv MulAut.conj g
      rw [h2] at h1
      exact h1
    refine OutdiagModel.mem_of_conj_induces hC hα hm ?_
    rw [inv_inv]
    exact hg

end OutdiagE6

end E6

end CFSG.StandardType

module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIKit
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr)
open Item434Kit Item434Alt Subgroup

namespace Item434SmallTwoIII

noncomputable def gf21Equiv : GaloisField 2 1 ≃+* ZMod 2 :=
  (GaloisField.equivZmodP 2).toRingEquiv

noncomputable def statedProjSp6Equiv : StatedProj (StatedSp 3 (ZMod 2)) ≃* H6 :=
  (QuotientGroup.quotientMulEquivOfEq Census.statedScalars_subgroupOf_sp6).trans
    QuotientGroup.quotientBot

noncomputable def sp62Equiv : projSp 3 (GaloisField 2 1) ≃* H6 :=
  (projSpEquivStatedProj 3 (GaloisField 2 1)).trans
    ((statedProjCongr (glCongr gf21Equiv)
      (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp gf21Equiv 3)
      (glCongr_statedScalars gf21Equiv)).trans statedProjSp6Equiv)

theorem card_outer_H6 : Nat.card (Outer H6) = 1 := by
  rw [← Nat.card_congr (equivalence statedProjSp6Equiv).toEquiv]
  have hK : Nat.card (ZMod 2)ˣ = 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have h1 := Sec19.Step1919EndProof.card_outer_statedSp_le (r := 3) le_rfl hK
  have h2 : Nat.card (ZMod 2 ≃+* ZMod 2) ≤ 1 := by
    have : Subsingleton (ZMod 2 ≃+* ZMod 2) :=
      ⟨fun σ τ => RingEquiv.ext fun x => by
        have h := congrArg (fun φ : ZMod 2 →+* ZMod 2 => φ x)
          (Subsingleton.elim (σ : ZMod 2 →+* ZMod 2) (τ : ZMod 2 →+* ZMod 2))
        exact h⟩
    exact Finite.card_le_one_iff_subsingleton.mpr this
  have hpos : 0 < Nat.card (Outer (StatedProj (StatedSp 3 (ZMod 2)))) := Nat.card_pos
  omega

theorem mem_range_conj_H6 (φ : MulAut H6) : φ ∈ (MulAut.conj : H6 →* MulAut H6).range := by
  have h : (inner H6).index = 1 := card_outer_H6
  rw [Subgroup.index_eq_one] at h
  change φ ∈ inner H6
  rw [h]
  exact Subgroup.mem_top φ

theorem center_eq_bot_of_isSimpleGroup {T : Type*} [Group T] [IsSimpleGroup T]
    [Group.IsPerfect T] : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : T, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    have htop : commutator T = ⊤ := Group.IsPerfect.commutator_eq_top
    have hbot : commutator T = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact hcomm y x
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    apply hab
    have ha : a ∈ (⊥ : Subgroup T) := by rw [← hbot, htop]; exact Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup T) := by rw [← hbot, htop]; exact Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

theorem center_eq_bot_of_mulEquiv {T T' : Type*} [Group T] [Group T'] (ψ : T ≃* T')
    (h : Subgroup.center T = ⊥) : Subgroup.center T' = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : ψ.symm z ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro a
    apply ψ.injective
    rw [map_mul, map_mul, ψ.apply_symm_apply]
    exact hz (ψ a)
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot, ← ψ.apply_symm_apply z, hz', map_one]

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem center_layer_eq_bot_of_sp62 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 3 (GaloisField 2 1)) :
    Subgroup.center (layer G) = ⊥ := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hodd : Odd (Nat.card (Subgroup.center (layer G))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_symplectic hodd
    (e₀.trans (projSpEquivStatedProj 3 (GaloisField 2 1)))

theorem false_of_sp62_nine (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 3 (GaloisField 2 1))
    (h9 : Nat.card (A.map (layerConj G)) = 9) : False :=
  false_of_E27_of_card_nine h (center_layer_eq_bot_of_sp62 h e₀) (e₀.trans sp62Equiv)
    (isElemAbelian_baseA wreathFacts_zH) (card_baseA wreathFacts_zH) h9

theorem false_of_sp62 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 3 (GaloisField 2 1)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := center_layer_eq_bot_of_sp62 h e₀
  set θ := e₀.trans sp62Equiv with hθ
  have hf := wreathFacts_zH
  have hCA := Item434Kit.inf_centralizer_layer_eq_bot h hZ θ (isElemAbelian_baseA hf)
    (card_baseA hf)
  have hA27 := card_map_quotConj h hCA θ
  have hZX : Subgroup.center H6 = ⊥ := by
    have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := h.isQuasisimple.2.1
    have : Group.IsPerfect (layer G) := h.isQuasisimple.1
    have : Group.IsPerfect (layer G ⧸ Subgroup.center (layer G)) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (layer G)))
        (QuotientGroup.mk'_surjective _)
    exact center_eq_bot_of_mulEquiv θ center_eq_bot_of_isSimpleGroup
  have hinj := conj_injective_of_center_eq_bot hZX
  have hout : ¬ 3 ∣ Nat.card (Outer H6) := by
    rw [card_outer_H6]
    norm_num
  set P := (A.map (quotConj θ)).comap (MulAut.conj : H6 →* MulAut H6) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj θ) := map_comap_conj_eq h θ hout
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, hA27]
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    isElemAbelian_of_map_injective hinj (hPmap ▸ isElemAbelian_map_quotConj h θ)
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW zH tH)
    (by rw [card_wreathW_zH, factorization_card_H6]; norm_num) hPp
  have hPg : P.map (MulAut.conj g⁻¹).toMonoidHom = baseA zH :=
    eq_baseA_of_le_wreathW hf card_wreathW_zH (Item434AltPerm.map_conj_inv_le hg)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hPe)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP27])
  have hPeq : P = (baseA zH).map (MulAut.conj g).toMonoidHom := by
    rw [← hPg, Item434AltPerm.map_conj_map_conj_inv]
  refine false_of_normalizer_conj h θ (P := (baseA zH).map MulAut.conj) ?_ (MulAut.conj g) ?_
  · intro Y hY3 hYN
    set Y' := Y.comap (MulAut.conj : H6 →* MulAut H6) with hY'
    have hYmap : Y'.map MulAut.conj = Y :=
      Subgroup.map_comap_eq_self fun φ _ => mem_range_conj_H6 φ
    have hY'card : Nat.card Y' = Nat.card Y := by
      conv_rhs => rw [← hYmap]
      rw [Subgroup.card_map_of_injective hinj]
    have hAN : baseA zH ≤ Subgroup.normalizer (Y' : Set H6) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hc := Subgroup.mem_normalizer_iff.mp (hYN ⟨a, ha, rfl⟩) (MulAut.conj y)
      rw [hY', Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact hc
    have hbot := eq_bot_of_baseA_le_normalizer (by rwa [hY'card]) hAN
    rw [← hYmap, hbot, Subgroup.map_bot]
  · have hcomp : (MulAut.conj : H6 →* MulAut H6).comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (MulAut.conj g)).toMonoidHom.comp MulAut.conj := by
      refine MonoidHom.ext fun x => ?_
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    rw [← hPmap, hPeq, Subgroup.map_map, Subgroup.map_map, hcomp]

end Item434SmallTwoIII

section Families


theorem item434SmallTwoIII_Sp62_9 : Item434SecForCard IsSmallTwoSp62 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  obtain ⟨e₀⟩ := hL
  exact (Item434SmallTwoIII.false_of_sp62_nine hc e₀ h9).elim

theorem item434SmallTwoIII_Sp62_27 : Item434SecForCard IsSmallTwoSp62 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL _
  obtain ⟨e₀⟩ := hL
  exact (Item434SmallTwoIII.false_of_sp62 hc e₀).elim

theorem item434SmallTwoIII_Sp62 : Item434SmallTwoIII_Sp62 :=
  item434SecFor_of_card item434SmallTwoIII_Sp62_9 item434SmallTwoIII_Sp62_27

end Families

end CFSG.RankThree.PartTwo.Sec4

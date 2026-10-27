module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVKit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Local
public import Certificates.Certificate9615
import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Sylow
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (f4TwoIndex primePowerTwo)

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open Item434Kit Item434Alt
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)


section Certs


namespace Item434F42

theorem exists_model {X : Type} [Group X] (e : X ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (X ≃* adjointGroup ReeTag.F4.tag K) := by
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 primePowerTwo f4TwoIndex.2 rfl e
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hmodel
  exact ⟨K, inferInstance, inferInstance, hK, ⟨φ⟩⟩

theorem not_three_dvd_card_outer {X : Type} [Group X]
    (e : X ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group) : ¬ 3 ∣ Nat.card (Outer X) := by
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 primePowerTwo f4TwoIndex.2 rfl e
  obtain ⟨Y, _, _, hY, ⟨e'⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hmodel
  have hY' : Nat.card Y = 2 ^ 1 := hY
  have : CharP Y 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (le_refl 1) hY'
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ :=
    CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (le_refl 1) Y hY'
  have h1 : Nat.card (Outer X) = Nat.card (Outer (adjointGroup ReeTag.F4.tag Y)) :=
    Nat.card_congr (equivalence e').toEquiv
  have h2 : Nat.card (Outer (adjointGroup ReeTag.F4.tag Y)) =
      Nat.card (Multiplicative (ZMod (2 * 1))) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)).toEquiv
  have hc : Nat.card (Multiplicative (ZMod (2 * 1))) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    simp
  rw [h1, h2, hc]
  norm_num

theorem exists_e9_le_e81_f42 {X : Type} [Group X]
    (e : X ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group) {P : Subgroup X}
    (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    ∃ P₁ : Subgroup X, P₁ ≤ P ∧ Nat.card P₁ = 9 ∧
      ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ P₁ ≤ E := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := exists_model e
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (le_refl 1) hK'
  have hG : Nat.card (adjointGroup ReeTag.F4.tag K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hK] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  have : Finite (adjointGroup ReeTag.F4.tag K) :=
    Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  obtain ⟨Q, hQcard, hgood⟩ := f42_sound (K := K) f42Data Certificates.certificate9615
  have hQ : 3 * Nat.card Q = 3 ^ (Nat.card (adjointGroup ReeTag.F4.tag K)).factorization 3 := by
    rw [hQcard, hG, show (3311126603366400 : ℕ) = 3 ^ 6 * 4542011801600 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 6 (by norm_num)]
    rfl
  set P' := P.map φ.toMonoidHom with hP'
  have hP'e : CFSG.Assembly.IsElemAbelian 3 P' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP
  have hP'27 : Nat.card P' = 27 := by
    rw [hP', Subgroup.card_map_of_injective φ.injective, hP27]
  obtain ⟨P₁', hP₁'P', hP₁'9, E', hE'e, hE'81, hP₁'E'⟩ :=
    exists_e9_le_e81 hQ (fun x hx y hy => hgood x y hx hy) hP'e hP'27
  refine ⟨P₁'.map φ.symm.toMonoidHom, ?_, ?_, E'.map φ.symm.toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E' hE'e, ?_,
    Subgroup.map_mono hP₁'E'⟩
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨r, hr, rfl⟩ := hP₁'P' hq
    simpa using hr
  · rw [Subgroup.card_map_of_injective φ.symm.injective, hP₁'9]
  · rw [Subgroup.card_map_of_injective φ.symm.injective]
    exact hE'81

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_f42_27 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group)
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h27' : Nat.card h.layerStar = 27 := h27
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases h.card_layerStar with h9 | ⟨-, hZ⟩
    · omega
    · exact hZ
  have hcen := Item434SmallTwoIV.center_eq_bot_of_layer_quotient h e₀
  have hinj := conj_injective_of_center_eq_bot hcen
  have hA27 : Nat.card (A.map (quotConj e₀)) = 27 := by
    rw [Item434Spor.card_map_quotConj h e₀, h27']
  have hKe := isElemAbelian_map_quotConj h e₀
  have hX3 : ¬ 3 ∣ Nat.card (Outer (TauCeti.CFSGIndex.lie f4TwoIndex).Group) :=
    not_three_dvd_card_outer (MulEquiv.refl _)
  have hmap := map_comap_conj_eq h e₀ hX3
  set K := A.map (quotConj e₀) with hK
  set P := K.comap (MulAut.conj : (TauCeti.CFSGIndex.lie f4TwoIndex).Group →* _) with hP
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hA27]
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    isElemAbelian_of_map_injective hinj (by rw [hmap]; exact hKe)
  obtain ⟨P₁, hP₁P, hP₁9, E, hEe, hE81, hP₁E⟩ := exists_e9_le_e81_f42 (MulEquiv.refl _) hPe hP27
  set F₁ := P₁.map (MulAut.conj : (TauCeti.CFSGIndex.lie f4TwoIndex).Group →* _) with hF₁
  have hF₁K : F₁ ≤ K := by
    rw [← hmap]
    exact Subgroup.map_mono hP₁P
  have hF₁9 : Nat.card F₁ = 9 := by
    rw [hF₁, Subgroup.card_map_of_injective hinj, hP₁9]
  refine false_of_fixed h hZ e₀ (B := A ⊓ F₁.comap (quotConj e₀)) inf_le_left
    (hF₁9.symm.le.trans (card_le_card_inf_comap e₀ hF₁K)) hEe hE81 ?_
  rintro b ⟨-, hb⟩ d hd
  obtain ⟨p, hp, hpb⟩ := hb
  have hpd : p * d = d * p := congrArg Subtype.val (hEe.1.is_comm.comm ⟨p, hP₁E hp⟩ ⟨d, hd⟩)
  rw [← hpb, MulAut.conj_apply, hpd, mul_inv_cancel_right]

end Ctx

end Item434F42

open Item434F42


theorem item434SmallTwoIV_F42_27 : Item434SmallTwoIV_F42_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  exact (false_of_f42_27 hc e₀ h27).elim

end Certs

end CFSG.RankThree.PartTwo.Sec4

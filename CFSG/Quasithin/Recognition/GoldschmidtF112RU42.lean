module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport
public import CFSG.Quasithin.Recognition.GoldschmidtF112RU42Model
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9Group
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Trans
public import CFSG.Quasithin.EmptyFaithful.Gold14610CmpMain
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FaithfulA5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Short2OfA5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M3
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Alt5OfOrth
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Omega4MinusOfOrth

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open CFSG.Quasithin.H13.F431.U42 U42F431

variable {G : Type} [Group G] [Finite G]

theorem parabolic_le_normalizer_right {L1 L2 S : Subgroup G} (h : Hyp111 L1 L2 S) :
    L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
  refine sup_le Subgroup.le_normalizer (sup_le (sup_le h.h2.borel_le ?_) h.h2.normalizes)
  exact (inf_le_left : borelOf L2 S ≤ L2).trans Subgroup.le_normalizer

theorem card_eq_of_VA5 {L : Subgroup G} (h : VA5 L) :
    Nat.card L = 60 * Nat.card (pCoreOf 2 L) := by
  have h60 : Nat.card (oTwoQuot ↥L) = 60 := by
    rw [IsL2Quot.card (by norm_num) h]
    norm_num
  have h1 : Nat.card L = Nat.card (OTwoQuot L) * Nat.card (CFSG.Open.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [h1]
  have h2 : Nat.card (OTwoQuot L) = 60 := h60
  rw [h2, pCoreOf, Subgroup.card_map_of_injective L.subtype_injective]

theorem y9U42_plain {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (h2 : VA5 L2)
    (hA : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 1)) :
    (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
        centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
      IsSpecialPow 2 (2 ^ 1) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsBlock2 L2 L2 ∧ IsOmega4MinusType L2 1 ∧ IsAltType L2 5 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hF.1
  have hN2 := parabolic_le_normalizer_right hH
  have hL2P : L2 ≤ L2 ⊔ bigB L1 L2 S := le_sup_left
  have hc := card_eq_of_VA5 h2
  rcases exists_iso_pair hA with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  swap
  · exfalso
    have h576 : Nat.card ↥(L2 ⊔ bigB L1 L2 S) = 576 :=
      (Nat.card_congr e.φ2.toEquiv).trans card_P1
    have h5 : 5 ∣ Nat.card ↥(L2 ⊔ bigB L1 L2 S) :=
      (hc ▸ Dvd.dvd.mul_right (by norm_num) _ : 5 ∣ Nat.card L2).trans
        (Subgroup.card_dvd_of_le hL2P)
    rw [h576] at h5
    norm_num at h5
  have φ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥P1 := e.φ1
  have φ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥P2 := e.φ2
  obtain ⟨P, hP⟩ : ∃ P, P = L2 ⊔ bigB L1 L2 S := ⟨_, rfl⟩
  rw [← hP] at φ2 hN2 hL2P
  have h960 : Nat.card P = 960 := (Nat.card_congr φ2.toEquiv).trans card_P2
  have hO16 : Nat.card (pCoreOf 2 P) = 16 :=
    (card_pCoreOf_of_mulEquiv φ2 2).trans (by rw [pCoreOf_P2]; exact CFSG.GH74.QTGen4.U42.card_Vsub_eq)
  have hO2L : pCoreOf 2 L2 = L2 ⊓ pCoreOf 2 P := pCoreOf_eq_inf_pCoreOf hL2P hN2
  have hdvd : Nat.card (pCoreOf 2 L2) ∣ 16 :=
    hO16 ▸ Subgroup.card_dvd_of_le (hO2L ▸ inf_le_right)
  have hidx : L2.relIndex P * Nat.card L2 = 960 := by
    have := Subgroup.relIndex_mul_card (H := L2) (K := P)
    rwa [inf_eq_left.mpr hL2P, h960] at this
  have hpos : 0 < Nat.card (pCoreOf 2 L2) := Nat.card_pos
  have hr16 : L2.relIndex P * Nat.card (pCoreOf 2 L2) = 16 := by
    rw [hc] at hidx
    nlinarith
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (show L2.relIndex P ∣ 2 ^ 4 from ⟨_, hr16.symm⟩)
  haveI : (L2.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN2
  have hq : IsPGroup 2 (P ⧸ L2.subgroupOf P) := IsPGroup.of_card (n := k) hk
  have hperf : ⁅P, P⁆ = P := perfect_of_mulEquiv φ2 CFSG.Quasithin.F112R.U42M.perfect_P2
  have hLeq : L2 = P := eq_of_perfect_of_pGroup_quotient hL2P hq hperf
  have hE : IsElemAbelian 2 (pCoreOf 2 P) := by
    apply isElemAbelian_pCoreOf_of_mulEquiv φ2
    rw [pCoreOf_P2]
    refine ⟨⟨⟨fun a b => Subtype.ext (Vsub_comm a.2 b.2)⟩⟩, fun x hx => ?_⟩
    rw [pow_two]
    exact Vsub_sq hx
  have hNat : ¬ NatSec P ⊥ (pCoreOf 2 P) := by
    have hw := exists_three_fix_of_mulEquiv φ2 (p := 2)
      (by rw [pCoreOf_P2]; exact CFSG.Quasithin.F112R.U42M.exists_three_fix_P2)
    obtain ⟨x, hx, ho, v, hv, hv1, hvx⟩ := hw
    intro hn
    apply hv1
    have := hn x hx ho v hv (by
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hvx)
    exact Subgroup.mem_bot.mp this
  have hcen : ∀ g ∈ P, (∀ k ∈ P, g * k = k * g) → g = 1 :=
    fun g hg => eq_one_of_central_of_mulEquiv φ2
      (fun b hb hb' => CFSG.Quasithin.F112R.U42M.eq_one_of_central_P2 hb hb') hg
  have hct : CharTwo P := by
    rw [hP, ← bigB_comm L1 L2 S, F1.parabolic_eq]
    exact hH.h2.charTwo
  have hSP : S ≤ P := hP ▸ (le_sup_right.trans le_sup_right)
  subst hLeq
  haveI : DSLeaf LeafFaithfulA5 := ⟨leafFaithfulA5⟩
  haveI : DSLeaf LeafShort2OfA5 := ⟨leafShort2OfA5⟩
  haveI : DSLeaf LeafM3 := ⟨leafM3⟩
  haveI : DSLeaf LeafAlt5OfOrth := ⟨leafAlt5OfOrth⟩
  refine ⟨?_, ?_, Gold14610.isBlock2_of_short (leafShort2OfA5 h2 hct hE hO16) le_rfl Subgroup.le_normalizer,
    leafOmega4MinusOfOrth h2 hct hE hO16 hNat, leafAlt5OfOrth h2 hct hE hO16 hNat⟩
  · intro hz z hz'
    have hz1 : z = 1 := hcen z (hSP hz'.1) fun k hk =>
      (Subgroup.mem_centralizer_iff.mp (hz hz') k hk).symm
    rw [hz1]
    exact Subgroup.one_mem _
  · rw [pow_one]
    exact IsSpecialPow.of_mulEquiv (pCoreOfMulEquiv φ1 2).symm
      CFSG.Quasithin.F112R.U42M.isSpecialPow_pCoreOf_P1

end CFSG.Quasithin.F112R

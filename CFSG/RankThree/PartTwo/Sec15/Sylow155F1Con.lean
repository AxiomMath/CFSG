module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155F1Bal
import CFSG.RankThree.PartTwo.Sec4.StepsBender
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.RelativeZJ
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Sylow155F1

theorem le_pPrimeCore_of_bender_of_constrained {X : Type} [Group X] [Finite X]
    (hX : Subgroup.centralizer
        (CFSG.pCore 3 (X ⧸ CFSG.pPrimeCore 3 X) : Set (X ⧸ CFSG.pPrimeCore 3 X)) ≤
      CFSG.pCore 3 (X ⧸ CFSG.pPrimeCore 3 X))
    {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA3 : ∀ y ∈ Subgroup.centralizer (A : Set X), y ^ 3 = 1 → y ∈ A) {Y : Subgroup X}
    (hY : ¬ 3 ∣ Nat.card Y) (hAY : A ≤ Subgroup.normalizer (Y : Set X)) :
    Y ≤ CFSG.pPrimeCore 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 X with hNdef
  have hN : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  set π := QuotientGroup.mk' N
  set P := CFSG.pCore 3 (X ⧸ N)
  have hPtop : Subgroup.normalizer (P : Set (X ⧸ N)) = ⊤ := Subgroup.normalizer_eq_top P
  have hS : ¬ 3 ∣ Nat.card (Y.map π) := fun h => hY (h.trans (Subgroup.card_map_dvd Y π))
  have hAS : A.map π ≤ Subgroup.normalizer ((Y.map π : Subgroup (X ⧸ N)) : Set (X ⧸ N)) :=
    (Subgroup.map_mono hAY).trans (Subgroup.le_normalizer_map π)
  have hcomm : ⁅P, Y.map π⁆ = ⊥ :=
    Sec4.commutator_eq_bot_of_bender_quotient hA hA3 hN hS hAS CFSG.pCore_isPGroup
      (by rw [hPtop]; exact le_top) (by rw [hPtop]; exact le_top)
  have hYC : Y.map π ≤ Subgroup.centralizer (P : Set (X ⧸ N)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm, hcomm]
  have hYP : IsPGroup 3 (Y.map π) := CFSG.pCore_isPGroup.to_le (hYC.trans hX)
  have hbot : Y.map π = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hYP
    rcases k with _ | k
    · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
    · exact (hS (by rw [hk]; exact dvd_pow_self 3 (Nat.succ_ne_zero k))).elim
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

variable {G : Type} [Group G] [Finite G]

theorem inf_le_pPrimeCoreOf_of_isPConstrained {A H Q : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA3 : ∀ x ∈ Subgroup.centralizer (A : Set G), x ^ 3 = 1 → x ∈ A) (hAH : A ≤ H)
    (hH : CFSG.ABGLocalTools.IsPConstrained 3 ↥H) (hQ : ¬ 3 ∣ Nat.card Q)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) : Q ⊓ H ≤ pPrimeCoreOf 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := CFSG.ABGTheoremB.RelativeZJ.centralizer_pCore_quotient_le hH
  have hA' : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf H) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h := hA.1.is_comm.comm (⟨((a : H) : G), a.2⟩ : A) ⟨((b : H) : G), b.2⟩
      simpa using congrArg Subtype.val h
    · have h3 := hA.2 _ (Subgroup.mem_subgroupOf.mp hx)
      simpa using h3
  have hA3' : ∀ y ∈ Subgroup.centralizer ((A.subgroupOf H : Subgroup H) : Set H), y ^ 3 = 1 →
      y ∈ A.subgroupOf H := by
    intro y hy hy3
    have hy3' : (y : G) ^ 3 = 1 := by
      have h := congrArg Subtype.val hy3
      simpa using h
    refine Subgroup.mem_subgroupOf.mpr (hA3 y ?_ hy3')
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := Subgroup.mem_centralizer_iff.mp hy ⟨a, hAH ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h
  have hYH : Q ⊓ H ≤ H := inf_le_right
  have hY' : ¬ 3 ∣ Nat.card ((Q ⊓ H).subgroupOf H) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv]
    exact fun h => hQ (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hAY : A ≤ Subgroup.normalizer ((Q ⊓ H : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAQ (hAH.trans Subgroup.le_normalizer)
  have hAY' : A.subgroupOf H ≤
      Subgroup.normalizer (((Q ⊓ H).subgroupOf H : Subgroup H) : Set H) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h := Subgroup.mem_normalizer_iff.mp (hAY (Subgroup.mem_subgroupOf.mp ha)) y
    simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv] using h
  have h := le_pPrimeCore_of_bender_of_constrained hX hA' hA3' hY' hAY'
  rw [← Subgroup.map_subgroupOf_eq_of_le hYH]
  exact Subgroup.map_mono h

theorem mem_of_mem_centralizer_of_sec14Std {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) :
    ∀ x ∈ Subgroup.centralizer (A : Set G), x ^ 3 = 1 → x ∈ A := by
  intro x hx hx3
  have hsup := isElemAbelian_sup_zpowers h.isE27.1 hx3 (Subgroup.mem_centralizer_iff.mp hx)
  exact (h.toSec13Data.eq_of_le hsup le_sup_left).le
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

theorem commutator_le_pPrimeCoreOf_of_isPConstrained {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {V : Subgroup G} (hV3 : ¬ 3 ∣ Nat.card V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) {B : Subgroup G} (hBA : IsHyperplane A B)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G))) {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G)) :
    ⁅V ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  have hA : Late.IsE27 A := h.isE27
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨e, hBA.1 he⟩ ⟨a, ha⟩)
  have hVB := inf_le_pPrimeCoreOf_of_isPConstrained hA.1
    (mem_of_mem_centralizer_of_sec14Std h) hAB hcon hV3 hAV
  have hgB : g ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBA.1) hgA
  rw [Subgroup.commutator_le]
  intro v hv y hy
  have hyB : y ∈ Subgroup.centralizer (B : Set G) := (Subgroup.zpowers_le.mpr hgB) hy
  have h1 : y * v⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
    (Subgroup.mem_normalizer_iff.mp (Sec14.le_normalizer_pPrimeCoreOf 3 _ hyB) v⁻¹).mp
      (inv_mem (hVB hv))
  rw [commutatorElement_def]
  simpa [mul_assoc] using mul_mem (hVB hv) h1

end Sylow155F1

variable {G : Type} [Group G] [Finite G]

@[expose] def Step155BalCompW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
      ∀ g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M,
        g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) →
          Odd (orderOf g) →
          ∀ B : Subgroup G, IsHyperplane A B → (∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) →
            ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G)) →
            ⁅CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ ≤
              pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))

theorem step155BalW_of_balComp {A : Subgroup G} {c : G} {L : Subgroup G}
    (hB : Step155BalCompW A c L) : Step155BalW A c L := by
  intro h X K Y M T P hC hmax hab hE h146 hRP hIX g hg hgZ hodd B hBA hfree
  by_cases hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G))
  · have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
    have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
      hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    have hV3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 M) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
      rw [hk]
      intro h3
      have := Nat.prime_three.dvd_of_dvd_pow h3
      omega
    exact Sylow155F1.commutator_le_pPrimeCoreOf_of_isPConstrained h hV3 hAV hBA hcon
      (pPrimeCoreOf_le 3 _ hg.1)
  · exact hB h X K Y M T P hC hmax hab hE h146 hRP hIX g hg hgZ hodd B hBA hfree hcon

theorem step155HostCharSupW_of_balComp {A : Subgroup G} {c : G} {L : Subgroup G}
    (h142 : Concl142S14) (h1444 : Item1444S14) (hB : Step155BalCompW A c L) :
    Step155HostCharSupW A c L := fun h =>
  step155HostCharSupW_of_f1Zero (h1444 G A c L h)
    (step155F1ZeroW_of_bal (h142 G A c L h) (step155BalW_of_balComp hB)) h

end CFSG.RankThree.PartTwo.Sec15

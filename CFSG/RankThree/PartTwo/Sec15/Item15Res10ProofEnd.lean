module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofEnd
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155wProof
import CFSG.RankThree.PartTwo.Sec15.Item1523Proof
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A L Y : Subgroup G} {c : G}

namespace Proof15Res10

theorem normalizer_eq_n155
    (h : Conf1515HJ A c L Y) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) :
    Subgroup.normalizer (Y : Set G) = n155 A Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (h.n155_le_normalizer h152 h153)
  have hO1 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := h.mem_scriptY0Star.prop.2.2
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hO1
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hNM : Subgroup.normalizer (Y : Set G) ≤ M :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y).trans hle
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hNM (sup_le Subgroup.le_normalizer h.A_le_normalizer hx)⟩
  rw [(h153 Y h.mem_scriptY0Star).1] at hMm
  have hMeq : M = n155 A Y := Set.mem_singleton_iff.mp hMm
  exact hMeq ▸ hNM

theorem isCharacteristicP_normalizer
    (h : Conf1515HJ A c L Y)
    (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A)) :
    IsCharacteristicP 2 ↥(Subgroup.normalizer (Y : Set G)) := by
  have hmem := n155_mem_maximalTwoLocalsContaining h153 h.mem_scriptY0Star
  rw [normalizer_eq_n155 h h152 h153]
  exact CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.sec15R.toTheoremFourHyp.charTwoType
    hmem.1.1

omit [Finite G] in
theorem commutator_pCoreOf_ne_bot {N : Subgroup G} (hN : IsCharacteristicP 2 ↥N) {c : G}
    (hcN : c ∈ N) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ⁅CFSG.Open.pCoreOf 2 N, Subgroup.zpowers c⁆ ≠ ⊥ := by
  intro hbot
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
  have hcC : (⟨c, hcN⟩ : ↥N) ∈
      Subgroup.centralizer ((CFSG.pCore 2 ↥N : Subgroup ↥N) : Set ↥N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxO : (x : G) ∈ CFSG.Open.pCoreOf 2 N := (mem_pCoreOf_iff1523 x).mpr hx
    have hxc := Subgroup.mem_centralizer_iff.mp (hbot hxO) c (Subgroup.mem_zpowers c)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hxc.symm
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥N)) ⟨_, hN hcC⟩
  have hck : c ^ (2 ^ k) = 1 := by
    have := congrArg (fun x : ↥(CFSG.pCore 2 ↥N) => ((x : ↥N) : G)) hk
    simpa using this
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have hord : orderOf c = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hck)
      (orderOf_dvd_of_pow_eq_one hc3))
  exact hc1 (orderOf_eq_one_iff.mp hord)

theorem commutator_le_centralizer {L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
      Subgroup.centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set Q := CFSG.Open.pCoreOf 2 N with hQdef
  set Z := Subgroup.zpowers c with hZdef
  have hZL : ⁅Z, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hcl : Commute l c := Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
    exact (hcl.zpow_right k).eq
  have hQN : Q ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hLQ : ⁅L, Q⁆ ≤ CFSG.Open.pCoreOf 2 L := by
    have h1 : ⁅L, Q⁆ ≤ L ⊓ Q := by
      rw [Subgroup.commutator_le]
      intro l hl q hq
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · have hql : q * l⁻¹ * q⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hQN hq) l⁻¹).mp (L.inv_mem hl)
        have e : l * q * l⁻¹ * q⁻¹ = l * (q * l⁻¹ * q⁻¹) := by group
        rw [e]
        exact L.mul_mem hl hql
      · have hlq : l * q * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hNQ (hLN hl)) q).mp hq
        exact Q.mul_mem hlq (Q.inv_mem hq)
    refine h1.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_)
    · exact Late.le_normalizer_inf Subgroup.le_normalizer (hLN.trans hNQ)
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le inf_le_right
  have hOZ : ⁅CFSG.Open.pCoreOf 2 L, Z⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 L) le_rfl).trans
      ((Subgroup.commutator_comm L Z).trans hZL).le)
  have h2 : ⁅⁅L, Q⁆, Z⁆ = ⊥ := le_bot_iff.mp ((Subgroup.commutator_mono hLQ le_rfl).trans hOZ.le)
  have h1 : ⁅⁅Z, L⁆, Q⁆ = ⊥ := by rw [hZL, Subgroup.commutator_bot_left]
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at h3

end Proof15Res10

open Proof15Res4 Proof15Res10

theorem Proof15Res10.false_of_commutator_le
    (h : Conf1515HJ A c L L)
    (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A)) {d : G}
    (hodd : Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))))
    (hRP : ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.sec13Data
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set R := ⁅CFSG.Open.pCoreOf 2 N, Subgroup.zpowers c⁆ with hRdef
  have hchar := isCharacteristicP_normalizer h h152 h153
  have hcN : c ∈ N := hD.le_normalizer hD.mem_A
  have hc3 : c ^ 3 = 1 := by rw [← hD.orderOf_eq]; exact pow_orderOf_eq_one c
  have hR1 : R ≠ ⊥ := commutator_pCoreOf_ne_bot hchar hcN hc3 hD.ne_one
  have hRQ : R ≤ CFSG.Open.pCoreOf 2 N := by
    refine Subgroup.le_normalizer_iff_commutator_le_left.mp ?_
    exact (Subgroup.zpowers_le.mpr hcN).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)
  have hRN : R ≤ N := hRQ.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 N)
  have hR2 : IsPGroup 2 R := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le hRQ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hR1 (Subgroup.eq_bot_of_card_eq R (by rw [hn, pow_zero]))
  have h2R : 2 ∣ Nat.card R := hn ▸ dvd_pow_self 2 hn0
  have h2 : 2 ∣ Nat.card ↥(N ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) :=
    h2R.trans (Subgroup.card_dvd_of_le (le_inf hRN hRP))
  have hmod := Nat.odd_iff.mp hodd
  have hmod' := Nat.mod_eq_zero_of_dvd h2
  omega

@[expose] noncomputable def Step1515HJEndFpfRCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Conf1515HJ A c L L →
    (∀ e ∈ A, e ≠ 1 → IsZCentral L e →
      CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) →
    ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))

section Core

theorem step1515HJEndFpfX_of_core (h152 : Item152R) (h153 : Item153MainR)
    (hC : Step1515HJEndFpfRCore) : Step1515HJEndFpfX := by
  intro G _ _ A c L h hfree d hdA hd1 hdZ hodd
  exact (false_of_commutator_le h (h152 G A c L h.sec15R) (h153 G A c L h.sec15R) hodd
    (hC G A c L h hfree d hdA hd1 hdZ hodd)).elim

theorem step1515HJEndFpfT0_of_core (h152 : Item152R) (h153 : Item153MainR)
    (hC : Step1515HJEndFpfRCore) : Step1515HJEndFpfT0 := by
  intro G _ _ A c L h hfree d hdA hd1 hdZ hodd _hX
  exact false_of_commutator_le h (h152 G A c L h.sec15R) (h153 G A c L h.sec15R) hodd
    (hC G A c L h hfree d hdA hd1 hdZ hodd)

end Core

end CFSG.RankThree.PartTwo.Sec15

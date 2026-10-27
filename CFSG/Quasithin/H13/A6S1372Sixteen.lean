module

public import CFSG.Quasithin.H13.A6S1372FifteenB
public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6Sixteen

variable {P : Type} [CommGroup P] [Finite P]

theorem isTwoReduced_of_pCoreOf {X K : Subgroup (MulAut P)} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut P))) (hO2 : pCoreOf 2 X = ⊥) :
    XMod.IsTwoReduced ↥K (⊤ : Subgroup P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro D hD hdk d hd l _
  set D' : Subgroup (MulAut P) := D.map K.subtype with hD'
  have hD'2 : IsPGroup 2 ↥D' := by
    rintro ⟨_, e, he, rfl⟩
    obtain ⟨k, hk⟩ := hdk e he
    refine ⟨k, Subtype.ext ?_⟩
    apply MulEquiv.ext
    intro p
    exact hk p (Subgroup.mem_top p)
  have hD'K : D' ≤ K := Subgroup.map_subtype_le D
  have hD'n : (D'.subgroupOf K).Normal := by
    have : D'.subgroupOf K = D := Subgroup.comap_map_eq_self_of_injective K.subtype_injective D
    rw [this]
    exact hD
  have h1 : D' ≤ pCoreOf 2 K := CFSG.LieType.BorelTits.le_pCoreOf 2 hD'K hD'n hD'2
  have h2 : pCoreOf 2 K ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKX)
      (hXN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hdD : ((d : ↥K) : MulAut P) ∈ D' := ⟨d, hd, rfl⟩
  have h3 := h2 (h1 hdD)
  rw [hO2, Subgroup.mem_bot] at h3
  show ((d : ↥K) : MulAut P) l = l
  rw [h3]
  rfl

theorem odd_card_eqvAut_of_irrPlus (hP : ∀ p : P, p ^ 2 = 1) {X K : Subgroup (MulAut P)}
    (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut P))) (hO2 : pCoreOf 2 X = ⊥)
    (hcomm : commV K = ⊤) (hU : commV K ∈ IrrPlus K ⊤) :
    Odd (Nat.card ↥(XMod.eqvAut ↥K P)) := by
  rw [hcomm] at hU
  obtain ⟨-, hc, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hU
  refine XMod.odd_card_eqvAut hP (by rw [commOf_eq_commSub, hc]) ?_
    (isTwoReduced_of_pCoreOf hKX hXN hO2)
  rw [fixed_eq_inf_fixV]
  exact ⟨hlt, fun J hJ hfJ hJt => hirr J ((isInv_iff K J).1 hJ) hfJ hJt⟩

theorem odd_card_eqvAut_of_copies (hP : ∀ p : P, p ^ 2 = 1) {K : Subgroup (MulAut P)}
    (hKq : CFSG.IsQuasisimple ↥K) (hcomm : commV K = ⊤) {n : ℕ} (hn : 2 ≤ n)
    (h : DirectSumOfCopies K (commV K) ⊥
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) 1) :
    Odd (Nat.card ↥(XMod.eqvAut ↥K P)) := by
  obtain ⟨I, π, -, -, hsup, hR⟩ := h
  have hI : I 0 = ⊤ := by
    rw [← hcomm, ← hsup, bot_sup_eq, iSup_unique]
    rfl
  have hirr := B5.isIrr_of_realizes hn (hR 0)
  rw [hI] at hirr
  exact InternalSec.odd_card_eqvAut_of_irr hP hirr.2
    (InternalSec.exists_noncomm_of_isQuasisimple hKq)

omit [Finite P] in
theorem eq_one_of_odd {K : Subgroup (MulAut P)} (hodd : Odd (Nat.card ↥(XMod.eqvAut ↥K P)))
    {q : MulAut P} (hq : q ∈ Subgroup.centralizer (K : Set (MulAut P))) {k : ℕ}
    (hk : q ^ 2 ^ k = 1) : q = 1 := by
  have hqe : q ∈ XMod.eqvAut ↥K P := by
    intro a p
    exact (congrArg (fun f : MulAut P => f p) (Subgroup.mem_centralizer_iff.1 hq a a.2)).symm
  have hk' : (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥K P)) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
  have hd1 : orderOf (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥K P)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hd2 := orderOf_dvd_natCard (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥K P))
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(XMod.eqvAut ↥K P)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  exact congrArg Subtype.val h1

omit [Finite P] in
theorem inf_centralizer_eq_bot {K : Subgroup (MulAut P)}
    (hodd : Odd (Nat.card ↥(XMod.eqvAut ↥K P))) {Y : Subgroup (MulAut P)} (hY : IsPGroup 2 ↥Y) :
    Y ⊓ Subgroup.centralizer (K : Set (MulAut P)) = ⊥ := by
  rw [eq_bot_iff]
  rintro q ⟨hqY, hqC⟩
  obtain ⟨k, hk⟩ := hY ⟨q, hqY⟩
  exact Subgroup.mem_bot.2 (eq_one_of_odd hodd hqC (by simpa using congrArg Subtype.val hk))

end A6Sixteen

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}
  {H : Subgroup G}

theorem isPGroup_T_plus [IsMulCommutative ↥(conjClosure S.V3 H)] (hTH : T ≤ H) :
    IsPGroup 2 (autSec (autOn T (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨q, hqT, rfl⟩ := (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H)
    S.le_normalizer_U0 hTH).1 hψ
  obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨q, hqT⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hq : q ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  show (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) S.le_normalizer_U0 q) ^ 2 ^ k = 1
  rw [← map_pow, hq, map_one]

namespace Conf

@[expose] def KData [IsMulCommutative ↥(conjClosure S.V3 H)] (C : S.Conf H)
    (B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))))
    (K : Subgroup G) : Prop :=
  IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B ∧
    B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
    K ∈ cComp H ∧
    CFSG.Open.IsComponentOf (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
      (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∧
    B ≤ Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
        Subgroup _) : Set _) ∧
    ¬ B ≤ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
        Subgroup _) : Set _) ∧
    autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ≤
      Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
          Subgroup _) : Set _) ∧
    commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) = ⊤ ∧
    quasithinGenFitting (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) =
      autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
    Nat.card (commV B) ≤ 4 ∧
    A6FifteenB.K15 (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))
      (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B ∧
    pCoreOf 2 (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) = ⊥

end Conf

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem exists_KData
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) (hLem : Lem1374One) (h56 : AsB56) (h51 : AsB51) (h42 : AsB42)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    ∃ B K, C.KData B K := by
  obtain ⟨B, hB, hBA, K, hKc, hKcomp, hBN, hBnot, hXN, hcomm, hFJ, hB4, h15⟩ :=
    C.exists_K_b42 hNS h13315 h1356two hH hab hhat hNU hna h13314 hLem h56 h51 h42
  exact ⟨B, K, hB, hBA, hKc, hKcomp, hBN, hBnot, hXN, hcomm, hFJ, hB4, h15,
    S.pCoreOf_plus_eq_bot hNS h13315 h1356two hH hab hNU hhat hLem⟩

end Hat

end Conf

end NonAb

namespace Conf

variable [IsMulCommutative ↥(conjClosure S.V3 H)] {C : S.Conf H}
  {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
  {K : Subgroup G}

theorem KData.odd_card_eqvAut
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K) :
    Odd (Nat.card ↥(XMod.eqvAut ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
      (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))) := by
  obtain ⟨-, -, -, hKcomp, -, -, hXN, hcomm, -, -, h15, hO2⟩ := hK
  have hV' : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hV := Bridge.sec_sq_eq_one hV' (⊤ : Subgroup ↥(conjClosure S.V3 H))
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))
  have hKq : CFSG.IsQuasisimple ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) :=
    B1Red.isQuasisimple_of_open hKcomp.2.2
  rcases h15 with ⟨h1, -⟩ | ⟨-, n, hn, hcop⟩
  · exact A6Sixteen.odd_card_eqvAut_of_irrPlus hV hKcomp.1 hXN hO2 hcomm h1.1
  · exact A6Sixteen.odd_card_eqvAut_of_copies hV hKq hcomm
      (by rcases hn with rfl | rfl <;> norm_num) hcop

theorem KData.inf_centralizer_eq_bot
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K)
    {Y : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
    (hY : IsPGroup 2 ↥Y) :
    Y ⊓ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
        Subgroup _) : Set _) = ⊥ :=
  A6Sixteen.inf_centralizer_eq_bot (hK.odd_card_eqvAut hab) hY

theorem KData.T_plus_inf_centralizer_eq_bot (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    (hK : C.KData B K) (hTH : T ≤ H) :
    autSec (autOn T (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ⊓
      Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
        Subgroup _) : Set _) = ⊥ :=
  hK.inf_centralizer_eq_bot hab (isPGroup_T_plus hTH)

end Conf

end Setting4

end CFSG.Quasithin.H13.A6

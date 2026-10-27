module

public import CFSG.RankThree.PartTwo.Sec17.Item1727Proof
public import CFSG.RankThree.PartTwo.Sec17.Item1724NRouteProofCore
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

namespace Proof1724N

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G} {s d r : G}

theorem mem_centralizer_d (h415 : Sec4.Item4_15) (h1721 : Item1721) (h1725 : Item1725)
    (h : Sec17Data G A c L Y₀ Y₁ S p P w Q s d r)
    (hQc : Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥)
    (hne : Q ⊓ Subgroup.centralizer ({d} : Set G) ≠ ⊥) :
    d ∈ Subgroup.centralizer ((omegaOneZ p Q ⊓ Y₁ : Subgroup G) : Set G) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  set Z := omegaOneZ p Q with hZdef
  set Z₁ := Z ⊓ Y₁ with hZ₁def
  obtain ⟨hdA, hdL⟩ := Subgroup.mem_inf.mp h.d_mem
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp h.w_mem).1
  have hwL : w ∈ L := (Subgroup.mem_inf.mp h.w_mem).2
  have hwd : w * d = d * w := commute_of_isThreeCentralIn h415 hJ h.isE27.isPGroup hwL hwA
    h.w_pow_three hdA hdL h.d_ne_one h.d_threeCentral
  have hZQ : Z ≤ Q := omegaOneZ_le p Q
  have hZe : CFSG.Assembly.IsElemAbelian p Z := isElemAbelian_omegaOneZ p Q
  have hNZ := normalizer_le_normalizer_omegaOneZ p Q
  have hAY : A ≤ Subgroup.normalizer (Y₁ : Set G) := h.mem_y1Star.prop.1.1.1.2
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := h.le_normalizer_Q
  set R := Q ⊓ Subgroup.centralizer ({d} : Set G) with hRdef
  have hRp : IsPGroup p R := h.isPGroup_Q.to_le inf_le_left
  have hRN : Subgroup.zpowers w ⊔ A ≤ Subgroup.normalizer (R : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (mem_normalizer_inf_centralizer h.w_normalizes_Q hwd))
      (fun a ha => mem_normalizer_inf_centralizer (hAQ ha) (h.commute_of_mem ha hdA))
  have hZR : omegaOneZ p R ≤ Z := le_omegaOneZ_of_invariant h1725 h.toSec17S hQc
    ((omegaOneZ_le p R).trans inf_le_left) (hRN.trans (normalizer_le_normalizer_omegaOneZ p R))
    (fun x hx => hx.2.2)
  have hZd : Z ⊓ Subgroup.centralizer ({d} : Set G) ≠ ⊥ := by
    intro hbot
    apply omegaOneZ_ne_bot hRp hne
    rw [eq_bot_iff, ← hbot]
    exact le_inf hZR ((omegaOneZ_le p R).trans inf_le_right)
  have hXQ : Z ⊓ Subgroup.centralizer ({d} : Set G) ≤ Q := inf_le_left.trans hZQ
  have hXN : Subgroup.zpowers w ⊔ A ≤
      Subgroup.normalizer ((Z ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (mem_normalizer_inf_centralizer (hNZ h.w_normalizes_Q) hwd))
      (fun a ha => mem_normalizer_inf_centralizer (hNZ (hAQ ha)) (h.commute_of_mem ha hdA))
  have hXinv : Z ⊓ Subgroup.centralizer ({d} : Set G) ∈
      invariantPiSubgroups Q (Subgroup.zpowers w ⊔ A) (piOf p) :=
    ⟨hXQ, fun q hq => h.isPiSubgroup_Q q (hq.trans (Subgroup.card_dvd_of_le hXQ)), hXN⟩
  obtain ⟨-, -, hX3⟩ := h1725 G A c L Y₀ Y₁ S p P w Q h.toSec17WQ _ hXinv
  have hXcard : Nat.card (Z ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) =
      Nat.card (Z ⊓ Subgroup.centralizer ({d} : Set G) ⊓ Y₁ : Subgroup G) ^ 3 := by
    rw [← yI_one Y₁ w]
    exact hX3 (isElemAbelian_of_le hZe inf_le_left).1
  set Yd := Z₁ ⊓ Subgroup.centralizer ({d} : Set G) with hYddef
  have hYd : Z ⊓ Subgroup.centralizer ({d} : Set G) ⊓ Y₁ = Yd := inf_right_comm _ _ _
  have hYd1 : Yd ≠ ⊥ := by
    intro hbot
    rw [hYd, hbot, Subgroup.card_bot, one_pow] at hXcard
    exact hZd (Subgroup.card_eq_one.mp hXcard)
  obtain ⟨hZ₁p2, -⟩ := card_omegaOneZ h1725 h.toSec17S hQc
  have hZ₁e : CFSG.Assembly.IsElemAbelian p Z₁ := isElemAbelian_of_le hZe inf_le_left
  have hcZ₁ : c ∈ Subgroup.normalizer (Z₁ : Set G) :=
    mem_normalizer_omegaOneZ_inf (hAQ h.c_mem) (hAY h.c_mem)
  have hsZ₁ : s ∈ Subgroup.normalizer (Z₁ : Set G) :=
    mem_normalizer_omegaOneZ_inf h.s_normalizes_Q h.s_normalizes_y1
  have hCsd : Subgroup.centralizer ({s * d * s⁻¹} : Set G) =
      Subgroup.centralizer ({d} : Set G) :=
    KFacts.KS14.centralizer_eq_of_zpowers_eq (h.zpowers_conj_s h415 h1721).2
  have hsYd : s ∈ Subgroup.normalizer (Yd : Set G) := by
    refine mem_normalizer_of_map_conj_eq' ?_
    rw [hYddef, map_conj_inf_centralizer hsZ₁, hCsd]
  have hcYd : c ∈ Subgroup.normalizer (Yd : Set G) :=
    mem_normalizer_inf_centralizer hcZ₁ (h.commute_of_mem h.c_mem hdA)
  have hYde : CFSG.Assembly.IsElemAbelian p Yd := isElemAbelian_of_le hZ₁e inf_le_left
  have hYdfix : Yd ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ (inf_le_left.trans (inf_le_left.trans hZQ))).trans
      hQc.le)
  have hYdne := card_ne_of_inverts hYde hYd1 h.c_pow_three hcYd hYdfix hsYd h.s_inverts_c
  have hYdZ₁ : Yd = Z₁ := by
    have hdvd : Nat.card Yd ∣ p ^ 2 := hZ₁p2 ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow h.p_prime).mp hdvd
    interval_cases m
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hmc)) hYd1
    · exact absurd (by simpa using hmc) hYdne
    · exact Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hmc, hZ₁p2])
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [← hYdZ₁] at hz
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hz).2

end Proof1724N

end CFSG.RankThree.PartTwo.Sec17

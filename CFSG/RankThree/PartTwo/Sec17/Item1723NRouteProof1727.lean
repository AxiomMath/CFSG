module

public import CFSG.RankThree.PartTwo.Sec17.Item1723NRouteProofCore
public import CFSG.RankThree.PartTwo.Sec17.Item1724NRouteProof1727
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
public import CFSG.RankThree.PartTwo.Sec17.Item1727HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1727Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

namespace Proof1723N

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G} {s d r : G}

theorem exists_normalizes_inverts (h415 : Sec4.Item4_15) (h1715 : Item1715)
    (h1721 : Item1721) (h1723 : Item1723N) (h : Sec17Data G A c L Y₀ Y₁ S p P w Q s d r)
    (htr : ∀ Q₁ ∈ scriptQPiStar A (lB A) ⊤ (piOf p), ∀ Q₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf p),
      IsConjIn (xA A) Q₁ Q₂) {e : G} (heAL : e ∈ A ⊓ L)
    (hed : e ∉ Subgroup.zpowers d) :
    ∃ t₂ : G, t₂ ∈ Subgroup.normalizer (Q : Set G) ∧ t₂ ∈ Subgroup.normalizer (Y₁ : Set G) ∧
      t₂ * c * t₂⁻¹ = c ∧ e * (t₂ * e * t₂⁻¹) ∈ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  obtain ⟨-, -, h9, hAeq⟩ := h.hj_facts h1715 h415 hJ
  have hcA : c ∈ A := h.c_mem
  obtain ⟨hdA, hdL⟩ := Subgroup.mem_inf.mp h.d_mem
  obtain ⟨heA, heL⟩ := Subgroup.mem_inf.mp heAL
  have hd3 : d ^ 3 = 1 := h.isE27.1.2 d hdA
  have he3 : e ^ 3 = 1 := h.isE27.1.2 e heA
  have hde : d * e = e * d := h.commute_of_mem hdA heA
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp h.w_mem).1
  have hwL : w ∈ L := (Subgroup.mem_inf.mp h.w_mem).2
  have hwd : w * d = d * w := commute_of_isThreeCentralIn h415 hJ h.isE27.isPGroup hwL hwA
    h.w_pow_three hdA hdL h.d_ne_one h.d_threeCentral
  have hdAL : Subgroup.zpowers d ≤ A ⊓ L := Subgroup.zpowers_le.mpr h.d_mem
  obtain ⟨hTsyl, hwN⟩ := isSylowOf_inf_sup_zpowers h415 hJ h.isE27 h9 hwA hwL h.w_not_mem
    h.orderOf_w
  obtain ⟨t, htL, -, htx⟩ := exists_inverts_mod_zpowers h415 hJ hTsyl
    (le_sup_left (a := A ⊓ L) h.d_mem) h.d_ne_one h.d_threeCentral
  have htAL : t ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have e' : t * x * t⁻¹ = x⁻¹ * (x * (t * x * t⁻¹)) := by group
    rw [e']
    exact mul_mem (inv_mem hx) (hdAL (htx x (le_sup_left (a := A ⊓ L) hx)))
  have htc : t * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c htL)
  have htA : t ∈ Subgroup.normalizer (A : Set G) := by
    rw [hAeq]
    exact mem_normalizer_sup
      (Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer (h.le_centralizer_c htL))
      htAL
  obtain ⟨x, hx, hxQ⟩ := htr Q h.mem_qStar_G _ (map_conj_mem_qStarTop htA h.mem_qStar_G)
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hx
  have hxA : x ∈ Subgroup.normalizer (A : Set G) := xA_le_normalizer A hx
  set t₁ := x⁻¹ * t with ht₁def
  have ht₁Q : t₁ ∈ Subgroup.normalizer (Q : Set G) :=
    inv_mul_mem_normalizer_of_map_conj_eq hxQ.symm
  have ht₁A : t₁ ∈ Subgroup.normalizer (A : Set G) := mul_mem (inv_mem hxA) htA
  have ht₁a : ∀ a ∈ A, t₁ * a * t₁⁻¹ = t * a * t⁻¹ := by
    intro a ha
    have hta : t * a * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htA a).mp ha
    have hxta : (t * a * t⁻¹) * x = x * (t * a * t⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hxC _ hta
    calc t₁ * a * t₁⁻¹ = x⁻¹ * ((t * a * t⁻¹) * x) := by rw [ht₁def]; group
      _ = t * a * t⁻¹ := by rw [hxta, inv_mul_cancel_left]
  obtain ⟨j, hj⟩ := exists_conj_eq_pow h1723 h.toSec17W ht₁A
  refine ⟨(w ^ j)⁻¹ * t₁, mul_mem (inv_mem (pow_mem h.w_normalizes_Q j)) ht₁Q,
    inv_mul_mem_normalizer_of_map_conj_eq hj.symm, ?_, ?_⟩
  ·
    have hwjc : w ^ j * c = c * w ^ j :=
      (Commute.pow_left (show Commute w c from h.w_commute_c.symm) j).eq
    have h1 : t₁ * c * t₁⁻¹ = c := by rw [ht₁a c hcA, htc, mul_inv_cancel_right]
    calc (w ^ j)⁻¹ * t₁ * c * ((w ^ j)⁻¹ * t₁)⁻¹ = (w ^ j)⁻¹ * (t₁ * c * t₁⁻¹) * (w ^ j) := by
          group
      _ = c := by rw [h1, mul_assoc, ← hwjc, ← mul_assoc, inv_mul_cancel, one_mul]
  ·
    have hwAL : w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
      hwN (Subgroup.mem_zpowers w)
    have hweAL : w * e * w⁻¹ ∈ A ⊓ L := (Subgroup.mem_normalizer_iff.mp hwAL e).mp heAL
    have heo : orderOf e = 3 := orderOf_eq_prime he3 (fun h1 => hed (h1 ▸ one_mem _))
    have hAL : A ⊓ L = Subgroup.zpowers e ⊔ Subgroup.zpowers d := by
      have hle : Subgroup.zpowers e ⊔ Subgroup.zpowers d ≤ A ⊓ L :=
        sup_le (Subgroup.zpowers_le.mpr heAL) hdAL
      have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) :=
        Subgroup.zpowers_le.mpr (Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer
          (Subgroup.mem_centralizer_singleton_iff.mpr hde))
      have hdisj : Disjoint (Subgroup.zpowers e) (Subgroup.zpowers d) := by
        rw [disjoint_iff, inf_comm]
        exact inf_zpowers_eq_bot heo hed
      have hcard : Nat.card (Subgroup.zpowers e ⊔ Subgroup.zpowers d : Subgroup G) = 9 := by
        rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hdN hdisj,
          Nat.card_zpowers, Nat.card_zpowers, heo, orderOf_eq_prime hd3 h.d_ne_one]
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hcard])).symm
    have heC : e ∈ Subgroup.centralizer (Subgroup.zpowers d : Set G) := by
      rw [KFacts.KS14.centralizer_zpowers_eq]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hde.symm
    have hweAL' := hweAL
    rw [hAL] at hweAL'
    obtain ⟨a₁, l₁, hl₁, hwe⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup heC hweAL'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl₁
    have hwe' : w * e * w⁻¹ = e * d ^ i :=
      conj_eq_mul_zpow_of_pow_three he3 hde hed h.w_pow_three hwd hwe
    have hwdz : ∀ k : ℤ, w⁻¹ * d ^ k * w = d ^ k := fun k => by
      have hc := (Commute.zpow_right (show Commute w d from hwd) k).eq
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    have hwinv : w⁻¹ * e * w = e * d ^ (-i) := by
      have h1 : w⁻¹ * (w * e * w⁻¹) * w = e := by group
      rw [hwe'] at h1
      calc w⁻¹ * e * w = (w⁻¹ * (e * d ^ i) * w) * (w⁻¹ * d ^ i * w)⁻¹ := by group
        _ = e * d ^ (-i) := by rw [h1, hwdz, zpow_neg]
    have hwn : ∀ n : ℕ, ∃ m : ℤ, (w ^ n)⁻¹ * e * w ^ n = e * d ^ m := by
      intro n
      induction n with
      | zero => exact ⟨0, by simp⟩
      | succ n ih =>
        obtain ⟨m, hm⟩ := ih
        refine ⟨-i + m, ?_⟩
        calc (w ^ (n + 1))⁻¹ * e * w ^ (n + 1) = w⁻¹ * ((w ^ n)⁻¹ * e * w ^ n) * w := by
              rw [pow_succ]; group
          _ = w⁻¹ * (e * d ^ m) * w := by rw [hm]
          _ = (w⁻¹ * e * w) * (w⁻¹ * d ^ m * w) := by group
          _ = e * d ^ (-i) * d ^ m := by rw [hwinv, hwdz]
          _ = e * d ^ (-i + m) := by rw [mul_assoc, ← zpow_add]
    obtain ⟨m, hm⟩ := hwn j
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (htx e (le_sup_left (a := A ⊓ L) heAL))
    have hte : t * e * t⁻¹ = e⁻¹ * d ^ k := by rw [hk]; group
    have hwjdk : (w ^ j)⁻¹ * d ^ k * w ^ j = d ^ k := by
      have hc := (Commute.zpow_right (Commute.pow_left (show Commute w d from hwd) j) k).eq
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    have h3 : (w ^ j)⁻¹ * t₁ * e * ((w ^ j)⁻¹ * t₁)⁻¹ = (e * d ^ m)⁻¹ * d ^ k := by
      calc (w ^ j)⁻¹ * t₁ * e * ((w ^ j)⁻¹ * t₁)⁻¹ =
            (w ^ j)⁻¹ * (t₁ * e * t₁⁻¹) * w ^ j := by group
        _ = (w ^ j)⁻¹ * (e⁻¹ * d ^ k) * w ^ j := by rw [ht₁a e heA, hte]
        _ = ((w ^ j)⁻¹ * e * w ^ j)⁻¹ * ((w ^ j)⁻¹ * d ^ k * w ^ j) := by group
        _ = (e * d ^ m)⁻¹ * d ^ k := by rw [hm, hwjdk]
    rw [h3]
    have hcomm : e * (d ^ m)⁻¹ = (d ^ m)⁻¹ * e :=
      ((Commute.zpow_right (show Commute e d from hde.symm) m).inv_right).eq
    have h4 : e * ((e * d ^ m)⁻¹ * d ^ k) = (d ^ m)⁻¹ * d ^ k := by
      calc e * ((e * d ^ m)⁻¹ * d ^ k) = e * (d ^ m)⁻¹ * e⁻¹ * d ^ k := by group
        _ = (d ^ m)⁻¹ * e * e⁻¹ * d ^ k := by rw [hcomm]
        _ = (d ^ m)⁻¹ * d ^ k := by group
    rw [h4]
    exact mul_mem (inv_mem (Subgroup.zpow_mem_zpowers d m)) (Subgroup.zpow_mem_zpowers d k)

theorem item1727_at (h415 : Sec4.Item4_15) (h1715 : Item1715) (h1719 : Item1719)
    (h1721 : Item1721) (h1723 : Item1723N) (h1725 : Item1725)
    (h : Sec17Data G A c L Y₀ Y₁ S p P w Q s d r)
    (htr : ∀ Q₁ ∈ scriptQPiStar A (lB A) ⊤ (piOf p), ∀ Q₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf p),
      IsConjIn (xA A) Q₁ Q₂)
    (hQc : Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) :
    Q ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : p ≠ 3 := h.three_lt_p.ne'
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  obtain ⟨-, -, h9, -⟩ := h.hj_facts h1715 h415 hJ
  by_contra hne
  set Z₁ := omegaOneZ p Q ⊓ Y₁ with hZ₁def
  have hdC := Proof1724N.mem_centralizer_d h415 h1721 h1725 h hQc hne
  have hcA : c ∈ A := h.c_mem
  obtain ⟨hdA, hdL⟩ := Subgroup.mem_inf.mp h.d_mem
  have hd3 : d ^ 3 = 1 := h.isE27.1.2 d hdA
  have hAY : A ≤ Subgroup.normalizer (Y₁ : Set G) := h.mem_y1Star.prop.1.1.1.2
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := h.le_normalizer_Q
  obtain ⟨e, heAL, hed⟩ : ∃ e ∈ A ⊓ L, e ∉ Subgroup.zpowers d := by
    by_contra hcon
    have hle : A ⊓ L ≤ Subgroup.zpowers d := fun x hx => by
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
    have hle' := Subgroup.card_le_of_le hle
    rw [h9, Nat.card_zpowers, orderOf_eq_prime hd3 h.d_ne_one] at hle'
    omega
  obtain ⟨heA, heL⟩ := Subgroup.mem_inf.mp heAL
  have he3 : e ^ 3 = 1 := h.isE27.1.2 e heA
  have heo : orderOf e = 3 := orderOf_eq_prime he3 (fun h1 => hed (h1 ▸ one_mem _))
  have hde : d * e = e * d := h.commute_of_mem hdA heA
  have hdAL : Subgroup.zpowers d ≤ A ⊓ L := Subgroup.zpowers_le.mpr h.d_mem
  have hAL : A ⊓ L = Subgroup.zpowers e ⊔ Subgroup.zpowers d := by
    have hle : Subgroup.zpowers e ⊔ Subgroup.zpowers d ≤ A ⊓ L :=
      sup_le (Subgroup.zpowers_le.mpr heAL) hdAL
    have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) :=
      Subgroup.zpowers_le.mpr (Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer
        (Subgroup.mem_centralizer_singleton_iff.mpr hde))
    have hdisj : Disjoint (Subgroup.zpowers e) (Subgroup.zpowers d) := by
      rw [disjoint_iff, inf_comm]
      exact inf_zpowers_eq_bot heo hed
    have hcard : Nat.card (Subgroup.zpowers e ⊔ Subgroup.zpowers d : Subgroup G) = 9 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hdN hdisj,
        Nat.card_zpowers, Nat.card_zpowers, heo, orderOf_eq_prime hd3 h.d_ne_one]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hcard])).symm
  have heC : e ∈ Subgroup.centralizer (Subgroup.zpowers d : Set G) := by
    rw [KFacts.KS14.centralizer_zpowers_eq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hde.symm
  have hdzC : Subgroup.zpowers d ≤ Subgroup.centralizer (Z₁ : Set G) :=
    Subgroup.zpowers_le.mpr hdC
  obtain ⟨hsL, -⟩ := h.zpowers_conj_s h415 h1721
  have hsAL : s ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    le_normalizer_inf (Subgroup.zpowers_le.mpr h.s_mem_W) (Subgroup.zpowers_le.mpr hsL)
      (Subgroup.mem_zpowers s)
  have hseAL : s * e * s⁻¹ ∈ A ⊓ L := (Subgroup.mem_normalizer_iff.mp hsAL e).mp heAL
  rw [hAL] at hseAL
  obtain ⟨k₂, l₂, hl₂, hse⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup heC hseAL
  obtain ⟨t₂, ht₂Q, ht₂Y, ht₂c, ht₂e⟩ :=
    exists_normalizes_inverts h415 h1715 h1721 h1723 h htr heAL hed
  obtain ⟨hZ₁p2, -⟩ := Proof1724N.card_omegaOneZ h1725 h.toSec17S hQc
  have hZ₁e : CFSG.Assembly.IsElemAbelian p Z₁ :=
    isElemAbelian_of_le (isElemAbelian_omegaOneZ p Q) inf_le_left
  have hfix : Z₁ ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ (inf_le_left.trans (omegaOneZ_le p Q))).trans hQc.le)
  have heZ : e ∈ Subgroup.centralizer (Z₁ : Set G) :=
    mem_centralizer_of_inverts hp3 hZ₁e hZ₁p2 h.c_pow_three he3 (h.commute_of_mem hcA heA)
      (mem_normalizer_omegaOneZ_inf (hAQ hcA) (hAY hcA))
      (mem_normalizer_omegaOneZ_inf (hAQ heA) (hAY heA))
      (mem_normalizer_omegaOneZ_inf h.s_normalizes_Q h.s_normalizes_y1)
      (mem_normalizer_omegaOneZ_inf ht₂Q ht₂Y) hfix h.s_inverts_c ht₂c
      ⟨k₂, l₂, hdzC hl₂, hse⟩ ⟨e * (t₂ * e * t₂⁻¹), hdzC ht₂e, by group⟩
  have hALC : A ⊓ L ≤ Subgroup.centralizer (Z₁ : Set G) := by
    rw [hAL]
    exact sup_le (Subgroup.zpowers_le.mpr heZ) hdzC
  have hPp : IsPGroup p P := (isPiSubgroup_piOf_iff h.p_prime P).mp h.mem_qStar_p.prop.2
  have hPY : P ≤ Y₁ := h.mem_qStar_p.prop.1.2
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := h.mem_qStar_p.prop.1.1.1.2.2
  have hcop : Nat.Coprime (Nat.card (A ⊓ L : Subgroup G)) (Nat.card P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
    rw [h9, hn, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow 2 n ((Nat.coprime_primes Nat.prime_three h.p_prime).mpr hp3.symm)
  have hALP : A ⊓ L ≤ Subgroup.centralizer (P : Set G) :=
    le_centralizer_of_forall_pow_eq_one' (by have := h.three_lt_p; omega) hPp hcop
      (inf_le_left.trans hAP) (fun y hy x hx hxp => by
        have hxZ₁ : x ∈ Z₁ :=
          Proof1724N.mem_omegaOneZ_of_pow_eq_one h1725 h.toSec17S hQc (h.le_Q hx) (hPY hx) hxp
        exact (Subgroup.mem_centralizer_iff.mp (hALC hy) x hxZ₁).symm)
  have hcP : c ∉ Subgroup.centralizer (P : Set G) := by
    intro hcP
    apply h.commutator_not_le_M
    have hbot : ⁅P, Subgroup.zpowers c⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [KFacts.KS14.centralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hcP x hx
    rw [hbot]
    exact bot_le
  have hle : A ⊓ L ≤ A ⊓ Subgroup.centralizer (P : Set G) := le_inf inf_le_left hALP
  have hdvd : Nat.card (A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h.isE27.2]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hge : 9 ≤ Nat.card (A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :=
    h9 ▸ Subgroup.card_le_of_le hle
  have hne27 : Nat.card (A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) ≠ 27 := by
    intro h27
    have heqA : A ⊓ Subgroup.centralizer (P : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, h.isE27.2])
    have hcAP : c ∈ A ⊓ Subgroup.centralizer (P : Set G) := by
      rw [heqA]
      exact hcA
    exact hcP (Subgroup.mem_inf.mp hcAP).2
  have h9' : Nat.card (A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 9 := by
    obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases m
    · rw [hmc] at hge
      norm_num at hge
    · rw [hmc] at hge
      norm_num at hge
    · rw [hmc]
      norm_num
    · exfalso
      apply hne27
      rw [hmc]
      norm_num
  exact h1719 G A c L Y₀ Y₁ S p P h.toSec17Y1
    (Subgroup.eq_of_le_of_card_ge hle (by rw [h9', h9]))

end Proof1723N

theorem item1727_of_1723N (h415 : Sec4.Item4_15) (h1715 : Item1715) (h1719 : Item1719)
    (h1721 : Item1721) (h1723 : Item1723N) (h1724 : Item1724N) (h1725 : Item1725) :
    Item1727 := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q s d r h
  obtain ⟨htr, h3⟩ := h1724 G A c L Y₀ Y₁ S p P w Q h.toSec17W
  exact Proof1723N.item1727_at h415 h1715 h1719 h1721 h1723 h1725 h htr
    (Proof1724N.inf_centralizer_c_eq_bot h.toSec17W h3)

end CFSG.RankThree.PartTwo.Sec17

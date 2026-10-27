module

public import CFSG.RankThree.PartTwo.Sec11.Item1115
public import CFSG.RankThree.PartTwo.Sec11.FixedPoints
import CFSG.RankThree.PartTwo.Sec11.RFactsK
import CFSG.RankThree.PartTwo.Sec11.Item1116Proof
public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
public import CFSG.RankThree.PartTwo.Sec11.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1125Proof

section Elementary

variable {G : Type*} [Group G]

theorem three_pow_succ_dvd_orderOf {y : G} (hy : ∃ k : ℕ, y ^ 3 ^ k = 1) {m : ℕ}
    (hm : 3 ^ m < orderOf y) : 3 ^ (m + 1) ∣ orderOf y := by
  obtain ⟨k, hk⟩ := hy
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  rw [hn] at hm ⊢
  exact pow_dvd_pow 3 ((Nat.pow_lt_pow_iff_right (by norm_num)).mp hm)

theorem mem_zpowers_pow_three {y c : G} (hc3 : c ^ 3 = 1) (hcy : c ∈ Subgroup.zpowers y)
    (h9 : 9 ∣ orderOf y) : c ∈ Subgroup.zpowers (y ^ 3) := by
  obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcy
  have h1 : y ^ (e * 3) = 1 := by
    rw [zpow_mul]
    exact_mod_cast hc3
  have h3 : ((9 : ℕ) : ℤ) ∣ e * 3 :=
    (Int.natCast_dvd_natCast.mpr h9).trans (orderOf_dvd_iff_zpow_eq_one.mpr h1)
  obtain ⟨t, ht⟩ : (3 : ℤ) ∣ e := by omega
  refine Subgroup.mem_zpowers_iff.mpr ⟨t, ?_⟩
  rw [ht, ← zpow_natCast, ← zpow_mul]
  push_cast
  rfl

theorem mem_zpowers_conj_mul_inv {j y : G} (hy : ∃ k : ℕ, y ^ 3 ^ k = 1) {n : ℕ}
    (hn : 3 * n ∣ orderOf y) (hjy : j * y * j⁻¹ ∈ Subgroup.zpowers y)
    (hinv : j * y ^ n * j⁻¹ = (y ^ n)⁻¹) : y ∈ Subgroup.zpowers (j * y * j⁻¹ * y⁻¹) := by
  obtain ⟨v, hv⟩ := Subgroup.mem_zpowers_iff.mp hjy
  have hpos : 0 < orderOf y := by
    obtain ⟨k, hk⟩ := hy
    exact Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hk) (by positivity)
  have hn0 : (n : ℤ) ≠ 0 := by
    intro h0
    have h0' : n = 0 := by exact_mod_cast h0
    rw [h0', mul_zero, zero_dvd_iff] at hn
    omega
  have h1 : j * y ^ n * j⁻¹ = y ^ (v * n) := by
    rw [← conj_pow, ← hv, ← zpow_natCast, ← zpow_mul]
  have h2 : y ^ ((v + 1) * n) = 1 := by
    rw [add_mul, zpow_add, ← h1, hinv, one_mul, zpow_natCast, inv_mul_cancel]
  have h3 : ((3 * n : ℕ) : ℤ) ∣ (v + 1) * n :=
    (Int.natCast_dvd_natCast.mpr hn).trans (orderOf_dvd_iff_zpow_eq_one.mpr h2)
  push_cast at h3
  have h4 : (3 : ℤ) ∣ v + 1 := (mul_dvd_mul_iff_right hn0).mp h3
  have h5 : j * y * j⁻¹ * y⁻¹ = y ^ (v - 1) := by rw [← hv, zpow_sub_one]
  rw [h5]
  exact Item1116Proof.mem_zpowers_zpow_of_not_dvd hy (by omega)

theorem eq_one_of_mem_zpowers_of_mem [Finite G] {a w : G} {I : Subgroup G}
    (ha : orderOf a = 3) (haI : a ∉ I) (hw : w ∈ Subgroup.zpowers a) (hwI : w ∈ I) : w = 1 := by
  by_contra hw1
  have hw3 : orderOf w = 3 := by
    have h := orderOf_dvd_of_mem_zpowers hw
    rw [ha] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have heq : Subgroup.zpowers w = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, ha, hw3])
  have haw : a ∈ Subgroup.zpowers w := heq ▸ Subgroup.mem_zpowers a
  exact haI (Subgroup.zpowers_le.mpr hwI haw)

end Elementary

end Item1125Proof

section Data


variable {G : Type} [Group G] [Finite G]

theorem Sec11Data.of_closure_eq {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    Sec11Data G A c L a R Y d x s a g := by
  have hle : ∀ u v : G, Subgroup.closure ({u, s} : Set G) = Subgroup.closure {v, s} →
      Subgroup.closure ({u, x, s} : Set G) ≤ Subgroup.closure {v, x, s} := by
    intro u v huv
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    refine ⟨?_, Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
    have hu : u ∈ Subgroup.closure ({v, s} : Set G) := huv ▸ Subgroup.subset_closure (by simp)
    refine Subgroup.closure_mono ?_ hu
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  exact { h with
    R_eq := h.R_eq.trans (le_antisymm (hle r a hrs) (hle a r hrs.symm))
    a_mem_closure := Subgroup.subset_closure (by simp) }

theorem Sec11Data.normalizer_sec11P_le_normalizer_zpowers_d (h113 : Item113) (h117 : Item117)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G)) :
    Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  have hdA : d ∈ A := by
    have hd : d ∈ A ⊓ L := by
      rw [h.inf_eq]
      exact Subgroup.mem_zpowers d
    exact hd.1
  have hd3 : orderOf d = 3 := orderOf_eq_prime (h.mem_partTwoF.1.2 d hdA)
    (h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq).2.2
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one
  have hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    (h117 G A c L a R Y h.toSec11Std d h.inf_eq (Subgroup.zpowers d)
      (Subgroup.zpowers_le.mpr hdA) (by rw [Nat.card_zpowers, hd3])).mpr rfl
  have hPd := (h.sec11P_le_normalizer_A h113).trans hWd
  have hgP : g ∈ sec11P R g :=
    (le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g)
  have htrans := h.htrans_of_mem_normalizer (hPd hgP)
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set D := (Subgroup.zpowers d).map (MulAut.conj n).toMonoidHom with hD
  have hPD : ∀ q ∈ sec11P R g, D.map (MulAut.conj q).toMonoidHom = D := by
    intro q hq
    have hq' : n⁻¹ * q * n ∈ sec11P R g := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) q).mp hq
      rwa [inv_inv] at h1
    have h1 : (Subgroup.zpowers d).map (MulAut.conj (n⁻¹ * q * n)).toMonoidHom =
        Subgroup.zpowers d := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPd hq')
    rw [hD, map_conj_map_conj, show q * n = n * (n⁻¹ * q * n) by group, ← map_conj_map_conj, h1]
  have hDcd : D ≤ Subgroup.closure {c, d} := by
    rw [hD, MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact (Subgroup.mem_normalizer_iff.mp (hcdN hn) d).mp (Subgroup.subset_closure (by simp))
  have hDcard : Nat.card D = Nat.card (Subgroup.zpowers c) := by
    rw [hD, Subgroup.card_map_of_injective (MulAut.conj n).injective, Nat.card_zpowers,
      Nat.card_zpowers, hd3, hc3]
  obtain ⟨p, hp, hpD⟩ := htrans D hDcd hDcard hne
  have hcD : Subgroup.zpowers c = D := by
    have h1 : D.map (MulAut.conj p⁻¹).toMonoidHom = Subgroup.zpowers c := by
      rw [hpD, map_conj_map_conj, inv_mul_cancel, map_one]
      ext z
      simp
    exact h1.symm.trans (hPD p⁻¹ (inv_mem hp))
  apply h.g_not_mem
  have hgc : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c := by
    rw [hcD]
    exact hPD g hgP
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgc

theorem Sec11Data.mem_normalizer_closure_of_inverts (h45 : Sec4.Item4_5) (h113 : Item113)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) (hx9 : 9 < orderOf x)
    (hsc : Subgroup.zpowers s ≠ Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {j : G}
    (hjg : j ∈ Subgroup.centralizer {g})
    (hja : j ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G))
    (hjP : j ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G))
    (hjinv : ∀ y ∈ Subgroup.closure ({s ^ 3, x ^ 9} : Set G), j * y * j⁻¹ = y⁻¹) :
    g ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) := by
  set V := Subgroup.closure ({s, x} : Set G) with hVdef
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hks := Item1116Proof.exists_pow_eq_one_of_mem h hsR
  have hkx := Item1116Proof.exists_pow_eq_one_of_mem h hxR
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hcs := h.c_mem_zpowers_s
  have h9s : 9 ∣ orderOf s := by
    have h1 := Item1125Proof.three_pow_succ_dvd_orderOf hks (m := 1)
      (lt_of_lt_of_le (by norm_num) (Item1116Proof.nine_le_orderOf_s h hsc))
    simpa using h1
  have h27x : 27 ∣ orderOf x := by
    have h1 := Item1125Proof.three_pow_succ_dvd_orderOf hkx (m := 2) (by simpa using hx9)
    simpa using h1
  have hcU : c ∈ Subgroup.closure ({s ^ 3, x ^ 9} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      (Item1125Proof.mem_zpowers_pow_three hc3 hcs h9s)
  have hjH : j ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    rw [hjinv c hcU]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)
  have hjL := h.toSec11Std.normalizer_le_normalizer_L h45 hjH
  have haj : j * a = a * j := by
    have hI := commutator_mem_innerPreimage outAbelian1016 h.isList1016 hjL
      h.toHyp81.a_mem_normalizer
    have hZ : j * a * j⁻¹ * a⁻¹ ∈ Subgroup.zpowers a :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hja a).mp (Subgroup.mem_zpowers a))
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
    have h1 := Item1125Proof.eq_one_of_mem_zpowers_of_mem
      (orderOf_eq_prime (h.mem_partTwoF.1.2 a h.a_mem) h.a_ne_one)
      h.toSec11Std.a_not_mem_innerPreimage hZ hI
    calc j * a = (j * a * j⁻¹ * a⁻¹) * (a * j) := by group
      _ = a * j := by rw [h1, one_mul]
  have hjR : j ∈ Subgroup.normalizer (R : Set G) := by
    have h1 := Subgroup.inf_normalizer_le_normalizer_inf ⟨hjP, Subgroup.le_normalizer hjL⟩
    rwa [h.inf_normalizer_L h45 h113] at h1
  have hjx : j * x * j⁻¹ ∈ Subgroup.zpowers x := by
    have hN := Subgroup.inf_normalizer_le_normalizer_inf ⟨hjR, hjL⟩
    rw [h.inf_L_eq] at hN
    exact (Subgroup.mem_normalizer_iff.mp hN x).mp (Subgroup.mem_zpowers x)
  have hjs : j * s * j⁻¹ ∈ Subgroup.zpowers s := by
    have hN := Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hjR, Sec6.normalizer_le_normalizer_thetaQuotCentralizer L hjL⟩
    rw [h.inf_centralizer_eq] at hN
    exact (Subgroup.mem_normalizer_iff.mp hN s).mp (Subgroup.mem_zpowers s)
  have hs' : s ∈ Subgroup.zpowers (j * s * j⁻¹ * s⁻¹) :=
    Item1125Proof.mem_zpowers_conj_mul_inv hks (n := 3) (by simpa using h9s) hjs
      (hjinv _ (Subgroup.subset_closure (by simp)))
  have hx' : x ∈ Subgroup.zpowers (j * x * j⁻¹ * x⁻¹) :=
    Item1125Proof.mem_zpowers_conj_mul_inv hkx (n := 9) (by simpa using h27x) hjx
      (hjinv _ (Subgroup.subset_closure (by simp)))
  have hR' : R = Subgroup.closure {a, x, s} := (h.of_closure_eq hrs).R_eq
  have hRV := h.R_le_normalizer_V h45
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have hQ : ∀ y ∈ R, j * y * j⁻¹ * y⁻¹ ∈ V := by
    intro y hy
    have hy' : y ∈ Subgroup.closure ({a, x, s} : Set G) := hR'.le hy
    clear hy
    induction hy' using Subgroup.closure_induction with
    | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz <;> rw [hz]
      · rw [haj, mul_inv_cancel_right, mul_inv_cancel]
        exact V.one_mem
      · exact V.mul_mem (Subgroup.zpowers_le.mpr hxV hjx) (V.inv_mem hxV)
      · exact V.mul_mem (Subgroup.zpowers_le.mpr hsV hjs) (V.inv_mem hsV)
    | one => simp
    | mul y z hy _ ihy ihz =>
      have hyN := hRV (hR'.ge hy)
      have e : j * (y * z) * j⁻¹ * (y * z)⁻¹ =
          (j * y * j⁻¹ * y⁻¹) * (y * (j * z * j⁻¹ * z⁻¹) * y⁻¹) := by group
      rw [e]
      exact V.mul_mem ihy ((Subgroup.mem_normalizer_iff.mp hyN _).mp ihz)
    | inv y hy ihy =>
      have hyN := Subgroup.inv_mem _ (hRV (hR'.ge hy))
      have e : j * y⁻¹ * j⁻¹ * y⁻¹⁻¹ = y⁻¹ * (j * y * j⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hyN _).mp (V.inv_mem ihy)
  set K := Subgroup.closure {w | ∃ y ∈ R, w = j * y * j⁻¹ * y⁻¹} with hKdef
  have hKV : K ≤ V := by
    rw [hKdef, Subgroup.closure_le]
    rintro w ⟨y, hy, rfl⟩
    exact hQ y hy
  have hsK : j * s * j⁻¹ * s⁻¹ ∈ K := by
    rw [hKdef]
    exact Subgroup.subset_closure ⟨s, hsR, rfl⟩
  have hxK : j * x * j⁻¹ * x⁻¹ ∈ K := by
    rw [hKdef]
    exact Subgroup.subset_closure ⟨x, hxR, rfl⟩
  have hVK : V ≤ K := by
    rw [hVdef, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Subgroup.zpowers_le.mpr hsK hs', Subgroup.zpowers_le.mpr hxK hx'⟩
  have hgj : g * j * g⁻¹ = j := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hjg]
    group
  have hgK : g ∈ Subgroup.normalizer (K : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    have hw' : w ∈ Subgroup.closure {w | ∃ y ∈ R, w = j * y * j⁻¹ * y⁻¹} := hw
    clear hw
    induction hw' using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      have hgy : g * y * g⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp h.g_mem_normalizer y).mp hy
      have e : g * (j * y * j⁻¹ * y⁻¹) * g⁻¹ =
          j * (g * y * g⁻¹) * j⁻¹ * (g * y * g⁻¹)⁻¹ := by
        conv_rhs => rw [← hgj]
        group
      rw [e]
      exact Subgroup.subset_closure ⟨_, hgy, rfl⟩
    | one => simp
    | mul u v _ _ ihu ihv =>
      have e : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
      rw [e]
      exact K.mul_mem ihu ihv
    | inv u _ ihu =>
      have e : g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ := by group
      rw [e]
      exact K.inv_mem ihu
  rw [← le_antisymm hKV hVK]
  exact hgK

theorem item1125_of (h45 : Sec4.Item4_5) (h113 : Item113) : Item1125 := by
  rintro G _ _ A c L a R Y d x s r g h hcdN hNd hsc hrs ⟨j, ⟨⟨hjg, hja⟩, hjP⟩, hjinv⟩
  have hD := h.toSec11Data
  have hgV := hD.mem_normalizer_closure_of_inverts h45 h113 h.orderOf_x_gt hsc hrs hjg hja hjP
    hjinv
  have haR : a ∈ R := by
    rw [(hD.of_closure_eq hrs).R_eq]
    exact Subgroup.subset_closure (by simp)
  have hag : a * g = g * a :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)).symm
  exact rank3II_11_15_of (hD.of_closure_eq hrs) hag hD.commute_s_x (hD.R_le_normalizer_V h45) hgV
    (hD.normalizer_P_le_normalizer_V h45 h113) (hD.commutator_mem_V h45 h113 outAbelian1016 haR)
    hD.a_not_mem_V hcdN hNd (hD.htrans hcdN hNd)

end Data

end CFSG.RankThree.PartTwo.Sec11

module

public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2PCore
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Act
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open CFSG CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

variable {G : Type} [Group G]

theorem al1_conj_eq_one_iff_mem_center {Q : Type*} [Group Q] (x : Q) :
    MulAut.conj x = 1 ↔ x ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have hg := congrArg (fun φ : MulAut Q => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    exact (mul_inv_eq_iff_eq_mul.mp hg).symm
  · intro h
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, ← h g, mul_inv_cancel_right]

theorem al1_eq_one_of_mem_center_of_pow {Q : Type*} [Group Q] [Finite Q] {n : ℕ}
    (hcop : Nat.Coprime n (Nat.card (Subgroup.center Q))) {w : Q} (hw : w ∈ Subgroup.center Q)
    (hwn : w ^ n = 1) : w = 1 := by
  have hx : (⟨w, hw⟩ : Subgroup.center Q) ^ n = 1 := Subtype.ext (by simpa using hwn)
  have h1 : orderOf (⟨w, hw⟩ : Subgroup.center Q) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hx) (orderOf_dvd_natCard _)
  have h2 : (⟨w, hw⟩ : Subgroup.center Q) = 1 := orderOf_eq_one_iff.mp h1
  simpa using congrArg Subtype.val h2

theorem al1_exists_central_root {Q : Type*} [Group Q] [Finite Q] {n : ℕ}
    (hcop : Nat.Coprime n (Nat.card (Subgroup.center Q))) {v : Q} (hv : v ∈ Subgroup.center Q) :
    ∃ z ∈ Subgroup.center Q, z ^ n = v := by
  have hm0 : Nat.card (Subgroup.center Q) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop hm0
  have ht' : n * t ≡ 1 [MOD Nat.card (Subgroup.center Q)] := ht
  have hvm : orderOf v ∣ Nat.card (Subgroup.center Q) := Subgroup.orderOf_dvd_natCard _ hv
  have hmod : (t * n) % orderOf v = 1 % orderOf v := by
    rw [Nat.mul_comm]
    exact Nat.ModEq.of_dvd hvm ht'
  refine ⟨v ^ t, pow_mem hv t, ?_⟩
  calc (v ^ t) ^ n = v ^ (t * n) := by rw [← pow_mul]
    _ = v ^ ((t * n) % orderOf v) := (pow_mod_orderOf v (t * n)).symm
    _ = v ^ (1 % orderOf v) := by rw [hmod]
    _ = v ^ 1 := pow_mod_orderOf v 1
    _ = v := pow_one v

theorem al1_eq_of_conj_eq {Q : Type*} [Group Q] [Finite Q] {n : ℕ}
    (hcop : Nat.Coprime n (Nat.card (Subgroup.center Q))) {x y : Q}
    (hconj : MulAut.conj x = MulAut.conj y) (hx : x ^ n = 1) (hy : y ^ n = 1) : x = y := by
  have hw : x * y⁻¹ ∈ Subgroup.center Q := by
    rw [← al1_conj_eq_one_iff_mem_center, map_mul, map_inv, hconj, mul_inv_cancel]
  have hc : Commute (x * y⁻¹) y := (Subgroup.mem_center_iff.mp hw y).symm
  have h1 : x ^ n = (x * y⁻¹) ^ n * y ^ n := by
    rw [← hc.mul_pow, inv_mul_cancel_right]
  rw [hy, mul_one] at h1
  exact mul_inv_eq_one.mp (al1_eq_one_of_mem_center_of_pow hcop hw (h1.symm.trans hx))

theorem al1_conj_mul_eq {Q : Type*} [Group Q] (d : MulAut Q) (x : Q) :
    MulAut.conj (d x) * d = d * MulAut.conj x := by
  ext g
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

theorem exists_two_element_fixed {Q : Type*} [Group Q] [Finite Q]
    (hZ : Odd (Nat.card (Subgroup.center Q))) {q₀ : Q} {k : ℕ}
    (hk : (MulAut.conj q₀) ^ (2 ^ k) = 1) (D : Subgroup (MulAut Q))
    (hD : ∀ d ∈ D, d * MulAut.conj q₀ = MulAut.conj q₀ * d) :
    ∃ q : Q, MulAut.conj q = MulAut.conj q₀ ∧ (∃ j : ℕ, q ^ (2 ^ j) = 1) ∧ ∀ d ∈ D, d q = q := by
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Subgroup.center Q)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hZ)
  have hu : q₀ ^ (2 ^ k) ∈ Subgroup.center Q :=
    (al1_conj_eq_one_iff_mem_center _).mp (by rw [map_pow]; exact hk)
  obtain ⟨z, hz, hz2⟩ := al1_exists_central_root hcop (inv_mem hu)
  have hcomm : Commute q₀ z := Subgroup.mem_center_iff.mp hz q₀
  have hconjz : MulAut.conj z = 1 := (al1_conj_eq_one_iff_mem_center z).mpr hz
  have hq2 : (q₀ * z) ^ (2 ^ k) = 1 := by
    rw [hcomm.mul_pow, hz2, mul_inv_cancel]
  have hconjq : MulAut.conj (q₀ * z) = MulAut.conj q₀ := by
    rw [map_mul, hconjz, mul_one]
  refine ⟨q₀ * z, hconjq, ⟨k, hq2⟩, ?_⟩
  intro d hd
  have hconjdq : MulAut.conj (d (q₀ * z)) = MulAut.conj (q₀ * z) := by
    refine mul_right_cancel (b := d) ?_
    rw [al1_conj_mul_eq, hconjq]
    exact hD d hd
  have hdq2 : (d (q₀ * z)) ^ (2 ^ k) = 1 := by
    rw [← map_pow d (q₀ * z) (2 ^ k), hq2, map_one]
  exact al1_eq_of_conj_eq hcop hconjdq hdq2 hq2

theorem mem_pPrimeCoreOf_of_commutators {Q : Type*} [Group Q] [Finite Q] (C : Subgroup Q) {y : Q}
    (hyC : y ∈ C) (hy2 : ∃ j : ℕ, y ^ (2 ^ j) = 1)
    (h : ∀ c ∈ C, ⁅y, c⁆ ∈ pPrimeCoreOf 3 C) : y ∈ pPrimeCoreOf 3 C := by
  obtain ⟨j, hj⟩ := hy2
  set N : Subgroup Q := pPrimeCoreOf 3 C with hN_def
  have hNC : N ≤ C := pPrimeCoreOf_le_self 3 C
  have hzC : Subgroup.zpowers y ≤ C := Subgroup.zpowers_le.mpr hyC
  have hzN : Subgroup.zpowers y ≤ Subgroup.normalizer (N : Set Q) :=
    hzC.trans (le_normalizer_pPrimeCoreOf_gen 3 C)
  set H : Subgroup Q := Subgroup.zpowers y ⊔ N with hH_def
  have hyH : y ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hNH : N ≤ H := le_sup_right
  have hHC : H ≤ C := sup_le hzC hNC
  have hdec : ∀ w ∈ H, ∃ k : ℤ, ∃ n ∈ N, w = y ^ k * n := by
    intro w hw
    have hw' : w ∈ (↑(Subgroup.zpowers y ⊔ N) : Set Q) := hw
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzN] at hw'
    obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.mp hw'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ⟨k, n, hn, rfl⟩
  have hnormH : ∀ c ∈ C, ∀ w ∈ H, c * w * c⁻¹ ∈ H := by
    intro c hc w hw
    obtain ⟨k, n, hn, rfl⟩ := hdec w hw
    have hcN : c * n * c⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf_gen 3 C hc) n).mp hn
    have hcy : c * y * c⁻¹ ∈ H := by
      have hcomm : c * y * c⁻¹ = (⁅y, c⁆)⁻¹ * y := by
        rw [commutatorElement_def]; group
      rw [hcomm]
      exact H.mul_mem (H.inv_mem (hNH (h c hc))) hyH
    have heq : c * (y ^ k * n) * c⁻¹ = (c * y * c⁻¹) ^ k * (c * n * c⁻¹) := by
      rw [conj_zpow]; group
    rw [heq]
    exact H.mul_mem (H.zpow_mem hcy k) (hNH hcN)
  have hcop : Nat.Coprime 3 (Nat.card H) := by
    have hKn : (N.subgroupOf H).Normal := by
      refine ⟨fun n hn x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hxN := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pPrimeCoreOf_gen 3 C (hHC x.2)) (n : Q)).mp hn
      simpa using hxN
    haveI := hKn
    have hKc : Nat.card (N.subgroupOf H) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
    have hcopN : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 C
    obtain ⟨g, hg⟩ : ∃ g : H ⧸ N.subgroupOf H, g = QuotientGroup.mk ⟨y, hyH⟩ := ⟨_, rfl⟩
    have hgen : ∀ x : H ⧸ N.subgroupOf H, x ∈ Subgroup.zpowers g := by
      intro x
      obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨k, n, hn, hh⟩ := hdec (h' : Q) h'.2
      have hKmem : (⟨n, hNH hn⟩ : H) ∈ N.subgroupOf H := Subgroup.mem_subgroupOf.mpr hn
      have e1 : h' = (⟨y, hyH⟩ : H) ^ k * ⟨n, hNH hn⟩ := Subtype.ext (by simpa using hh)
      have hmk : (QuotientGroup.mk h' : H ⧸ N.subgroupOf H) = g ^ k := by
        rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
          (QuotientGroup.eq_one_iff (⟨n, hNH hn⟩ : H)).mpr hKmem, mul_one, hg]
      rw [hmk]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) k
    have hord : orderOf g = Nat.card (H ⧸ N.subgroupOf H) :=
      orderOf_eq_card_of_forall_mem_zpowers hgen
    have hg2 : g ^ (2 ^ j) = 1 := by
      have hyj : (⟨y, hyH⟩ : H) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj)
      rw [hg, ← QuotientGroup.mk_pow, hyj, QuotientGroup.mk_one]
    have hdvd : Nat.card (H ⧸ N.subgroupOf H) ∣ 2 ^ j := by
      rw [← hord]; exact orderOf_dvd_of_pow_eq_one hg2
    have h23 : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left j (by norm_num)
    have hquot : Nat.Coprime 3 (Nat.card (H ⧸ N.subgroupOf H)) :=
      (Nat.Coprime.coprime_dvd_left hdvd h23).symm
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H), hKc]
    exact Nat.Coprime.mul_right hquot hcopN
  have hle : H ≤ pPrimeCoreOf 3 C := le_pPrimeCoreOf_of_normalized hHC hnormH hcop
  exact hle hyH


theorem aux_mem_of_normalizer {S : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G))
    {y : G} (hy : y ∈ S) : g * y * g⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp hg y).mp hy

theorem aux_le_normalizer {B S : Subgroup G} (h : ∀ g ∈ B, ∀ y ∈ S, g * y * g⁻¹ ∈ S) :
    B ≤ Subgroup.normalizer (S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h g hg y hy, fun hy => ?_⟩
  have := h g⁻¹ (B.inv_mem hg) _ hy
  simpa [mul_assoc] using this

@[expose] def aux_smul {A N : Subgroup G} {y : G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ N)
    (a : A) (n : N) : N :=
  ⟨y⁻¹ * ((a : G) * (y * n) * (a : G)⁻¹), by
    have e : y⁻¹ * ((a : G) * (y * n) * (a : G)⁻¹) =
        (y⁻¹ * (a * y * (a : G)⁻¹)) * (a * n * (a : G)⁻¹) := by group
    rw [e]
    exact N.mul_mem (hy a a.2) (aux_mem_of_normalizer (hAN a.2) n.2)⟩

theorem aux_smul_coe {A N : Subgroup G} {y : G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ N)
    (a : A) (n : N) :
    ((aux_smul hAN hy a n : N) : G) = y⁻¹ * ((a : G) * (y * n) * (a : G)⁻¹) := rfl

@[expose, instance_reducible] def aux_cosetAction {A N : Subgroup G} {y : G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ N) :
    MulAction A N where
  smul := aux_smul hAN hy
  one_smul n := by
    apply Subtype.ext
    show ((aux_smul hAN hy 1 n : N) : G) = n
    rw [aux_smul_coe]
    simp
  mul_smul a b n := by
    apply Subtype.ext
    show ((aux_smul hAN hy (a * b) n : N) : G) =
      ((aux_smul hAN hy a (aux_smul hAN hy b n) : N) : G)
    rw [aux_smul_coe, aux_smul_coe, aux_smul_coe]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem aux_exists_fixed_mem_coset [Finite G] {p : ℕ} (hp : p.Prime) {A N : Subgroup G}
    (hA : IsPGroup p A) (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hN : ¬ p ∣ Nat.card N)
    {y : G} (hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ N) :
    ∃ n ∈ N, y * n ∈ Subgroup.centralizer (A : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  let _ : MulAction A N := aux_cosetAction hAN hy
  obtain ⟨n, hn⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card N hN
  refine ⟨n, n.2, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  have h := MulAction.mem_fixedPoints.mp hn ⟨a, ha⟩
  have h2 : y⁻¹ * (a * (y * n) * a⁻¹) = n :=
    congrArg Subtype.val (show aux_smul hAN hy ⟨a, ha⟩ n = n from h)
  have h3 : a * (y * n) * a⁻¹ = y * n := by
    calc a * (y * n) * a⁻¹ = y * (y⁻¹ * (a * (y * n) * a⁻¹)) := by group
      _ = y * n := by rw [h2]
  calc a * (y * n) = a * (y * n) * a⁻¹ * a := by group
    _ = y * n * a := by rw [h3]

theorem aux_pCore_mem {Y : Subgroup G} (σ : MulAut ↥Y) {x : ↥Y} (hx : x ∈ CFSG.pCore 2 ↥Y) :
    σ x ∈ CFSG.pCore 2 ↥Y := by
  have h : (CFSG.pCore 2 ↥Y).map (MulEquiv.toMonoidHom σ) = CFSG.pCore 2 ↥Y :=
    Subgroup.characteristic_iff_map_eq.1 (inferInstance : (CFSG.pCore 2 ↥Y).Characteristic) σ
  rw [← h]
  exact Subgroup.mem_map_of_mem _ hx

theorem aux_conj_pCore {Y : Subgroup G} {d : G} (hd : d ∈ Subgroup.normalizer (Y : Set G))
    {y : G} (hy : y ∈ (CFSG.pCore 2 ↥Y).map Y.subtype) :
    d * y * d⁻¹ ∈ (CFSG.pCore 2 ↥Y).map Y.subtype := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact Subgroup.mem_map.mpr ⟨Subgroup.normalizerMonoidHom Y ⟨d, hd⟩ x,
    aux_pCore_mem _ hx, rfl⟩

theorem aux_le_normalizer_pCore {Y D : Subgroup G} (hDY : D ≤ Subgroup.normalizer (Y : Set G)) :
    D ≤ Subgroup.normalizer (((CFSG.pCore 2 ↥Y).map Y.subtype : Subgroup G) : Set G) := by
  apply aux_le_normalizer
  intro g hg _ hy
  exact aux_conj_pCore (hDY hg) hy

theorem aux_mem_map_of_quot_eq {Y : Subgroup G} {u v : ↥Y}
    (h : (QuotientGroup.mk u : ↥Y ⧸ CFSG.pCore 2 ↥Y) = QuotientGroup.mk v) :
    (u : G)⁻¹ * (v : G) ∈ (CFSG.pCore 2 ↥Y).map Y.subtype :=
  Subgroup.mem_map_of_mem Y.subtype (QuotientGroup.eq.mp h)

theorem exists_mem_centralizer_of_fixed [Finite G] {Y D : Subgroup G}
    (hDY : D ≤ Subgroup.normalizer (Y : Set G)) (hD3 : IsPGroup 3 D)
    (ĉ : ↥Y ⧸ CFSG.pCore 2 ↥Y)
    (hfix : ∀ d : ↥(Subgroup.normalizer (Y : Set G)), (d : G) ∈ D → rho Y d ĉ = ĉ) :
    ∃ c : ↥Y, (c : G) ∈ Subgroup.centralizer (D : Set G) ∧ QuotientGroup.mk c = ĉ := by
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective ĉ
  have hN2 : IsPGroup 2 ((CFSG.pCore 2 ↥Y).map Y.subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map Y.subtype
  have hNcard : ¬ 3 ∣ Nat.card ((CFSG.pCore 2 ↥Y).map Y.subtype) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    rw [hk]
    intro h
    have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h2
  have hy : ∀ a ∈ D, (c₀ : G)⁻¹ * (a * (c₀ : G) * a⁻¹) ∈ (CFSG.pCore 2 ↥Y).map Y.subtype := by
    intro a ha
    have hfa := hfix ⟨a, hDY ha⟩ ha
    rw [rho_mk] at hfa
    exact aux_mem_map_of_quot_eq hfa.symm
  obtain ⟨n, hnN, hcent⟩ := aux_exists_fixed_mem_coset Nat.prime_three hD3
    (aux_le_normalizer_pCore hDY) hNcard hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hnN
  refine ⟨c₀ * x, hcent, ?_⟩
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff x).mpr hx, mul_one]

@[expose] noncomputable def fixQ (Y D : Subgroup G) : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
  FixedPoints.subgroup ((D.subgroupOf (Subgroup.normalizer (Y : Set G))).map (rho Y))
    (↥Y ⧸ CFSG.pCore 2 ↥Y)

theorem mem_fixQ_iff {Y D : Subgroup G} {ĉ : ↥Y ⧸ CFSG.pCore 2 ↥Y} :
    ĉ ∈ fixQ Y D ↔
      ∀ d : ↥(Subgroup.normalizer (Y : Set G)), (d : G) ∈ D → rho Y d ĉ = ĉ := by
  unfold fixQ
  rw [FixedPoints.mem_subgroup]
  constructor
  · intro h d hd
    exact h ⟨rho Y d, Subgroup.mem_map_of_mem (rho Y) (Subgroup.mem_subgroupOf.mpr hd)⟩
  · intro h m
    obtain ⟨d, hd, hdm⟩ := Subgroup.mem_map.mp m.2
    have hm : (m : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) = rho Y d := hdm.symm
    show (m : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) ĉ = ĉ
    rw [hm]
    exact h d (Subgroup.mem_subgroupOf.mp hd)


theorem mk_mem_pPrimeCoreOf_fixQ [Finite G] {Y D : Subgroup G}
    (hDY : D ≤ Subgroup.normalizer (Y : Set G)) (hD3 : IsPGroup 3 D) (r : ↥Y)
    (hr : (r : G) ∈ pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G))) :
    (QuotientGroup.mk r : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ pPrimeCoreOf 3 (fixQ Y D) := by
  obtain ⟨O, hO⟩ : ∃ O : Subgroup G, O = pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)) :=
    ⟨_, rfl⟩
  rw [← hO] at hr
  have hOC : O ≤ Subgroup.centralizer (D : Set G) := by
    rw [hO]
    exact pPrimeCoreOf_le_self 3 _
  have hOnorm : Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (O : Set G) := by
    rw [hO]
    exact le_normalizer_pPrimeCoreOf_gen 3 _
  have hOcop : Nat.Coprime 3 (Nat.card O) := by
    rw [hO]
    exact coprime_card_pPrimeCoreOf 3 _
  obtain ⟨R, hR⟩ : ∃ R : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y),
      R = (O.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) := ⟨_, rfl⟩
  have memR : ∀ z : ↥Y ⧸ CFSG.pCore 2 ↥Y, z ∈ R ↔
      ∃ w : ↥Y, (w : G) ∈ O ∧ (QuotientGroup.mk w : ↥Y ⧸ CFSG.pCore 2 ↥Y) = z := by
    intro z
    rw [hR]
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      exact ⟨w, Subgroup.mem_subgroupOf.mp hw, hwz⟩
    · rintro ⟨w, hw, rfl⟩
      exact Subgroup.mem_map.mpr ⟨w, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
  have hRle : R ≤ fixQ Y D := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (memR _).mp hz
    refine mem_fixQ_iff.mpr fun d hd => ?_
    have hc : (d : G) * (w : G) = (w : G) * (d : G) :=
      Subgroup.mem_centralizer_iff.mp (hOC hw) (d : G) hd
    rw [rho_mk]
    congr 1
    apply Subtype.ext
    show (d : G) * (w : G) * (d : G)⁻¹ = (w : G)
    rw [hc, mul_inv_cancel_right]
  have hnorm : ∀ c ∈ fixQ Y D, ∀ z ∈ R, c * z * c⁻¹ ∈ R := by
    intro c hc z hz
    obtain ⟨w, hw, rfl⟩ := (memR _).mp hz
    obtain ⟨c', hc'C, rfl⟩ := exists_mem_centralizer_of_fixed hDY hD3 c (mem_fixQ_iff.mp hc)
    have hconj : (c' : G) * (w : G) * (c' : G)⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hOnorm hc'C) (w : G)).mp hw
    refine (memR _).mpr ⟨c' * w * c'⁻¹, hconj, ?_⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hcop : Nat.Coprime 3 (Nat.card R) := by
    rw [hR]
    refine Nat.Coprime.coprime_dvd_right
      ((Subgroup.card_map_dvd (O.subgroupOf Y) (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).trans ?_) hOcop
    rw [← Subgroup.card_subtype Y (O.subgroupOf Y), Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hmem : (QuotientGroup.mk r : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ R := (memR _).mpr ⟨r, hr, rfl⟩
  exact le_pPrimeCoreOf_of_normalized hRle hnorm hcop hmem

theorem rho_eq_one_of_inner_local [Finite G] (hKF : KFactL3CentOdd) {f : ℕ} (hf : 1 ≤ f)
    {Y D : Subgroup G} {x : G} (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hε : IsLThreeEpsAt ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) 2 f)
    (hDY : D ≤ Subgroup.normalizer (Y : Set G)) (hD : CFSG.Assembly.IsElemAbelian 3 D)
    (hxY : x ∈ Subgroup.normalizer (Y : Set G)) (hx2 : ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (hxD : x ∈ pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)))
    (hin : rho Y ⟨x, hxY⟩ ∈ innQ Y) : rho Y ⟨x, hxY⟩ = 1 := by
  classical
  have hZ : Odd (Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))) := odd_card_center_quot Y
  obtain ⟨q₀, hq₀⟩ := hin
  obtain ⟨k, hk⟩ := hx2
  have hrk : (rho Y ⟨x, hxY⟩) ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨x, hxY⟩ : ↥(Subgroup.normalizer (Y : Set G))) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hxC : x ∈ Subgroup.centralizer (D : Set G) := pPrimeCoreOf_le_self 3 _ hxD
  have hD3 : IsPGroup 3 D := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hD.2 g g.2⟩
  set Dq : Subgroup (MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
    (D.subgroupOf (Subgroup.normalizer (Y : Set G))).map (rho Y) with hDq
  have hcomm : ∀ d ∈ Dq, d * MulAut.conj q₀ = MulAut.conj q₀ * d := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hq₀, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxC (d : G) (Subgroup.mem_subgroupOf.mp hd)
  obtain ⟨q, hqc, ⟨j, hj⟩, hfix⟩ :=
    exists_two_element_fixed hZ (q₀ := q₀) (k := k) (by rw [hq₀]; exact hrk) Dq hcomm
  have hqC : q ∈ fixQ Y D :=
    mem_fixQ_iff.mpr fun d hd => hfix _ ⟨d, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  have hcommut : ∀ ĉ ∈ fixQ Y D, ⁅q, ĉ⁆ ∈ pPrimeCoreOf 3 (fixQ Y D) := by
    intro ĉ hĉ
    obtain ⟨c, hcD, rfl⟩ := exists_mem_centralizer_of_fixed hDY hD3 ĉ (mem_fixQ_iff.mp hĉ)
    have hxcY : x * (c : G) * x⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hxY c).mp c.2
    have hrY : x * (c : G) * x⁻¹ * (c : G)⁻¹ ∈ Y := Y.mul_mem hxcY (Y.inv_mem c.2)
    have hrO : x * (c : G) * x⁻¹ * (c : G)⁻¹ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)) := by
      have h1 : (c : G) * x⁻¹ * (c : G)⁻¹ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)) :=
        (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pPrimeCoreOf_gen 3 (Subgroup.centralizer (D : Set G)) hcD) x⁻¹).mp
          (Subgroup.inv_mem _ hxD)
      have h2 := Subgroup.mul_mem _ hxD h1
      simpa [mul_assoc] using h2
    have hmk := mk_mem_pPrimeCoreOf_fixQ hDY hD3 ⟨_, hrY⟩ hrO
    have hcq : q * (QuotientGroup.mk c) * q⁻¹ = rho Y ⟨x, hxY⟩ (QuotientGroup.mk c) := by
      rw [← hq₀, ← hqc]
      rfl
    have : ⁅q, (QuotientGroup.mk c : ↥Y ⧸ CFSG.pCore 2 ↥Y)⁆ =
        (QuotientGroup.mk ⟨x * (c : G) * x⁻¹ * (c : G)⁻¹, hrY⟩ : ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
      rw [commutatorElement_def, hcq, rho_mk]
      rfl
    rw [this]
    exact hmk
  have hmem : q ∈ pPrimeCoreOf 3 (fixQ Y D) :=
    mem_pPrimeCoreOf_of_commutators (fixQ Y D) hqC ⟨j, hj⟩ hcommut
  have hDq_el : CFSG.Assembly.IsElemAbelian 3 Dq := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := a.2
      obtain ⟨b', hb', hb'e⟩ := b.2
      apply Subtype.ext
      show (a : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) * (b : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) =
        (b : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) * (a : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y))
      rw [← ha'e, ← hb'e, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      haveI := hD.1
      exact setLike_mul_comm (Subgroup.mem_subgroupOf.mp ha') (Subgroup.mem_subgroupOf.mp hb')
    · rintro _ ⟨d, hd, rfl⟩
      rw [← map_pow]
      have : d ^ 3 = 1 := Subtype.ext (hD.2 _ (Subgroup.mem_subgroupOf.mp hd))
      rw [this, map_one]
  have hodd := hKF (↥Y ⧸ CFSG.pCore 2 ↥Y) f hf hq hZ hε Dq hDq_el
  have hq1 : q = 1 := by
    have h1 : orderOf q ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    have h2 : orderOf q ∣ Nat.card ↥(pPrimeCoreOf 3 (fixQ Y D)) :=
      Subgroup.orderOf_dvd_natCard _ hmem
    have hcop : Nat.Coprime (2 ^ j) (Nat.card ↥(pPrimeCoreOf 3 (fixQ Y D))) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  rw [← hq₀, ← hqc, hq1, map_one]


end CFSG.RankThree.PartTwo.Sec15.F153L3C2

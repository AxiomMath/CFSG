module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.StandardType

namespace GGL48

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def commModSubgroup (K : Subgroup G) (y : G) : Subgroup G where
  carrier := {z | z ∈ normalizer (K : Set G) ∧ ⁅y, z⁆ ∈ K}
  mul_mem' := by
    rintro a b ⟨ha, hya⟩ ⟨hb, hyb⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact K.mul_mem hya ((mem_normalizer_iff.mp ha _).mp hyb)
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact K.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, hya⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : ⁅y, a⁻¹⁆ = a⁻¹ * ⁅y, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.mp (inv_mem ha) _).mp (K.inv_mem hya)

theorem mem_commModSubgroup {K : Subgroup G} {y z : G} :
    z ∈ commModSubgroup K y ↔ z ∈ normalizer (K : Set G) ∧ ⁅y, z⁆ ∈ K :=
  Iff.rfl

theorem commutatorElement_mem_of_mem_sup_sup {K : Subgroup G} {r g : G}
    (hr : r ∈ normalizer (K : Set G)) (hg : g ∈ normalizer (K : Set G)) (hrg : ⁅r, g⁆ ∈ K)
    {a b : G} (ha : a ∈ zpowers r ⊔ zpowers g ⊔ K) (hb : b ∈ zpowers r ⊔ zpowers g ⊔ K) :
    ⁅a, b⁆ ∈ K := by
  have hKN : K ≤ normalizer (K : Set G) := le_normalizer
  have key : ∀ y : G, y ∈ normalizer (K : Set G) → ⁅y, r⁆ ∈ K → ⁅y, g⁆ ∈ K →
      zpowers r ⊔ zpowers g ⊔ K ≤ commModSubgroup K y := by
    intro y hy hyr hyg
    refine sup_le (sup_le (zpowers_le.mpr ⟨hr, hyr⟩) (zpowers_le.mpr ⟨hg, hyg⟩)) fun k hk => ?_
    refine ⟨hKN hk, ?_⟩
    rw [commutatorElement_def]
    exact K.mul_mem ((mem_normalizer_iff.mp hy k).mp hk) (K.inv_mem hk)
  have hgr : ⁅g, r⁆ ∈ K := by
    rw [← commutatorElement_inv]
    exact K.inv_mem hrg
  have har : a ∈ commModSubgroup K r :=
    key r hr (by rw [commutatorElement_self]; exact K.one_mem) hrg ha
  have hag : a ∈ commModSubgroup K g :=
    key g hg hgr (by rw [commutatorElement_self]; exact K.one_mem) ha
  have h1 : ⁅a, r⁆ ∈ K := by
    rw [← commutatorElement_inv]
    exact K.inv_mem har.2
  have h2 : ⁅a, g⁆ ∈ K := by
    rw [← commutatorElement_inv]
    exact K.inv_mem hag.2
  exact (key a har.1 h1 h2 hb).2

theorem le_of_relIndex_le_prime [Finite G] {p : ℕ} [hp : Fact p.Prime] {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C) (hC : IsPGroup p C) (hind : A.relIndex C ≤ p)
    (hBA : ¬ B ≤ A) : C ≤ B := by
  have hmul := relIndex_mul_relIndex A B C hAB hBC
  obtain ⟨n, hn⟩ := (hC.to_le hBC).index (A.subgroupOf B)
  have hn' : A.relIndex B = p ^ n := hn
  have hne : A.relIndex B ≠ 1 := fun h => hBA (relIndex_eq_one.mp h)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (by rw [hn', pow_zero])
  have hpB : p ≤ A.relIndex B := by
    rw [hn']
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos (Nat.one_le_iff_ne_zero.mpr hn0)
  have hpos : 0 < B.relIndex C := Nat.pos_of_ne_zero FiniteIndex.index_ne_zero
  have h1 : B.relIndex C ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h2 : p * 2 ≤ A.relIndex B * B.relIndex C := Nat.mul_le_mul hpB hlt
    rw [hmul] at h2
    have hp2 := hp.out.two_le
    omega
  exact relIndex_eq_one.mp (le_antisymm h1 hpos)

theorem mem_zpowers_sup_of_not_mem {p : ℕ} [hp : Fact p.Prime] {K : Subgroup G} {g a b : G}
    (hg : g ∈ normalizer (K : Set G)) {k : ℕ} (hgk : g ^ p ^ k = 1)
    (ha : a ∈ zpowers g ⊔ K) (hb : b ∈ zpowers g ⊔ K) (haK : a ∉ K) (hbp : b ^ p ∈ K) :
    b ∈ zpowers a ⊔ K := by
  have : (K.subgroupOf (normalizer (K : Set G))).Normal := Subgroup.normal_in_normalizer
  have hzN : zpowers g ≤ normalizer (K : Set G) := zpowers_le.mpr hg
  have hMN : zpowers g ⊔ K ≤ normalizer (K : Set G) := sup_le hzN le_normalizer
  have hfin : IsOfFinOrder g :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ k, pow_pos hp.out.pos k, hgk⟩
  let π := QuotientGroup.mk' (K.subgroupOf (normalizer (K : Set G)))
  have hker : ∀ (c : G) (hc : c ∈ normalizer (K : Set G)), π ⟨c, hc⟩ = 1 ↔ c ∈ K :=
    fun c hc => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have himg : ∀ (c : G) (hc : c ∈ zpowers g ⊔ K), ∃ n : ℕ,
      π ⟨c, hMN hc⟩ = π ⟨g, hg⟩ ^ n := by
    intro c hc
    have hc' := hc
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hzN] at hc'
    obtain ⟨u, hu, w, hw, huw⟩ := hc'
    obtain ⟨n, rfl⟩ := hfin.mem_powers_iff_mem_zpowers.mpr hu
    refine ⟨n, ?_⟩
    have e : (⟨c, hMN hc⟩ : normalizer (K : Set G)) =
        (⟨g, hg⟩ : normalizer (K : Set G)) ^ n * ⟨w, le_normalizer hw⟩ :=
      Subtype.ext (by simp [← huw])
    rw [e, map_mul, map_pow, (hker w _).mpr hw, mul_one]
  obtain ⟨n, hn⟩ := himg a ha
  obtain ⟨m, hm⟩ := himg b hb
  have hgk' : π ⟨g, hg⟩ ^ p ^ k = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : normalizer (K : Set G)) ^ p ^ k = 1 := Subtype.ext (by simp [hgk])
    rw [this, map_one]
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hgk')
  have hna : ¬ orderOf (π ⟨g, hg⟩) ∣ n := fun h =>
    haK ((hker a _).mp (by rw [hn]; exact orderOf_dvd_iff_pow_eq_one.mp h))
  have hmp : orderOf (π ⟨g, hg⟩) ∣ m * p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, ← hm, ← map_pow]
    rw [show (⟨b, hMN hb⟩ : normalizer (K : Set G)) ^ p =
      ⟨b ^ p, pow_mem (hMN hb) p⟩ from Subtype.ext (by simp)]
    exact (hker _ _).mpr hbp
  rw [he] at hna hmp
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hna (by rw [pow_zero]; exact one_dvd n)
  obtain ⟨α, hα, hαe⟩ := (Nat.dvd_prime_pow hp.out).mp (Nat.gcd_dvd_right n (p ^ e))
  obtain ⟨β, -, hβe⟩ := (Nat.dvd_prime_pow hp.out).mp (Nat.gcd_dvd_right m (p ^ e))
  have hαlt : α < e := by
    rcases Nat.lt_or_ge α e with h | h
    · exact h
    · exfalso
      apply hna
      rw [← le_antisymm hα h, ← hαe]
      exact Nat.gcd_dvd_left n _
  have hm1 : p ^ (e - 1) ∣ m := by
    have h1 : p ^ (e - 1) * p ∣ m * p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he0)]
      exact hmp
    exact Nat.dvd_of_mul_dvd_mul_right hp.out.pos h1
  have hβge : e - 1 ≤ β := by
    have h1 : p ^ (e - 1) ∣ Nat.gcd m (p ^ e) :=
      Nat.dvd_gcd hm1 (Nat.pow_dvd_pow p (Nat.sub_le e 1))
    rw [hβe] at h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h1
  have hdvd : Nat.gcd n (p ^ e) ∣ Nat.gcd m (p ^ e) := by
    rw [hαe, hβe]
    exact Nat.pow_dvd_pow p (by omega)
  have hle : zpowers (π ⟨g, hg⟩ ^ (m : ℤ)) ≤ zpowers (π ⟨g, hg⟩ ^ (n : ℤ)) := by
    rw [Subgroup.zpowers_le_zpowers_iff, he, Int.gcd_natCast_natCast, Int.gcd_natCast_natCast]
    exact hdvd
  have hbmem : π ⟨b, hMN hb⟩ ∈ zpowers (π ⟨a, hMN ha⟩) := by
    rw [hm, hn, ← zpow_natCast, ← zpow_natCast]
    exact hle (mem_zpowers _)
  obtain ⟨t, ht⟩ := mem_zpowers_iff.mp hbmem
  have hc : (a ^ t)⁻¹ * b ∈ normalizer (K : Set G) :=
    mul_mem (inv_mem (zpow_mem (hMN ha) t)) (hMN hb)
  have hmem : (a ^ t)⁻¹ * b ∈ K := by
    have h1 : π (((⟨a, hMN ha⟩ : normalizer (K : Set G)) ^ t)⁻¹ * ⟨b, hMN hb⟩) = 1 := by
      rw [map_mul, map_inv, map_zpow, ht, inv_mul_cancel]
    rw [show ((⟨a, hMN ha⟩ : normalizer (K : Set G)) ^ t)⁻¹ * ⟨b, hMN hb⟩ =
      ⟨(a ^ t)⁻¹ * b, hc⟩ from Subtype.ext (by simp)] at h1
    exact (hker _ _).mp h1
  have e : b = a ^ t * ((a ^ t)⁻¹ * b) := by group
  rw [e]
  exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers a) t)) (mem_sup_right hmem)

theorem mem_centralizer_of_coprime {p : ℕ} [hp : Fact p.Prime] {U₁ B₁ : Subgroup G}
    (hab : IsMulCommutative U₁) (hU₁p : ∀ u ∈ U₁, ∃ k : ℕ, u ^ p ^ k = 1)
    (hB₁ : ∀ u : G, u ∈ B₁ ↔ u ∈ U₁ ∧ u ^ p = 1) {d : G}
    (hdN : d ∈ normalizer (U₁ : Set G)) (hdB : d ∈ centralizer (B₁ : Set G)) {m : ℕ}
    (hm : ¬ p ∣ m) (hdm : d ^ m = 1) : d ∈ centralizer (U₁ : Set G) := by
  have hcomm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hfix : ∀ b ∈ B₁, d * b * d⁻¹ = b := fun b hb => by
    have h := mem_centralizer_iff.mp hdB b hb
    rw [← h]
    group
  have hcop : Nat.Coprime m p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)
  have key : ∀ k : ℕ, ∀ u ∈ U₁, u ^ p ^ k = 1 → d * u * d⁻¹ = u := by
    intro k
    induction k with
    | zero =>
      intro u _ hu
      rw [pow_zero, pow_one] at hu
      rw [hu]
      group
    | succ k ih =>
      intro u hu hupk
      have hw : d * u ^ p * d⁻¹ = u ^ p :=
        ih _ (U₁.pow_mem hu p) (by rw [← pow_mul, ← pow_succ']; exact hupk)
      have hu'U : d * u * d⁻¹ ∈ U₁ := (mem_normalizer_iff.mp hdN u).mp hu
      have hvU : d * u * d⁻¹ * u⁻¹ ∈ U₁ := U₁.mul_mem hu'U (U₁.inv_mem hu)
      have hvp : (d * u * d⁻¹ * u⁻¹) ^ p = 1 := by
        have hc : Commute (d * u * d⁻¹) u⁻¹ := hcomm _ hu'U _ (U₁.inv_mem hu)
        rw [hc.mul_pow, conj_pow, hw, inv_pow, mul_inv_cancel]
      have hdv : d * (d * u * d⁻¹ * u⁻¹) * d⁻¹ = d * u * d⁻¹ * u⁻¹ :=
        hfix _ ((hB₁ _).mpr ⟨hvU, hvp⟩)
      have hiter : ∀ j : ℕ, d ^ j * u * (d ^ j)⁻¹ = (d * u * d⁻¹ * u⁻¹) ^ j * u := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          calc d ^ (j + 1) * u * (d ^ (j + 1))⁻¹ = d * (d ^ j * u * (d ^ j)⁻¹) * d⁻¹ := by
                rw [pow_succ']
                group
            _ = d * ((d * u * d⁻¹ * u⁻¹) ^ j * u) * d⁻¹ := by rw [ihj]
            _ = (d * (d * u * d⁻¹ * u⁻¹) * d⁻¹) ^ j * (d * u * d⁻¹) := by
                rw [conj_pow]
                group
            _ = (d * u * d⁻¹ * u⁻¹) ^ (j + 1) * u := by
                rw [hdv, pow_succ]
                group
      have hvm : (d * u * d⁻¹ * u⁻¹) ^ m = 1 := by
        have h := hiter m
        rw [hdm, one_mul, inv_one, mul_one] at h
        calc (d * u * d⁻¹ * u⁻¹) ^ m = (d * u * d⁻¹ * u⁻¹) ^ m * u * u⁻¹ :=
              (mul_inv_cancel_right _ u).symm
          _ = u * u⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel u
      have hv1 : d * u * d⁻¹ * u⁻¹ = 1 := by
        have h := pow_gcd_eq_one.mpr ⟨hvm, hvp⟩
        rwa [hcop.gcd_eq_one, pow_one] at h
      calc d * u * d⁻¹ = (d * u * d⁻¹ * u⁻¹) * u := by group
        _ = u := by rw [hv1, one_mul]
  rw [mem_centralizer_iff]
  intro u hu
  obtain ⟨k, hk⟩ := hU₁p u hu
  have h := key k u hu hk
  calc u * d = (d * u * d⁻¹) * d := by rw [h]
    _ = d * u := by group

theorem forall_commutatorElement_mem_of_relIndex_prime {p : ℕ} [hp : Fact p.Prime]
    {N K C Y : Subgroup G} (hCN : N ≤ normalizer (C : Set G)) (hYN : N ≤ normalizer (Y : Set G))
    (hKN : K ≤ N) (hind : K.relIndex N = p) (hnorm : ¬ (K.subgroupOf N).Normal)
    (hK : ∀ k ∈ K, ∀ y ∈ Y, ⁅k, y⁆ ∈ C) : ∀ n ∈ N, ∀ y ∈ Y, ⁅n, y⁆ ∈ C := by
  have hYconj : ∀ n ∈ N, ∀ y ∈ Y, n⁻¹ * y * n ∈ Y := fun n hn y hy => by
    have := (mem_normalizer_iff.mp (hYN (N.inv_mem hn)) y).mp hy
    simpa using this
  let Ker : Subgroup G :=
    { carrier := {n | n ∈ N ∧ ∀ y ∈ Y, ⁅n, y⁆ ∈ C}
      mul_mem' := by
        rintro a b ⟨ha, hay⟩ ⟨hb, hby⟩
        refine ⟨N.mul_mem ha hb, fun y hy => ?_⟩
        have e : ⁅a * b, y⁆ = (a * ⁅b, y⁆ * a⁻¹) * ⁅a, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact C.mul_mem ((mem_normalizer_iff.mp (hCN ha) _).mp (hby y hy)) (hay y hy)
      one_mem' := ⟨N.one_mem, fun y _ => by rw [commutatorElement_one_left]; exact C.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, hay⟩
        refine ⟨N.inv_mem ha, fun y hy => ?_⟩
        have e : ⁅a⁻¹, y⁆ = ⁅a, a⁻¹ * y * a⁆⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact C.inv_mem (hay _ (hYconj a ha y hy)) }
  have hKerN : Ker ≤ N := fun n hn => hn.1
  have hKK : K ≤ Ker := fun k hk => ⟨hKN hk, hK k hk⟩
  have hKern : (Ker.subgroupOf N).Normal := ⟨fun a ha g => by
    rw [mem_subgroupOf] at ha ⊢
    obtain ⟨-, hay⟩ := ha
    refine ⟨N.mul_mem (N.mul_mem g.2 a.2) (N.inv_mem g.2), fun y hy => ?_⟩
    have e : ⁅(g : G) * a * (g : G)⁻¹, y⁆ =
        (g : G) * ⁅(a : G), (g : G)⁻¹ * y * g⁆ * (g : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    simp only [coe_mul, coe_inv]
    rw [e]
    exact (mem_normalizer_iff.mp (hCN g.2) _).mp (hay _ (hYconj g g.2 y hy))⟩
  have hmul := relIndex_mul_relIndex K Ker N hKK hKerN
  rw [hind] at hmul
  rcases hp.out.eq_one_or_self_of_dvd (Ker.relIndex N) (Dvd.intro_left _ hmul) with h1 | h1
  · intro n hn y hy
    exact (relIndex_eq_one.mp h1 hn).2 y hy
  · exfalso
    rw [h1] at hmul
    have h2 : K.relIndex Ker = 1 :=
      Nat.eq_of_mul_eq_mul_right hp.out.pos (hmul.trans (one_mul p).symm)
    have heq : Ker = K := le_antisymm (relIndex_eq_one.mp h2) hKK
    rw [heq] at hKern
    exact hnorm hKern

end GGL48

end CFSG.StandardType

end

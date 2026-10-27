module

public import CFSG.RankThree.PartOne.K1214.OmegaAlg
public import CFSG.RankThree.PartOne.KF.F128Cyclic
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG.RankThree.PartOne

variable {G : Type*} [Group G]

theorem conj_pow_eq_of_conj_eq {x g : G} {s : ℕ} (h : x * g * x⁻¹ = g ^ s) (n : ℕ) :
    x ^ n * g * (x ^ n)⁻¹ = g ^ (s ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x ^ (n + 1) * g * (x ^ (n + 1))⁻¹ = x * (x ^ n * g * (x ^ n)⁻¹) * x⁻¹ := by
          rw [pow_succ']; group
      _ = x * g ^ (s ^ n) * x⁻¹ := by rw [ih]
      _ = (x * g * x⁻¹) ^ (s ^ n) := (conj_pow).symm
      _ = (g ^ s) ^ (s ^ n) := by rw [h]
      _ = g ^ (s ^ (n + 1)) := by rw [← pow_mul, mul_comm, ← pow_succ]

theorem dvd_sub_one_of_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) {u : ℤ} (h : (p : ℤ) ∣ u ^ p - 1) :
    (p : ℤ) ∣ u - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hferm : (p : ℤ) ∣ u ^ p - u := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card]
    ring
  have := dvd_sub hferm h
  have e : u ^ p - u - (u ^ p - 1) = -(u - 1) := by ring
  rw [e] at this
  exact (dvd_neg).mp this


theorem isCyclic_of_pow_eq_one_subset [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hG : IsPGroup p G) {b : G} (hb : orderOf b = p)
    (h : ∀ g : G, g ^ p = 1 → g ∈ Subgroup.zpowers b) : IsCyclic G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgmax⟩ := Finite.exists_max (fun x : G => orderOf x)
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨g, ?_⟩
  by_contra hne
  have := hG.isNilpotent
  have hlt : Subgroup.zpowers g < Subgroup.normalizer (Subgroup.zpowers g) :=
    Group.normalizerCondition_of_isNilpotent (Subgroup.zpowers g) (lt_top_iff_ne_top.2 hne)
  obtain ⟨y, hyN, hyg⟩ := IsConcreteLE.exists_of_lt hlt
  have hexs : ∃ t : ℕ, y ^ (p ^ t) ∈ Subgroup.zpowers g := by
    obtain ⟨m, hm⟩ := hG y
    exact ⟨m, by rw [hm]; exact Subgroup.one_mem _⟩
  have htmem : y ^ (p ^ Nat.find hexs) ∈ Subgroup.zpowers g := Nat.find_spec hexs
  have ht0 : Nat.find hexs ≠ 0 := by
    intro h0
    apply hyg
    have := htmem
    rwa [h0, pow_zero, pow_one] at this
  obtain ⟨t', ht'⟩ := Nat.exists_eq_succ_of_ne_zero ht0
  have hxg : y ^ (p ^ t') ∉ Subgroup.zpowers g := Nat.find_min hexs (by omega)
  have hxN : y ^ (p ^ t') ∈ Subgroup.normalizer (Subgroup.zpowers g) := Subgroup.pow_mem _ hyN _
  have hxp : (y ^ (p ^ t')) ^ p ∈ Subgroup.zpowers g := by
    have : (y ^ (p ^ t')) ^ p = y ^ (p ^ Nat.find hexs) := by
      rw [← pow_mul, ht', pow_succ]
    rw [this]
    exact htmem
  generalize y ^ (p ^ t') = x at hxg hxN hxp
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hG) g
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    have hbm : orderOf b ≤ orderOf g := hgmax b
    rw [hb, hk, hk0] at hbm
    have : p ≤ 1 := by simpa using hbm
    have := hp.one_lt
    omega
  obtain ⟨s, hs⟩ : ∃ s : ℕ, x * g * x⁻¹ = g ^ s := by
    have h1 : x * g * x⁻¹ ∈ Subgroup.zpowers g :=
      (Subgroup.mem_normalizer_iff.1 hxN g).1 (Subgroup.mem_zpowers g)
    obtain ⟨s, hs⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 h1)
    exact ⟨s, hs.symm⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, x ^ p = g ^ a := by
    obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hxp)
    exact ⟨a, ha.symm⟩
  have hgs : g ^ (s ^ p) = g := by
    have h1 := conj_pow_eq_of_conj_eq hs p
    have h2 : x ^ p * g * (x ^ p)⁻¹ = g := by rw [ha]; group
    exact h1.symm.trans h2
  have hmod : s ^ p ≡ 1 [MOD orderOf g] := by
    have : g ^ (s ^ p) = g ^ 1 := by rw [pow_one]; exact hgs
    exact pow_eq_pow_iff_modEq.1 this
  have hdvd1 : (p : ℤ) ^ k ∣ (s : ℤ) ^ p - 1 := by
    have := Nat.modEq_iff_dvd.1 hmod.symm
    rw [hk] at this
    push_cast at this
    exact this
  have hlte := pow_dvd_mul_sub_one_of_dvd_pow_sub_one hp hp2 hdvd1
  have hps : (p : ℤ) ∣ (s : ℤ) - 1 :=
    dvd_sub_one_of_dvd_pow_sub_one hp ((dvd_pow_self _ (by omega : k ≠ 0)).trans hdvd1)
  have hdp : (g ^ ((s : ℤ) - 1)) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    apply orderOf_dvd_iff_zpow_eq_one.1
    rw [hk]
    push_cast
    rw [mul_comm]
    exact hlte
  have hdb : g ^ ((s : ℤ) - 1) ∈ Subgroup.zpowers b := h _ hdp
  have hbg : b ∈ Subgroup.zpowers g := by
    have hb' : (g ^ (p ^ (k - 1))) ^ p = 1 := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hk1, ← hk]
      exact pow_orderOf_eq_one g
    have hmem := h _ hb'
    have hne1 : g ^ (p ^ (k - 1)) ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf
      · exact (pow_pos hp.pos _).ne'
      · rw [hk]
        exact Nat.pow_lt_pow_right hp.one_lt (by omega)
    have heq := Torsion37.zpowers_eq_of_mem_of_ne_one hp hb hmem hne1
    have : b ∈ Subgroup.zpowers (g ^ (p ^ (k - 1))) := by
      rw [heq]
      exact Subgroup.mem_zpowers b
    exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _) this
  have hxb : x * b * x⁻¹ = b := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hbg
    have e1 : (g ^ s) ^ j = g ^ ((s : ℤ) * j) := by rw [← zpow_natCast, ← zpow_mul]
    have e2 : (g ^ j) ^ s = g ^ (j * (s : ℤ)) := by rw [← zpow_natCast, ← zpow_mul]
    have h1 : x * b * x⁻¹ = b ^ s := by
      rw [← hj, ← conj_zpow, hs, e1, e2, mul_comm]
    have h2 : b ^ s = b := by
      have h3 : b ^ ((s : ℤ) - 1) = 1 :=
        orderOf_dvd_iff_zpow_eq_one.1 (by rw [hb]; exact hps)
      rw [zpow_sub_one, zpow_natCast, mul_inv_eq_one] at h3
      exact h3
    rw [h1, h2]
  have hxbc : Commute x b := by
    show x * b = b * x
    calc x * b = (x * b * x⁻¹) * x := by group
      _ = b * x := by rw [hxb]
  by_cases hpa : p ∣ a
  ·
    obtain ⟨a', rfl⟩ := hpa
    have hF1 : x * g ^ (-(a' : ℤ)) * x⁻¹ = (g ^ s) ^ (-(a' : ℤ)) := by rw [← conj_zpow, hs]
    have hF2 : (g ^ s) ^ (-(a' : ℤ)) = g ^ (-((s : ℤ) * a')) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    have hδ : x * g ^ (-(a' : ℤ)) * x⁻¹ * (g ^ (-(a' : ℤ)))⁻¹ =
        (g ^ ((s : ℤ) - 1)) ^ (-(a' : ℤ)) := by
      rw [hF1, hF2, ← zpow_neg, ← zpow_add, ← zpow_mul]
      congr 1
      ring
    have hδb : (g ^ ((s : ℤ) - 1)) ^ (-(a' : ℤ)) ∈ Subgroup.zpowers b :=
      Subgroup.zpow_mem _ hdb _
    have hδp : ((g ^ ((s : ℤ) - 1)) ^ (-(a' : ℤ))) ^ p = 1 := by
      have := orderOf_dvd_of_mem_zpowers hδb
      rw [hb] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have hxδ : x * (g ^ ((s : ℤ) - 1)) ^ (-(a' : ℤ)) =
        (g ^ ((s : ℤ) - 1)) ^ (-(a' : ℤ)) * x := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hδb
      rw [← hi]
      exact (hxbc.zpow_right i).eq
    have hδq : (g ^ ((s : ℤ) - 1)) ^ (-(a' : ℤ)) * g ^ (-(a' : ℤ)) =
        g ^ (-(a' : ℤ)) * (g ^ ((s : ℤ) - 1)) ^ (-(a' : ℤ)) := by
      rw [← zpow_mul]
      exact (Commute.zpow_zpow_self g _ _).eq
    have hpow := mul_pow_of_comm_data hp hp2 hδ hxδ hδq hδp
    have hxq : (x * g ^ (-(a' : ℤ))) ^ p = 1 := by
      rw [hpow, ha, ← zpow_natCast, ← zpow_mul, ← zpow_natCast g (p * a'), ← zpow_add]
      rw [← zpow_zero g]
      congr 1
      push_cast
      ring
    have hxq' := h _ hxq
    apply hxg
    have hxq'' : x * g ^ (-(a' : ℤ)) ∈ Subgroup.zpowers g :=
      Subgroup.zpowers_le.2 hbg hxq'
    have hqg : g ^ (-(a' : ℤ)) ∈ Subgroup.zpowers g :=
      Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _
    have := Subgroup.mul_mem _ hxq'' (Subgroup.inv_mem _ hqg)
    simpa using this
  ·
    have hcop : Nat.Coprime (orderOf g) a := by
      rw [hk]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa)
    have h1 : orderOf (x ^ p) = p ^ k := by rw [ha, Nat.Coprime.orderOf_pow hcop, hk]
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hG) x
    have h2 : orderOf (x ^ p) = orderOf x / Nat.gcd (orderOf x) p := orderOf_pow' x hp.ne_zero
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · have : orderOf x = 1 := by rw [hm, hm0, pow_zero]
      exact hxg (by rw [orderOf_eq_one_iff.1 this]; exact Subgroup.one_mem _)
    · have hg : Nat.gcd (p ^ m) p = p := Nat.gcd_eq_right (dvd_pow_self p hm0.ne')
      rw [hm, hg] at h2
      have h3 : p ^ k = p ^ (m - 1) := by
        rw [← h1, h2]
        conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
        exact Nat.mul_div_cancel _ hp.pos
      have h4 : k = m - 1 := Nat.pow_right_injective hp.two_le h3
      have h5 : orderOf x ≤ orderOf g := hgmax x
      rw [hm, hk] at h5
      have h6 : m ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 h5
      omega

theorem isCyclic_subgroup_of_pow_eq_one_subset {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Z : Subgroup G} [Finite Z] (hZ : IsPGroup p ↥Z) {b : G} (hbZ : b ∈ Z) (hb : orderOf b = p)
    (h : ∀ z ∈ Z, z ^ p = 1 → z ∈ Subgroup.zpowers b) : IsCyclic ↥Z := by
  refine isCyclic_of_pow_eq_one_subset hp hp2 hZ (b := (⟨b, hbZ⟩ : ↥Z))
    (by rw [← Subgroup.orderOf_coe]; exact hb) fun g hg => ?_
  have h1 : (g : G) ^ p = 1 := by simpa using congrArg Subtype.val hg
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (h _ g.2 h1)
  exact Subgroup.mem_zpowers_iff.2 ⟨i, Subtype.ext (by simpa using hi)⟩

end CFSG.RankThree.PartOne.K1214

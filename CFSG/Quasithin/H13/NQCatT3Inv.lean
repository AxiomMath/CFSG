module

public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_inv_of_perm {T : Subgroup G} (hT2 : IsPGroup 2 ↥T) {x : G} (hx3 : orderOf x = 3)
    (hperm : ∀ t ∈ T, ∀ y ∈ Subgroup.zpowers x, ∃ y' ∈ Subgroup.zpowers x, ∃ t' ∈ T,
      t * y = y' * t')
    (hN : x ∉ Subgroup.normalizer (T : Set G)) :
    ∃ t ∈ T, t * x * t⁻¹ = x⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Subgroup.zpowers x with hP
  set Y := P ⊔ T with hY
  have hYset : (Y : Set G) = (P : Set G) * (T : Set G) := by
    let M : Subgroup G :=
      { carrier := (P : Set G) * (T : Set G)
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
          obtain ⟨c', hc', b', hb', hbc⟩ := hperm b hb c hc
          refine ⟨a * c', P.mul_mem ha hc', b' * d, T.mul_mem hb' hd, ?_⟩
          calc a * c' * (b' * d) = a * (c' * b') * d := by group
            _ = a * (b * c) * d := by rw [hbc]
            _ = a * b * (c * d) := by group
        one_mem' := ⟨1, P.one_mem, 1, T.one_mem, mul_one 1⟩
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          obtain ⟨a', ha', b', hb', hab⟩ := hperm b⁻¹ (T.inv_mem hb) a⁻¹ (P.inv_mem ha)
          exact ⟨a', ha', b', hb', by rw [mul_inv_rev, hab]⟩ }
    refine le_antisymm ?_ ?_
    · have : Y ≤ M := sup_le (fun z hz => ⟨z, hz, 1, T.one_mem, mul_one z⟩)
        (fun z hz => ⟨1, P.one_mem, z, hz, one_mul z⟩)
      exact this
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mul_mem_sup ha hb
  by_contra hno
  push Not at hno
  let PY : Subgroup ↥Y := P.subgroupOf Y
  have hPY3 : Nat.card PY = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hP,
      Nat.card_zpowers, hx3]
  have hTY : T ≤ Y := le_sup_right
  have hcop : Nat.Coprime (Nat.card P) (Nat.card T) := by
    rw [hP, Nat.card_zpowers, hx3]
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hcard : Nat.card Y = 3 * Nat.card T := by
    have hd : P ⊓ T = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    let f : ↥P × ↥T → ↥Y := fun z => ⟨z.1 * z.2, Subgroup.mul_mem_sup z.1.2 z.2.2⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨a, b⟩ ⟨c, d⟩ hab
        have h1 : (a : G) * b = c * d := congrArg Subtype.val hab
        have h2 : (c : G)⁻¹ * a = d * (b : G)⁻¹ := by
          calc (c : G)⁻¹ * a = (c : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
            _ = (c : G)⁻¹ * (c * d) * (b : G)⁻¹ := by rw [h1]
            _ = d * (b : G)⁻¹ := by group
        have hmem : (c : G)⁻¹ * a ∈ P ⊓ T :=
          ⟨P.mul_mem (P.inv_mem c.2) a.2, h2 ▸ T.mul_mem d.2 (T.inv_mem b.2)⟩
        rw [hd, Subgroup.mem_bot] at hmem
        have hac : (a : G) = c := by
          calc (a : G) = c * ((c : G)⁻¹ * a) := by group
            _ = c := by rw [hmem, mul_one]
        have hbd : (b : G) = d := by
          rw [hac] at h1
          exact mul_left_cancel h1
        exact Prod.ext (Subtype.ext hac) (Subtype.ext hbd)
      · rintro ⟨z, hz⟩
        have hz' : z ∈ (Y : Set G) := hz
        rw [hYset] at hz'
        obtain ⟨a, ha, b, hb, rfl⟩ := hz'
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, hP, Nat.card_zpowers, hx3]
  have hPYi : ¬ 3 ∣ PY.index := by
    have h1 := Subgroup.card_mul_index PY
    rw [hPY3, hcard] at h1
    have h2 : PY.index = Nat.card T := by omega
    rw [h2]
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  let PS : Sylow 3 ↥Y := (IsPGroup.of_card (n := 1) (by rw [hPY3, pow_one]) :
    IsPGroup 3 PY).toSylow hPYi
  have hPS : (PS : Subgroup ↥Y) = PY := rfl
  have hNC : Subgroup.normalizer ((PS : Subgroup ↥Y) : Set ↥Y) ≤
      Subgroup.centralizer ((PS : Subgroup ↥Y) : Set ↥Y) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    rw [hPS, SetLike.mem_coe, Subgroup.mem_subgroupOf] at hp
    have hxP : (⟨x, Subgroup.mem_sup_left (Subgroup.mem_zpowers x)⟩ : ↥Y) ∈ PY :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x)
    have h1 := (Subgroup.mem_normalizer_iff.mp hn _).mp (hPS ▸ hxP)
    rw [hPS, Subgroup.mem_subgroupOf] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hk
    have hn' : (n : G) ∈ (Y : Set G) := n.2
    rw [hYset] at hn'
    obtain ⟨a, ha, t, ht, hat⟩ := hn'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hat' : x ^ i * t = n := hat
    have htx : t * x * t⁻¹ = x ^ k := by
      have : (n : G) * x * (n : G)⁻¹ = x ^ i * (t * x * t⁻¹) * (x ^ i)⁻¹ := by
        rw [← hat']; group
      rw [← hk] at this
      have h2 : t * x * t⁻¹ = (x ^ i)⁻¹ * x ^ k * x ^ i := by rw [this]; group
      rw [h2, ← zpow_neg, ← zpow_add, ← zpow_add]
      congr 1
      ring
    have hk3 : x ^ k = x ∨ x ^ k = x⁻¹ := by
      have hxk : x ^ k = x ^ (k % 3) := by
        have := (zpow_mod_orderOf x k).symm
        rwa [hx3, Nat.cast_ofNat] at this
      have hxo : orderOf (x ^ k) = 3 := by
        rw [hk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx3]
      have hm : 0 ≤ k % 3 ∧ k % 3 < 3 := ⟨Int.emod_nonneg _ (by norm_num),
        Int.emod_lt_of_pos _ (by norm_num)⟩
      rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
      · exfalso
        rw [hxk, h, zpow_zero, orderOf_one] at hxo
        omega
      · left; rw [hxk, h, zpow_one]
      · right
        rw [hxk, h]
        have : x ^ (2 : ℤ) * x = 1 := by
          rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, zpow_ofNat, ← hx3,
            pow_orderOf_eq_one]
        exact eq_inv_of_mul_eq_one_left this
    have hcomm : t * x = x * t := by
      rcases hk3 with h | h
      · rw [h] at htx
        calc t * x = t * x * t⁻¹ * t := by group
          _ = x * t := by rw [htx]
      · exact absurd (htx.trans h) (hno t ht)
    have hnx : (n : G) * x = x * n := by
      rw [← hat']
      have hc : x ^ i * x = x * x ^ i := (Commute.zpow_self x i).eq
      calc x ^ i * t * x = x ^ i * (t * x) := by group
        _ = x ^ i * (x * t) := by rw [hcomm]
        _ = (x ^ i * x) * t := by group
        _ = (x * x ^ i) * t := by rw [hc]
        _ = x * (x ^ i * t) := by group
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hp
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hj]
    exact (Commute.zpow_left (Commute.symm hnx) j).eq
  let K := (MonoidHom.transferSylow PS hNC).ker
  have hKc := MonoidHom.ker_transferSylow_isComplement' PS hNC
  have hKn : K.Normal := MonoidHom.normal_ker _
  have hKcard : Nat.card K * 3 = 3 * Nat.card T := by
    have h1 := hKc.card_mul_card
    have h3 : Nat.card ↥(PS : Subgroup ↥Y) = 3 := hPY3
    rw [h3, hcard] at h1
    exact h1
  have hK : Nat.card K = Nat.card T := by omega
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have hK2 : IsPGroup 2 K := IsPGroup.of_card (n := n) (by rw [hK, hn])
  let TY : Subgroup ↥Y := T.subgroupOf Y
  have hTY2 : IsPGroup 2 TY := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
  have hTYc : Nat.card TY = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv
  have hTYi : ¬ 2 ∣ TY.index := by
    have h1 := Subgroup.card_mul_index TY
    rw [hTYc, hcard] at h1
    have hpos : 0 < Nat.card T := Nat.card_pos
    have h3 : TY.index = 3 := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [h1]
      ring
    rw [h3]
    norm_num
  have hKT : K ≤ TY := hK2.le_sylow_of_normal (hTY2.toSylow hTYi)
  have hKeq : K = TY := Subgroup.eq_of_le_of_card_ge hKT (by rw [hTYc, hK])
  apply hN
  have hconj : ∀ t ∈ T, x * t * x⁻¹ ∈ T := by
    intro t ht
    have h1 : (⟨t, hTY ht⟩ : ↥Y) ∈ K := by
      rw [hKeq]
      exact Subgroup.mem_subgroupOf.mpr ht
    have h2 := hKn.conj_mem _ h1 ⟨x, Subgroup.mem_sup_left (Subgroup.mem_zpowers x)⟩
    rw [hKeq, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hle : T.map (MulAut.conj x).toMonoidHom ≤ T := by
    rintro _ ⟨t, ht, rfl⟩
    exact hconj t ht
  have heq : T.map (MulAut.conj x).toMonoidHom = T := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨hconj t, fun ht => ?_⟩
  rw [← heq] at ht
  obtain ⟨u, hu, hue⟩ := ht
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hue
  have : u = t := by simpa using hue
  rwa [← this]

end CFSG.Quasithin.H13.NQCat.T3

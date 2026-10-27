module

public import CFSG.Quasithin.Recognition.HSTypeFactM22
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Actions
public import CFSG.Quasithin.Recognition.M22WittData

public section

namespace CFSG.Quasithin.H13.KGM22

open MulAction CFSG.ComponentClassification.WittDesign
open scoped Pointwise

theorem exists_sylow_normalized {G : Type*} [Group G] [Finite G] {K : Subgroup G} [K.Normal]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P) {q : ℕ} [Fact q.Prime]
    (hmod : ¬ p ∣ Nat.card (Sylow q ↥K)) :
    ∃ Q : Sylow q ↥K,
      P ≤ Subgroup.normalizer (((Q : Subgroup ↥K).map K.subtype : Subgroup G) : Set G) := by
  let _ : MulAction ↥P (Sylow q ↥K) :=
    MulAction.compHom _ ((MulAut.conjNormal : G →* MulAut ↥K).comp P.subtype)
  obtain ⟨Q, hQ⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q ↥K) hmod
  refine ⟨Q, ?_⟩
  have hfwd : ∀ g ∈ P, ∀ z ∈ (Q : Subgroup ↥K).map K.subtype,
      g * z * g⁻¹ ∈ (Q : Subgroup ↥K).map K.subtype := by
    rintro g hg _ ⟨k, hk, rfl⟩
    have hfix : (MulAut.conjNormal g : MulAut ↥K) • Q = Q := hQ ⟨g, hg⟩
    have h1 : (MulAut.conjNormal g : MulAut ↥K) • k ∈
        (MulAut.conjNormal g : MulAut ↥K) • (Q : Subgroup ↥K) :=
      Subgroup.smul_mem_pointwise_smul k _ _ hk
    rw [← Sylow.pointwise_smul_def, hfix] at h1
    exact ⟨_, h1, by simp [MulAut.conjNormal_apply]⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hfwd g hg y hy, fun hy => ?_⟩
  have h := hfwd g⁻¹ (P.inv_mem hg) _ hy
  simpa [mul_assoc] using h

theorem factorization_pow_mul {q a m : ℕ} (hq : q.Prime) (hm : ¬ q ∣ m) :
    (q ^ a * m).factorization q = a := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero q)
  rw [Nat.factorization_mul (pow_ne_zero a hq.ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow hq, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem sylow_facts {G : Type*} [Group G] [Finite G] {q : ℕ} [hq : Fact q.Prime] {a m : ℕ}
    (hG : Nat.card G = q ^ a * m) (hm : ¬ q ∣ m) :
    (∀ Q : Sylow q G, Nat.card (Q : Subgroup G) = q ^ a) ∧ Nat.card (Sylow q G) ∣ m ∧
      Nat.card (Sylow q G) % q = 1 := by
  have hcard : ∀ Q : Sylow q G, Nat.card (Q : Subgroup G) = q ^ a := fun Q => by
    rw [Q.card_eq_multiplicity, hG, factorization_pow_mul hq.out hm]
  refine ⟨hcard, ?_, ?_⟩
  · let Q : Sylow q G := default
    have hidx : (Q : Subgroup G).index = m := by
      have h := Subgroup.card_mul_index (Q : Subgroup G)
      rw [hcard Q, hG] at h
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.out.pos a) h
    exact hidx ▸ Sylow.card_dvd_index Q
  · have h := card_sylow_modEq_one (p := q) (G := G)
    rw [Nat.ModEq, Nat.one_mod_eq_one.mpr hq.out.ne_one] at h
    exact h

theorem index_arith' : ∀ k : Fin 176, 99 ≤ (k : ℕ) → (k : ℕ) ∣ 443520 →
    (11 ∣ (k : ℕ) ∨ ∃ f ∈ Nat.divisors 55, (k : ℕ) % 11 = f % 11 ∧ 55 / f ∣ 443520 / k) →
    (7 ∣ (k : ℕ) ∨ ∃ f ∈ Nat.divisors 21, (k : ℕ) % 7 = f % 7 ∧ 21 / f ∣ 443520 / k) →
    (5 ∣ (k : ℕ) ∨ ∃ f ∈ Nat.divisors 20, (k : ℕ) % 5 = f % 5 ∧ 20 / f ∣ 443520 / k) →
    (k : ℕ) = 126 ∨ (k : ℕ) = 154 := by
  decide +kernel

theorem index_cond {p m n : ℕ} [Fact p.Prime] (hm : 443520 = p * m)
    (hpm : ¬ p ∣ m)
    (hn : ∀ x : M22, orderOf x = p →
      Nat.card (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) = n)
    (hn0 : n ≠ 0) (H : Subgroup M22) (hk : ¬ p ∣ H.index) :
    ∃ f ∈ Nat.divisors n, H.index % p = f % p ∧ n / f ∣ Nat.card H := by
  obtain ⟨x, -, hx, hmod⟩ := exists_sylow_le_of_not_dvd (p := p) hm hpm H hk
  set N := Subgroup.normalizer (Subgroup.zpowers x : Set M22)
  have hN := hn x hx
  have hmul := Subgroup.relIndex_mul_card H N
  rw [hN] at hmul
  refine ⟨H.relIndex N, Nat.mem_divisors.mpr ⟨⟨_, hmul.symm⟩, hn0⟩, hmod, ?_⟩
  have hpos : 0 < H.relIndex N := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_mul] at hmul
    exact hn0 hmul.symm
  rw [← hmul, Nat.mul_div_cancel_left _ hpos]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem index_mem'
    (H : Subgroup M22) (h99 : 99 ≤ H.index) (h176 : H.index < 176) :
    H.index = 126 ∨ H.index = 154 := by
  have hdvd : H.index ∣ 443520 := card_M22' ▸ H.index_dvd_card
  have hcard : Nat.card H = 443520 / H.index := by
    have := Subgroup.card_mul_index H
    rw [card_M22'] at this
    rw [← this, Nat.mul_div_cancel _ (by omega)]
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h11 : 11 ∣ H.index ∨ ∃ f ∈ Nat.divisors 55, H.index % 11 = f % 11 ∧
      55 / f ∣ 443520 / H.index := by
    by_cases h : 11 ∣ H.index
    · exact Or.inl h
    · exact Or.inr (hcard ▸ index_cond (m := 40320) (by norm_num) (by norm_num)
        (fun x hx => card_normalizer_of_orderOf_eleven hx) (by norm_num) H h)
  have h7 : 7 ∣ H.index ∨ ∃ f ∈ Nat.divisors 21, H.index % 7 = f % 7 ∧
      21 / f ∣ 443520 / H.index := by
    by_cases h : 7 ∣ H.index
    · exact Or.inl h
    · exact Or.inr (hcard ▸ index_cond (m := 63360) (by norm_num) (by norm_num)
        (fun x hx => card_normalizer_of_orderOf_seven hx) (by norm_num) H h)
  have h5 : 5 ∣ H.index ∨ ∃ f ∈ Nat.divisors 20, H.index % 5 = f % 5 ∧
      20 / f ∣ 443520 / H.index := by
    by_cases h : 5 ∣ H.index
    · exact Or.inl h
    · exact Or.inr (hcard ▸ index_cond (m := 88704) (by norm_num) (by norm_num)
        (fun x hx => card_normalizer_of_orderOf_five hx) (by norm_num) H h)
  exact index_arith' ⟨H.index, h176⟩ h99 hdvd h11 h7 h5

theorem exists_normalized_of_selfNormalizing {p : ℕ} [hp : Fact p.Prime] {H : Subgroup M22}
    {x : M22} (hxH : x ∈ H) (hx : orderOf x = p)
    (hNH : H ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set M22) = Subgroup.zpowers x)
    {m : ℕ} (hH : Nat.card H = p * m) (hpm : ¬ p ∣ m) {q a m' : ℕ} [hq : Fact q.Prime]
    (hm : m = q ^ a * m') (hqm : ¬ q ∣ m')
    (hcount : ∀ n ∈ Nat.divisors m', n % q = 1 → ¬ p ∣ n) :
    ∃ Q : Subgroup M22, Nat.card Q = q ^ a ∧
      x ∈ Subgroup.normalizer (Q : Set M22) := by
  set x' : ↥H := ⟨x, hxH⟩ with hx'
  have hox' : orderOf x' = p := by rw [← Subgroup.orderOf_coe]; exact hx
  set P₀ : Subgroup ↥H := Subgroup.zpowers x' with hP₀
  have hP₀card : Nat.card P₀ = p := by rw [hP₀, Nat.card_zpowers, hox']
  have hP₀p : IsPGroup p P₀ := IsPGroup.of_card (n := 1) (by rw [hP₀card, pow_one])
  have hP₀i : ¬ p ∣ P₀.index := by
    have h := Subgroup.card_mul_index P₀
    rw [hP₀card, hH] at h
    rw [Nat.eq_of_mul_eq_mul_left hp.out.pos h]
    exact hpm
  set P : Sylow p ↥H := hP₀p.toSylow hP₀i with hP
  have hPeq : (P : Subgroup ↥H) = P₀ := IsPGroup.toSylow_coe hP₀p hP₀i
  have hmap₀ : P₀.map H.subtype = Subgroup.zpowers x := by
    rw [hP₀, MonoidHom.map_zpowers]
    rfl
  have hNC : Subgroup.normalizer ((P : Subgroup ↥H) : Set ↥H) ≤
      Subgroup.centralizer ((P : Subgroup ↥H) : Set ↥H) := by
    intro g hg
    rw [hPeq] at hg ⊢
    have h1 : (g : M22) ∈ Subgroup.normalizer (Subgroup.zpowers x : Set M22) := by
      rw [← hmap₀]
      exact Subgroup.le_normalizer_map H.subtype ⟨g, hg, rfl⟩
    have h2 : (g : M22) ∈ Subgroup.zpowers x := hNH ▸ Subgroup.mem_inf.mpr ⟨g.2, h1⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
    have hg' : g = x' ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [hg']
    exact (Commute.zpow_zpow_self x' j k).eq
  set K : Subgroup ↥H := (MonoidHom.transferSylow P hNC).ker with hK
  have hKc := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hPcard : Nat.card (P : Subgroup ↥H) = p := by rw [hPeq]; exact hP₀card
  have hKcard : Nat.card K = m := by
    have h := hKc.card_mul_card
    rw [hPcard, hH] at h
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos (by rw [h, mul_comm])
  obtain ⟨hQcard, hndvd, hnmod⟩ := sylow_facts (G := ↥K) (q := q) (a := a) (m := m')
    (by rw [hKcard, hm]) hqm
  have hm'0 : m' ≠ 0 := fun h => hqm (h ▸ dvd_zero q)
  obtain ⟨Q, hQ⟩ := exists_sylow_normalized (K := K) (P := (P : Subgroup ↥H)) P.isPGroup'
    (q := q) (hcount _ (Nat.mem_divisors.mpr ⟨hndvd, hm'0⟩) hnmod)
  refine ⟨((Q : Subgroup ↥K).map K.subtype).map H.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.card_map_of_injective K.subtype_injective, hQcard Q]
  · have hx'P : x' ∈ (P : Subgroup ↥H) := by
      rw [hPeq]
      exact Subgroup.mem_zpowers x'
    exact Subgroup.le_normalizer_map H.subtype ⟨x', hQ hx'P, rfl⟩

theorem inf_normalizer_eq {H : Subgroup M22} {x : M22} (hxH : x ∈ H)
    (hcard : Nat.card ↥(H ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set M22)) = orderOf x) :
    H ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set M22) = Subgroup.zpowers x := by
  refine (Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, Nat.card_zpowers])).symm
  rw [Subgroup.zpowers_le]
  exact Subgroup.mem_inf.mpr ⟨hxH, Subgroup.le_normalizer (Subgroup.mem_zpowers x)⟩

theorem orderOf_dvd_twenty
    {Q : Subgroup M22} (hQ : Nat.card Q = 5) {x : M22}
    (hx : x ∈ Subgroup.normalizer (Q : Set M22)) : orderOf x ∣ 20 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Nontrivial ↥Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; norm_num)
  obtain ⟨w, hw⟩ := exists_ne (1 : ↥Q)
  have how : orderOf (w : M22) = 5 := by
    rw [Subgroup.orderOf_coe]
    have h := orderOf_dvd_natCard w
    rw [hQ] at h
    rcases (Nat.dvd_prime (by norm_num)).mp h with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hw
    · exact h1
  have hQw : Q = Subgroup.zpowers (w : M22) := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ (by rw [hQ, Nat.card_zpowers, how])).symm
    rw [Subgroup.zpowers_le]
    exact w.2
  rw [hQw] at hx
  have h := orderOf_dvd_natCard
    (⟨x, hx⟩ : Subgroup.normalizer (Subgroup.zpowers (w : M22) : Set M22))
  rwa [Subgroup.orderOf_mk, card_normalizer_of_orderOf_five how] at h

theorem index_ne_126
    (H : Subgroup M22) : H.index ≠ 126 := by
  intro h126
  have hH : Nat.card H = 3520 := by have := card_of_index h126; omega
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hxH, hx, hmod⟩ := exists_sylow_le_of_not_dvd (p := 11) (m := 40320) (by norm_num)
    (by norm_num) H (by rw [h126]; norm_num)
  have hN := card_normalizer_of_orderOf_eleven hx
  have hmul := Subgroup.relIndex_mul_card H (Subgroup.normalizer (Subgroup.zpowers x : Set M22))
  have hf := Subgroup.relIndex_dvd_card H (Subgroup.normalizer (Subgroup.zpowers x : Set M22))
  rw [hN] at hmul hf
  rw [Nat.ModEq, h126] at hmod
  have hf5 : H.relIndex (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) = 5 := by
    generalize H.relIndex (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) = f at hf hmod
    have := Nat.le_of_dvd (by norm_num) hf
    interval_cases f <;> simp_all
  rw [hf5] at hmul
  have hNH := inf_normalizer_eq hxH (by rw [hx]; omega)
  obtain ⟨Q, hQ, hxQ⟩ := exists_normalized_of_selfNormalizing (p := 11) (q := 5) (a := 1)
    (m' := 64) hxH hx hNH (m := 320) (by rw [hH]) (by norm_num) (by norm_num) (by norm_num)
    (by decide)
  have h := orderOf_dvd_twenty (by rw [hQ, pow_one]) hxQ
  rw [hx] at h
  norm_num at h

theorem index_ne_154
    (H : Subgroup M22) : H.index ≠ 154 := by
  intro h154
  have hH : Nat.card H = 2880 := by have := card_of_index h154; omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyH, hy, hmod⟩ := exists_sylow_le_of_not_dvd (p := 5) (m := 88704) (by norm_num)
    (by norm_num) H (by rw [h154]; norm_num)
  have hN := card_normalizer_of_orderOf_five hy
  have hmul := Subgroup.relIndex_mul_card H (Subgroup.normalizer (Subgroup.zpowers y : Set M22))
  have hf := Subgroup.relIndex_dvd_card H (Subgroup.normalizer (Subgroup.zpowers y : Set M22))
  rw [hN] at hmul hf
  rw [Nat.ModEq, h154] at hmod
  have hf4 : H.relIndex (Subgroup.normalizer (Subgroup.zpowers y : Set M22)) = 4 := by
    generalize H.relIndex (Subgroup.normalizer (Subgroup.zpowers y : Set M22)) = f at hf hmod
    have := Nat.le_of_dvd (by norm_num) hf
    interval_cases f <;> simp_all
  rw [hf4] at hmul
  have hNH := inf_normalizer_eq hyH (by rw [hy]; omega)
  obtain ⟨R, hR, hyR⟩ := exists_normalized_of_selfNormalizing (p := 5) (q := 3) (a := 2)
    (m' := 64) hyH hy hNH (m := 576) (by rw [hH]) (by norm_num) (by norm_num) (by norm_num)
    (by decide)
  classical
  have : Fintype ↥R := Fintype.ofFinite _
  let f : Function.End ↥R := fun r => ⟨y * r * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyR r).mp r.2⟩
  have hfpow : ∀ n : ℕ, ∀ r : ↥R, ((f ^ n) r : M22) = y ^ n * r * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro r
      rw [pow_zero, pow_zero, one_mul, inv_one, mul_one]
      rfl
    | succ n ih =>
      intro r
      rw [pow_succ']
      show y * ((f ^ n) r : M22) * y⁻¹ = _
      rw [ih r, pow_succ']
      group
  have hf5 : f ^ 5 ^ 1 = 1 := by
    funext r
    apply Subtype.ext
    rw [pow_one, hfpow 5 r, ← hy, pow_orderOf_eq_one, inv_one, one_mul, mul_one]
    rfl
  have hcong := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) hf5
  rw [← Nat.card_eq_fintype_card, hR] at hcong
  have hfix1 : (1 : ↥R) ∈ Function.fixedPoints f := by
    show f 1 = 1
    apply Subtype.ext
    show y * 1 * y⁻¹ = 1
    group
  have h2 : 1 < Fintype.card (Function.fixedPoints f) := by
    have h1 : 0 < Fintype.card (Function.fixedPoints f) :=
      Fintype.card_pos_iff.mpr ⟨⟨1, hfix1⟩⟩
    have : Fintype.card (Function.fixedPoints f) % 5 = 4 := by
      rw [Nat.ModEq] at hcong
      omega
    omega
  obtain ⟨⟨r, hr⟩, hr1⟩ := Fintype.exists_ne_of_one_lt_card h2 ⟨1, hfix1⟩
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hry : y * (r : M22) * y⁻¹ = r := congrArg Subtype.val hr
  have hrN : (r : M22) ∈ Subgroup.normalizer (Subgroup.zpowers y : Set M22) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hcomm : (r : M22) * y = y * r := by
      calc (r : M22) * y = y * r * y⁻¹ * y := by rw [hry]
        _ = y * r := by group
    constructor
    · intro hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have : (r : M22) * y ^ k * (r : M22)⁻¹ = y ^ k := by
        rw [(Commute.zpow_right hcomm k).eq, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.zpow_mem_zpowers y k
    · intro hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hc := (Commute.zpow_right hcomm k).eq
      have : z = y ^ k := by
        calc z = (r : M22)⁻¹ * ((r : M22) * z * (r : M22)⁻¹) * r := by group
          _ = (r : M22)⁻¹ * (y ^ k * r) := by rw [← hk, mul_assoc]
          _ = y ^ k := by rw [← hc, inv_mul_cancel_left]
      rw [this]
      exact Subgroup.zpow_mem_zpowers y k
  have h20 : orderOf (r : M22) ∣ 20 := by
    have h := orderOf_dvd_natCard (⟨r, hrN⟩ : Subgroup.normalizer (Subgroup.zpowers y : Set M22))
    rwa [Subgroup.orderOf_mk, hN] at h
  have h9 : orderOf (r : M22) ∣ 9 := by
    have h := orderOf_dvd_natCard r
    rw [hR] at h
    rwa [← Subgroup.orderOf_coe] at h
  have h1 : orderOf (r : M22) = 1 := Nat.dvd_one.mp (by
    have := Nat.dvd_gcd h20 h9
    rwa [show Nat.gcd 20 9 = 1 by norm_num] at this)
  exact hr1' (Subtype.ext (orderOf_eq_one_iff.mp h1))

theorem factM22SubgroupIndex_holds :
    CFSG.Quasithin.HSType.FactM22SubgroupIndex := by
  intro W hW
  obtain ⟨-, -, -, -, ⟨hpt, hhex, -, -, hc22, hc77, hlow⟩, -⟩ := m22_point_hexad_actions
  by_cases htop : W = ⊤
  · exact Or.inl htop
  rcases Nat.lt_or_ge W.index 99 with h99 | h99
  · rcases hlow W htop h99 with h | h
    · exact Or.inr (Or.inl (hc22 _ W (hpt 0) h))
    · have hidx : CFSG.Quasithin.Asc94.m22HexStab.index = 77 := by
        rw [← CFSG.Quasithin.M22Witt.stabilizer_m22HexadF]
        exact hhex _ CFSG.Quasithin.M22Witt.m22HexadF_mem_hexads
      exact Or.inr (Or.inr (hc77 _ W hidx h))
  · exfalso
    rcases index_mem' W h99 hW with h | h
    · exact index_ne_126 W h
    · exact index_ne_154 W h

end CFSG.Quasithin.H13.KGM22

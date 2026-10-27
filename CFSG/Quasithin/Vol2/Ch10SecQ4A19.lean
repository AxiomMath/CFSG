module

public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch10SecQ4A3
public import CFSG.Quasithin.Vol2.Ch10SecQ4A7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G : Type} [Group G] [Finite G] {K J X : Subgroup G}

omit [Finite G] in
theorem eq_one_of_pow_odd {P : Subgroup G} (hP : IsPGroup 2 P) {c : G} (hc : c ∈ P) {n : ℕ}
    (hn : Odd n) (hcn : c ^ n = 1) : c = 1 := by
  obtain ⟨e, he⟩ := hP ⟨c, hc⟩
  have he' : c ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have h1 := orderOf_dvd_of_pow_eq_one hcn
  have h2 := orderOf_dvd_of_pow_eq_one he'
  have hcop : Nat.Coprime (2 ^ e) n := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hn)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h1))

theorem exists_center_three (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) (hUQ : blockU K ≤ pCoreOf 2 J)
    (h5 : IsAltType K 5) (hJ : J ∈ cComp X)
    (hhat : IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)))
    (hZW : ∀ j : ↥J, (QuotientGroup.mk j : ↥J ⧸ CFSG.pCore 2 ↥J) ∈ Subgroup.center _ →
      (j : G) ∈ Subgroup.centralizer (conjClosure (blockU K) J : Set G)) :
    ∃ z ∈ J, z ∈ Subgroup.centralizer (J : Set G) ∧ orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPnorm : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  have hP2 : IsPGroup 2 (pCoreOf 2 J) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center
    (↥J ⧸ CFSG.pCore 2 ↥J))) 3 (by rw [hhat.2.1])
  obtain ⟨j₀, hj₀⟩ := QuotientGroup.mk_surjective (y : ↥J ⧸ CFSG.pCore 2 ↥J)
  set r := orderOf j₀ with hr
  have hr0 : r ≠ 0 := (orderOf_pos j₀).ne'
  set m := 2 ^ r.factorization 2 with hm
  have hmr : m ∣ r := Nat.ordProj_dvd r 2
  set j₁ := j₀ ^ m with hj₁
  have hj₁o : orderOf j₁ = r / m := orderOf_pow_of_dvd (by positivity) hmr
  have hodd : Odd (orderOf j₁) := by
    rw [hj₁o]
    exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hr0)
  have hj₁c : (QuotientGroup.mk j₁ : ↥J ⧸ CFSG.pCore 2 ↥J) ∈ Subgroup.center _ := by
    rw [hj₁, QuotientGroup.mk_pow, hj₀]
    exact Subgroup.pow_mem _ y.2 m
  have hj₁1 : (QuotientGroup.mk j₁ : ↥J ⧸ CFSG.pCore 2 ↥J) ≠ 1 := by
    rw [hj₁, QuotientGroup.mk_pow, hj₀]
    intro h
    have h' : y ^ m = 1 := Subtype.ext (by simpa using h)
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hy, hm] at this
    exact absurd (Nat.prime_three.dvd_of_dvd_pow this) (by norm_num)
  have hj₁W := hZW j₁ hj₁c
  set g : G := (j₁ : G) with hg
  have hgo : orderOf g = orderOf j₁ := Subgroup.orderOf_coe j₁
  have hgQ : ∀ q ∈ pCoreOf 2 J, g * q = q * g := by
    intro q hq
    set w := g * q * g⁻¹ * q⁻¹ with hw
    have hwW : w ∈ conjClosure (blockU K) J := commutator_mem_conjClosure hK hKJ hQK h5 hJ j₁.2 hq
    have hgw : w * g = g * w := Subgroup.mem_centralizer_iff.mp hj₁W w hwW
    have hpow : ∀ i : ℕ, g ^ i * q * (g ^ i)⁻¹ = w ^ i * q := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have hgw' : g * w ^ i * g⁻¹ = w ^ i := by
          rw [← (Commute.pow_left (show Commute w g from hgw) i).eq, mul_inv_cancel_right]
        calc g ^ (i + 1) * q * (g ^ (i + 1))⁻¹ = g * (g ^ i * q * (g ^ i)⁻¹) * g⁻¹ := by group
          _ = g * w ^ i * g⁻¹ * (g * q * g⁻¹) := by rw [ih]; group
          _ = w ^ (i + 1) * q := by rw [hgw', pow_succ, hw]; group
    have h1 := hpow (orderOf g)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, right_eq_mul] at h1
    have hw2 : w ^ 2 = 1 := (isElemAbelian_conjClosure hK hKJ hQK hUQ).2 w hwW
    have hwo : w ^ orderOf g = w := by
      obtain ⟨k, hk⟩ := (hgo ▸ hodd : Odd (orderOf g))
      rw [hk, pow_succ, pow_mul, hw2, one_pow, one_mul]
    rw [hwo, hw] at h1
    have h2 : g * q * g⁻¹ = q := mul_inv_eq_one.mp h1
    calc g * q = g * q * g⁻¹ * g := by group
      _ = q * g := by rw [h2]
  have hgc : ∀ x ∈ J, x * g = g * x := by
    intro x hx
    set c := x * g * x⁻¹ * g⁻¹ with hc
    have hcQ : c ∈ pCoreOf 2 J := by
      have hcomm := Subgroup.mem_center_iff.mp hj₁c (QuotientGroup.mk ⟨x, hx⟩)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
      have hd : (x * g)⁻¹ * (g * x) ∈ pCoreOf 2 J := mem_blockQ_of_mem_pCore hcomm
      have h' : c = (x * g) * ((x * g)⁻¹ * (g * x))⁻¹ * (x * g)⁻¹ := by rw [hc]; group
      rw [h']
      exact (Subgroup.mem_normalizer_iff.mp (hPnorm (J.mul_mem hx j₁.2)) _).mp
        ((pCoreOf 2 J).inv_mem hd)
    have hcg : g * c = c * g := hgQ c hcQ
    have hxg : x * g * x⁻¹ = c * g := by rw [hc]; group
    have hcn : c ^ orderOf g = 1 := by
      have h1 : (x * g * x⁻¹) ^ orderOf g = 1 := by
        rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
      rw [hxg, (Commute.mul_pow (Commute.symm hcg) _), pow_orderOf_eq_one, mul_one] at h1
      exact h1
    have hc1 := eq_one_of_pow_odd hP2 hcQ (hgo ▸ hodd) hcn
    rw [hc] at hc1
    have := mul_inv_eq_one.mp hc1
    calc x * g = x * g * x⁻¹ * x := by group
      _ = g * x := by rw [this]
  have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥J) j₁ =
      (y : ↥J ⧸ CFSG.pCore 2 ↥J) ^ m := by
    rw [hj₁, map_pow, QuotientGroup.mk'_apply, hj₀]
  have h3 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥J) j₁) = 3 := by
    refine orderOf_eq_prime ?_ (by rw [QuotientGroup.mk'_apply]; exact hj₁1)
    have hy3 : (y : ↥J ⧸ CFSG.pCore 2 ↥J) ^ 3 = 1 := by
      rw [← SubgroupClass.coe_pow, ← hy, pow_orderOf_eq_one, OneMemClass.coe_one]
    rw [hmk, ← pow_mul, mul_comm, pow_mul, hy3, one_pow]
  have h3g : 3 ∣ orderOf g := by
    rw [hgo, ← h3]
    exact orderOf_map_dvd _ _
  refine ⟨g ^ (orderOf g / 3), J.pow_mem j₁.2 _, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_,
    orderOf_pow_orderOf_div (orderOf_pos g).ne' h3g⟩
  exact (Commute.pow_right (hgc x hx) _).eq

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR
public import CFSG.GroupTheory.ConjNormalFaithful
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAutSylow
public import CFSG.GF2Type.Aschbacher1976Full.HSGL3Simple
public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicSylow
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbitsGroup
public import CFSG.RankThree.PartTwo.Sec13.K135G1Out

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
  (restrictAut coe_restrictAut_pow eq_top_of_forall_sylow_le eq_one_of_pow_seven_of_modEq
    isPGroup_zpowers_of_pow_seven)
open CFSG.HardMathSupport.Dickson.I271
  (fixedSubgroupOf mem_fixedSubgroupOf card_fixedSubgroupOf_modEq exists_fixed_orderOf_eq_prime)

namespace L2Small

theorem prime_pow_le_of_dvd_sixty {p k : ℕ} (hp : p.Prime) (hd : p ^ k ∣ 60) : p ^ k ≤ 5 := by
  have key : ∀ d ∈ Nat.divisors 60, d ≤ 5 ∨ (2 ∣ d ∧ 3 ∣ d) ∨ (2 ∣ d ∧ 5 ∣ d) ∨
      (3 ∣ d ∧ 5 ∣ d) := by decide
  rcases key _ (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · exact absurd ((Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hp h1).trans
      (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three hp h2).symm) (by norm_num)
  · exact absurd ((Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hp h1).trans
      (Nat.prime_eq_prime_of_dvd_pow (by norm_num) hp h2).symm) (by norm_num)
  · exact absurd ((Nat.prime_eq_prime_of_dvd_pow Nat.prime_three hp h1).trans
      (Nat.prime_eq_prime_of_dvd_pow (by norm_num) hp h2).symm) (by norm_num)

theorem prime_pow_le_of_dvd_168 {p k : ℕ} (hp : p.Prime) (hd : p ^ k ∣ 168) : p ^ k ≤ 8 := by
  have key : ∀ d ∈ Nat.divisors 168, d ≤ 8 ∨ (2 ∣ d ∧ 3 ∣ d) ∨ (2 ∣ d ∧ 7 ∣ d) ∨
      (3 ∣ d ∧ 7 ∣ d) := by decide
  rcases key _ (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · exact absurd ((Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hp h1).trans
      (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three hp h2).symm) (by norm_num)
  · exact absurd ((Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hp h1).trans
      (Nat.prime_eq_prime_of_dvd_pow (by norm_num) hp h2).symm) (by norm_num)
  · exact absurd ((Nat.prime_eq_prime_of_dvd_pow Nat.prime_three hp h1).trans
      (Nat.prime_eq_prime_of_dvd_pow (by norm_num) hp h2).symm) (by norm_num)

theorem prime_pow_le_of_dvd_360 {p k : ℕ} (hp : p.Prime) (hd : p ^ k ∣ 360) : p ^ k ≤ 9 := by
  have key : ∀ d ∈ Nat.divisors 360, d ≤ 9 ∨ (2 ∣ d ∧ 3 ∣ d) ∨ (2 ∣ d ∧ 5 ∣ d) ∨
      (3 ∣ d ∧ 5 ∣ d) := by decide
  rcases key _ (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · exact absurd ((Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hp h1).trans
      (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three hp h2).symm) (by norm_num)
  · exact absurd ((Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hp h1).trans
      (Nat.prime_eq_prime_of_dvd_pow (by norm_num) hp h2).symm) (by norm_num)
  · exact absurd ((Nat.prime_eq_prime_of_dvd_pow Nat.prime_three hp h1).trans
      (Nat.prime_eq_prime_of_dvd_pow (by norm_num) hp h2).symm) (by norm_num)

theorem mulAut_eq_one_of_prime_pow_lt {K : Type*} [Group K] [Finite K] {r : ℕ} (hr : r.Prime)
    (hlt : ∀ p k : ℕ, p.Prime → p ^ k ∣ Nat.card K → p ^ k < r)
    (α : MulAut K) (hα : α ^ r = 1) : α = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hrK : ¬ r ∣ Nat.card K := by
    intro h
    have h1 := hlt r 1 hr (by rw [pow_one]; exact h)
    rw [pow_one] at h1
    exact lt_irrefl r h1
  have hA : IsPGroup r (zpowers α) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  have htop : MonoidHom.eqLocus (α : K →* K) (MonoidHom.id K) = ⊤ := by
    refine eq_top_of_forall_sylow_le _ fun p hp => ?_
    have := Fact.mk hp
    have hrn : ¬ r ∣ Nat.card (Sylow p K) := fun h => hrK (h.trans
      ((Classical.arbitrary (Sylow p K)).card_dvd_index.trans (index_dvd_card _)))
    obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card _ hrn
    have hPα : (P : Subgroup K).map (α : K →* K) = P :=
      congrArg Sylow.toSubgroup (hP ⟨α, mem_zpowers α⟩)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
    have hβ : restrictAut α P hPα ^ r = 1 := by
      ext y
      rw [coe_restrictAut_pow, hα]
      rfl
    have hPlt : Nat.card (P : Subgroup K) < r := by
      rw [hk]
      exact hlt p k hp (by rw [← hk]; exact card_subgroup_dvd_card _)
    have h1 := CFSG.RankThree.PartTwo.Sec13.F135Last.g1o_aut_eq_one_of_card_lt hr hPlt _ hβ
    exact ⟨P, fun x hx => congrArg (fun γ : MulAut (P : Subgroup K) => (γ ⟨x, hx⟩ : K)) h1⟩
  ext x
  have hx : x ∈ MonoidHom.eqLocus (α : K →* K) (MonoidHom.id K) := htop ▸ mem_top x
  exact hx

theorem mulAut_eq_one_of_pow_seven_of_card_360 {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup K] (hK : Nat.card K = 360) (α : MulAut K) (hα : α ^ 7 = 1) : α = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hA := isPGroup_zpowers_of_pow_seven hα
  have h7K : ¬ 7 ∣ Nat.card K := by rw [hK]; norm_num
  have hinv : ∀ p : ℕ, p.Prime → ∃ P : Sylow p K, (P : Subgroup K).map (α : K →* K) = P := by
    intro p hp
    have := Fact.mk hp
    have h7n : ¬ 7 ∣ Nat.card (Sylow p K) := fun h => h7K (h.trans
      ((Classical.arbitrary (Sylow p K)).card_dvd_index.trans (index_dvd_card _)))
    obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card _ h7n
    exact ⟨P, congrArg Sylow.toSubgroup (hP ⟨α, mem_zpowers α⟩)⟩
  have hfix : ∀ (P : Subgroup K) (hP : P.map (α : K →* K) = P),
      (∀ d, d ∣ Nat.card P → d ≡ Nat.card P [MOD 7] → d = Nat.card P) →
      P ≤ fixedSubgroupOf α := by
    intro P hP hdiv x hx
    have hβ : restrictAut α P hP ^ 7 = 1 := by
      ext y
      rw [coe_restrictAut_pow, hα]
      rfl
    have h1 := eq_one_of_pow_seven_of_modEq _ hβ hdiv
    exact congrArg (fun γ : MulAut P => (γ ⟨x, hx⟩ : K)) h1
  obtain ⟨P3, hP3⟩ := hinv 3 Nat.prime_three
  obtain ⟨P5, hP5⟩ := hinv 5 (by norm_num)
  have hc3 : Nat.card (P3 : Subgroup K) = 9 := by
    rw [P3.card_eq_multiplicity, hK]
    have : Nat.factorization 360 3 = 2 := by decide +kernel
    rw [this]
    norm_num
  have hc5 : Nat.card (P5 : Subgroup K) = 5 := by
    rw [P5.card_eq_multiplicity, hK]
    have : Nat.factorization 360 5 = 1 := by decide +kernel
    rw [this]
    norm_num
  have hF3 : (P3 : Subgroup K) ≤ fixedSubgroupOf α := hfix _ hP3 (by
    rw [hc3]
    intro d hd hmod
    have key : ∀ d ∈ Nat.divisors 9, d % 7 = 9 % 7 → d = 9 := by decide
    exact key d (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) hmod)
  have hF5 : (P5 : Subgroup K) ≤ fixedSubgroupOf α := hfix _ hP5 (by
    rw [hc5]
    intro d hd hmod
    have key : ∀ d ∈ Nat.divisors 5, d % 7 = 5 % 7 → d = 5 := by decide
    exact key d (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) hmod)
  set F := fixedSubgroupOf α with hFdef
  have h9 : 9 ∣ Nat.card F := hc3 ▸ card_dvd_of_le hF3
  have h5 : 5 ∣ Nat.card F := hc5 ▸ card_dvd_of_le hF5
  have h45 : 45 ∣ Nat.card F := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h9 h5
  have hmod : Nat.card K ≡ Nat.card F [MOD 7] := card_fixedSubgroupOf_modEq α hα
  have hFdvd : Nat.card F ∣ 360 := hK ▸ card_subgroup_dvd_card F
  have hcases : Nat.card F = 45 ∨ Nat.card F = 360 := by
    have key : ∀ d ∈ Nat.divisors 360, 45 ∣ d → 360 % 7 = d % 7 → d = 45 ∨ d = 360 := by
      decide
    rw [hK] at hmod
    exact key _ (Nat.mem_divisors.2 ⟨hFdvd, by norm_num⟩) h45 hmod
  rcases hcases with h45F | h360F
  · exfalso
    have hsub : Nat.card ((P5 : Subgroup K).subgroupOf F) = 5 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF5).toEquiv).trans hc5
    let Q : Sylow 5 F := Sylow.ofCard ((P5 : Subgroup K).subgroupOf F) (by
      rw [hsub, h45F]
      have : Nat.factorization 45 5 = 1 := by decide +kernel
      rw [this]
      norm_num)
    have hQcard : Nat.card (Q : Subgroup F) = 5 := hsub
    have hn1 : Nat.card (Sylow 5 F) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 F
    have hndvd : Nat.card (Sylow 5 F) ∣ (Q : Subgroup F).index := Q.card_dvd_index
    have hidx : (Q : Subgroup F).index = 9 := by
      have h := Subgroup.card_mul_index (Q : Subgroup F)
      rw [hQcard, h45F] at h
      omega
    have hn : Nat.card (Sylow 5 F) = 1 := by
      rw [hidx] at hndvd
      have key : ∀ d ∈ Nat.divisors 9, d % 5 = 1 % 5 → d = 1 := by decide
      exact key _ (Nat.mem_divisors.2 ⟨hndvd, by norm_num⟩) hn1
    have : Subsingleton (Sylow 5 F) := (Nat.card_eq_one_iff_unique.1 hn).1
    have hQn : ((P5 : Subgroup K).subgroupOf F).Normal := Sylow.normal_of_subsingleton Q
    have hFN : F ≤ normalizer ((P5 : Subgroup K) : Set K) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hF5).1 hQn
    set N := normalizer ((P5 : Subgroup K) : Set K) with hN
    have h45N : 45 ∣ Nat.card N := h45F ▸ card_dvd_of_le hFN
    have hNidx : N.index = Nat.card (Sylow 5 K) := (Sylow.card_eq_index_normalizer P5).symm
    have hn5 : Nat.card (Sylow 5 K) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 K
    have hmulN := Subgroup.card_mul_index N
    rw [hK] at hmulN
    have hidx1 : N.index = 1 := by
      obtain ⟨c, hc⟩ := h45N
      have h8 : c * N.index = 8 := by
        have : 45 * (c * N.index) = 45 * 8 := by rw [← mul_assoc, ← hc, hmulN]
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
      have hd : N.index ∣ 8 := Dvd.intro_left c h8
      have key : ∀ d ∈ Nat.divisors 8, d % 5 = 1 % 5 → d = 1 := by decide
      exact key _ (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) (by rw [hNidx]; exact hn5)
    have hNtop : N = ⊤ := Subgroup.index_eq_one.1 hidx1
    have hPn : (P5 : Subgroup K).Normal := Subgroup.normalizer_eq_top_iff.1 hNtop
    have := hPn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P5 : Subgroup K) with h | h
    · rw [h, Subgroup.card_bot] at hc5
      omega
    · rw [h, Subgroup.card_top, hK] at hc5
      omega
  · have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [h360F, hK])
    ext x
    have hx : x ∈ F := htop ▸ mem_top x
    exact hx

theorem false_of_card_168_of_commute {Y : Type} [Group Y] [Finite Y] (Kb : Subgroup Y)
    [Kb.Normal] [IsSimpleGroup Kb]
    (hinj : Function.Injective (MulAut.conjNormal : Y →* MulAut Kb))
    (h168 : Nat.card Kb = 168) {e v : Y} (he : orderOf e = 7) (hv : orderOf v = 2)
    (hev : e * v = v * e) : False := by
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut Kb) :=
    Finite.of_injective (fun f : MulAut Kb => (f : Kb → Kb)) DFunLike.coe_injective
  have heK : e ∈ Kb := by
    by_contra hne
    have h1 : orderOf (QuotientGroup.mk' Kb e) = 7 := by
      have hdvd : orderOf (QuotientGroup.mk' Kb e) ∣ 7 := he ▸ orderOf_map_dvd _ e
      rcases (Nat.dvd_prime h7.out).1 hdvd with h | h
      · exfalso
        apply hne
        rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
        exact h
      · exact h
    have h7q : 7 ∣ Nat.card (Y ⧸ Kb) := h1 ▸ orderOf_dvd_natCard _
    have hY : Nat.card Y = Nat.card (Y ⧸ Kb) * Nat.card Kb :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup Kb
    have h49 : 7 ^ 2 ∣ Nat.card Y := by
      rw [hY, h168, pow_two]
      exact Nat.mul_dvd_mul h7q (by norm_num)
    exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.not_sq_seven_dvd_card_mulAut_of_card_168 h168
      (h49.trans (Subgroup.card_dvd_of_injective _ hinj))
  set σ : MulAut Kb := MulAut.conjNormal v with hσ
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσ, ← map_pow, ← hv, pow_orderOf_eq_one, map_one]
  obtain ⟨s, hs2, hss⟩ := exists_fixed_orderOf_eq_prime (p := 2) σ hσ2 (by rw [h168]; norm_num)
  have hsF : s ∈ fixedSubgroupOf σ := hss
  have heF : (⟨e, heK⟩ : Kb) ∈ fixedSubgroupOf σ := by
    rw [mem_fixedSubgroupOf]
    apply Subtype.ext
    rw [hσ, MulAut.conjNormal_apply]
    rw [← hev, mul_inv_cancel_right]
  have h2F : 2 ∣ Nat.card (fixedSubgroupOf σ) := by
    have := orderOf_dvd_natCard (⟨s, hsF⟩ : fixedSubgroupOf σ)
    rwa [Subgroup.orderOf_mk, hs2] at this
  have h7F : 7 ∣ Nat.card (fixedSubgroupOf σ) := by
    have := orderOf_dvd_natCard (⟨⟨e, heK⟩, heF⟩ : fixedSubgroupOf σ)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, he] at this
  have h14 : 14 ∣ Nat.card (fixedSubgroupOf σ) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2F h7F
  have htop := CFSG.GF2Type.Aschbacher1976Full.HS.eq_top_of_dvd_fourteen_simple168 h168 h14
  have hσ1 : σ = 1 := by
    ext x
    have hx : x ∈ fixedSubgroupOf σ := htop ▸ mem_top x
    exact congrArg Subtype.val hx
  have hv1 : v = 1 := hinj (by rw [map_one]; exact hσ1)
  rw [hv1, orderOf_one] at hv
  exact absurd hv (by norm_num)

end L2Small

theorem k_19_glue7_L2small_holds : K_19_glue7_L2small := by
  intro Y _ _ Kb hN hS hC hcard e v he he7 hv hev
  have := hN
  have := hS
  have hcardKb : Nat.card Kb ≠ 1 := by rcases hcard with h | h | h <;> omega
  have hZ : center Kb = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Kb) with h | h
    · exact h
    · exfalso
      have hle : Kb ≤ centralizer (Kb : Set Y) := by
        intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        have hxc : (⟨x, hx⟩ : Kb) ∈ center Kb := h ▸ mem_top _
        exact congrArg Subtype.val ((mem_center_iff.1 hxc) ⟨y, hy⟩)
      rw [hC, le_bot_iff] at hle
      apply hcardKb
      rw [hle, card_bot]
  have hinj : Function.Injective (MulAut.conjNormal : Y →* MulAut Kb) :=
    conjNormal_injective_of_centralizer_le (by rw [hC]; exact bot_le) hZ
  generalize hr : orderOf e = r at he he7
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hr
    subst hr
    exact Nat.not_prime_one he
  set α : MulAut Kb := MulAut.conjNormal e with hαdef
  have hα : α ^ r = 1 := by rw [hαdef, ← map_pow, ← hr, pow_orderOf_eq_one, map_one]
  have hα1 : α ≠ 1 := fun h => he1 (hinj (by rw [map_one]; exact h))
  have h11 : r ≠ 7 → 11 ≤ r := by
    intro h7
    by_contra hlt
    interval_cases r
    all_goals first
      | exact absurd rfl h7
      | norm_num at he
  rcases hcard with h60 | h168 | h360
  · exact hα1 (L2Small.mulAut_eq_one_of_prime_pow_lt he (fun p k hp hd => by
      have := L2Small.prime_pow_le_of_dvd_sixty hp (h60 ▸ hd)
      omega) α hα)
  · by_cases h7 : r = 7
    · subst h7
      exact L2Small.false_of_card_168_of_commute Kb hinj h168 hr hv hev
    · have := h11 h7
      exact hα1 (L2Small.mulAut_eq_one_of_prime_pow_lt he (fun p k hp hd => by
        have := L2Small.prime_pow_le_of_dvd_168 hp (h168 ▸ hd)
        omega) α hα)
  · by_cases h7 : r = 7
    · subst h7
      exact hα1 (L2Small.mulAut_eq_one_of_pow_seven_of_card_360 h360 α hα)
    · have := h11 h7
      exact hα1 (L2Small.mulAut_eq_one_of_prime_pow_lt he (fun p k hp hd => by
        have := L2Small.prime_pow_le_of_dvd_360 hp (h360 ▸ hd)
        omega) α hα)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

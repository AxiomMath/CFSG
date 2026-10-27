module

public import CFSG.Quasithin.Background.F1Cartan
public import CFSG.Quasithin.H13.A5F91
public import CFSG.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

section Gen

variable {G : Type} [Group G]

theorem oTwoRes_oTwoRes (X : Subgroup G) : oTwoRes (oTwoRes X) = oTwoRes X := by
  refine le_antisymm (oTwoRes_le _) ((Subgroup.closure_le _).mpr ?_)
  rintro x ⟨hx, m, hm, hxm⟩
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hx, m, hm, hxm⟩, m, hm, hxm⟩

theorem le_normalizer_oTwoRes {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    H ≤ Subgroup.normalizer (oTwoRes N : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ x ∈ oTwoRes N,
      g * x * g⁻¹ ∈ oTwoRes N := by
    intro g hg x hx
    have hx' : x ∈ Subgroup.closure {y | y ∈ N ∧ ∃ m : ℕ, Odd m ∧ y ^ m = 1} := hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxN, m, hm, hxm⟩ := hx
      exact Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxN, m, hm,
        by rw [conj_pow, hxm, mul_one, mul_inv_cancel]⟩
    | one => simp
    | mul x y _ _ ihx ihy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact (oTwoRes N).mul_mem ihx ihy
    | inv x _ ih =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact (oTwoRes N).inv_mem ih
  intro h hh
  refine B6.mem_normalizer_of_forall_mem (key h (hHN hh)) fun x hx => ?_
  simpa using key h⁻¹ (Subgroup.inv_mem _ (hHN hh)) x hx

end Gen

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem lemma_13_6_26_two (h1338 : A6.Stmt13_3_8)
    (hsolv : ∀ H : Subgroup G, InH T H → Group.IsSolvable ↥H →
      H ≤ Subgroup.normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ S.Hz) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {N : Subgroup G}
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hON : pCoreOf 2 H ≤ N)
    (hNp : ∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 H) : N = pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hO2 : pCoreOf 2 H ≠ ⊥ := hH.1.2
  have hHM : ¬ H ≤ Subgroup.normalizer (L : Set G) := hH.2.2
  have hO2p : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHO2 : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hnorm : ((pCoreOf 2 H).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hON).mpr fun x hx => hHO2 (hNH hx)
  have hq : IsPGroup p (↥N ⧸ (pCoreOf 2 H).subgroupOf N) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hNp x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hk
  have hqs : Group.IsSolvable (↥N ⧸ (pCoreOf 2 H).subgroupOf N) := by
    have : Group.IsNilpotent (↥N ⧸ (pCoreOf 2 H).subgroupOf N) := hq.isNilpotent
    infer_instance
  have hNs : Group.IsSolvable ↥N :=
    F1.isSolvable_of_normal_subgroupOf hON (F1.isSolvable_of_isPGroup_two hO2p) hqs
  have hXs : Group.IsSolvable ↥(N ⊔ T) :=
    F1.isSolvable_sup_of_le_normalizer hNs (F1.isSolvable_of_isPGroup_two S.isPGroup_T)
      (hTH.trans hHN)
  have hXH : N ⊔ T ≤ H := sup_le hNH hTH
  have hXO2 : pCoreOf 2 (N ⊔ T) ≠ ⊥ := by
    intro h
    apply hO2
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hON.trans le_sup_left)
      (hXH.trans hHO2) hO2p
    rw [h] at this
    exact le_bot_iff.mp this
  have hXM := hsolv (N ⊔ T) ⟨le_sup_right, hXO2⟩ hXs
  have hYN : oTwoRes N ≤ N := oTwoRes_le N
  have hY23 := (h1338 G T L L H (oTwoRes N) S.h13 S.h13.faithful ⟨hTH, hO2⟩ hHM
    (oTwoRes_oTwoRes N) (hYN.trans hNH) (le_normalizer_oTwoRes hHN)
    (hYN.trans (le_sup_left.trans hXM))).2
  have hN2 : IsPGroup 2 N := by
    intro x
    obtain ⟨a, m, hm, ha⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    by_cases hm1 : m = 1
    · refine ⟨a, ?_⟩
      rw [← orderOf_dvd_iff_pow_eq_one, ha, hm1, mul_one]
    exfalso
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    have h2a : (2 ^ a : ℕ) ≠ 0 := by positivity
    have hoy : orderOf ((x : G) ^ 2 ^ a) = m := by
      rw [orderOf_pow' _ h2a, Subgroup.orderOf_coe, ha, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hyY : (x : G) ^ 2 ^ a ∈ oTwoRes N :=
      Subgroup.subset_closure ⟨N.pow_mem x.2 _, m, hm, by rw [← hoy, pow_orderOf_eq_one]⟩
    have hmY : m ∣ Nat.card ↥(oTwoRes N) := by
      rw [← hoy]
      exact Subgroup.orderOf_dvd_natCard _ hyY
    have hq3 : q = 3 := by
      rcases hY23 q hq (hqm.trans hmY) with h | h
      · exact absurd (h ▸ hqm) (by
          intro h2
          obtain ⟨c, hc⟩ := h2
          rw [hc] at hm
          exact Nat.not_even_iff_odd.mpr hm (even_two_mul c))
      · exact h
    obtain ⟨k, hk⟩ := hNp x x.2
    obtain ⟨b, hb⟩ := hO2p ⟨_, hk⟩
    have hb' : (x : G) ^ (p ^ k * 2 ^ b) = 1 := by
      rw [pow_mul]
      exact congrArg Subtype.val hb
    have hdvd : orderOf x ∣ p ^ k * 2 ^ b := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by simpa using hb')
    have hmp : m ∣ p ^ k * 2 ^ b := (Dvd.intro_left _ ha.symm).trans hdvd
    have hcop : Nat.Coprime m (2 ^ b) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
    have hmp' : m ∣ p ^ k := hcop.dvd_of_dvd_mul_right hmp
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp
      (hq.dvd_of_dvd_pow (hqm.trans hmp'))
    omega
  exact le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNH hHN hN2) hON

end Setting

end CFSG.Quasithin.H13.A5

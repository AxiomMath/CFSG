module

public import Mathlib.GroupTheory.PGroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import Mathlib.NumberTheory.Basic

public section

namespace CFSG.Quasithin

namespace S153L

open Subgroup

private theorem nsf_isCyclic {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 3 P) (hE : ∀ E : Subgroup G, (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3) :
    IsCyclic P := by
  by_contra hnc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨hP⟩
  obtain ⟨E, -, hcard, hel⟩ := CFSG.lemma_4_5_a (R := P) (p := 3) (by norm_num) hnc
  have h := hE (E.map P.subtype) (by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) (p := 3) e he, map_one])
  rw [card_map_of_injective P.subtype_injective, hcard] at h
  norm_num at h

private theorem nsf_exists_conj_eq_zpow {G : Type*} [Group G] {P : Subgroup G} (hcyc : IsCyclic P)
    {n : G} (hn : n ∈ normalizer (P : Set G)) : ∃ k : ℤ, ∀ g ∈ P, n * g * n⁻¹ = g ^ k := by
  let σ : P →* P :=
    { toFun := fun g => ⟨n * g * n⁻¹, (mem_normalizer_iff.mp hn g).mp g.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic σ
  refine ⟨k, fun g hg => ?_⟩
  have := congrArg Subtype.val (hk ⟨g, hg⟩)
  simpa [σ] using this

private theorem nsf_pow_conj {G : Type*} [Group G] {P : Subgroup G} {n : G} {k : ℤ}
    (hk : ∀ g ∈ P, n * g * n⁻¹ = g ^ k) (j : ℕ) :
    ∀ g ∈ P, n ^ j * g * (n ^ j)⁻¹ = g ^ (k ^ j) := by
  induction j with
  | zero => intro g _; simp
  | succ j ih =>
    intro g hg
    calc n ^ (j + 1) * g * (n ^ (j + 1))⁻¹ = n * (n ^ j * g * (n ^ j)⁻¹) * n⁻¹ := by group
      _ = n * g ^ (k ^ j) * n⁻¹ := by rw [ih g hg]
      _ = (n * g * n⁻¹) ^ (k ^ j) := by rw [conj_zpow]
      _ = (g ^ k) ^ (k ^ j) := by rw [hk g hg]
      _ = g ^ (k ^ (j + 1)) := by rw [← zpow_mul, pow_succ']

private theorem nsf_normalizer_le_centralizer {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 3)] (P : Sylow 3 G) (hcyc : IsCyclic (P : Subgroup G))
    (h3 : 3 ∣ Nat.card (P : Subgroup G)) (hcent : ∀ x y : G, orderOf x = 3 → x * y = y * x) :
    normalizer P ≤ centralizer (P : Set G) := by
  intro n hn
  obtain ⟨k, hk⟩ := nsf_exists_conj_eq_zpow hcyc hn
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hc' : orderOf (c : G) = 3 := by rw [orderOf_coe]; exact hc
  have hk1 : (3 : ℤ) ∣ k - 1 := by
    have h1 : n * c * n⁻¹ = (c : G) ^ k := hk c c.2
    have h2 : n * c * n⁻¹ = c := by rw [← hcent c n hc', mul_inv_cancel_right]
    have h4 : (c : G) ^ (k - 1) = 1 := by rw [zpow_sub_one, ← h1, h2, mul_inv_cancel]
    have h5 := orderOf_dvd_iff_zpow_eq_one.mpr h4
    rw [hc'] at h5
    exact_mod_cast h5
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  have hkP : (Nat.card (P : Subgroup G) : ℤ) ∣ k ^ Nat.card (P : Subgroup G) - 1 := by
    have h := dvd_sub_pow_of_dvd_sub (R := ℤ) (p := 3) (a := k) (b := 1) (by exact_mod_cast hk1) a
    rw [one_pow] at h
    rw [ha]
    push_cast at h ⊢
    exact (pow_dvd_pow _ (Nat.le_succ a)).trans h
  have hc1 : n ^ Nat.card (P : Subgroup G) ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    have h1 := nsf_pow_conj hk (Nat.card (P : Subgroup G)) g hg
    have h2 : g ^ (k ^ Nat.card (P : Subgroup G)) = g := by
      have hd : (orderOf g : ℤ) ∣ k ^ Nat.card (P : Subgroup G) - 1 :=
        (Int.natCast_dvd_natCast.mpr (Subgroup.orderOf_dvd_natCard _ hg)).trans hkP
      rw [← mul_inv_eq_one, ← zpow_sub_one]
      exact orderOf_dvd_iff_zpow_eq_one.mp hd
    rw [h2, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hc2 : n ^ P.index ∈ centralizer (P : Set G) := by
    have hpow : (n ^ P.index) ^ Nat.card (P : Subgroup G) = 1 := by
      rw [← pow_mul, index_mul_card, pow_card_eq_one']
    have hpg : IsPGroup 3 (zpowers (n ^ P.index)) := by
      refine IsPGroup.of_card_dvd_pow (n := a) ?_
      rw [Nat.card_zpowers, ← ha]
      exact orderOf_dvd_of_pow_eq_one hpow
    have hmem : n ^ P.index ∈ zpowers (n ^ P.index) ⊓ normalizer P :=
      mem_inf.mpr ⟨mem_zpowers _, pow_mem hn _⟩
    rw [hpg.inf_normalizer_sylow P] at hmem
    have := hcyc
    exact le_centralizer (P : Subgroup G) (mem_inf.mp hmem).2
  have hb := Nat.gcd_eq_gcd_ab (Nat.card (P : Subgroup G)) P.index
  rw [show Nat.gcd (Nat.card (P : Subgroup G)) P.index = 1 from P.card_coprime_index,
    Nat.cast_one] at hb
  have hn_eq : n = (n ^ Nat.card (P : Subgroup G)) ^ Nat.gcdA (Nat.card (P : Subgroup G)) P.index *
      (n ^ P.index) ^ Nat.gcdB (Nat.card (P : Subgroup G)) P.index := by
    rw [← zpow_natCast, ← zpow_natCast n P.index, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb,
      zpow_one]
  rw [hn_eq]
  exact mul_mem (zpow_mem hc1 _) (zpow_mem hc2 _)

private theorem nsf_eq_bot {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hperf : commutator G = ⊤) (P : Sylow p G) (hN : normalizer P ≤ centralizer (P : Set G)) :
    (P : Subgroup G) = ⊥ := by
  have hf : ∀ x : G, MonoidHom.transferSylow P hN x = 1 := by
    intro x
    have hle : commutator G ≤ (MonoidHom.transferSylow P hN).ker := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (hN (le_normalizer (MonoidHom.transferSylow P hN b).2) _
        (MonoidHom.transferSylow P hN a).2)
    exact hle (hperf ▸ mem_top x)
  rw [eq_bot_iff]
  intro g hg
  have h1 : g ^ P.index = 1 := by
    have := congrArg Subtype.val (MonoidHom.transferSylow_eq_pow P hN g hg)
    rw [hf] at this
    exact this.symm
  rw [mem_bot, ← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes P.card_coprime_index
    (Subgroup.orderOf_dvd_natCard _ hg) (orderOf_dvd_of_pow_eq_one h1)

theorem noncentral_three_absurd {Γ : Type*} [Group Γ] [Finite Γ] (K Y : Subgroup Γ)
    (hK : ⁅K, K⁆ = K) (h3 : 3 ∣ Nat.card K)
    (hcent : ∀ x ∈ K, orderOf x = 3 → ∀ k ∈ K, x * k = k * x)
    (hY : ∀ x ∈ K, orderOf x = 3 → x ∈ Y)
    (hY3 : ∀ E : Subgroup Γ, E ≤ Y → IsPGroup 3 E → Nat.card E ≤ 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hE : ∀ E : Subgroup K, (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3 := by
    intro E hE3
    have hle : E.map K.subtype ≤ Y := by
      rintro _ ⟨x, hx, rfl⟩
      have hx3 : (x : Γ) ^ 3 = 1 := by
        simpa using congrArg Subtype.val (hE3 x hx)
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h1 | h1
      · rw [orderOf_eq_one_iff] at h1
        show (x : Γ) ∈ Y
        rw [h1]
        exact Y.one_mem
      · exact hY x x.2 h1
    have hp : IsPGroup 3 (E.map K.subtype) :=
      IsPGroup.map (fun x => ⟨1, Subtype.ext (by simpa using hE3 x x.2)⟩) K.subtype
    have := hY3 _ hle hp
    rwa [card_map_of_injective K.subtype_injective] at this
  have hKtop : commutator K = ⊤ := by
    apply map_injective K.subtype_injective
    rw [map_subtype_commutator, ← MonoidHom.range_eq_map, range_subtype, hK]
  refine P.ne_bot_of_dvd_card h3 (nsf_eq_bot hKtop P ?_)
  exact nsf_normalizer_le_centralizer P (nsf_isCyclic P.isPGroup' hE)
    (P.dvd_card_of_dvd_card h3) fun x y hx =>
      Subtype.ext (hcent x x.2 ((orderOf_coe x).trans hx) y y.2)

end S153L

end CFSG.Quasithin

module

public import CFSG.RankThree.PartOne.S11d.OutCentral
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem exists_invariant_sylowOf [Finite G] {p : ℕ} [Fact p.Prime] {J E : Subgroup G}
    (hEN : E ≤ normalizer (J : Set G)) (hEp : IsPGroup p E) :
    ∃ P : Subgroup G, IsSylowOf p P J ∧ E ≤ normalizer (P : Set G) := by
  classical
  set W : Subgroup G := J ⊔ E with hW
  have hJW : J ≤ W := le_sup_left
  have hEW : E ≤ W := le_sup_right
  have hWN : W ≤ normalizer (J : Set G) := sup_le le_normalizer hEN
  have hE' : IsPGroup p (E.subgroupOf W) := hEp.comap_subtype
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  set S : Subgroup G := (Q : Subgroup W).map W.subtype with hS
  have hSW : IsSylowOf p S W := ⟨Q, rfl⟩
  have hES : E ≤ S := by
    intro e he
    exact ⟨⟨e, hEW he⟩, hQ (Subgroup.mem_subgroupOf.mpr he), rfl⟩
  refine ⟨S ⊓ J, hSW.inf_of_le_normalizer hJW hWN, ?_⟩
  intro e he
  exact mem_normalizer_inf (hES he) (hEN he)

theorem pow_dvd_mul_sub_one_of_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ}
    {u : ℤ} (h : (p : ℤ) ^ k ∣ u ^ p - 1) : (p : ℤ) ^ k ∣ (p : ℤ) * (u - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hpZ : (p : ℤ) ∣ u ^ p - 1 := (dvd_pow_self _ hk.ne').trans h
  have hferm : (p : ℤ) ∣ u ^ p - u := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card]
    ring
  have hu1 : (p : ℤ) ∣ u - 1 := by
    have := dvd_sub hferm hpZ
    have e : u ^ p - u - (u ^ p - 1) = -(u - 1) := by ring
    rw [e] at this
    exact (dvd_neg).mp this
  by_cases hu : u = 1
  · simp [hu]
  have hup : ¬ (p : ℤ) ∣ u := by
    intro hpu
    have : (p : ℤ) ∣ 1 := by
      have := dvd_sub hpu hu1
      simpa using this
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hlte : emultiplicity (p : ℤ) (u ^ p - 1 ^ p) = emultiplicity (p : ℤ) (u - 1) + 1 :=
    emultiplicity_pow_prime_sub_pow_prime hpp hodd (by simpa using hu1) hup
  rw [one_pow] at hlte
  have hle : (k : ℕ∞) ≤ emultiplicity (p : ℤ) (u - 1) + 1 := by
    rw [← hlte]
    exact pow_dvd_iff_le_emultiplicity.mp h
  have hk1 : ((k - 1 : ℕ) : ℕ∞) ≤ emultiplicity (p : ℤ) (u - 1) := by
    have h1 : ((k - 1 : ℕ) : ℕ∞) + 1 = (k : ℕ∞) := by
      have : (k - 1 + 1 : ℕ) = k := Nat.sub_add_cancel hk
      exact_mod_cast this
    rw [← h1] at hle
    exact (ENat.add_le_add_iff_right (ENat.natCast_ne_top 1)).mp hle
  have hdvd : (p : ℤ) ^ (k - 1) ∣ u - 1 := pow_dvd_iff_le_emultiplicity.mpr hk1
  have e : (p : ℤ) ^ k = p * (p : ℤ) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [e]
  exact mul_dvd_mul_left _ hdvd

theorem commutator_pow_eq_one_of_cyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    {y e : G} (hP : IsPGroup p P) (hyP : y ∈ P) (hgen : ∀ x ∈ P, ∃ k : ℤ, y ^ k = x)
    (heN : e ∈ normalizer (P : Set G)) (hep : e ^ p = 1) : (e * y * e⁻¹ * y⁻¹) ^ p = 1 := by
  obtain ⟨u, hu⟩ := hgen _ ((mem_normalizer_iff.mp heN y).mp hyP)
  have hconj : ∀ m : ℕ, e ^ m * y * (e ^ m)⁻¹ = y ^ (u ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc e ^ (m + 1) * y * (e ^ (m + 1))⁻¹ = e * (e ^ m * y * (e ^ m)⁻¹) * e⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = e * y ^ (u ^ m) * e⁻¹ := by rw [ih]
        _ = (e * y * e⁻¹) ^ (u ^ m) := by rw [conj_zpow]
        _ = (y ^ u) ^ (u ^ m) := by rw [hu]
        _ = y ^ (u ^ (m + 1)) := by rw [← zpow_mul, pow_succ']
  have hyp : y ^ (u ^ p) = y := by
    rw [← hconj p, hep]
    simp
  obtain ⟨k, hk⟩ := hP ⟨y, hyP⟩
  have hk' : y ^ (p ^ k) = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk')
  have hdvd : (p : ℤ) ^ j ∣ u ^ p - 1 := by
    have h1 : y ^ (u ^ p - 1) = 1 := by
      rw [zpow_sub, zpow_one, hyp, mul_inv_cancel]
    have h2 : ((orderOf y : ℕ) : ℤ) ∣ u ^ p - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hj, Nat.cast_pow] at h2
  have hdvd2 : ((orderOf y : ℕ) : ℤ) ∣ (p : ℤ) * (u - 1) := by
    rw [hj, Nat.cast_pow]
    exact pow_dvd_mul_sub_one_of_dvd_pow_sub_one hp hp2 hdvd
  have hz : e * y * e⁻¹ * y⁻¹ = y ^ (u - 1) := by
    rw [← hu, zpow_sub, zpow_one]
  rw [hz, ← zpow_natCast, ← zpow_mul]
  rw [mul_comm]
  exact orderOf_dvd_iff_zpow_eq_one.mp hdvd2

theorem mem_zpowers_of_pow_eq_one_of_cyclic {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    [Finite G] [IsCyclic P] {d z : G} (hdP : d ∈ P) (hzP : z ∈ P) (hdp : orderOf d = p)
    (hzp : z ^ p = 1) : z ∈ zpowers d := by
  classical
  have : Fintype P := Fintype.ofFinite P
  let _ : CommGroup P := IsCyclic.commGroup
  set K : Subgroup P := (powMonoidHom p : P →* P).ker with hK
  have hKcard : Nat.card K ≤ p := by
    have h1 := IsCyclic.card_pow_eq_one_le (α := P) hp.pos
    have h2 : Fintype.card K = (Finset.univ.filter fun a : P => a ^ p = 1).card := by
      rw [Fintype.card_subtype]
      apply congrArg Finset.card
      ext a
      simp [hK, MonoidHom.mem_ker]
    rw [Nat.card_eq_fintype_card, h2]
    exact h1
  set H : Subgroup P := (zpowers d).subgroupOf P with hH
  have hHK : H ≤ K := by
    intro x hx
    rw [hK, MonoidHom.mem_ker]
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
    apply Subtype.ext
    show (x : G) ^ p = 1
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      show d ^ p = 1 by rw [← hdp]; exact pow_orderOf_eq_one d, one_zpow]
  have hHcard : Nat.card H = p := by
    rw [hH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.mpr hdP)).toEquiv,
      Nat.card_zpowers, hdp]
  have hHeq : H = K := Subgroup.eq_of_le_of_card_ge hHK (by omega)
  have hz : (⟨z, hzP⟩ : P) ∈ K := by
    rw [hK, MonoidHom.mem_ker]
    exact Subtype.ext (by simpa using hzp)
  rw [← hHeq] at hz
  exact Subgroup.mem_subgroupOf.mp hz

theorem kf128_of_cyclic [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J E P : Subgroup G}
    {a d : G}
    (hPJ : P ≤ J) (hPp : IsPGroup p P) [hcyc : IsCyclic P] (hEel : CFSG.IsElementaryAbelian p E)
    (hEP : E ≤ normalizer (P : Set G)) (hdE : d ∈ E) (hdP : d ∈ P) (hd1 : d ≠ 1)
    (hmove : ¬ ∀ s ∈ P, a * s * a⁻¹ = s) :
    ∃ y ∈ J, (∃ k : ℕ, orderOf y = p ^ k) ∧ y * d * y⁻¹ = d ∧ y * a * y⁻¹ ≠ a ∧
      ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ zpowers d := by
  have : Fact p.Prime := ⟨hp⟩
  have hEpow : ∀ x ∈ E, x ^ p = 1 := fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  have hdord : orderOf d = p := orderOf_eq_prime (hEpow d hdE) hd1
  obtain ⟨y₀, hy₀⟩ := hcyc.exists_generator
  have hgen : ∀ x ∈ P, ∃ k : ℤ, (y₀ : G) ^ k = x := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hy₀ ⟨x, hx⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hyP : (y₀ : G) ∈ P := y₀.2
  refine ⟨y₀, hPJ hyP, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hPp y₀
    have hk' : (y₀ : G) ^ (p ^ k) = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk')
    exact ⟨j, hj⟩
  · obtain ⟨kd, hkd⟩ := hgen d hdP
    rw [← hkd]
    group
  · intro hcomm
    apply hmove
    intro s hs
    obtain ⟨k, hk⟩ := hgen s hs
    have h1 : (y₀ : G) * a = a * y₀ := mul_inv_eq_iff_eq_mul.mp hcomm
    have hay : a * (y₀ : G) * a⁻¹ = y₀ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact h1.symm
    rw [← hk]
    calc a * (y₀ : G) ^ k * a⁻¹ = (a * (y₀ : G) * a⁻¹) ^ k := conj_zpow.symm
      _ = (y₀ : G) ^ k := by rw [hay]
  · intro e he
    have hz := commutator_pow_eq_one_of_cyclic hp hp2 hPp hyP hgen (hEP he) (hEpow e he)
    have hzP : e * (y₀ : G) * e⁻¹ * (y₀ : G)⁻¹ ∈ P := by
      refine P.mul_mem (((mem_normalizer_iff.mp (hEP he) y₀).mp hyP)) (P.inv_mem hyP)
    have hzd := mem_zpowers_of_pow_eq_one_of_cyclic hp hdP hzP hdord hz
    have : (y₀ : G) * e * (y₀ : G)⁻¹ * e⁻¹ = (e * (y₀ : G) * e⁻¹ * (y₀ : G)⁻¹)⁻¹ := by group
    rw [this]
    exact (zpowers d).inv_mem hzd

theorem kf128_of_moves [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J E : Subgroup G}
    {a d : G} (hJ : CFSG.pRank p ↥J ≤ 1) (hEel : CFSG.IsElementaryAbelian p E)
    (hEN : E ≤ normalizer (J : Set G)) (hdE : d ∈ E) (hdJ : d ∈ J) (hd1 : d ≠ 1)
    (hmove : ∀ S : Subgroup G, IsSylowOf p S J → ¬ ∀ s ∈ S, a * s * a⁻¹ = s) :
    ∃ y ∈ J, (∃ k : ℕ, orderOf y = p ^ k) ∧ y * d * y⁻¹ = d ∧ y * a * y⁻¹ ≠ a ∧
      ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ zpowers d := by
  have : Fact p.Prime := ⟨hp⟩
  have hEpow : ∀ x ∈ E, x ^ p = 1 := fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hEpow g.1 g.2)⟩
  obtain ⟨P, hP, hEP⟩ := exists_invariant_sylowOf hEN hEp
  have hdord : orderOf d = p := orderOf_eq_prime (hEpow d hdE) hd1
  have hdP : d ∈ P :=
    mem_of_pElement_mem_normalizer hP hdJ (hEP hdE) ⟨1, by rw [hdord, pow_one]⟩
  have hcyc : IsCyclic P := isCyclic_of_pRank_le_one hp hp2 hP.le hP.isPGroup hJ
  exact kf128_of_cyclic hp hp2 hP.le hP.isPGroup hEel hEP hdE hdP hd1 (hmove P hP)

end CFSG.RankThree.PartOne

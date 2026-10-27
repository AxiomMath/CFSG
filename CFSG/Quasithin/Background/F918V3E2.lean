module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin

namespace F918V3E2

theorem three_pow_dvd_sub_or_add {j : ℕ} {a : ℤ} (h : (3 : ℤ) ^ j ∣ a * a - 1) :
    (3 : ℤ) ^ j ∣ a - 1 ∨ (3 : ℤ) ^ j ∣ a + 1 := by
  have hfac : a * a - 1 = (a - 1) * (a + 1) := by ring
  rw [hfac] at h
  have hirr : Irreducible (3 : ℤ) := Int.prime_three.irreducible
  by_cases h3 : (3 : ℤ) ∣ a + 1
  · right
    have h3' : ¬ (3 : ℤ) ∣ a - 1 := by
      intro h1
      have : (3 : ℤ) ∣ (a + 1) - (a - 1) := dvd_sub h3 h1
      omega
    have hcop : IsCoprime ((3 : ℤ) ^ j) (a - 1) := (hirr.coprime_iff_not_dvd.mpr h3').pow_left
    exact hcop.dvd_of_dvd_mul_left h
  · left
    have hcop : IsCoprime ((3 : ℤ) ^ j) (a + 1) := (hirr.coprime_iff_not_dvd.mpr h3).pow_left
    exact hcop.dvd_of_dvd_mul_right h

theorem sq_conj_eq {K : Type*} [Group K] [Finite K] (P : Sylow 3 K)
    (hP1 : (P : Subgroup K) ≠ ⊥) (hPc : IsCyclic ↥(P : Subgroup K)) {n : K}
    (hn : n ∈ Subgroup.normalizer (P : Set K)) (y : K) (hy : y ∈ (P : Subgroup K)) :
    n * (n * y * n⁻¹) * n⁻¹ = y := by
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have hPC : (P : Subgroup K) ≤ Subgroup.centralizer (P : Set K) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨b, hb⟩ : ↥(P : Subgroup K)) ⟨a, ha⟩)
  let ψ := (P : Subgroup K).normalizerMonoidHom
  have hker : ψ.ker = (Subgroup.centralizer (P : Set K)).subgroupOf
      (Subgroup.normalizer (P : Set K)) := Subgroup.normalizerMonoidHom_ker _
  have hdvd : Nat.card ψ.range ∣ Nat.card (MulAut ↥(P : Subgroup K)) :=
    Subgroup.card_subgroup_dvd_card _
  rw [IsCyclic.card_mulAut] at hdvd
  obtain ⟨j, hj⟩ := P.isPGroup'.exists_card_eq
  have hj1 : j ≠ 0 := by
    rintro rfl
    exact hP1 (Subgroup.card_eq_one.mp (by simpa using hj))
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj1
  rw [hj, Nat.totient_prime_pow_succ Nat.prime_three] at hdvd
  have hcop : Nat.Coprime (Nat.card ψ.range) 3 := by
    have e : Nat.card ψ.range = (Subgroup.centralizer (P : Set K)).relIndex
        (Subgroup.normalizer (P : Set K)) := by
      rw [← Subgroup.index_ker, hker]; rfl
    rw [e]
    apply Nat.Coprime.coprime_dvd_left (Subgroup.relIndex_dvd_of_le_left _ hPC)
    apply Nat.Coprime.coprime_dvd_left (Subgroup.relIndex_dvd_index_of_le P.le_normalizer)
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact P.not_dvd_index
  have h2 : Nat.card ψ.range ∣ 2 := by
    have := (hcop.pow_right i).dvd_of_dvd_mul_left hdvd
    simpa using this
  have hsq : ψ ⟨n, hn⟩ ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := h2
    have hz : (⟨ψ ⟨n, hn⟩, ⟨_, rfl⟩⟩ : ψ.range) ^ 2 = 1 := by
      rw [hc, pow_mul, pow_card_eq_one', one_pow]
    exact congrArg Subtype.val hz
  have hψ : ∀ (m : K) (hm : m ∈ Subgroup.normalizer (P : Set K)) (z : ↥(P : Subgroup K)),
      ((ψ ⟨m, hm⟩ z : ↥(P : Subgroup K)) : K) = m * z * m⁻¹ := fun _ _ _ => rfl
  have := congrArg (fun f : MulAut ↥(P : Subgroup K) => (f ⟨y, hy⟩ : K)) hsq
  simpa [pow_two, hψ] using this

theorem inv_of_mem_normalizer_not_mem_centralizer {K : Type*} [Group K] [Finite K]
    (P : Sylow 3 K) (hP1 : (P : Subgroup K) ≠ ⊥) (hPc : IsCyclic ↥(P : Subgroup K)) {g : K}
    (hg : g ∈ Subgroup.normalizer (P : Set K)) (hgC : g ∉ Subgroup.centralizer (P : Set K)) :
    ∀ y ∈ (P : Subgroup K), g * y * g⁻¹ = y⁻¹ := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := ↥(P : Subgroup K))
  obtain ⟨j, hj⟩ := P.isPGroup'.exists_card_eq
  have hord : orderOf (x : K) = 3 ^ j := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx, hj]
  have hpow : ∀ y ∈ (P : Subgroup K), ∃ c : ℤ, (x : K) ^ c = y := by
    intro y hy
    obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp (hx ⟨y, hy⟩)
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  have hy₀ : g * (x : K) * g⁻¹ ∈ (P : Subgroup K) :=
    (Subgroup.mem_normalizer_iff.mp hg _).mp x.2
  obtain ⟨a, ha⟩ := hpow _ hy₀
  have hsq := sq_conj_eq P hP1 hPc hg (x : K) x.2
  have hxa : (x : K) ^ (a * a) = x := by
    calc (x : K) ^ (a * a) = ((x : K) ^ a) ^ a := zpow_mul _ _ _
      _ = (g * (x : K) * g⁻¹) ^ a := by rw [ha]
      _ = g * (x : K) ^ a * g⁻¹ := conj_zpow
      _ = g * (g * (x : K) * g⁻¹) * g⁻¹ := by rw [ha]
      _ = x := hsq
  have hdvd : ((3 : ℤ) ^ j) ∣ a * a - 1 := by
    have h1 : (x : K) ^ (a * a - 1) = 1 := by
      rw [zpow_sub, hxa, zpow_one, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hord] at this
    exact_mod_cast this
  rcases three_pow_dvd_sub_or_add hdvd with h | h
  · exfalso
    apply hgC
    have h1 : (x : K) ^ (a - 1) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hord]; exact_mod_cast h)
    have h2 : (x : K) ^ a = x := by
      rw [zpow_sub_one, mul_inv_eq_one] at h1
      exact h1
    have hcomm : Commute (x : K) g := by
      have : g * (x : K) * g⁻¹ = x := by rw [← ha, h2]
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨c, rfl⟩ := hpow z hz
    exact (hcomm.zpow_left c).eq
  · have h1 : (x : K) ^ (a + 1) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hord]; exact_mod_cast h)
    have h2 : (x : K) ^ a = (x : K)⁻¹ := by
      rw [zpow_add_one, mul_eq_one_iff_eq_inv] at h1
      exact h1
    have hinv : g * (x : K) * g⁻¹ = (x : K)⁻¹ := by rw [← ha, h2]
    intro y hy
    obtain ⟨c, rfl⟩ := hpow y hy
    rw [← conj_zpow, hinv, inv_zpow]

end F918V3E2

end CFSG.Quasithin

module

public import CFSG.Quasithin.EmptyFaithful.S151S8C1

public section

namespace CFSG.Quasithin.S151S8C2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Lift

variable {G Gb : Type} [Group G] [Group Gb] [Finite G] [Finite Gb] (π : G →* Gb)

omit [Finite Gb] in
theorem inf_ker_le_pCoreOf (hK : IsPGroup 2 ↥π.ker) (A : Subgroup G) :
    A ⊓ π.ker ≤ pCoreOf 2 A := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    (hK.to_le inf_le_right)
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun n hn => ⟨A.mul_mem (A.mul_mem hg hn.1) (A.inv_mem hg), ?_⟩
  refine MonoidHom.mem_ker.mpr ?_
  rw [map_mul, map_mul, MonoidHom.mem_ker.mp hn.2, mul_one, map_inv, mul_inv_cancel]

theorem map_pCoreOf_eq (hK : IsPGroup 2 ↥π.ker) (A : Subgroup G) :
    (pCoreOf 2 A).map π = pCoreOf 2 (A.map π) := by
  refine le_antisymm (CFSG.LieType.BorelTits.map_pCoreOf_le π A) ?_
  intro y hy
  obtain ⟨a, haA, rfl⟩ := CFSG.LieType.BorelTits.pCoreOf_le 2 (A.map π) hy
  set R : Subgroup G := A ⊓ (pCoreOf 2 (A.map π)).comap π with hR
  have hRn : A ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun r hr => ⟨A.mul_mem (A.mul_mem hg hr.1) (A.inv_mem hg), ?_⟩
    have h1 : π r ∈ pCoreOf 2 (A.map π) := hr.2
    have h2 : π g ∈ Subgroup.normalizer (pCoreOf 2 (A.map π) : Set Gb) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (A.map π) ⟨g, hg, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp h2 (π r)).mp h1
    simpa using this
  have hRp : IsPGroup 2 ↥R := by
    rintro ⟨r, hrA, hrP⟩
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (A.map π)) ⟨π r, hrP⟩
    have hm' : π r ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have hker : r ^ 2 ^ m ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hm'
    obtain ⟨n, hn⟩ := hK ⟨r ^ 2 ^ m, hker⟩
    have hn' : (r ^ 2 ^ m) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    exact ⟨m + n, Subtype.ext (by simpa [pow_add, pow_mul] using hn')⟩
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hRn hRp
  exact ⟨a, hle ⟨haA, hy⟩, rfl⟩

theorem charTwo_of_map (hK : IsPGroup 2 ↥π.ker) {A : Subgroup G} (h : CharTwo (A.map π)) :
    CharTwo A := by
  rintro x ⟨hxA, hxC⟩
  have h1 : π x ∈ A.map π ⊓ Subgroup.centralizer (pCoreOf 2 (A.map π) : Set Gb) := by
    refine ⟨⟨x, hxA, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [← map_pCoreOf_eq π hK A] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    have := Subgroup.mem_centralizer_iff.mp hxC p hp
    rw [← map_mul, ← map_mul, this]
  have h2 := h h1
  rw [← map_pCoreOf_eq π hK A] at h2
  obtain ⟨p, hp, hpx⟩ := h2
  have hpA : p ∈ A := CFSG.LieType.BorelTits.pCoreOf_le 2 A hp
  have hk : p⁻¹ * x ∈ A ⊓ π.ker :=
    ⟨A.mul_mem (A.inv_mem hpA) hxA,
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hpx, inv_mul_cancel])⟩
  have hk' := inf_ker_le_pCoreOf π hK A hk
  have := (pCoreOf 2 A).mul_mem hp hk'
  simpa using this

theorem map_twoResidual (A : Subgroup G) :
    (twoResidual A).map π = twoResidual (A.map π) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    have hN : A ≤ Subgroup.normalizer ((A ⊓ (twoResidual (A.map π)).comap π : Subgroup G) : Set G) := by
      intro g hg
      refine Subgroup.mem_normalizer_fintype fun n hn => ⟨A.mul_mem (A.mul_mem hg hn.1) (A.inv_mem hg), ?_⟩
      have h2 : π g ∈ Subgroup.normalizer (twoResidual (A.map π) : Set Gb) :=
        le_normalizer_twoResidual (A.map π) ⟨g, hg, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp h2 (π n)).mp hn.2
      simpa using this
    have h2q : ∀ y ∈ A, ∃ k : ℕ, y ^ 2 ^ k ∈ A ⊓ (twoResidual (A.map π)).comap π := by
      intro y hy
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (A.map π) (π y) ⟨y, hy, rfl⟩
      exact ⟨k, A.pow_mem hy _, by simpa using hk⟩
    exact (twoResidual_le_of_isTwoQuotient inf_le_left hN h2q).trans inf_le_right
  · refine twoResidual_le_of_isTwoQuotient (Subgroup.map_mono (twoResidual_le A)) ?_ ?_
    · exact (Subgroup.map_mono (le_normalizer_twoResidual A)).trans (Subgroup.le_normalizer_map π)
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient A a ha
      exact ⟨k, ⟨a ^ 2 ^ k, hk, by simp⟩⟩

omit [Finite G] [Finite Gb] in
theorem exists_three_lift (hK : IsPGroup 2 ↥π.ker) {a₀ : G} {j : ℕ} (hj : π a₀ ^ 3 ^ j = 1) :
    ∃ c : ℕ, π (a₀ ^ c) = π a₀ ∧ ∃ i : ℕ, orderOf (a₀ ^ c) = 3 ^ i := by
  have hk : a₀ ^ 3 ^ j ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hj
  obtain ⟨m, hm⟩ := hK ⟨a₀ ^ 3 ^ j, hk⟩
  have hm' : (a₀ ^ 3 ^ j) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hcop : Nat.Coprime (3 ^ j) (2 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨c, ?_, ?_⟩
  · rw [map_pow]
    have hord : orderOf (π a₀) ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hj
    have : c ≡ 1 [MOD orderOf (π a₀)] := Nat.ModEq.of_dvd hord hc1
    rw [← pow_eq_pow_iff_modEq] at this
    simpa using this
  · have hdvd2 : 2 ^ m ∣ c := (Nat.modEq_zero_iff_dvd).mp hc2
    obtain ⟨u, hu⟩ := hdvd2
    have h1 : (a₀ ^ c) ^ 3 ^ j = 1 := by
      have e : (a₀ ^ c) ^ 3 ^ j = ((a₀ ^ 3 ^ j) ^ 2 ^ m) ^ u := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, hu]
        congr 1
        ring
      rw [e, hm', one_pow]
    have hdvd : orderOf (a₀ ^ c) ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one h1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact ⟨i, hi⟩

omit [Finite G] [Finite Gb] in
theorem map_oPrimeResidualOf (hK : IsPGroup 2 ↥π.ker) (A : Subgroup G) :
    (CFSG.Quasithin.oPrimeResidualOf 3 A).map π = CFSG.Quasithin.oPrimeResidualOf 3 (A.map π) := by
  unfold CFSG.Quasithin.oPrimeResidualOf
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro _ ⟨x, ⟨hxA, k, hk⟩, rfl⟩
    refine ⟨⟨x, hxA, rfl⟩, ?_⟩
    have : orderOf (π x) ∣ 3 ^ k := hk ▸ orderOf_map_dvd π x
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp this
    exact ⟨i, hi⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨⟨a₀, ha₀A, rfl⟩, k, hk⟩
    have hj : π a₀ ^ 3 ^ k = 1 := hk ▸ pow_orderOf_eq_one _
    obtain ⟨c, hpa, i, hi⟩ := exists_three_lift π hK hj
    exact Subgroup.subset_closure ⟨a₀ ^ c, ⟨A.pow_mem ha₀A c, i, hi⟩, hpa⟩

theorem numC126_of_map (hK : IsPGroup 2 ↥π.ker) {H : Subgroup G} (h : NumC126 (H.map π)) :
    NumC126 H := by
  have hQ : (twoResidual H).map π = twoResidual (H.map π) := map_twoResidual π H
  have hP : (pCoreOf 2 (twoResidual H)).map π = pCoreOf 2 (twoResidual (H.map π)) := by
    rw [map_pCoreOf_eq π hK, hQ]
  refine ⟨fun x hx => ?_, fun x hx hx3 => ?_⟩
  · have hxb : π x ∈ twoResidual (H.map π) := hQ ▸ Subgroup.mem_map_of_mem π hx
    obtain ⟨k, hk⟩ := h.1 (π x) hxb
    rw [← hP] at hk
    obtain ⟨y, hy, hyx⟩ := hk
    refine ⟨k, ?_⟩
    have hyQ : y ∈ twoResidual H := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
    have hz : y⁻¹ * x ^ 3 ^ k ∈ twoResidual H ⊓ π.ker :=
      ⟨(twoResidual H).mul_mem ((twoResidual H).inv_mem hyQ) ((twoResidual H).pow_mem hx _),
        MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, map_pow, hyx, inv_mul_cancel])⟩
    have hz' := inf_ker_le_pCoreOf π hK (twoResidual H) hz
    have := (pCoreOf 2 (twoResidual H)).mul_mem hy hz'
    simpa using this
  · have hxb : π x ∈ twoResidual (H.map π) := hQ ▸ Subgroup.mem_map_of_mem π hx
    have hne : π x ≠ 1 := by
      intro h1
      have hxk : x ∈ π.ker := MonoidHom.mem_ker.mpr h1
      obtain ⟨m, hm⟩ := hK ⟨x, hxk⟩
      have hxm : x ^ 2 ^ m = 1 := congrArg Subtype.val hm
      have hdvd : 3 ∣ 2 ^ m := hx3 ▸ orderOf_dvd_of_pow_eq_one hxm
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      omega
    have hx3b : orderOf (π x) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine orderOf_eq_prime ?_ hne
      rw [← map_pow, ← hx3, pow_orderOf_eq_one, map_one]
    have h4 := h.2 (π x) hxb hx3b
    have hcomm : ⁅pCoreOf 2 (twoResidual (H.map π)), Subgroup.zpowers (π x)⁆ =
        (⁅pCoreOf 2 (twoResidual H), Subgroup.zpowers x⁆).map π := by
      rw [Subgroup.map_commutator, hP, MonoidHom.map_zpowers]
    rw [hcomm] at h4
    refine lt_of_lt_of_le h4 ?_
    refine Nat.card_le_card_of_surjective
      (fun d : ↥⁅pCoreOf 2 (twoResidual H), Subgroup.zpowers x⁆ =>
        (⟨π d, Subgroup.mem_map_of_mem π d.2⟩ : ↥((⁅pCoreOf 2 (twoResidual H),
          Subgroup.zpowers x⁆).map π))) ?_
    rintro ⟨y, d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩

end Lift

end CFSG.Quasithin.S151S8C2

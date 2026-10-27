module

public import CFSG.Quasithin.Background.A318PC7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.Quasithin

namespace A318P

section Cyclic3

open scoped Pointwise

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem orderOf_eq_nine {Z : Subgroup X} (hZ : Nat.card Z = 3) {j : X} (hj3 : j ^ 3 ∈ Z)
    (hj3ne : j ^ 3 ≠ 1) : orderOf j = 9 := by
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hj9 : j ^ 9 = 1 := by
    have := hZ3 _ hj3
    rw [← pow_mul] at this
    exact this
  have hd : orderOf j ∣ 9 := orderOf_dvd_of_pow_eq_one hj9
  have hd' : orderOf j ∣ 3 ^ 2 := by simpa using hd
  have hnd : ¬ orderOf j ∣ 3 := fun h => hj3ne (orderOf_dvd_iff_pow_eq_one.1 h)
  obtain ⟨i, hi, hji⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd'
  interval_cases i
  · exact absurd (by rw [hji]; norm_num) hnd
  · exact absurd (by rw [hji]; norm_num) hnd
  · simpa using hji

theorem three_elements_mem_of_arith {C Z : Subgroup X} [hC : C.Normal] [hZn : Z.Normal]
    (hZC : Z ≤ C) (hZ : Nat.card Z = 3) (h1 : ∀ c ∈ C, orderOf c = 3 → c ∈ Z) {j : X}
    (hj3 : j ^ 3 ∈ Z) (hj3ne : j ^ 3 ≠ 1) (hno : ∀ c ∈ C, (c * j) ^ 3 ≠ 1) :
    ∀ c ∈ C, (∃ k : ℕ, orderOf c = 3 ^ k) → c ∈ Z := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro c hcC ⟨k, hk⟩
  by_contra hcZ
  have hjord : orderOf j = 9 := orderOf_eq_nine hZ hj3 hj3ne
  have hjp : IsPGroup 3 (Subgroup.zpowers j) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hjord]; norm_num)
  obtain ⟨P, hjP⟩ := hjp.exists_le_sylow
  have hjP' : j ∈ (P : Subgroup X) := hjP (Subgroup.mem_zpowers j)
  have hcp : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨P₁, hcP₁⟩ := hcp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P
  set c' : X := g * c * g⁻¹ with hc'
  have hc'P : c' ∈ (P : Subgroup X) := by
    have h1 : c ∈ (P₁ : Subgroup X) := hcP₁ (Subgroup.mem_zpowers c)
    have h2 : (MulAut.conj g) c ∈ (MulAut.conj g) • (P₁ : Subgroup X) :=
      Subgroup.smul_mem_pointwise_smul c (MulAut.conj g) _ h1
    have h3 : ((g • P₁ : Sylow 3 X) : Subgroup X) = (P : Subgroup X) := by rw [hg]
    rw [Sylow.coe_subgroup_smul] at h3
    rw [← h3]
    exact h2
  have hc'C : c' ∈ C := by
    have := hC.conj_mem c hcC g
    exact this
  have hc'Z : c' ∉ Z := by
    intro h
    apply hcZ
    have := hZn.conj_mem c' h g⁻¹
    simpa [hc', mul_assoc] using this
  have hc'ord : orderOf c' = 3 ^ k := by
    rw [hc', ← hk]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · rw [pow_zero, orderOf_eq_one_iff] at hc'ord
      exact hc'Z (hc'ord ▸ Z.one_mem)
    · exact hc'Z (h1 c' hc'C (by simpa using hc'ord))
  set Q : Subgroup X := (P : Subgroup X) ⊓ C with hQ
  have hQp : IsPGroup 3 Q := P.isPGroup'.to_le inf_le_left
  have hQcyc : IsCyclic Q := isCyclic_of_unique_three hQp hZ fun r hr hr3 => h1 r hr.2 hr3
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Q)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hQp) u
  have hc'Q : c' ∈ Q := Subgroup.mem_inf.2 ⟨hc'P, hc'C⟩
  have hmem : ∀ q ∈ Q, ∃ n : ℤ, (u : X) ^ n = q := by
    intro q hq
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hu ⟨q, hq⟩)
    exact ⟨n, congrArg Subtype.val hn⟩
  have hmo : orderOf (u : X) = 3 ^ m := by rw [Subgroup.orderOf_coe]; exact hm
  have hm2 : 2 ≤ m := by
    have hdvd : orderOf c' ∣ orderOf (u : X) := by
      obtain ⟨n, hn⟩ := hmem c' hc'Q
      rw [← hn]
      exact orderOf_dvd_of_pow_eq_one (by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
          one_zpow])
    rw [hc'ord, hmo] at hdvd
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 hdvd
    omega
  have hjQ : j * (u : X) * j⁻¹ ∈ Q := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hjP' (Subgroup.mem_inf.1 u.2).1) (inv_mem hjP')
    · have := hC.conj_mem (u : X) (Subgroup.mem_inf.1 u.2).2 j
      exact this
  obtain ⟨t, ht⟩ := hmem _ hjQ
  have hj3Q : j ^ 3 ∈ Q :=
    Subgroup.mem_inf.2 ⟨pow_mem hjP' 3, hZC hj3⟩
  obtain ⟨s, hs⟩ := hmem _ hj3Q
  have hmax : orderOf j ≤ 3 ^ m := by
    rw [hjord]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  obtain ⟨i, hi⟩ := exists_cube_eq_one (by omega) hmo (t := t) (s := s) ht.symm hs.symm hmax
  have huC : (u : X) ^ i ∈ C := zpow_mem (Subgroup.mem_inf.1 u.2).2 i
  exact hno _ huC hi

end Cyclic3

section Burnside

variable {X : Type*} [Group X] [Finite X]

theorem normal_le_of_three_elements {C Z : Subgroup X} [hCnorm : C.Normal] (hZC : Z ≤ C)
    (hZ : Nat.card Z = 3) (hZc : ∀ z ∈ Z, ∀ c ∈ C, c * z = z * c)
    (h3 : ∀ c ∈ C, (∃ k : ℕ, orderOf c = 3 ^ k) → c ∈ Z) (hP : CFSG.pPrimeCore 3 X = ⊥) :
    C ≤ Z := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z'' : Subgroup ↥C := Z.subgroupOf C with hZ''
  have hZ''card : Nat.card Z'' = 3 := by
    rw [hZ'', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, hZ]
  have hZ''p : IsPGroup 3 Z'' := IsPGroup.of_card (n := 1) (by rw [hZ''card]; norm_num)
  obtain ⟨P, hZP⟩ := hZ''p.exists_le_sylow
  have hPZ : (P : Subgroup ↥C) ≤ Z'' := by
    intro g hg
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') ⟨g, hg⟩
    have hk' : orderOf ((g : ↥C) : X) = 3 ^ k := by
      rw [Subgroup.orderOf_coe]
      have := Subgroup.orderOf_coe (⟨g, hg⟩ : (P : Subgroup ↥C))
      simp only at this
      rw [this, hk]
    exact h3 _ g.2 ⟨k, hk'⟩
  have hPeq : (P : Subgroup ↥C) = Z'' := le_antisymm hPZ hZP
  have hPcard : Nat.card (P : Subgroup ↥C) = 3 := by rw [hPeq, hZ''card]
  have hPc : ∀ (z : ↥C), z ∈ (P : Subgroup ↥C) → ∀ g : ↥C, g * z = z * g := by
    intro z hz g
    rw [hPeq] at hz
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hZc _ hz _ g.2
  have hnorm : Subgroup.normalizer ((P : Subgroup ↥C) : Set ↥C) ≤
      Subgroup.centralizer ((P : Subgroup ↥C) : Set ↥C) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hPc z hz g).symm
  set φ := MonoidHom.transferSylow P hnorm with hφ
  have hN3 : ¬ 3 ∣ Nat.card φ.ker := MonoidHom.not_dvd_card_ker_transferSylow P hnorm
  have hker : ∀ c : ↥C, ¬ 3 ∣ orderOf c → c ∈ φ.ker := by
    intro c hc
    rw [MonoidHom.mem_ker]
    have h1 : orderOf (φ c) ∣ orderOf c := orderOf_map_dvd φ c
    have h2 : orderOf (φ c) ∣ 3 := by
      have := orderOf_dvd_natCard (φ c)
      rwa [hPcard] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ h1) hc
  have hord_ker : ∀ n : ↥C, n ∈ φ.ker → ¬ 3 ∣ orderOf n := by
    intro n hn hdiv
    apply hN3
    have := orderOf_dvd_natCard (⟨n, hn⟩ : φ.ker)
    rw [← Subgroup.orderOf_coe (⟨n, hn⟩ : φ.ker)] at this
    exact hdiv.trans this
  set K : Subgroup X := φ.ker.map C.subtype with hKdef
  have hKnorm : K.Normal := by
    constructor
    rintro _ ⟨n, hn, rfl⟩ g
    have hgn : g * (n : X) * g⁻¹ ∈ C := hCnorm.conj_mem _ n.2 g
    refine ⟨⟨g * (n : X) * g⁻¹, hgn⟩, hker _ ?_, rfl⟩
    have hord : orderOf (⟨g * (n : X) * g⁻¹, hgn⟩ : ↥C) = orderOf n := by
      rw [← Subgroup.orderOf_coe (⟨g * (n : X) * g⁻¹, hgn⟩ : ↥C), ← Subgroup.orderOf_coe n]
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (n : X)
      simpa [MulAut.conj_apply] using this
    rw [hord]
    exact hord_ker n hn
  have hKcop : Nat.Coprime 3 (Nat.card K) := by
    rw [hKdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3
  have hKbot : K = ⊥ := CFSG.pPrimeCore_eq_bot_iff.mp hP K hKnorm hKcop
  have hkerbot : φ.ker = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hKbot
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hkerbot
  have hcard : Nat.card ↥C ≤ 3 := by
    rw [← hPcard]
    exact Nat.card_le_card_of_injective φ hinj
  have hPtop : (P : Subgroup ↥C) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 : Nat.card (P : Subgroup ↥C) ≤ Nat.card ↥C := Subgroup.card_le_card_group _
    omega
  intro c hc
  have : (⟨c, hc⟩ : ↥C) ∈ (P : Subgroup ↥C) := by rw [hPtop]; exact Subgroup.mem_top _
  rw [hPeq] at this
  exact this

end Burnside

end A318P

end CFSG.Quasithin

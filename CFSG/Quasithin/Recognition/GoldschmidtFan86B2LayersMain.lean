module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86B2Layers

public section

namespace CFSG.Quasithin.Fan86

variable {G : Type*} [Group G]

namespace CoprimeLayer

variable {x : G} {M N : Subgroup G}

theorem relIndex_prodCent_modEq (h : CoprimeLayer x M N) :
    (prodCent x M N).relIndex M ≡ 1 [MOD 5] := by
  have hfin := h.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_cases hx1 : x = 1
  · have hM : M ≤ prodCent x M N := by
      intro m hm
      apply cent_le_prodCent x M N
      refine Subgroup.mem_inf.2 ⟨?_, hm⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg, hx1]
      simp
    rw [Subgroup.relIndex_eq_one.2 hM]
  · have hord : orderOf x = 5 := orderOf_eq_prime h.pow_five hx1
    have h1 := relIndex_centralizer_modEq M h.pgroup hord h.xM
    have h2 : (Subgroup.centralizer ({x} : Set G)).relIndex N ≡ 1 [MOD 5] := by
      have := h.finite_N
      exact relIndex_centralizer_modEq N h.pgroup_N hord h.xN
    rw [h.relIndex_centralizer_eq_mul] at h1
    have h3 := Nat.ModEq.mul_left ((prodCent x M N).relIndex M) h2
    simpa using h3.symm.trans h1

theorem relIndex_prodCent_eq_one_or (h : CoprimeLayer x M N) :
    (prodCent x M N).relIndex M = 1 ∨ 16 ≤ (prodCent x M N).relIndex M := by
  have hfin := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := h.relIndex_prodCent_modEq
  obtain ⟨k, hk⟩ := h.pgroup.index ((prodCent x M N).subgroupOf M)
  have hk' : (prodCent x M N).relIndex M = 2 ^ k := hk
  rw [hk'] at hmod ⊢
  by_cases h4 : k < 4
  · interval_cases k
    · left
      norm_num
    all_goals exact absurd hmod (by norm_num [Nat.ModEq])
  · right
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem relIndex_prodCent_eq_one_iff (h : CoprimeLayer x M N) :
    (prodCent x M N).relIndex M = 1 ↔ ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ ∈ N := by
  rw [Subgroup.relIndex_eq_one]
  constructor
  · intro hMD m hm
    have hnorm : Subgroup.centralizer ({x} : Set G) ⊓ M ≤ Subgroup.normalizer (N : Set G) :=
      inf_le_right.trans h.le_normalizer
    have hm' : m ∈ ((Subgroup.centralizer ({x} : Set G) ⊓ M ⊔ N : Subgroup G) : Set G) := by
      have : prodCent x M N = (Subgroup.centralizer ({x} : Set G) ⊓ M) ⊔ N := sup_comm _ _
      rw [← this]
      exact hMD hm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hm'
    obtain ⟨c, hc, n, hn, rfl⟩ := hm'
    have hcx : x * c = c * x := Subgroup.mem_centralizer_iff.1 hc.1 x rfl
    have hcM : c ∈ M := hc.2
    have e : x * (c * n) * x⁻¹ * (c * n)⁻¹ = c * (x * n * x⁻¹ * n⁻¹) * c⁻¹ := by
      calc x * (c * n) * x⁻¹ * (c * n)⁻¹ = (x * c) * n * x⁻¹ * (n⁻¹ * c⁻¹) := by group
        _ = (c * x) * n * x⁻¹ * (n⁻¹ * c⁻¹) := by rw [hcx]
        _ = c * (x * n * x⁻¹ * n⁻¹) * c⁻¹ := by group
    rw [e]
    exact h.conj_mem hcM (Subgroup.mul_mem N (h.xN n hn) (Subgroup.inv_mem N hn))
  · intro hcomm m hm
    obtain ⟨n, hn, hfix⟩ := h.exists_fixed hm (hcomm m hm)
    have hmn : m * n ∈ Subgroup.centralizer ({x} : Set G) ⊓ M := by
      refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mul_mem M hm (h.le hn)⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact mul_inv_eq_iff_eq_mul.1 hfix
    have e : m = (m * n) * n⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (cent_le_prodCent x M N hmn)
      (Subgroup.inv_mem _ (le_prodCent x M N hn))

end CoprimeLayer

theorem three_layers {x : G} {Q N1 N2 : Subgroup G} [Finite Q] (hQ : IsPGroup 2 Q)
    (hx : x ^ 5 = 1) (h1Q : N1 ≤ Q) (h21 : N2 ≤ N1)
    (hn1 : (N1.subgroupOf Q).Normal) (hn2 : (N2.subgroupOf N1).Normal)
    (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hxN1 : ∀ n ∈ N1, x * n * x⁻¹ ∈ N1)
    (hxN2 : ∀ n ∈ N2, x * n * x⁻¹ ∈ N2)
    (a1 : ∃ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∉ N1) (a2 : ∃ n ∈ N1, x * n * x⁻¹ * n⁻¹ ∉ N2)
    (a3 : ∃ m ∈ N2, x * m * x⁻¹ * m⁻¹ ≠ 1) :
    2 ^ 12 ≤ (Subgroup.centralizer ({x} : Set G)).relIndex Q := by
  have hL1 : CoprimeLayer x Q N1 := ⟨hx, h1Q, hn1, hxQ, hxN1, inferInstance, hQ⟩
  have hfin1 : Finite N1 := hL1.finite_N
  have hp1 : IsPGroup 2 N1 := hL1.pgroup_N
  have hL2 : CoprimeLayer x N1 N2 := ⟨hx, h21, hn2, hxN1, hxN2, hfin1, hp1⟩
  have hfin2 : Finite N2 := hL2.finite_N
  have hp2 : IsPGroup 2 N2 := hL2.pgroup_N
  have hx1 : x ≠ 1 := by
    rintro rfl
    obtain ⟨q, hq, hnq⟩ := a1
    apply hnq
    simp
  have hord : orderOf x = 5 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime hx hx1
  have f1 : 16 ≤ (prodCent x Q N1).relIndex Q := by
    rcases hL1.relIndex_prodCent_eq_one_or with h | h
    · exfalso
      obtain ⟨q, hq, hnq⟩ := a1
      exact hnq ((hL1.relIndex_prodCent_eq_one_iff).1 h q hq)
    · exact h
  have f2 : 16 ≤ (prodCent x N1 N2).relIndex N1 := by
    rcases hL2.relIndex_prodCent_eq_one_or with h | h
    · exfalso
      obtain ⟨n, hn, hnn⟩ := a2
      exact hnn ((hL2.relIndex_prodCent_eq_one_iff).1 h n hn)
    · exact h
  have f3 : 16 ≤ (Subgroup.centralizer ({x} : Set G)).relIndex N2 := by
    rcases relIndex_centralizer_eq_one_or N2 hp2 hord hxN2 with h | h
    · exfalso
      have hle : N2 ≤ Subgroup.centralizer ({x} : Set G) := Subgroup.relIndex_eq_one.1 h
      obtain ⟨m, hm, hne⟩ := a3
      apply hne
      have hcomm : x * m = m * x := Subgroup.mem_centralizer_iff.1 (hle hm) x rfl
      rw [hcomm]
      group
    · exact h
  rw [hL1.relIndex_centralizer_eq_mul, hL2.relIndex_centralizer_eq_mul]
  calc 2 ^ 12 = 16 * (16 * 16) := by norm_num
    _ ≤ _ := Nat.mul_le_mul f1 (Nat.mul_le_mul f2 f3)

end CFSG.Quasithin.Fan86

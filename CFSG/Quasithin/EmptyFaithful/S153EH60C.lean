module

public import CFSG.Quasithin.EmptyFaithful.S153EH60B

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace S153EH60

variable {X : Type*} [Group X]

theorem mem_or_mul_mem_of_relIndex_two {A K : Subgroup X} (h : K.relIndex A = 2) {b x : X}
    (hb : b ∈ A) (hx : x ∈ A) (hxK : x ∉ K) : b ∈ K ∨ b * x ∈ K := by
  obtain ⟨a₀, -, -, h₀⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp h
  have h1 : x⁻¹ * a₀ ∈ K := by
    rcases h₀ x⁻¹ (A.inv_mem hx) with h2 | h2
    · exact h2
    · exact absurd (K.inv_mem_iff.mp h2) hxK
  by_cases hbK : b ∈ K
  · exact Or.inl hbK
  · right
    have h2 : b * a₀ ∈ K := by
      rcases h₀ b hb with h2 | h2
      · exact h2
      · exact absurd h2 hbK
    have := K.mul_mem h2 (K.inv_mem h1)
    simpa [mul_assoc] using this

theorem exists_preimage_order_three {K : Subgroup X} (π : L32 →* ↥K) (hπ : Function.Bijective π)
    {a : X} (ha : a ∈ K) (ha3 : orderOf a = 3) : ∃ γ : L32, π γ = ⟨a, ha⟩ ∧ orderOf γ = 3 := by
  obtain ⟨γ, hγ⟩ := hπ.2 ⟨a, ha⟩
  refine ⟨γ, hγ, ?_⟩
  rw [← orderOf_injective π hπ.1 γ, hγ]
  exact (Subgroup.orderOf_coe ⟨a, ha⟩).symm.trans ha3

theorem exists_inv_conj_mem {K : Subgroup X} (π : L32 →* ↥K) (hπ : Function.Bijective π) {a : X}
    (ha : a ∈ K) (ha3 : orderOf a = 3) : ∃ j ∈ K, j * a * j⁻¹ = a⁻¹ := by
  obtain ⟨γ, hγ, hγ3⟩ := exists_preimage_order_three π hπ ha ha3
  obtain ⟨η, hη⟩ := exists_inv_conj hγ3
  refine ⟨((π η : ↥K) : X), (π η).2, ?_⟩
  have h1 := congrArg π hη
  simp only [map_mul, map_inv] at h1
  rw [hγ] at h1
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem exists_outer_centralizer [Finite X] {A K : Subgroup X} (hKA : K ≤ A) (hidx : K.relIndex A = 2)
    (hK : Nat.card K = 168) (π : L32 →* ↥K) (hπ : Function.Bijective π) {a : X} (ha : a ∈ K)
    (ha3 : orderOf a = 3) : ∃ x ∈ A, x ∉ K ∧ x * a = a * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnorm : ∀ x ∈ A, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    have hN : (K.subgroupOf A).Normal := Subgroup.normal_of_index_eq_two (by rwa [Subgroup.relIndex] at hidx)
    intro x hx k hk
    have := hN.conj_mem ⟨k, hKA hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨x₀, hx₀A, hx₀K⟩ : ∃ x₀ ∈ A, x₀ ∉ K := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.relIndex_eq_one.mpr (show A ≤ K from hcon)
    omega
  have hb : x₀ * a * x₀⁻¹ ∈ K := hnorm x₀ hx₀A a ha
  have hb3 : orderOf (x₀ * a * x₀⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ha3
  have hP : Subgroup.zpowers a ≤ K ∧ IsPGroup 3 (Subgroup.zpowers a) ∧
      ¬ 3 ∣ (Subgroup.zpowers a).relIndex K := by
    have hle : Subgroup.zpowers a ≤ K := (Subgroup.zpowers_le).mpr ha
    refine ⟨hle, IsPGroup.of_card (n := 1) ?_, ?_⟩
    · rw [Nat.card_zpowers, ha3]
      norm_num
    · have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers a) K
      rw [inf_eq_left.mpr hle, Nat.card_zpowers, ha3, hK] at h1
      omega
  have hQ : IsPGroup 3 (Subgroup.zpowers (x₀ * a * x₀⁻¹)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hb3]
    norm_num
  obtain ⟨k, hkK, hk⟩ := S153E.exists_conj_of_isSylow hP hQ ((Subgroup.zpowers_le).mpr hb)
  have hk' : k * (x₀ * a * x₀⁻¹) * k⁻¹ ∈ Subgroup.zpowers a :=
    mem_conjSubgroup_iff.mp (hk (Subgroup.mem_zpowers _))
  have hk3 : orderOf (k * (x₀ * a * x₀⁻¹) * k⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hb3
  have hx₁A : k * x₀ ∈ A := A.mul_mem (hKA hkK) hx₀A
  have hx₁K : k * x₀ ∉ K := fun h => hx₀K (by simpa using K.mul_mem (K.inv_mem hkK) h)
  have hconj : (k * x₀) * a * (k * x₀)⁻¹ = k * (x₀ * a * x₀⁻¹) * k⁻¹ := by group
  rcases eq_or_eq_inv_of_mem_zpowers ha3 hk' hk3 with h | h
  · refine ⟨k * x₀, hx₁A, hx₁K, ?_⟩
    rw [← hconj] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · obtain ⟨j, hjK, hj⟩ := exists_inv_conj_mem π hπ ha ha3
    refine ⟨j * (k * x₀), A.mul_mem (hKA hjK) hx₁A, fun hmem => hx₁K ?_, ?_⟩
    · simpa using K.mul_mem (K.inv_mem hjK) hmem
    · have h2 : j * (k * x₀) * a * (j * (k * x₀))⁻¹ = a := by
        calc j * (k * x₀) * a * (j * (k * x₀))⁻¹ = j * ((k * x₀) * a * (k * x₀)⁻¹) * j⁻¹ := by group
          _ = j * a⁻¹ * j⁻¹ := by rw [hconj, h]
          _ = (j * a * j⁻¹)⁻¹ := by group
          _ = a := by rw [hj, inv_inv]
      exact mul_inv_eq_iff_eq_mul.mp h2

theorem odd_card_inf_centralizer [Finite X] {K : Subgroup X} (π : L32 →* ↥K)
    (hπ : Function.Bijective π) {a : X} (ha : a ∈ K) (ha3 : orderOf a = 3) :
    Odd (Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff]
  by_contra hne
  have h2 : 2 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) := by omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨γ, hγ, hγ3⟩ := exists_preimage_order_three π hπ ha ha3
  have hyK : (y : X) ∈ K := (y.2).1
  obtain ⟨η, hη⟩ := hπ.2 ⟨(y : X), hyK⟩
  have hy2 : orderOf (y : X) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hη2 : orderOf η = 2 := by
    rw [← orderOf_injective π hπ.1 η, hη]
    exact (Subgroup.orderOf_coe ⟨(y : X), hyK⟩).symm.trans hy2
  refine no_comm_of_order hγ3 hη2 (hπ.1 ?_)
  rw [map_mul, map_mul, hγ, hη]
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (y.2).2 a rfl

theorem card_inf_centralizer [Finite X] {A K : Subgroup X} (hKA : K ≤ A) (hidx : K.relIndex A = 2)
    (hK : Nat.card K = 168) (π : L32 →* ↥K) (hπ : Function.Bijective π) {a : X} (ha : a ∈ K)
    (ha3 : orderOf a = 3) :
    ∃ c : ℕ, Odd c ∧ Nat.card ↥(A ⊓ Subgroup.centralizer ({a} : Set X)) = 2 * c := by
  obtain ⟨x, hxA, hxK, hxa⟩ := exists_outer_centralizer hKA hidx hK π hπ ha ha3
  refine ⟨Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set X)), odd_card_inf_centralizer π hπ ha ha3, ?_⟩
  set C : Subgroup X := A ⊓ Subgroup.centralizer ({a} : Set X) with hC
  set CK : Subgroup X := K ⊓ Subgroup.centralizer ({a} : Set X) with hCK
  have hle : CK ≤ C := inf_le_inf_right _ hKA
  have hx_in : x ∈ C := ⟨hxA, Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
    exact hxa.symm⟩
  have h2 : CK.relIndex C = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨x, hx_in, fun hx => hxK hx.1, fun b hb => ?_⟩
    rcases mem_or_mul_mem_of_relIndex_two hidx hb.1 hxA hxK with h | h
    · exact Or.inr ⟨h, hb.2⟩
    · exact Or.inl ⟨h, (Subgroup.centralizer ({a} : Set X)).mul_mem hb.2 hx_in.2⟩
  have h3 := Subgroup.relIndex_mul_card CK C
  rw [inf_eq_left.mpr hle, h2] at h3
  exact h3.symm

end S153EH60

end CFSG.Quasithin

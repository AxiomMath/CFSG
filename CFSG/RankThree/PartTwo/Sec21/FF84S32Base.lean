module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3P
public import CFSG.GH74.GLS.Balance.Bender.ExtSylow

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.GH74.GLS.Balance (IsSylowIn)

section SylowHelpers
variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_iff_isSylowIn {p : ℕ} [Fact p.Prime] {P K : Subgroup G} :
    IsSylowOf p P K ↔ IsSylowIn p P K := by
  rw [CFSG.GH74.GLS.Balance.BenderExt.isSylowIn_iff_isSylowOf]
  constructor
  · rintro ⟨hPK, hP, hcop⟩
    have hi : ¬ p ∣ (P.subgroupOf K).index :=
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hcop
    have hH : IsPGroup p ↥(P.subgroupOf K) := hP.comap_subtype
    refine ⟨CFSG.Quasithin.SBc17.sylowOfIndex _ hH hi, ?_⟩
    change (P.subgroupOf K).map K.subtype = P
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPK]
  · rintro ⟨Q, rfl⟩
    refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩
    have : ((Q : Subgroup ↥K).map K.subtype).subgroupOf K = (Q : Subgroup ↥K) :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    change Nat.Coprime p (((Q : Subgroup ↥K).map K.subtype).subgroupOf K).index
    rw [this]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 Q.not_dvd_index

theorem exists_isSylowOf_ge' {p : ℕ} [Fact p.Prime] {P K : Subgroup G} (hPK : P ≤ K)
    (hP : IsPGroup p P) : ∃ T, IsSylowOf p T K ∧ P ≤ T := by
  have hP' : IsPGroup p ↥(P.subgroupOf K) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥K).map K.subtype, ?_, ?_⟩
  · rw [isSylowOf_iff_isSylowIn, CFSG.GH74.GLS.Balance.BenderExt.isSylowIn_iff_isSylowOf]
    exact ⟨Q, rfl⟩
  · intro x hx
    have : (⟨x, hPK hx⟩ : ↥K) ∈ P.subgroupOf K := hx
    exact ⟨_, hQ this, rfl⟩

end SylowHelpers

section Coord
variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem cmul (h : FF84Sec3 b L B b₁ b₂) (a c d a' c' d' : ℤ) :
    (b ^ a * b₁ ^ c * b₂ ^ d) * (b ^ a' * b₁ ^ c' * b₂ ^ d') =
      b ^ (a + a') * b₁ ^ (c + c') * b₂ ^ (d + d') := by
  haveI : IsMulCommutative ↥B := h.mono.1.1.toIsMulCommutative
  let β : ↥B := ⟨b, mem_B_b h⟩
  let β₁ : ↥B := ⟨b₁, mem_B_b₁ h⟩
  let β₂ : ↥B := ⟨b₂, mem_B_b₂ h⟩
  have key : (β ^ a * β₁ ^ c * β₂ ^ d) * (β ^ a' * β₁ ^ c' * β₂ ^ d') =
      β ^ (a + a') * β₁ ^ (c + c') * β₂ ^ (d + d') := by
    simp only [zpow_add]
    ac_rfl
  exact congrArg Subtype.val key

theorem zpow_eq_one_of_dvd3 {g : G} (hg : g ^ 3 = 1) {k : ℤ} (hk : (3 : ℤ) ∣ k) : g ^ k = 1 := by
  obtain ⟨t, rfl⟩ := hk
  rw [zpow_mul]
  have : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
  rw [this, one_zpow]

theorem ceq (h : FF84Sec3 b L B b₁ b₂) {a c d a' c' d' : ℤ} :
    b ^ a * b₁ ^ c * b₂ ^ d = b ^ a' * b₁ ^ c' * b₂ ^ d' ↔
      (3 : ℤ) ∣ a - a' ∧ (3 : ℤ) ∣ c - c' ∧ (3 : ℤ) ∣ d - d' := by
  constructor
  · intro he
    have h1 : b ^ (a + -a') * b₁ ^ (c + -c') * b₂ ^ (d + -d') = 1 := by
      rw [← cmul h, he, cmul h]; simp
    obtain ⟨x, y, z⟩ := P_basis h _ _ _ h1
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    have e : b ^ a * b₁ ^ c * b₂ ^ d = (b ^ a' * b₁ ^ c' * b₂ ^ d') *
        (b ^ (a - a') * b₁ ^ (c - c') * b₂ ^ (d - d')) := by
      rw [cmul h]; simp
    rw [e, zpow_eq_one_of_dvd3 (pow3_of_mem_B h (mem_B_b h)) h1,
      zpow_eq_one_of_dvd3 (pow3_of_mem_B h (mem_B_b₁ h)) h2,
      zpow_eq_one_of_dvd3 (pow3_of_mem_B h (mem_B_b₂ h)) h3]
    simp

theorem six_coord {x : G} (hx : x ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G)) :
    ∃ a c d : ℤ, x = b ^ a * b₁ ^ c * b₂ ^ d ∧
      ((a = 1 ∧ c = 0 ∧ d = 0) ∨ (a = -1 ∧ c = 0 ∧ d = 0) ∨ (a = 0 ∧ c = 1 ∧ d = 0) ∨
        (a = 0 ∧ c = -1 ∧ d = 0) ∨ (a = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ c = 0 ∧ d = -1)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, 0, by simp, by simp⟩
  · exact ⟨-1, 0, 0, by simp, by simp⟩
  · exact ⟨0, 1, 0, by simp, by simp⟩
  · exact ⟨0, -1, 0, by simp, by simp⟩
  · exact ⟨0, 0, 1, by simp, by simp⟩
  · exact ⟨0, 0, -1, by simp, by simp⟩

theorem b_ne_of_mem_E (h : FF84Sec3 b L B b₁ b₂) {x : G}
    (hx : x ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G)) : b ≠ x := by
  intro hbx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have := (ceq h (a := 1) (c := 0) (d := 0) (a' := 0) (c' := 1) (d' := 0)).1 (by simpa using hbx)
    omega
  · have := (ceq h (a := 1) (c := 0) (d := 0) (a' := 0) (c' := -1) (d' := 0)).1 (by simpa using hbx)
    omega
  · have := (ceq h (a := 1) (c := 0) (d := 0) (a' := 0) (c' := 0) (d' := 1)).1 (by simpa using hbx)
    omega
  · have := (ceq h (a := 1) (c := 0) (d := 0) (a' := 0) (c' := 0) (d' := -1)).1 (by simpa using hbx)
    omega

theorem conj_pair_cases (h : FF84Sec3 b L B b₁ b₂) {n : G} (hn : n ∈ Nor B)
    (hc : n * (b₁ * b₂) * n⁻¹ = b₁ * b₂) :
    (n * b₁ * n⁻¹ = b₁ ∧ n * b₂ * n⁻¹ = b₂) ∨ (n * b₁ * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b₁) := by
  have hv := h.mono.2.2.1 n hn b₁ (by simp)
  have hw := h.mono.2.2.1 n hn b₂ (by simp)
  have hvw : (n * b₁ * n⁻¹) * (n * b₂ * n⁻¹) = b₁ * b₂ := by rw [← hc]; group
  obtain ⟨a, c, d, hva, hcase⟩ := six_coord hv
  obtain ⟨a', c', d', hwa, hcase'⟩ := six_coord hw
  rw [hva, hwa, cmul h] at hvw
  have h0 : b ^ (a + a') * b₁ ^ (c + c') * b₂ ^ (d + d') =
      b ^ (0 : ℤ) * b₁ ^ (1 : ℤ) * b₂ ^ (1 : ℤ) := by simpa using hvw
  obtain ⟨e1, e2, e3⟩ := (ceq h).1 h0
  have hcc : (a = 0 ∧ c = 1 ∧ d = 0 ∧ a' = 0 ∧ c' = 0 ∧ d' = 1) ∨
      (a = 0 ∧ c = 0 ∧ d = 1 ∧ a' = 0 ∧ c' = 1 ∧ d' = 0) := by omega
  rcases hcc with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · left; simp at hva hwa; exact ⟨hva, hwa⟩
  · right; simp at hva hwa; exact ⟨hva, hwa⟩

theorem conj_pair_cases_inv (h : FF84Sec3 b L B b₁ b₂) {n : G} (hn : n ∈ Nor B)
    (hc : n * (b₁ * b₂) * n⁻¹ = b₁ * b₂) :
    (n⁻¹ * b₁ * n = b₁ ∧ n⁻¹ * b₂ * n = b₂) ∨ (n⁻¹ * b₁ * n = b₂ ∧ n⁻¹ * b₂ * n = b₁) := by
  rcases conj_pair_cases h hn hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have e1 := mul_inv_eq_iff_eq_mul.1 h1
    have e2 := mul_inv_eq_iff_eq_mul.1 h2
    constructor
    · calc n⁻¹ * b₁ * n = n⁻¹ * (b₁ * n) := by group
        _ = b₁ := by rw [← e1]; group
    · calc n⁻¹ * b₂ * n = n⁻¹ * (b₂ * n) := by group
        _ = b₂ := by rw [← e2]; group
  · right
    constructor
    · calc n⁻¹ * b₁ * n = n⁻¹ * (n * b₂ * n⁻¹) * n := by rw [h2]
        _ = b₂ := by group
    · calc n⁻¹ * b₂ * n = n⁻¹ * (n * b₁ * n⁻¹) * n := by rw [h1]
        _ = b₁ := by group

theorem conj_b_cases (h : FF84Sec3 b L B b₁ b₂) {n : G} (hn : n ∈ Nor B)
    (hc : n * (b₁ * b₂) * n⁻¹ = b₁ * b₂) : n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹ := by
  have hu := h.mono.2.2.1 n hn b (by simp)
  have hinv := conj_pair_cases_inv h hn hc
  have hbu : ∀ u : G, n * b * n⁻¹ = u → b = n⁻¹ * u * n := fun u hu => by rw [← hu]; group
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with hu | hu | hu | hu | hu | hu
  · exact Or.inl hu
  · exact Or.inr hu
  · exfalso
    have hb := hbu _ hu
    rcases hinv with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at hb
    · exact b_ne_of_mem_E h (x := b₁) (by simp) hb
    · exact b_ne_of_mem_E h (x := b₂) (by simp) hb
  · exfalso
    have hb := hbu _ hu
    have hb' : b = (n⁻¹ * b₁ * n)⁻¹ := by rw [hb]; group
    rcases hinv with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at hb'
    · exact b_ne_of_mem_E h (x := b₁⁻¹) (by simp) hb'
    · exact b_ne_of_mem_E h (x := b₂⁻¹) (by simp) hb'
  · exfalso
    have hb := hbu _ hu
    rcases hinv with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hb
    · exact b_ne_of_mem_E h (x := b₂) (by simp) hb
    · exact b_ne_of_mem_E h (x := b₁) (by simp) hb
  · exfalso
    have hb := hbu _ hu
    have hb' : b = (n⁻¹ * b₂ * n)⁻¹ := by rw [hb]; group
    rcases hinv with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hb'
    · exact b_ne_of_mem_E h (x := b₂⁻¹) (by simp) hb'
    · exact b_ne_of_mem_E h (x := b₁⁻¹) (by simp) hb'

theorem sq_cenS_B (h : FF84Sec3 b L B b₁ b₂) {n : G} (hn : n ∈ Nor B)
    (hc : n * (b₁ * b₂) * n⁻¹ = b₁ * b₂) : n ^ 2 ∈ CenS B := by
  have hsq : ∀ x : G, n ^ 2 * x * (n ^ 2)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ := fun x => by rw [pow_two, mul_inv_rev]; group
  have hcen : ∀ x : G, n ^ 2 * x * (n ^ 2)⁻¹ = x → x ∈ Cen (n ^ 2) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 hx).symm
  have hb : n ^ 2 * b * (n ^ 2)⁻¹ = b := by
    rw [hsq]
    rcases conj_b_cases h hn hc with h1 | h1
    · rw [h1, h1]
    · rw [h1]
      have : n * b⁻¹ * n⁻¹ = (n * b * n⁻¹)⁻¹ := by group
      rw [this, h1]; group
  have hb₁ : n ^ 2 * b₁ * (n ^ 2)⁻¹ = b₁ ∧ n ^ 2 * b₂ * (n ^ 2)⁻¹ = b₂ := by
    rw [hsq, hsq]
    rcases conj_pair_cases h hn hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> simp only [h1, h2]
    · constructor <;> simp only [h1, h2]
  have hBle : B ≤ Cen (n ^ 2) := B_le_of_mem h (hcen _ hb) (hcen _ hb₁.1) (hcen _ hb₁.2)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.1 (hBle hx)

theorem three_elt_cenS_B (h : FF84Sec3 b L B b₁ b₂) {n : G} (hn : n ∈ Nor B)
    (hc : n * (b₁ * b₂) * n⁻¹ = b₁ * b₂) {k : ℕ} (hk : n ^ 3 ^ k = 1) : n ∈ CenS B := by
  have h2 := sq_cenS_B h hn hc
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have e : n ^ (2 * (m + 1)) = n := by
    rw [show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, hk, one_mul]
  rw [← e, pow_mul]
  exact Subgroup.pow_mem _ h2 _

end Coord

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end

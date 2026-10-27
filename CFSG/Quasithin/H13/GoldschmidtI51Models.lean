module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.Sp62Over

public section

namespace CFSG.Quasithin.H13.A6

open Matrix

namespace SL3

theorem core_X1 : ∀ n : S, (∀ g : S, InX1 (g⁻¹ * n * g)) → n = 1 := by decide +kernel

theorem core_X2 : ∀ n : S, (∀ g : S, InX2 (g⁻¹ * n * g)) → n = 1 := by decide +kernel

theorem center_X1 : ∀ n : S, InX1 n → (∀ a : S, InX1 a → a * n = n * a) → n = 1 := by
  decide +kernel

theorem center_X2 : ∀ n : S, InX2 n → (∀ a : S, InX2 a → a * n = n * a) → n = 1 := by
  decide +kernel

theorem index_X1 : X1.index = 7 := by
  have := Subgroup.card_mul_index X1
  rw [card_X1, card_S] at this
  omega

theorem index_X2 : X2.index = 7 := by
  have := Subgroup.card_mul_index X2
  rw [card_X2, card_S] at this
  omega

theorem s1_mem : InX2 s1 := by decide +kernel

theorem s2_mem : InX1 s2 := by decide +kernel

theorem fano_X1 : ∀ g : S, InX1 g ∨ ∃ a : S, InX1 a ∧ InX1 (s1⁻¹ * (a⁻¹ * g)) := by
  decide +kernel

theorem fano_X2 : ∀ g : S, InX2 g ∨ ∃ a : S, InX2 a ∧ InX2 (s2⁻¹ * (a⁻¹ * g)) := by
  decide +kernel

end SL3

namespace SL22

theorem index_X1 : X1.index = 3 := by
  have := Subgroup.card_mul_index X1
  rw [card_X1, card_K] at this
  omega

theorem index_X2 : X2.index = 3 := by
  have := Subgroup.card_mul_index X2
  rw [card_X2, card_K] at this
  omega

theorem inU_one : InU (1 : S2) := by decide +kernel

theorem core_pair : ∀ n : K, (∀ g : K, InU (g⁻¹ * n * g).2) → (∀ g : K, InU (g⁻¹ * n * g).1) →
    n = 1 := by
  decide +kernel

end SL22

theorem center_perm6 : ∀ σ : Equiv.Perm (Fin 6), (∀ τ : Equiv.Perm (Fin 6), σ * τ = τ * σ) →
    σ = 1 := by
  decide +kernel

theorem center_alt6 : ∀ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 →
    (∀ τ : Equiv.Perm (Fin 6), Equiv.Perm.sign τ = 1 → σ * τ = τ * σ) → σ = 1 := by
  decide +kernel

end CFSG.Quasithin.H13.A6

namespace CFSG.Quasithin.H13.I51

open CFSG.Quasithin.H13.A6

structure FanoModel {K : Type*} [Group K] (A B : Subgroup K) : Prop where
  coreA : ∀ n : K, (∀ g : K, g⁻¹ * n * g ∈ A) → n = 1
  coreB : ∀ n : K, (∀ g : K, g⁻¹ * n * g ∈ B) → n = 1
  centerA : ∀ n ∈ A, (∀ a ∈ A, a * n = n * a) → n = 1
  centerB : ∀ n ∈ B, (∀ a ∈ B, a * n = n * a) → n = 1
  fanoA : ∀ g : K, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ A, g = a * b * c
  fanoB : ∀ g : K, ∃ a ∈ B, ∃ b ∈ A, ∃ c ∈ B, g = a * b * c
  idxA : A.index = 7
  idxB : B.index = 7

structure DigonModel {K : Type*} [Group K] (A B : Subgroup K) : Prop where
  core : ∀ n : K, (∀ g : K, g⁻¹ * n * g ∈ A) → (∀ g : K, g⁻¹ * n * g ∈ B) → n = 1
  prodAB : ∀ g : K, ∃ a ∈ A, ∃ b ∈ B, g = a * b
  prodBA : ∀ g : K, ∃ a ∈ B, ∃ b ∈ A, g = a * b
  idxA : A.index = 3
  idxB : B.index = 3

theorem fanoModel_X1_X2 : FanoModel SL3.X1 SL3.X2 where
  coreA n h := SL3.core_X1 n h
  coreB n h := SL3.core_X2 n h
  centerA n hn h := SL3.center_X1 n hn h
  centerB n hn h := SL3.center_X2 n hn h
  fanoA g := by
    rcases SL3.fano_X1 g with h | ⟨a, ha, hc⟩
    · exact ⟨g, h, 1, SL3.X2.one_mem, 1, SL3.X1.one_mem, by simp⟩
    · exact ⟨a, ha, SL3.s1, SL3.s1_mem, _, hc, by group⟩
  fanoB g := by
    rcases SL3.fano_X2 g with h | ⟨a, ha, hc⟩
    · exact ⟨g, h, 1, SL3.X1.one_mem, 1, SL3.X2.one_mem, by simp⟩
    · exact ⟨a, ha, SL3.s2, SL3.s2_mem, _, hc, by group⟩
  idxA := SL3.index_X1
  idxB := SL3.index_X2

theorem fanoModel_X2_X1 : FanoModel SL3.X2 SL3.X1 where
  coreA := fanoModel_X1_X2.coreB
  coreB := fanoModel_X1_X2.coreA
  centerA := fanoModel_X1_X2.centerB
  centerB := fanoModel_X1_X2.centerA
  fanoA := fanoModel_X1_X2.fanoB
  fanoB := fanoModel_X1_X2.fanoA
  idxA := fanoModel_X1_X2.idxB
  idxB := fanoModel_X1_X2.idxA

theorem digonModel_X1_X2 : DigonModel SL22.X1 SL22.X2 where
  core n h1 h2 := SL22.core_pair n (fun g => SL22.mem_X1.1 (h1 g)) (fun g => SL22.mem_X2.1 (h2 g))
  prodAB g := ⟨(g.1, 1), SL22.mem_X1.2 SL22.inU_one, (1, g.2),
    SL22.mem_X2.2 SL22.inU_one, by ext <;> simp⟩
  prodBA g := ⟨(1, g.2), SL22.mem_X2.2 SL22.inU_one, (g.1, 1),
    SL22.mem_X1.2 SL22.inU_one, by ext <;> simp⟩
  idxA := SL22.index_X1
  idxB := SL22.index_X2

theorem digonModel_X2_X1 : DigonModel SL22.X2 SL22.X1 where
  core n h1 h2 := digonModel_X1_X2.core n h2 h1
  prodAB := digonModel_X1_X2.prodBA
  prodBA := digonModel_X1_X2.prodAB
  idxA := digonModel_X1_X2.idxB
  idxB := digonModel_X1_X2.idxA

end CFSG.Quasithin.H13.I51

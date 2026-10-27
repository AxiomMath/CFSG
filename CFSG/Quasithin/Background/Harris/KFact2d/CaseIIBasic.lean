module

public import CFSG.Quasithin.Background.Harris.KFact2d.Defs
public import CFSG.Quasithin.Background.Harris.KFact2d.OddCore
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Cases

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2P CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem case2d_facts {T N K K0 : Subgroup G} (hc : CFSG.Quasithin.Gap6R2.E22Case2d K T N K0) :
    T ≤ Subgroup.normalizer (K0 : Set G) ∧
    ∀ x : G, x ∈ kerIn N K ↔ x ∈ K0 ⊔ pCoreOf 2 K ∧
      ∀ y ∈ K0 ⊔ pCoreOf 2 K, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
  have hc' := hc
  unfold CFSG.Quasithin.Gap6R2.E22Case2d at hc'
  dsimp only at hc'
  exact ⟨hc'.1, hc'.2.1⟩

section Basic

variable {T N K K0 : Subgroup G}

theorem K0_le_normalizer (hKK0 : K = K0 ⊔ T) (hTn : T ≤ Subgroup.normalizer (K0 : Set G)) :
    K ≤ Subgroup.normalizer (K0 : Set G) := by
  rw [hKK0]
  exact sup_le Subgroup.le_normalizer hTn

theorem D_le_K (hK0 : K0 ∈ cComp K) : K0 ⊔ pCoreOf 2 K ≤ K :=
  sup_le (le_of_mem_cComp hK0) (pCoreOf_le 2 K)

theorem Q_le_J (hK0 : K0 ∈ cComp K)
    (hker : ∀ x : G, x ∈ kerIn N K ↔ x ∈ K0 ⊔ pCoreOf 2 K ∧
      ∀ y ∈ K0 ⊔ pCoreOf 2 K, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K) :
    pCoreOf 2 K ≤ kerIn N K := by
  intro x hx
  refine (hker x).mpr ⟨Subgroup.mem_sup_right hx, fun y hy => ?_⟩
  have hyK : y ∈ K := D_le_K hK0 hy
  have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hyK) x⁻¹).mp
    ((pCoreOf 2 K).inv_mem hx)
  have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  rw [this]
  exact (pCoreOf 2 K).mul_mem hx h

theorem odd_of_J
    (hker : ∀ x : G, x ∈ kerIn N K ↔ x ∈ K0 ⊔ pCoreOf 2 K ∧
      ∀ y ∈ K0 ⊔ pCoreOf 2 K, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K)
    (hJK : kerIn N K ≤ K) :
    ∀ y ∈ kerIn N K, (∃ k : ℕ, y ^ 2 ^ k ∈ pCoreOf 2 K) → y ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab : ∀ a ∈ kerIn N K, ∀ b ∈ kerIn N K, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 K := fun a ha b hb =>
    ((hker a).mp ha).2 b ((hker b).mp hb).1
  have hQN : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K
  have hP := twoPartMod_le_pCoreOf (pCoreOf_isPGroup 2 K) hQN hJK
    (le_normalizer_kerIn N K) hab
  intro y hy hk
  exact hP ⟨hy, hk⟩

theorem exists_minimal_inv {T Q J : Subgroup G} (hQJ : Q < J)
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) :
    ∃ J1 : Subgroup G, Q < J1 ∧ J1 ≤ J ∧ T ≤ Subgroup.normalizer (J1 : Set G) ∧
      ∀ Y : Subgroup G, Q ≤ Y → Y ≤ J1 → T ≤ Subgroup.normalizer (Y : Set G) → Y = Q ∨ Y = J1 := by
  let S : Set (Subgroup G) := {Y | Q < Y ∧ Y ≤ J ∧ T ≤ Subgroup.normalizer (Y : Set G)}
  obtain ⟨J1, hJ1, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min S ⟨J, hQJ, le_rfl, hTJ⟩
  refine ⟨J1, hJ1.1, hJ1.2.1, hJ1.2.2, fun Y hQY hYJ1 hTY => ?_⟩
  by_cases hY : Y = Q
  · exact Or.inl hY
  · right
    have hQY' : Q < Y := lt_of_le_of_ne hQY (Ne.symm hY)
    have hYS : Y ∈ S := ⟨hQY', hYJ1.trans hJ1.2.1, hTY⟩
    exact eq_of_le_of_not_lt hYJ1 (hmin Y hYS)

end Basic

theorem isL3U3_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {p : ℕ}
    (h : IsL3U3 p B) : IsL3U3 p A := by
  rcases h with ⟨h4, h⟩ | ⟨h4, h⟩
  · obtain ⟨h1, F, h2, h3, hc, ⟨e'⟩⟩ := h
    exact Or.inl ⟨h4, h1, F, h2, h3, hc, ⟨e.trans e'⟩⟩
  · obtain ⟨h1, F, h2, h3, hc, ⟨e'⟩⟩ := h
    exact Or.inr ⟨h4, h1, F, h2, h3, hc, ⟨e.trans e'⟩⟩

end CFSG.Quasithin.Background.Harris.KFact2d

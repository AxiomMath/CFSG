module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G]

theorem eq_or_eq_sup_of_minimal {T Y Q : Subgroup G} (hQT : Q ≤ T) (hQY : Q ≤ Y)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hmin : ∀ Y' : Subgroup G, Q ≤ Y' → Y' ≤ Y → T ≤ Subgroup.normalizer (Y' : Set G) →
      Y' = Q ∨ Y' = Y)
    {B : Subgroup G} (hTB : T ≤ B) (hBA : B ≤ T ⊔ Y) : B = T ∨ B = T ⊔ Y := by
  have hcarr : (↑(T ⊔ Y) : Set G) = (T : Set G) * (Y : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right T Y hTY
  have hded : (T : Set G) * ((Y ⊓ B : Subgroup G) : Set G) =
      ((T : Set G) * (Y : Set G)) ∩ (B : Set G) := Subgroup.mul_inf_assoc T Y B hTB
  have hnorm : T ≤ Subgroup.normalizer ((Y ⊓ B : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 := (Subgroup.mem_normalizer_iff.mp (hTY ht) g)
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_normalizer_iff.mpr
      (fun x => by
        constructor
        · intro hx
          have : t * x * t⁻¹ ∈ B := B.mul_mem (B.mul_mem (hTB ht) hx) (B.inv_mem (hTB ht))
          exact this
        · intro hx
          have : t⁻¹ * (t * x * t⁻¹) * t ∈ B :=
            B.mul_mem (B.mul_mem (B.inv_mem (hTB ht)) hx) (hTB ht)
          simpa [mul_assoc] using this) : t ∈ Subgroup.normalizer (B : Set G)) g)
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr h1 h2
  rcases hmin (Y ⊓ B) (le_inf hQY (hQT.trans hTB)) inf_le_left hnorm with h | h
  · left
    apply le_antisymm
    · intro b hb
      have : b ∈ (↑(T ⊔ Y) : Set G) ∩ B := ⟨hBA hb, hb⟩
      rw [hcarr, ← hded, h] at this
      obtain ⟨t, ht, q, hq, rfl⟩ := this
      exact T.mul_mem ht (hQT hq)
    · exact hTB
  · right
    apply le_antisymm hBA
    exact sup_le hTB (h ▸ inf_le_right)

theorem comm_mem_of_atom {T N V Q Y : Subgroup G} (hT2 : IsPGroup 2 T) (hTN : T ≤ N)
    (hYN : Y ≤ N) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hVT : V ≤ T)
    (hodd : ∀ y ∈ Y, (∃ k : ℕ, y ^ 2 ^ k ∈ Q) → y ∈ Q)
    (hmin : ∀ B : Subgroup G, T ≤ B → B ≤ T ⊔ Y → B = T ∨ B = T ⊔ Y)
    (hat : ∀ A : Subgroup G, T ≤ A → A ≤ N → ¬ A ≤ Subgroup.normalizer (V : Set G) →
      (∀ B : Subgroup G, T ≤ B → B < A → B ≤ Subgroup.normalizer (V : Set G)) →
      IsElemAbelian 2 (conjClosure V A)) :
    ∀ v ∈ V, ∀ y ∈ Y, v * y * v⁻¹ * y⁻¹ ∈ Q := by
  intro v hv y hy
  have hvY : v * y * v⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hTY (hVT hv)) y).mp hy
  have hcY : v * y * v⁻¹ * y⁻¹ ∈ Y := Y.mul_mem hvY (Y.inv_mem hy)
  by_cases hA : T ⊔ Y ≤ Subgroup.normalizer (V : Set G)
  · have hyA : y ∈ T ⊔ Y := Subgroup.mem_sup_right hy
    have hyV : y * v⁻¹ * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hA hyA) v⁻¹).mp (V.inv_mem hv)
    have hcV : v * y * v⁻¹ * y⁻¹ ∈ V := by
      have := V.mul_mem hv hyV
      simpa [mul_assoc] using this
    obtain ⟨k, hk⟩ := hT2 ⟨_, hVT hcV⟩
    refine hodd _ hcY ⟨k, ?_⟩
    have : (v * y * v⁻¹ * y⁻¹) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [this]
    exact Q.one_mem
  · have hW := hat (T ⊔ Y) le_sup_left (sup_le hTN hYN) hA (fun B hTB hBA => by
      rcases hmin B hTB (le_of_lt hBA) with h | h
      · exact h ▸ hTV
      · exact absurd h (ne_of_lt hBA))
    have hv1 : v ∈ conjClosure V (T ⊔ Y) :=
      Subgroup.subset_closure ⟨1, Subgroup.one_mem _, v, hv, by simp⟩
    have hv2 : y * v⁻¹ * y⁻¹ ∈ conjClosure V (T ⊔ Y) :=
      Subgroup.subset_closure ⟨y, Subgroup.mem_sup_right hy, v⁻¹, V.inv_mem hv, rfl⟩
    have hcW : v * y * v⁻¹ * y⁻¹ ∈ conjClosure V (T ⊔ Y) := by
      have := (conjClosure V (T ⊔ Y)).mul_mem hv1 hv2
      simpa [mul_assoc] using this
    refine hodd _ hcY ⟨1, ?_⟩
    have := hW.2 _ hcW
    rw [pow_one, this]
    exact Q.one_mem

end CFSG.Quasithin.Background.Harris.KFact2d

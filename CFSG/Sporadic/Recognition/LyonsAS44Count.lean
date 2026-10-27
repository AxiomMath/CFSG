module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.CardEmbedding

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

private def Sends {K : Type*} [Group K] (Y : Fin 10 → K) (g : K) (i j : Fin 10) : Prop :=
  g * Y i * g⁻¹ = Y j ∨ g * Y i * g⁻¹ = (Y j)⁻¹

section Sends

variable {K : Type*} [Group K] {Y : Fin 10 → K}

private theorem Sends.unique (hY : ∀ i j, (Y i = Y j ∨ Y i = (Y j)⁻¹) → i = j) {g : K}
    {i j j' : Fin 10} (h : Sends Y g i j) (h' : Sends Y g i j') : j = j' := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact hY j j' (Or.inl (h.symm.trans h'))
  · exact hY j j' (Or.inr (h.symm.trans h'))
  · exact (hY j' j (Or.inr (h'.symm.trans h))).symm
  · exact hY j j' (Or.inl (inv_injective (h.symm.trans h')))

private theorem Sends.one (i : Fin 10) : Sends Y 1 i i :=
  Or.inl (by simp)

private theorem Sends.mul {g h : K} {i j k : Fin 10} (hh : Sends Y h i j) (hg : Sends Y g j k) :
    Sends Y (g * h) i k := by
  have e : g * h * Y i * (g * h)⁻¹ = g * (h * Y i * h⁻¹) * g⁻¹ := by
    simp [mul_assoc]
  unfold Sends at hh hg ⊢
  rw [e]
  rcases hh with hh | hh <;> rw [hh]
  · exact hg
  · have e' : g * (Y j)⁻¹ * g⁻¹ = (g * Y j * g⁻¹)⁻¹ := by
      simp [mul_assoc]
    rw [e']
    rcases hg with hg | hg <;> rw [hg]
    · exact Or.inr rfl
    · exact Or.inl (inv_inv _)

private theorem exists_perm_hom {N : Subgroup K}
    (hY : ∀ i j, (Y i = Y j ∨ Y i = (Y j)⁻¹) → i = j)
    (hperm : ∀ g ∈ N, ∀ i, ∃ j, Sends Y g i j) :
    ∃ φ : N →* Equiv.Perm (Fin 10), ∀ (g : N) (i : Fin 10), Sends Y g i (φ g i) := by
  have hperm' : ∀ (g : N) (i : Fin 10), ∃ j, Sends Y (g : K) i j := fun g i => hperm g g.2 i
  choose F hF using hperm'
  have hone : ∀ i, F 1 i = i := fun i => Sends.unique hY (hF 1 i) (Sends.one i)
  have hmul : ∀ g h i, F (g * h) i = F g (F h i) := fun g h i =>
    Sends.unique hY (hF (g * h) i) (Sends.mul (hF h i) (hF g (F h i)))
  let P : N → Equiv.Perm (Fin 10) := fun g =>
    { toFun := F g
      invFun := F g⁻¹
      left_inv := fun i => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun i => by rw [← hmul, mul_inv_cancel, hone] }
  exact ⟨{ toFun := P
           map_one' := Equiv.ext hone
           map_mul' := fun g h => Equiv.ext fun i => hmul g h i }, hF⟩

end Sends

private theorem card_injective_triples :
    Nat.card {b : Fin 3 → Fin 10 // Function.Injective b} = 720 := by
  rw [Nat.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin 3) (Fin 10)),
    Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  decide

theorem mem_of_fixes_three_points {K : Type*} [Group K] [Finite K] {N A : Subgroup K}
    (hAN : A ≤ N) (hAc : Nat.card A = 81) (hN : Nat.card N ≤ 58320) (Y : Fin 10 → K)
    (hY : ∀ i j, (Y i = Y j ∨ Y i = (Y j)⁻¹) → i = j)
    (hperm : ∀ g ∈ N, ∀ i, ∃ j, g * Y i * g⁻¹ = Y j ∨ g * Y i * g⁻¹ = (Y j)⁻¹)
    (hA : ∀ a ∈ A, ∀ i, a * Y i = Y i * a)
    (htrans : ∀ a b : Fin 3 → Fin 10, Function.Injective a → Function.Injective b →
      ∃ g ∈ N, ∀ i, g * Y (a i) * g⁻¹ = Y (b i) ∨ g * Y (a i) * g⁻¹ = (Y (b i))⁻¹)
    {g : K} (hg : g ∈ N) {a : Fin 3 → Fin 10} (ha : Function.Injective a)
    (hga : ∀ i, g * Y (a i) * g⁻¹ = Y (a i) ∨ g * Y (a i) * g⁻¹ = (Y (a i))⁻¹) : g ∈ A := by
  obtain ⟨φ, hφ⟩ := exists_perm_hom (N := N) hY hperm
  have hker : A.subgroupOf N ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun i => ?_
    have hx' : (x : K) ∈ A := hx
    have h1 : (x : K) * Y i * (x : K)⁻¹ = Y i := by
      rw [hA _ hx' i, mul_inv_cancel_right]
    exact Sends.unique hY (hφ x i) (Or.inl h1)
  have hAcard : Nat.card (A.subgroupOf N) = 81 := by
    rw [← hAc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have h81 : 81 ≤ Nat.card φ.ker := hAcard ▸ Subgroup.card_le_of_le hker
  let Ψ : φ.range → {b : Fin 3 → Fin 10 // Function.Injective b} := fun h =>
    ⟨fun i => h.1 (a i), h.1.injective.comp ha⟩
  have hΨ : Function.Surjective Ψ := by
    rintro ⟨b, hb⟩
    obtain ⟨g', hg', hg'b⟩ := htrans a b ha hb
    refine ⟨⟨φ ⟨g', hg'⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    funext i
    exact Sends.unique hY (hφ ⟨g', hg'⟩ (a i)) (hg'b i)
  have hrange : 720 ≤ Nat.card φ.range := by
    rw [← card_injective_triples]
    exact Nat.card_le_card_of_surjective Ψ hΨ
  have hk : Nat.card φ.ker * Nat.card φ.range = Nat.card N := Subgroup.card_ker_mul_card_range φ
  have hk81 : Nat.card φ.ker = 81 := by
    by_contra hne
    have h82 : 82 ≤ Nat.card φ.ker := by omega
    have := Nat.mul_le_mul h82 hrange
    omega
  have hr720 : Nat.card φ.range = 720 := by
    by_contra hne
    have h721 : 721 ≤ Nat.card φ.range := by omega
    have := Nat.mul_le_mul h81 h721
    omega
  have hkerEq : A.subgroupOf N = φ.ker := Subgroup.eq_of_le_of_card_ge hker (by omega)
  have hbij : Function.Bijective Ψ :=
    hΨ.bijective_of_nat_card_le (by rw [hr720, card_injective_triples])
  have hgN : (⟨g, hg⟩ : N) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : Ψ ⟨φ ⟨g, hg⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩ = Ψ 1 := by
      apply Subtype.ext
      funext i
      exact Sends.unique hY (hφ ⟨g, hg⟩ (a i)) (hga i)
    exact congrArg Subtype.val (hbij.1 h1)
  rw [← hkerEq] at hgN
  exact hgN

end CFSG.Sporadic.Recognition.LyonsSims

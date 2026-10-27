module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch210

open CFSG.Quasithin Subgroup

private instance a210orb_mulAction (Q : Type*) [Group Q] (T : Subgroup Q) :
    MulAction ↥T (Subgroup Q) where
  smul t X := conjSubgroup X (t : Q)⁻¹
  one_smul X := by
    show conjSubgroup X (1 : Q)⁻¹ = X
    rw [inv_one, conjSubgroup_one]
  mul_smul s t X := by
    show conjSubgroup X (↑(s * t) : Q)⁻¹ =
      conjSubgroup (conjSubgroup X (↑t : Q)⁻¹) (↑s : Q)⁻¹
    rw [conjSubgroup_conjSubgroup, Subgroup.coe_mul, mul_inv_rev]

private lemma a210orb_orbit_eq {Q : Type*} [Group Q] {T : Subgroup Q} (L : Subgroup Q) :
    MulAction.orbit ↥T L = {X : Subgroup Q | ∃ t ∈ T, X = conjSubgroup L t} := by
  ext X
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(t : Q)⁻¹, T.inv_mem t.2, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u⁻¹, T.inv_mem hu⟩, ?_⟩
    show conjSubgroup L (u⁻¹)⁻¹ = conjSubgroup L u
    rw [inv_inv]

theorem ncard_conj_orbit {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q} (hT : IsPGroup 2 ↥T)
    (L : Subgroup Q) :
    ∃ k : ℕ, Set.ncard {X : Subgroup Q | ∃ t ∈ T, X = conjSubgroup L t} = 2 ^ k := by
  obtain ⟨k, hk⟩ := hT.card_orbit L
  refine ⟨k, ?_⟩
  rw [← a210orb_orbit_eq L, ← Nat.card_coe_set_eq]
  exact hk

private lemma a210orb_exists_four {Q : Type*} [Group Q] [Finite Q] {T : Subgroup Q} (L : Subgroup Q)
    (h4 : 4 ≤ Set.ncard {X : Subgroup Q | ∃ t ∈ T, X = conjSubgroup L t}) :
    ∃ t : Fin 4 → Q, (∀ i, t i ∈ T) ∧ Function.Injective fun i => conjSubgroup L (t i) := by
  classical
  let S : Set (Subgroup Q) := {X : Subgroup Q | ∃ t ∈ T, X = conjSubgroup L t}
  have h4S : 4 ≤ Set.ncard S := h4
  have : Finite (Subgroup Q) :=
    Finite.of_injective (fun X : Subgroup Q => (X : Set Q)) SetLike.coe_injective
  have : Fintype ↥S := Fintype.ofFinite _
  have hcard : Fintype.card (Fin 4) ≤ Fintype.card ↥S := by
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
    exact h4S
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := ↥S) hcard
  let f : Fin 4 → Q := fun i => Classical.choose (e i).2
  have hf_mem : ∀ i, f i ∈ T := fun i => (Classical.choose_spec (e i).2).1
  have hf_eq : ∀ i, conjSubgroup L (f i) = (e i : Subgroup Q) :=
    fun i => ((Classical.choose_spec (e i).2).2).symm
  refine ⟨f, hf_mem, ?_⟩
  intro i j hij
  have hval : (e i : Subgroup Q) = (e j : Subgroup Q) := by
    rw [← hf_eq i, ← hf_eq j]
    exact hij
  exact e.injective (Subtype.ext hval)

theorem exists_four_conj {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q} (hT : IsPGroup 2 ↥T)
    (L : Subgroup Q) (h : 3 ≤ Set.ncard {X : Subgroup Q | ∃ t ∈ T, X = conjSubgroup L t}) :
    ∃ t : Fin 4 → Q, (∀ i, t i ∈ T) ∧ Function.Injective fun i => conjSubgroup L (t i) := by
  obtain ⟨k, hk⟩ := ncard_conj_orbit hT L
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k ≤ 1 := by omega
    have hle : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    simp at hle
    have h3 : 3 ≤ 2 ^ k := by rw [← hk]; exact h
    omega
  refine a210orb_exists_four L ?_
  rw [hk]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2

end CFSG.LocalAnalysis.WeakClosure81.Asch210

module

public import CFSG.Quasithin.Background.SmithB42Alt6Fix

public section

namespace CFSG.Quasithin

namespace B42Alt6

open Equiv Equiv.Perm CFSG.Quasithin.S143

@[expose] def x0 : Perm (Fin 6) := swap 0 1 * swap 2 3

theorem comm_x0 : ∀ y : Perm (Fin 6), sign y = 1 → y * y = 1 → y ≠ 1 → y ≠ x0 →
    y * x0 = x0 * y →
      y = swap 0 1 * swap 4 5 ∨ y = swap 2 3 * swap 4 5 ∨ y = swap 0 2 * swap 1 3 ∨
        y = swap 0 3 * swap 1 2 := by
  unfold x0
  decide +kernel

theorem length_le_card {G : Type*} [Group G] (K : Subgroup G) [Finite K] (l : List G)
    (hl : l.Nodup) (hK : ∀ x ∈ l, x ∈ K) : l.length ≤ Nat.card K := by
  let f : Fin l.length → K := fun i => ⟨l.get i, hK _ (List.get_mem l i)⟩
  have hf : Function.Injective f := fun i j hij =>
    (List.nodup_iff_injective_get.1 hl) (congrArg Subtype.val hij)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem n6Act_mul_apply (g h : Perm (Fin 6)) (a : N6) :
    n6Act (g * h) a = n6Act g (n6Act h a) := by
  rw [map_mul]
  rfl

theorem n6Act_inv_apply (g : Perm (Fin 6)) (a : N6) : n6Act g⁻¹ (n6Act g a) = a := by
  rw [← n6Act_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem n6Act_apply_inv (g : Perm (Fin 6)) (a : N6) : n6Act g (n6Act g⁻¹ a) = a := by
  rw [← n6Act_mul_apply, mul_inv_cancel, map_one]
  rfl

theorem card_kleinPairs6_ge : 4 ≤ Nat.card kleinPairs6 := by
  have m1 : swap 0 1 * swap 2 3 ∈ kleinPairs6 := Subgroup.subset_closure (by simp)
  have m2 : swap 2 3 * swap 4 5 ∈ kleinPairs6 := Subgroup.subset_closure (by simp)
  have h := length_le_card kleinPairs6 [1, swap 0 1 * swap 2 3, swap 2 3 * swap 4 5,
      (swap 0 1 * swap 2 3) * (swap 2 3 * swap 4 5)] (by decide) (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact m1
    · exact m2
    · exact kleinPairs6.mul_mem m1 m2)
  simpa using h

theorem altConj_of_fix {P : Subgroup (Perm (Fin 6))} (hPA : P ≤ alternatingGroup (Fin 6))
    (hP4 : Nat.card P = 4) (hel : ∀ x ∈ P, x * x = 1)
    (hfix : 4 ≤ Nat.card {a : N6 // ∀ σ ∈ P, n6Act σ a = a}) :
    ∃ c ∈ alternatingGroup (Fin 6), P = kleinPairs6.map (MulAut.conj c).toMonoidHom := by
  classical
  obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P, x ≠ 1 := by
    by_contra h
    push Not at h
    have : P = ⊥ := eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx)
    rw [this, Subgroup.card_bot] at hP4
    omega
  have hx0A : x0 ∈ alternatingGroup (Fin 6) := by unfold x0; rw [mem_alternatingGroup]; decide
  obtain ⟨ρ, hρA, hρx⟩ := alt6_invol_conj x x0 (hPA hxP) hx0A hx1 (by unfold x0; decide)
    (hel x hxP) (by unfold x0; decide)
  set P₁ := P.map (MulAut.conj ρ).toMonoidHom with hP₁
  have hmem₁ : ∀ y, y ∈ P₁ ↔ ρ⁻¹ * y * ρ ∈ P := by
    intro y
    rw [hP₁, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hx0P : x0 ∈ P₁ := by
    rw [hmem₁, ← hρx]
    simpa [mul_assoc] using hxP
  have hP₁4 : Nat.card P₁ = 4 := by
    rw [hP₁, Subgroup.card_map_of_injective (MulAut.conj ρ).injective, hP4]
  have hel₁ : ∀ y ∈ P₁, y * y = 1 := by
    intro y hy
    have h := hel _ ((hmem₁ y).1 hy)
    have : ρ⁻¹ * (y * y) * ρ = 1 := by
      calc ρ⁻¹ * (y * y) * ρ = (ρ⁻¹ * y * ρ) * (ρ⁻¹ * y * ρ) := by group
        _ = 1 := h
    have h2 : y * y = ρ * (ρ⁻¹ * (y * y) * ρ) * ρ⁻¹ := by group
    rw [h2, this]
    group
  have hcomm₁ : ∀ y ∈ P₁, ∀ z ∈ P₁, y * z = z * y := by
    intro y hy z hz
    have h1 := hel₁ _ (P₁.mul_mem hy hz)
    have h2 := hel₁ y hy
    have h3 := hel₁ z hz
    calc y * z = y * (y * z * (y * z)) * z := by rw [h1]; group
      _ = (y * y) * (z * y) * (z * z) := by group
      _ = z * y := by rw [h2, h3]; group
  have hPA₁ : P₁ ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (alternatingGroup.normal (α := Fin 6)).conj_mem y (hPA hy) ρ
  have hfix₁ : 4 ≤ Nat.card {a : N6 // ∀ σ ∈ P₁, n6Act σ a = a} := by
    refine hfix.trans (le_of_eq (Nat.card_congr
      { toFun := fun a => ⟨n6Act ρ a, fun σ hσ => ?_⟩
        invFun := fun a => ⟨n6Act ρ⁻¹ a, fun σ hσ => ?_⟩
        left_inv := fun a => Subtype.ext ?_
        right_inv := fun a => Subtype.ext ?_ }))
    · obtain ⟨τ, hτ, rfl⟩ := hσ
      show n6Act (ρ * τ * ρ⁻¹) (n6Act ρ a) = n6Act ρ a
      rw [n6Act_mul_apply, n6Act_mul_apply, n6Act_inv_apply, a.2 τ hτ]
    · have h := a.2 (ρ * σ * ρ⁻¹) ⟨σ, hσ, rfl⟩
      have h2 : n6Act σ (n6Act ρ⁻¹ a) = n6Act ρ⁻¹ (n6Act (ρ * σ * ρ⁻¹) a) := by
        rw [n6Act_mul_apply, n6Act_mul_apply, n6Act_inv_apply]
      rw [h2, h]
    · exact n6Act_inv_apply ρ a
    · exact n6Act_apply_inv ρ a
  obtain ⟨y, hyP, hy1, hyx⟩ : ∃ y ∈ P₁, y ≠ 1 ∧ y ≠ x0 := by
    by_contra h
    push Not at h
    have hle : P₁ ≤ Subgroup.zpowers x0 := by
      intro z hz
      by_cases h1 : z = 1
      · rw [h1]; exact one_mem _
      · rw [h z hz h1]; exact Subgroup.mem_zpowers _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcz : Nat.card (Subgroup.zpowers x0) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by unfold x0; decide) (by unfold x0; decide)
    have := Subgroup.card_le_of_le hle
    omega
  have hyA := hPA₁ hyP
  rw [mem_alternatingGroup] at hyA
  have hfin : swap 2 3 * swap 4 5 ∈ P₁ →
      ∃ c ∈ alternatingGroup (Fin 6), P = kleinPairs6.map (MulAut.conj c).toMonoidHom := by
    intro h2345
    have hK : kleinPairs6 ≤ P₁ := by
      unfold kleinPairs6
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact hx0P
      · exact h2345
    have heq : kleinPairs6 = P₁ :=
      Subgroup.eq_of_le_of_card_ge hK (by rw [hP₁4]; exact card_kleinPairs6_ge)
    refine ⟨ρ⁻¹, (alternatingGroup (Fin 6)).inv_mem hρA, ?_⟩
    have hid : (MulAut.conj ρ⁻¹).toMonoidHom.comp (MulAut.conj ρ).toMonoidHom =
        MonoidHom.id (Perm (Fin 6)) := by
      ext z : 1
      simp [MulAut.conj_apply, mul_assoc]
    rw [heq, hP₁, Subgroup.map_map, hid, Subgroup.map_id]
  have hreg : swap 0 2 * swap 1 3 ∉ P₁ := by
    intro h0213
    have hle : Nat.card {a : N6 // ∀ σ ∈ P₁, n6Act σ a = a} ≤ 2 := by
      refine le_trans ?_ (le_of_eq card_fix_V0)
      rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
      refine Fintype.card_le_of_injective (fun a => ⟨a.1, ?_⟩) ?_
      · exact ⟨a.2 _ hx0P, a.2 _ h0213⟩
      · intro a b hab
        exact Subtype.ext (by simpa using hab)
    omega
  rcases comm_x0 y hyA (hel₁ y hyP) hy1 hyx (hcomm₁ y hyP x0 hx0P) with h | h | h | h
  · refine hfin ?_
    have : swap 2 3 * swap 4 5 = x0 * y := by rw [h]; unfold x0; decide
    rw [this]
    exact P₁.mul_mem hx0P hyP
  · refine hfin ?_
    rw [← h]
    exact hyP
  · exact (hreg (h ▸ hyP)).elim
  · refine (hreg ?_).elim
    have : swap 0 2 * swap 1 3 = x0 * y := by rw [h]; unfold x0; decide
    rw [this]
    exact P₁.mul_mem hx0P hyP

end B42Alt6

end CFSG.Quasithin

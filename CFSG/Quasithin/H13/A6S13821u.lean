module

public import CFSG.Quasithin.H13.A6S13821s
public import CFSG.Quasithin.H13.L32AStRec

public section

namespace CFSG.Quasithin.H13.A6.A6S19

open CFSG.Quasithin.H6

theorem card_le_two_mul_card_fix {M : Type} [AddCommGroup M] [Finite M] (φ : M →+ M) (d : M)
    (h : ∀ m, φ m - m = 0 ∨ φ m - m = d) : Nat.card M ≤ 2 * Nat.card {m : M // φ m = m} := by
  set ψ : M →+ M := φ - AddMonoidHom.id M with hψ
  have hψm : ∀ m, ψ m = φ m - m := fun m => rfl
  have hker : Nat.card ψ.ker = Nat.card {m : M // φ m = m} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
    rw [AddMonoidHom.mem_ker, hψm, sub_eq_zero]
  have hrange : Nat.card (Set.range ψ) ≤ 2 := by
    have hsub : Set.range ψ ⊆ ({0, d} : Set M) := by
      rintro _ ⟨m, rfl⟩
      rw [hψm]
      rcases h m with h1 | h1
      · rw [h1]
        exact Set.mem_insert _ _
      · rw [h1]
        exact Set.mem_insert_of_mem _ rfl
    calc Nat.card (Set.range ψ) ≤ Nat.card ↥({0, d} : Set M) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 2 := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have h1 := AddSubgroup.card_mul_index ψ.ker
  rw [AddSubgroup.index_ker, hker] at h1
  rw [← h1]
  calc Nat.card {m : M // φ m = m} * Nat.card (Set.range ψ) ≤
        Nat.card {m : M // φ m = m} * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * _ := mul_comm _ _

@[expose] def NotNat {M : Type} [AddGroup M] (ρ : Γ →* AddMonoid.End M) : Prop :=
  IsoMod ρ ρCore ∨ IsoMod ρ ρSt ∨ IsoMod ρ (prodRep ρV ρSt) ∨ IsoMod ρ (prodRep ρCore ρSt)

theorem four_mul_card_fix_st' {g : Γ} (hg : g ∈ Ul) (hg1 : g ≠ 1) :
    4 * Nat.card {m : St // ρSt g m = m} ≤ Nat.card St := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact four_mul_card_fix_st g hg hg1

theorem four_mul_card_fix_core' {g : Γ} (hg : g ∈ Ul) (hg1 : g ≠ 1) :
    4 * Nat.card {m : Core // ρCore g m = m} ≤ Nat.card Core := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact four_mul_card_fix_core g hg hg1

theorem four_mul_card_fix_prod {N : Type} [AddGroup N] [Finite N] (σ : Γ →* AddMonoid.End N)
    {g : Γ} (hg : g ∈ Ul) (hg1 : g ≠ 1) :
    4 * Nat.card {y : N × St // prodRep σ ρSt g y = y} ≤ Nat.card (N × St) := by
  rw [card_fix_prodRep, Nat.card_prod]
  have h1 := four_mul_card_fix_st' hg hg1
  have h2 : Nat.card {n : N // σ g n = n} ≤ Nat.card N := Finite.card_subtype_le _
  calc 4 * (Nat.card {n : N // σ g n = n} * Nat.card {m : St // ρSt g m = m}) =
        Nat.card {n : N // σ g n = n} * (4 * Nat.card {m : St // ρSt g m = m}) := by ring
    _ ≤ Nat.card N * Nat.card St := Nat.mul_le_mul h2 h1

theorem false_of_transv_model {N : Type} [AddCommGroup N] [Finite N] {M : Type} [AddGroup M]
    {ρ : Γ →* AddMonoid.End M} {σ : Γ →* AddMonoid.End N} (h : IsoMod ρ σ) {g : Γ}
    (h4 : 4 * Nat.card {n : N // σ g n = n} ≤ Nat.card N) {d : M}
    (hd : ∀ m : M, ρ g m - m = 0 ∨ ρ g m - m = d) : False := by
  obtain ⟨f, hf, hfe⟩ := h
  obtain ⟨d', hd'⟩ := hf.2 d
  have hN : ∀ n : N, σ g n - n = 0 ∨ σ g n - n = d' := by
    intro n
    have e : f (σ g n - n) = ρ g (f n) - f n := by rw [map_sub, hfe]
    rcases hd (f n) with h1 | h1
    · left
      apply hf.1
      rw [e, h1, map_zero]
    · right
      apply hf.1
      rw [e, h1, hd']
  have h2 : Nat.card N ≤ 2 * Nat.card {n : N // σ g n = n} :=
    card_le_two_mul_card_fix (σ g) d' hN
  have hpos : 0 < Nat.card {n : N // σ g n = n} := by
    have : Nonempty {n : N // σ g n = n} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  omega

theorem false_of_quad_model {N : Type} [AddGroup N] {M : Type} [AddGroup M]
    {ρ : Γ →* AddMonoid.End M} {σ : Γ →* AddMonoid.End N} (h : IsoMod ρ σ)
    (hq : ∃ a b : Γ, a ∈ Ul ∧ b ∈ Ul ∧ ∃ n : N, σ b (n - σ a n) ≠ n - σ a n)
    (hM : ∀ a ∈ Ul, ∀ b ∈ Ul, ∀ m : M, ρ b (m - ρ a m) = m - ρ a m) : False := by
  obtain ⟨f, hf, hfe⟩ := h
  obtain ⟨a, b, ha, hb, n, hn⟩ := hq
  apply hn
  apply hf.1
  calc f (σ b (n - σ a n)) = ρ b (f n - ρ a (f n)) := by rw [hfe, map_sub, hfe]
    _ = f n - ρ a (f n) := hM a ha b hb (f n)
    _ = f (n - σ a n) := by rw [map_sub, hfe]

theorem not_quad_prod {N : Type} [AddGroup N] (σ : Γ →* AddMonoid.End N) :
    ∃ a b : Γ, a ∈ Ul ∧ b ∈ Ul ∧ ∃ y : N × St,
      prodRep σ ρSt b (y - prodRep σ ρSt a y) ≠ y - prodRep σ ρSt a y := by
  obtain ⟨a, b, ha, hb, m, hm⟩ := not_quad_st
  refine ⟨a, b, ha, hb, (0, m), fun h => hm ?_⟩
  exact congrArg Prod.snd h

theorem false_of_transv {M : Type} [AddGroup M] {ρ : Γ →* AddMonoid.End M} (h : NotNat ρ)
    {g : Γ} (hg : g ∈ Ul) (hg1 : g ≠ 1) {d : M}
    (hd : ∀ m : M, ρ g m - m = 0 ∨ ρ g m - m = d) : False := by
  rcases h with h | h | h | h
  · exact false_of_transv_model h (four_mul_card_fix_core' hg hg1) hd
  · exact false_of_transv_model h (four_mul_card_fix_st' hg hg1) hd
  · exact false_of_transv_model h (four_mul_card_fix_prod ρV hg hg1) hd
  · exact false_of_transv_model h (four_mul_card_fix_prod ρCore hg hg1) hd

theorem false_of_quad {M : Type} [AddGroup M] {ρ : Γ →* AddMonoid.End M} (h : NotNat ρ)
    (hM : ∀ a ∈ Ul, ∀ b ∈ Ul, ∀ m : M, ρ b (m - ρ a m) = m - ρ a m) : False := by
  rcases h with h | h | h | h
  · exact false_of_quad_model h not_quad_core hM
  · exact false_of_quad_model h not_quad_st hM
  · exact false_of_quad_model h (not_quad_prod ρV) hM
  · exact false_of_quad_model h (not_quad_prod ρCore) hM

theorem exists_sub_eq_v3 : ∀ v : V3, ∃ g : Γ, ∃ u : V3, g • u - u = v := by
  decide +kernel

theorem exists_three_isLl : ∃ c : Γ, IsLl c ∧ c ^ 3 = 1 ∧ c ≠ 1 := by
  decide +kernel

theorem exists_three_Ll : ∃ c : Γ, c ∈ Ll ∧ c ^ 3 = 1 ∧ c ≠ 1 :=
  exists_three_isLl

end CFSG.Quasithin.H13.A6.A6S19

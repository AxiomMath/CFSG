module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def LocTr (Γ : SimpleGraph V) (M : Subgroup G) (v : V) : Prop :=
  ∀ p q : V, Γ.Adj v p → Γ.Adj v q → ∃ m ∈ M, m • v = v ∧ m • p = q

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem locTr_of_fixers {M : Subgroup G} (ℓ : Line Γ) {w : ℤ}
    (h₁ : ∃ g ∈ M, g • ℓ.vert (w - 1) = ℓ.vert (w - 1) ∧ g • ℓ.vert w = ℓ.vert w ∧
      g • ℓ.vert (w + 1) ≠ ℓ.vert (w + 1))
    (h₂ : ∃ g ∈ M, g • ℓ.vert w = ℓ.vert w ∧ g • ℓ.vert (w + 1) = ℓ.vert (w + 1) ∧
      g • ℓ.vert (w - 1) ≠ ℓ.vert (w - 1)) : LocTr Γ M (ℓ.vert w) := by
  obtain ⟨g₁, hg₁M, h1u, h1α, h1w⟩ := h₁
  obtain ⟨g₂, hg₂M, h2α, h2w, h2u⟩ := h₂
  intro p q hp hq
  obtain ⟨m, hm, hmα, hmp⟩ := F.transitive_of_two_fixers (ℓ.adj_pred w) (ℓ.adj w)
    (ℓ.vert_pred_ne_succ w) (MulAction.mem_stabilizer_iff.2 h1α)
    (MulAction.mem_stabilizer_iff.2 h2α) h1u h1w h2w h2u hp hq
  have hle : Subgroup.closure ({g₁, g₂} : Set G) ≤ M := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hg₁M
    · exact hg₂M
  exact ⟨m, hle hm, hmα, hmp⟩

theorem locTr_conj {M : Subgroup G} {x : V} (hx : LocTr Γ M x) {h : G} (hh : h ∈ M) :
    LocTr Γ M (h • x) := by
  intro p q hp hq
  have hp' : Γ.Adj x (h⁻¹ • p) := by
    have := (F.adj_smul h⁻¹ _ _).2 hp
    rwa [inv_smul_smul] at this
  have hq' : Γ.Adj x (h⁻¹ • q) := by
    have := (F.adj_smul h⁻¹ _ _).2 hq
    rwa [inv_smul_smul] at this
  obtain ⟨m, hm, hmx, hmp⟩ := hx _ _ hp' hq'
  refine ⟨h * m * h⁻¹, M.mul_mem (M.mul_mem hh hm) (M.inv_mem hh), ?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, hmx]
  · rw [mul_smul, mul_smul, hmp, smul_inv_smul]

theorem locTr_all {M : Subgroup G} {α β : V} (hαβ : Γ.Adj α β) (hα : LocTr Γ M α)
    (hβ : LocTr Γ M β) : ∀ v, LocTr Γ M v := by
  have hS : ∀ v, ∃ h ∈ M, h • α = v ∨ h • β = v := by
    intro v
    have hr : Γ.Reachable α v := F.isTree.connected.preconnected α v
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => exact ⟨1, M.one_mem, Or.inl (one_smul _ _)⟩
    | @tail b c _ hstep ih =>
      obtain ⟨h, hh, hcases⟩ := ih
      rcases hcases with rfl | rfl
      · have hadj : Γ.Adj α (h⁻¹ • c) := by
          have := (F.adj_smul h⁻¹ _ _).2 hstep
          rwa [inv_smul_smul] at this
        obtain ⟨m, hm, -, hmβ⟩ := hα β (h⁻¹ • c) hαβ hadj
        exact ⟨h * m, M.mul_mem hh hm, Or.inr (by rw [mul_smul, hmβ, smul_inv_smul])⟩
      · have hadj : Γ.Adj β (h⁻¹ • c) := by
          have := (F.adj_smul h⁻¹ _ _).2 hstep
          rwa [inv_smul_smul] at this
        obtain ⟨m, hm, -, hmα⟩ := hβ α (h⁻¹ • c) hαβ.symm hadj
        exact ⟨h * m, M.mul_mem hh hm, Or.inl (by rw [mul_smul, hmα, smul_inv_smul])⟩
  intro v
  obtain ⟨h, hh, rfl | rfl⟩ := hS v
  · exact F.locTr_conj hα hh
  · exact F.locTr_conj hβ hh

omit F in
theorem exists_mem_smul_of_walk {M : Subgroup G} (hM : ∀ v, LocTr Γ M v) :
    ∀ (n : ℕ) {u w : V} (p : Γ.Walk u w), p.length = 2 * n → ∃ g ∈ M, g • u = w := by
  intro n
  induction n with
  | zero =>
    intro u w p hp
    obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero (by omega : p.length = 0)
    exact ⟨1, M.one_mem, one_smul _ _⟩
  | succ n ih =>
    intro u w p hp
    cases p with
    | nil => simp at hp
    | cons h1 p1 =>
      cases p1 with
      | nil =>
        simp at hp
        omega
      | cons h2 q =>
        obtain ⟨g, hg, -, hgu⟩ := hM _ _ _ h1.symm h2
        obtain ⟨g', hg', hg'w⟩ := ih q (by simp at hp; omega)
        exact ⟨g' * g, M.mul_mem hg' hg, by rw [mul_smul, hgu, hg'w]⟩

theorem walk_even_iff {u v : V} (p : Γ.Walk u v) :
    Fan86.valence Γ v = Fan86.valence Γ u ↔ Even p.length := by
  induction p with
  | nil => simp
  | @cons a y z h q ih =>
    have h1 := F.alternating _ _ h
    have h2 := F.valence a
    have h3 := F.valence y
    have h4 := F.valence z
    change Nat.card _ ≠ Nat.card _ at h1
    change Fan86.valence Γ z = Fan86.valence Γ y ↔ Even q.length at ih
    change Nat.card _ = 3 ∨ Nat.card _ = 5 at h2 h3 h4
    change Fan86.valence Γ z = Fan86.valence Γ a ↔ Even (q.length + 1)
    rw [Nat.even_add_one, ← ih]
    change Nat.card _ = Nat.card _ ↔ ¬ (Nat.card _ = Nat.card _)
    omega

theorem exists_mem_smul_eq {M : Subgroup G} (hM : ∀ v, LocTr Γ M v) {u v : V}
    (h : Fan86.valence Γ v = Fan86.valence Γ u) : ∃ g ∈ M, g • u = v := by
  obtain ⟨p⟩ := F.isTree.connected.preconnected u v
  obtain ⟨n, hn⟩ := (F.walk_even_iff p).1 h
  exact exists_mem_smul_of_walk hM n p (by omega)

theorem kernel_conj_le {M : Subgroup G} {x : V} (hK : ∀ k ∈ nbrStab Γ G x, k ∈ M) {h : G}
    (hh : h ∈ M) : ∀ k ∈ nbrStab Γ G (h • x), k ∈ M := by
  intro k hk
  have hk' : h⁻¹ * k * h ∈ nbrStab Γ G x := by
    refine mem_nbrStab.2 fun z hz => ?_
    have hz' : Γ.Adj (h • x) (h • z) := (F.adj_smul h _ _).2 hz
    have := mem_nbrStab.1 hk _ hz'
    rw [mul_smul, mul_smul, this, inv_smul_smul]
  have := M.mul_mem (M.mul_mem hh (hK _ hk')) (M.inv_mem hh)
  simpa [mul_assoc] using this

theorem exists_orderOf_of_locTr {M : Subgroup G} {v : V} (hM : LocTr Γ M v) :
    ∃ x ∈ M ⊓ MulAction.stabilizer G v, orderOf x = Fan86.valence Γ v := by
  set H : Subgroup G := M ⊓ MulAction.stabilizer G v with hH
  have hHv : H ≤ MulAction.stabilizer G v := inf_le_right
  have hfin : Finite ↥H := by
    have := F.loc_finite v
    exact Finite.of_injective (Subgroup.inclusion hHv) (Subgroup.inclusion_injective _)
  obtain ⟨b, hb⟩ := F.exists_adj v
  have hcard := F.card_eq_valence_mul hb hHv (fun u w hu hw => by
    obtain ⟨m, hm, hmv, hmu⟩ := hM u w hu hw
    exact ⟨m, ⟨hm, MulAction.mem_stabilizer_iff.2 hmv⟩, hmu⟩)
  have hp : (Fan86.valence Γ v).Prime := F.valence_isPrime v
  have : Fact (Fan86.valence Γ v).Prime := ⟨hp⟩
  obtain ⟨h₀, hh₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) (Fan86.valence Γ v)
    ⟨_, hcard⟩
  exact ⟨(h₀ : G), h₀.2, by rw [Subgroup.orderOf_coe]; exact hh₀⟩

end FanTree

end CFSG.Quasithin.Fan86

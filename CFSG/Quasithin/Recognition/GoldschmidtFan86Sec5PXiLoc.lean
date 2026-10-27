module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_central_involution_of_isPGroup {H : Subgroup G} [Finite H] [Nontrivial H]
    (hH : IsPGroup 2 H) :
    ∃ z ∈ H, z ≠ 1 ∧ z * z = 1 ∧ ∀ g ∈ H, g * z = z * g := by
  have hZ : Nontrivial (Subgroup.center H) := hH.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center H) := hH.to_subgroup _
  have hcard : Nat.card (Subgroup.center H) ≠ 1 := by
    have := Finite.one_lt_card (α := Subgroup.center H)
    omega
  have hdvd : 2 ∣ Nat.card (Subgroup.center H) := hZp.card_eq_or_dvd.resolve_left hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center H) 2 hdvd
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  refine ⟨((x : H) : G), (x : H).2, ?_, ?_, fun g hg => ?_⟩
  · intro h1
    have : x = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hx
    omega
  · have := congrArg (fun y : Subgroup.center H => ((y : H) : G)) hx2
    simpa [pow_two] using this
  · have := Subgroup.mem_center_iff.1 x.2 ⟨g, hg⟩
    exact congrArg (fun y : H => (y : G)) this

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem exists_local_involution {v a : V} (hva : Γ.Adj v a) :
    ∃ e ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a, e ∉ nbrStab Γ G v ∧
      e * e ∈ nbrStab Γ G v := by
  obtain ⟨φ, key, -⟩ := F.exists_edge_char hva
  obtain ⟨g, hg, hga, c, hc, hgc⟩ := F.frobenius_nonreg v a hva
  let g' : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) :=
    ⟨g, hg, MulAction.mem_stabilizer_iff.2 hga⟩
  have hφ : φ g' ≠ 1 := fun h => hgc (mem_nbrStab.1 ((key g').2 h) c hc)
  have hp : Fan86.valence Γ v = 3 ∨ Fan86.valence Γ v = 5 := F.valence v
  rcases hp with h3 | h5
  · have hsq : φ g' * φ g' = 1 := by
      by_contra hne
      have := units_three h3 (φ g') (φ g' * φ g') hφ hne
      exact hφ (mul_eq_left.1 this.symm)
    exact ⟨g, g'.2, fun hK => hφ ((key g').1 hK), (key (g' * g')).2 (by rw [map_mul]; exact hsq)⟩
  · obtain ⟨j, hj2, hj1⟩ := units_exists_involution h5 (φ g') hφ
    let e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) := g' ^ (j : ℕ)
    refine ⟨(e : G), e.2, fun hK => hj1 ?_, (key (e * e)).2 ?_⟩
    · rw [← map_pow]
      exact (key e).1 hK
    · rw [map_mul, ← pow_two, map_pow]
      exact hj2

theorem exists_involutive_moving {β α : V} (hβα : Γ.Adj β α) :
    ∃ y ∈ MulAction.stabilizer G β, y • α ≠ α ∧ (y * y) • α = α := by
  obtain ⟨a, haβ, hne⟩ := F.exists_adj_ne β α
  obtain ⟨e, he, heK, he2⟩ := F.exists_local_involution haβ
  refine ⟨e, he.1, fun h => heK ?_, mem_nbrStab.1 he2 α hβα⟩
  intro w hw
  exact F.frobenius_two β a α haβ hβα hne e he.1 (MulAction.mem_stabilizer_iff.1 he.2) h w hw

end FanTree

end CFSG.Quasithin.Fan86

module

public import CFSG.RankThree.PartOne.SRC.RankOneNoncentral

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Subgroup CFSG CFSG.RankThree.PartOne.SRC

theorem rank_four_of_cover_quasisimple {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : Type} [Group Q]
    [Finite Q] (hQ : CFSG.IsQuasisimple Q) (hZ : Nat.Coprime p (Nat.card (center Q))) (h : Q)
    (hhc : h ∉ center Q) (hho : Nat.Coprime (orderOf h) p)
    (hclosed : ∀ (W : Type) [Group W] [Finite W] (π : W →* Q), Function.Surjective π →
      π.ker ≤ center W → IsPGroup p π.ker → ∃ s : Q →* W, ∀ g, π (s g) = g)
    {E₀ : Subgroup Q} (hE₀ : IsElementaryAbelian p E₀) {k : ℕ} (hk : 4 ≤ k)
    (hcard : Nat.card E₀ = p ^ k) {W : Type} [Group W] [Finite W] (ρ : W →* Q)
    (hρ : Function.Surjective ρ) (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨W₀, -, hW₀min⟩ := Finite.exists_le_minimal (p := fun K : Subgroup W => K.map ρ = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective ρ hρ])
  set ρ₀ : W₀ →* Q := ρ.comp W₀.subtype with hρ₀
  have hρ₀s : Function.Surjective ρ₀ := by
    intro x
    have hx : x ∈ W₀.map ρ := by
      rw [hW₀min.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin₀ : ∀ M : Subgroup W₀, M.map ρ₀ = ⊤ → M = ⊤ := by
    intro M hM
    have h1 : (M.map W₀.subtype).map ρ = ⊤ := by
      rw [Subgroup.map_map]
      exact hM
    have h2 := hW₀min.le_of_le h1 (Subgroup.map_subtype_le M)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  have hker₀ : IsPGroup p ρ₀.ker := by
    intro x
    have hx1 : ρ ((x : W₀) : W) = 1 := MonoidHom.mem_ker.mp x.2
    obtain ⟨k, hk⟩ := hker ⟨((x : W₀) : W), hx1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun z : ρ.ker => (z : W)) hk))⟩
  have hperf : Group.IsPerfect W₀ := by
    rw [Group.isPerfect_def]
    apply hmin₀
    have h1 := hQ.1.commutator_eq_top
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hρ₀s]
    rwa [_root_.commutator_def] at h1
  suffices H : ∃ (E : Subgroup W₀) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧
      Nat.card E = p ^ k by
    obtain ⟨E, k, hk, hE, hc⟩ := H
    refine ⟨E.map W₀.subtype, k, hk, isElementaryAbelian_map' W₀.subtype hE, ?_⟩
    rw [Subgroup.card_map_of_injective W₀.subtype_injective, hc]
  by_cases hcen : ρ₀.ker ≤ center W₀
  ·
    obtain ⟨σ, hσ⟩ := hclosed W₀ ρ₀ hρ₀s hcen hker₀
    have hσinj : Function.Injective σ := fun a b hab => by
      have := congrArg ρ₀ hab
      rwa [hσ, hσ] at this
    refine ⟨E₀.map σ, k, hk, isElementaryAbelian_map' σ hE₀, ?_⟩
    rw [Subgroup.card_map_of_injective hσinj, hcard]
  ·
    by_contra hno
    push Not at hno
    apply hcen
    have hQp : p ^ k ∣ Nat.card Q := hcard ▸ Subgroup.card_subgroup_dvd_card E₀
    refine central_of_rank_le_three hp hp2 hk hQ ρ₀ hρ₀s hker₀ hmin₀ hQp hZ h hhc hho ?_
    intro E hE
    have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
    obtain ⟨k', hk'⟩ := hEp.exists_card_eq
    rw [hk']
    by_contra hlt
    have hk4 : 4 ≤ k' := by
      by_contra h4
      push Not at h4
      exact hlt (Nat.pow_le_pow_right hp.pos (by omega))
    exact hno E k' hk4 hE hk'

end CFSG.RankThree.PartOne.SLB4B

module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.Background.Harris.R1

open scoped commutatorElement

theorem perfect_le_of_index_le_four {G : Type*} [Group G] {K Stab : Subgroup G}
    (hK : ⁅K, K⁆ = K) (hle : Stab ≤ K) [Finite ↥K]
    (hidx : Nat.card (↥K ⧸ Stab.subgroupOf K) ≤ 4) : K ≤ Stab := by
  set X := ↥K ⧸ Stab.subgroupOf K with hX
  let φ : ↥K →* Equiv.Perm X := MulAction.toPermHom ↥K X
  have hsolv : Group.IsSolvable (Equiv.Perm X) := Equiv.Perm.isSolvable hidx
  obtain ⟨n, hn⟩ := hsolv.solvable
  have key : ∀ j : ℕ, ∀ k : ↥K, φ k ∈ derivedSeries (Equiv.Perm X) j := by
    intro j
    induction j with
    | zero => intro k; exact Subgroup.mem_top _
    | succ j ih =>
      intro k
      have hk : (k : G) ∈ ⁅K, K⁆ := by rw [hK]; exact k.2
      rw [Subgroup.commutator_def] at hk
      have hmain := Subgroup.closure_induction
        (p := fun g _ => ∃ hgK : g ∈ K, φ ⟨g, hgK⟩ ∈ derivedSeries (Equiv.Perm X) (j + 1))
        (k := {x : G | ∃ a ∈ K, ∃ b ∈ K, ⁅a, b⁆ = x})
        (fun x hx => by
          obtain ⟨a, ha, b, hb, rfl⟩ := hx
          have hc : ⁅a, b⁆ ∈ K := by
            rw [commutatorElement_def]
            exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
          refine ⟨hc, ?_⟩
          have e : (⟨⁅a, b⁆, hc⟩ : ↥K) = ⁅(⟨a, ha⟩ : ↥K), (⟨b, hb⟩ : ↥K)⁆ := rfl
          rw [e, map_commutatorElement, derivedSeries_succ]
          exact Subgroup.commutator_mem_commutator (ih _) (ih _))
        ⟨K.one_mem, by
          have : (⟨1, K.one_mem⟩ : ↥K) = 1 := rfl
          rw [this, map_one]
          exact Subgroup.one_mem _⟩
        (fun x y _ _ hx hy => by
          obtain ⟨hxK, hx'⟩ := hx
          obtain ⟨hyK, hy'⟩ := hy
          refine ⟨K.mul_mem hxK hyK, ?_⟩
          have : (⟨x * y, K.mul_mem hxK hyK⟩ : ↥K) = ⟨x, hxK⟩ * ⟨y, hyK⟩ := rfl
          rw [this, map_mul]
          exact Subgroup.mul_mem _ hx' hy')
        (fun x _ hx => by
          obtain ⟨hxK, hx'⟩ := hx
          refine ⟨K.inv_mem hxK, ?_⟩
          have : (⟨x⁻¹, K.inv_mem hxK⟩ : ↥K) = (⟨x, hxK⟩ : ↥K)⁻¹ := rfl
          rw [this, map_inv]
          exact Subgroup.inv_mem _ hx')
        hk
      obtain ⟨hkK, hk'⟩ := hmain
      exact hk'
  intro g hg
  have h1 : φ ⟨g, hg⟩ = 1 := by
    have := key n ⟨g, hg⟩
    rw [hn] at this
    exact Subgroup.mem_bot.mp this
  have h2 : (φ ⟨g, hg⟩) ((1 : ↥K) : X) = ((1 : ↥K) : X) := by rw [h1]; rfl
  have h3 : ((⟨g, hg⟩ : ↥K) : X) = ((1 : ↥K) : X) := by
    have : (φ ⟨g, hg⟩) ((1 : ↥K) : X) = ((⟨g, hg⟩ * 1 : ↥K) : X) := rfl
    rw [this, mul_one] at h2
    exact h2
  have h4 : (⟨g, hg⟩ : ↥K)⁻¹ * 1 ∈ Stab.subgroupOf K := QuotientGroup.eq.mp h3
  have h5 : g⁻¹ ∈ Stab := by
    have := Subgroup.mem_subgroupOf.mp h4
    simpa using this
  simpa using Stab.inv_mem h5

end CFSG.Quasithin.Background.Harris.R1

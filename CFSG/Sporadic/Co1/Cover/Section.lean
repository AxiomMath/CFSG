module

public import CFSG.Monster.Schur.Defs

public section

namespace CFSG.Sporadic.Co1.Cover

open CFSG.Monster.Schur

theorem exists_section_of_noPerfectDoubleCover {X P : Type} [Group X] [Group P]
    [hP : Group.IsPerfect P] (hND : NoPerfectDoubleCover P) (g : X →* P)
    (hg : Function.Surjective g) (hk : Nat.card g.ker = 2) :
    ∃ σ : P →* X, ∀ p, g (σ p) = p := by
  have hD : (commutator X).map g = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.2 hg]
    rw [← _root_.commutator_def]
    exact hP.commutator_eq_top
  have hsup : commutator X ⊔ g.ker = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : g x ∈ (commutator X).map g := by rw [hD]; trivial
    obtain ⟨d, hd, hdx⟩ := hx
    have : d⁻¹ * x ∈ g.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
    have hxx : x = d * (d⁻¹ * x) := by group
    rw [hxx]
    exact Subgroup.mul_mem_sup hd this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker_le : ¬ g.ker ≤ commutator X := by
    intro hle
    have htop : commutator X = ⊤ := by
      rw [eq_top_iff, ← hsup]
      exact sup_le le_rfl hle
    have hXp : Group.IsPerfect X := Group.isPerfect_def.2 htop
    have h2 := hND X g hg hXp
    exact h2 hk
  have hinf : commutator X ⊓ g.ker = ⊥ := by
    have hcard : Nat.card g.ker = 2 := hk
    have : Fact (Nat.card g.ker).Prime := ⟨by rw [hcard]; exact Nat.prime_two⟩
    have h1 := Subgroup.eq_bot_or_eq_top_of_prime_card
      ((commutator X ⊓ g.ker).subgroupOf g.ker)
    rcases h1 with h1 | h1
    · rw [Subgroup.subgroupOf_eq_bot] at h1
      exact eq_bot_iff.2 (fun x hx => by
        have hdis : Disjoint (commutator X ⊓ g.ker) g.ker := h1
        have := hdis.le_bot ⟨hx, hx.2⟩
        exact this)
    · exfalso
      apply hker_le
      intro x hx
      have : (⟨x, hx⟩ : g.ker) ∈ (commutator X ⊓ g.ker).subgroupOf g.ker := by
        rw [h1]; trivial
      exact (Subgroup.mem_subgroupOf.1 this).1
  have hinj : Function.Injective (g.comp (commutator X).subtype) := by
    intro d d' h
    have h' : g d = g d' := h
    have hmem : (d : X)⁻¹ * d' ∈ commutator X ⊓ g.ker := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ d.2) d'.2, ?_⟩
      show (d : X)⁻¹ * d' ∈ g.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, h', inv_mul_cancel]
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.1 hmem)
  have hsurj : Function.Surjective (g.comp (commutator X).subtype) := by
    intro p
    have hp : p ∈ (commutator X).map g := by rw [hD]; trivial
    obtain ⟨d, hd, hdp⟩ := hp
    exact ⟨⟨d, hd⟩, hdp⟩
  let e : commutator X ≃* P := MulEquiv.ofBijective (g.comp (commutator X).subtype) ⟨hinj, hsurj⟩
  refine ⟨(commutator X).subtype.comp e.symm.toMonoidHom, fun p => ?_⟩
  exact e.apply_symm_apply p

end CFSG.Sporadic.Co1.Cover

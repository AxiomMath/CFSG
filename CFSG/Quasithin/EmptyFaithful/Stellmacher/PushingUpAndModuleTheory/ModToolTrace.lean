module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolBase
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

section Trace

variable {G : Type*} [Group G] {W : Type*} [CommGroup W] (ρ : G →* MulAut W) (S : Subgroup G)

theorem rho_mul_apply (g h : G) (w : W) : ρ (g * h) w = ρ g (ρ h w) := by
  rw [map_mul]
  rfl

theorem trace_fixed [Fintype (G ⧸ S)] {c : W} (hc : ∀ s ∈ S, ρ s c = c) (g : G) :
    ρ g (∏ q : G ⧸ S, ρ q.out c) = ∏ q : G ⧸ S, ρ q.out c := by
  rw [map_prod]
  have h1 : ∀ q : G ⧸ S, ρ g (ρ q.out c) = ρ (g • q).out c := by
    intro q
    have hmk : (QuotientGroup.mk (g * q.out) : G ⧸ S) = QuotientGroup.mk (g • q).out := by
      rw [QuotientGroup.out_eq']
      calc (QuotientGroup.mk (g * q.out) : G ⧸ S) = g • (QuotientGroup.mk q.out : G ⧸ S) := rfl
        _ = g • q := by rw [QuotientGroup.out_eq']
    have hs := QuotientGroup.eq.mp hmk.symm
    rw [← rho_mul_apply]
    have : g * q.out = (g • q).out * ((g • q).out⁻¹ * (g * q.out)) := by group
    rw [this, rho_mul_apply, hc _ hs]
  simp only [h1]
  exact Fintype.prod_equiv (MulAction.toPerm g) _ _ (fun q => rfl)

theorem trace_eq_of_section [Fintype (G ⧸ S)] {c : W} (hc : ∀ s ∈ S, ρ s c = c)
    (rep : G ⧸ S → G) (hrep : ∀ q, (QuotientGroup.mk (rep q) : G ⧸ S) = q) :
    ∏ q : G ⧸ S, ρ (rep q) c = ∏ q : G ⧸ S, ρ q.out c := by
  refine Finset.prod_congr rfl fun q _ => ?_
  have hmk : (QuotientGroup.mk (rep q) : G ⧸ S) = QuotientGroup.mk q.out := by
    rw [hrep, QuotientGroup.out_eq']
  have hs := QuotientGroup.eq.mp hmk
  have : q.out = rep q * ((rep q)⁻¹ * q.out) := by group
  conv_rhs => rw [this, rho_mul_apply, hc _ hs]

theorem trace_exists [Finite G] (hsq : ∀ w : W, w * w = 1) (hodd : Odd S.index) (A : Subgroup G)
    (hAS : ∀ g : G, ∃ a ∈ A, ∃ s ∈ S, g = a * s) (N : Subgroup W)
    (hN : ∀ a ∈ A, ∀ w : W, ρ a w * w⁻¹ ∈ N) {c : W} (hc : ∀ s ∈ S, ρ s c = c) :
    ∃ n ∈ N, ∃ f : W, (∀ g : G, ρ g f = f) ∧ c = n * f := by
  have : Fintype (G ⧸ S) := Fintype.ofFinite _
  have hcard : Odd (Fintype.card (G ⧸ S)) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact hodd
  have hrep : ∀ q : G ⧸ S, ∃ a ∈ A, (QuotientGroup.mk a : G ⧸ S) = q := by
    intro q
    obtain ⟨a, ha, s, hs, h⟩ := hAS q.out
    refine ⟨a, ha, ?_⟩
    rw [← QuotientGroup.out_eq' q]
    conv_rhs => rw [h]
    rw [QuotientGroup.mk_mul_of_mem _ hs]
  choose rep hrepA hrepq using hrep
  set f : W := ∏ q : G ⧸ S, ρ q.out c with hf
  have hf' : f = ∏ q : G ⧸ S, ρ (rep q) c := (trace_eq_of_section ρ S hc rep hrepq).symm
  have hn : f * c⁻¹ ∈ N := by
    have : f * c⁻¹ = ∏ q : G ⧸ S, (ρ (rep q) c * c⁻¹) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, pow_odd_eq_self hsq hcard,
        ← hf']
    rw [this]
    exact Subgroup.prod_mem _ fun q _ => hN _ (hrepA q) c
  refine ⟨c * f⁻¹, ?_, f, trace_fixed ρ S hc, by simp⟩
  have := N.inv_mem hn
  rwa [mul_inv_rev, inv_inv] at this

end Trace

variable {n : ℕ}

theorem trace_model (M : Model n) {S G A : Subgroup (Perm (Fin n))} (hSG : S ≤ G)
    (hodd : Odd (S.relIndex G)) (hAS : ∀ g ∈ G, ∃ a ∈ A, ∃ s ∈ S, g = a * s)
    (N : Subgroup M.W) (hN : ∀ a ∈ A, ∀ w : M.W, M.act a w * w⁻¹ ∈ N) {c : M.W}
    (hc : c ∈ fixW M S) : ∃ n ∈ N, ∃ f ∈ fixW M G, c = n * f := by
  let ρ : ↥G →* MulAut M.W := M.act.comp G.subtype
  obtain ⟨m, hm, f, hf, hcf⟩ := trace_exists ρ (S.subgroupOf G) M.sq hodd (A.subgroupOf G)
    (fun g => by
      obtain ⟨a, ha, s, hs, h⟩ := hAS g g.2
      have haG : a ∈ G := by
        have : a = (g : Perm (Fin n)) * s⁻¹ := by rw [h]; group
        rw [this]
        exact G.mul_mem g.2 (G.inv_mem (hSG hs))
      exact ⟨⟨a, haG⟩, ha, ⟨s, hSG hs⟩, hs, Subtype.ext h⟩)
    N (fun a ha w => hN a ha w) (c := c) (fun s hs => hc s hs)
  exact ⟨m, hm, f, fun g hg => hf ⟨g, hg⟩, hcf⟩

end CFSG.Quasithin.F53Mod

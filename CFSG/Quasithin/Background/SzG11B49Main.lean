module

public import CFSG.Quasithin.Background.SzG11B49Lines
public import CFSG.Quasithin.Background.SzG11B49Quad
public import CFSG.Quasithin.Background.G10FourInputs

public section

namespace CFSG.Quasithin.G11.SzG11S

open Module CFSG.GroupTheory.GLnTwoSplitting
open B49Aux

namespace B49Hyp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V} {H : Subgroup (GLV V)}
  {U : Submodule (ZMod 2) V} (hy : B49Hyp B H U) {v p : V}

include hy

theorem isCenter_zero : B49Center B H U 0 0 := by
  refine ⟨fun u hu => rfl, fun z hz hz0 hvz => ⟨fun u hu => rfl, ?_⟩⟩
  obtain ⟨t, ht⟩ := hy.exists_isTv hz hvz
  exact ⟨t, ht, 0, by rw [map_zero, add_zero]⟩

theorem eq_zero_of_isCenter_of_mem [Finite V] (h : B49Center B H U v p) (hp : p ∈ U) : p = 0 := by
  have hv : ∀ u ∈ U, B v u = 0 := fun u hu => by rw [← h.1 u hu]; exact hy.iso p hp u hu
  obtain ⟨z, hz, hz0, hvz, -⟩ := hy.exists_common_zero v v
  obtain ⟨-, t, ht, x, hx⟩ := h.2 z hz hz0 hvz
  rw [hx, hy.tv_eq_one ht hv]
  exact two_add_self x

theorem exists_complement [Finite V] (hQ : ∀ z ∈ U, z ≠ 0 → B49Quad B H U z) :
    ∃ U' : Submodule (ZMod 2) V, Invariant H U' ∧ IsCompl U U' := by
  have hadd : ∀ {v v' p p' : V}, B49Center B H U v p → B49Center B H U v' p' →
      B49Center B H U (v + v') (p + p') := by
    intro v v' p p' h h'
    obtain ⟨p'', h''⟩ := hy.exists_isCenter hQ (v + v')
    have hmem : p + p' + p'' ∈ U := by
      refine hy.mem_of_orth fun u hu => ?_
      simp only [map_add, LinearMap.add_apply, h.1 u hu, h'.1 u hu, h''.1 u hu]
      generalize B v u = a
      generalize B v' u = b
      revert a b
      decide
    have hy0 : p + p' + p'' = 0 := by
      by_contra hne
      obtain ⟨x, hx⟩ := hy.exists_pair hne
      obtain ⟨q, hq⟩ := hy.exists_isCenter hQ x
      have h1 : B q (p + p' + p'') = 1 := by
        rw [hq.1 _ hmem, hy.symm x]
        exact hx
      have h2 : B q (p + p' + p'') = 0 := by
        rw [hy.symm q]
        simp only [map_add, LinearMap.add_apply, hy.isCenter_orth hQ h hq,
          hy.isCenter_orth hQ h' hq, hy.isCenter_orth hQ h'' hq, add_zero]
      rw [h1] at h2
      exact one_ne_zero h2
    have hpp : p + p' = p'' := (two_add_eq_iff.1 hy0).trans (zero_add _)
    rw [hpp]
    exact h''
  let S : Set V := {p | ∃ v, B49Center B H U v p}
  let U' : Submodule (ZMod 2) V :=
    { carrier := S
      add_mem' := fun {a b} ha hb => by
        obtain ⟨v, hv⟩ := ha
        obtain ⟨v', hv'⟩ := hb
        exact ⟨v + v', hadd hv hv'⟩
      zero_mem' := ⟨0, hy.isCenter_zero⟩
      smul_mem' := fun c x hx => by
        rcases zmod_two_eq_zero_or_one c with rfl | rfl
        · rw [zero_smul]
          exact ⟨0, hy.isCenter_zero⟩
        · rw [one_smul]
          exact hx }
  refine ⟨U', ?_, ?_⟩
  · intro k hk u hu
    obtain ⟨v, hv⟩ := hu
    exact ⟨k v, hy.isCenter_conj hv hk⟩
  · refine IsCompl.of_eq ?_ ?_
    · rw [Submodule.eq_bot_iff]
      rintro x ⟨hxU, v, hv⟩
      exact hy.eq_zero_of_isCenter_of_mem hv hxU
    · rw [eq_top_iff]
      intro x _
      obtain ⟨p, hp⟩ := hy.exists_isCenter hQ x
      have hxp : x + p ∈ U := by
        refine hy.mem_of_orth fun u hu => ?_
        rw [map_add, LinearMap.add_apply, hp.1 u hu]
        exact zmod_two_add_self _
      exact Submodule.mem_sup.2
        ⟨x + p, hxp, p, ⟨x, hp⟩, by rw [add_assoc, two_add_self, add_zero]⟩

end B49Hyp

theorem b49 : B49Stmt := by
  intro V _ _ _ B H U halt hnd hisom h3 hiso hdim hinv hfaith haut hE
  obtain ⟨E, hEH, hE4, ⟨a, haU, ha0, hcen⟩, hquad⟩ := hE
  have hy : B49Hyp B H U := ⟨halt, hnd, hisom, h3, hiso, hdim, hinv, hfaith, haut⟩
  exact hy.exists_complement (hy.quadAt_of_E E hEH hE4 haU ha0 hcen hquad)

end CFSG.Quasithin.G11.SzG11S

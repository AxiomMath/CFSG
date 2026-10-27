module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerHom
public import CFSG.Permutation.FiveTransitive.SetwiseSylowNormalizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.NormalizerSwappedOrbits

open MulAction FixedSetNormalizerHom FixedSetNormalizerPerm

theorem card_orbit_eq (G X : Type*) [Group G] [MulAction G X]
    (H : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (H : Set G)) (u : X) :
    Nat.card (orbit H u) = Nat.card (orbit H (g • u)) := by
  let e : MulAut H := H.normalizerMonoidHom ⟨g,hg⟩
  have he (h : H) (x : X) : g • (h • x) = e h • (g • x) := by
    change g • ((h : G) • x) = (g * (h : G) * g⁻¹) • (g • x)
    simp only [mul_smul,inv_smul_smul]
  apply Nat.card_congr (Equiv.subtypeEquiv (toPerm g) (fun x => ?_))
  constructor
  · rintro ⟨h,rfl⟩
    exact ⟨e h,(he h u).symm⟩
  · rintro ⟨h,hh⟩
    refine ⟨e.symm h,(toPerm g).injective ?_⟩
    change g • (e.symm h • u) = g • x
    rw [he,e.apply_symm_apply]
    exact hh

private theorem swap_mem_iff {Y : Type*} [DecidableEq Y] (t : Set Y) (a b x : Y)
    (hab : a ∈ t ↔ b ∈ t) : Equiv.swap a b x ∈ t ↔ x ∈ t := by
  by_cases hxa : x = a
  · subst x
    simpa using hab.symm
  by_cases hxb : x = b
  · subst x
    simpa using hab
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem exists_swapping
    (G X : Type*) [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (s : Set X) (hs : 1 < s.ncard)
    (hsub : s ⊆ fixedPoints Q X)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (u v : X) (hu : u ∈ fixedPoints Q X) (hv : v ∈ fixedPoints Q X)
    (hus : u ∉ s) (hvs : v ∉ s) (huv : u ≠ v) :
    ∃ g : G, g ∈ Subgroup.normalizer (fixingSubgroup G s : Set G) ∧ g • u = v := by
  classical
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ := Classical.decEq (fixedPoints Q X)
  obtain ⟨a,b,ha,hb,hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite s)).mp hs
  let A : fixedPoints Q X := ⟨a,hsub ha⟩
  let B : fixedPoints Q X := ⟨b,hsub hb⟩
  let U : fixedPoints Q X := ⟨u,hu⟩
  let V : fixedPoints Q X := ⟨v,hv⟩
  have hAB : A ≠ B := fun he => hab (congrArg Subtype.val he)
  have hUV : U ≠ V := fun he => huv (congrArg Subtype.val he)
  let p := Equiv.swap A B * Equiv.swap U V
  have hp : p ∈ alternatingGroup (fixedPoints Q X) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [p,Equiv.Perm.sign_swap hAB,Equiv.Perm.sign_swap hUV]
  rw [← himage] at hp
  obtain ⟨g,hg⟩ := hp
  have hpU : p U = V := by
    have hVA : V ≠ A := by
      intro he
      have ht : v = a := congrArg Subtype.val he
      exact hvs (ht ▸ ha)
    have hVB : V ≠ B := by
      intro he
      have ht : v = b := congrArg Subtype.val he
      exact hvs (ht ▸ hb)
    simp [p,Equiv.swap_apply_of_ne_of_ne hVA hVB]
  have hpbase (x : fixedPoints Q X) : (p x).val ∈ s ↔ x.val ∈ s := by
    let t : Set (fixedPoints Q X) := {x | x.val ∈ s}
    change Equiv.swap A B (Equiv.swap U V x) ∈ t ↔ x ∈ t
    rw [swap_mem_iff t A B _ (by exact ⟨fun _ => hb,fun _ => ha⟩)]
    exact swap_mem_iff t U V x (by exact ⟨fun h => (hus h).elim,fun h => (hvs h).elim⟩)
  have hgbase : ∀ x : X, x ∈ s ↔ (g : G) • x ∈ s := by
    intro x
    constructor
    · intro hx
      have he := congrArg (fun p : Equiv.Perm (fixedPoints Q X) => (p ⟨x,hsub hx⟩).val) hg
      change (g : G) • x = _ at he
      rw [he]
      exact (hpbase _).mpr hx
    · intro hx
      have hxf : x ∈ fixedPoints Q X := by
        have ht := smul_mem_fixedPoints G X Q (g : G)⁻¹
          ((Subgroup.normalizer (Q : Set G)).inv_mem g.property) (hsub hx)
        simpa only [inv_smul_smul] using ht
      have he := congrArg (fun p : Equiv.Perm (fixedPoints Q X) => (p ⟨x,hxf⟩).val) hg
      change (g : G) • x = _ at he
      exact (hpbase _).mp (he ▸ hx)
  refine ⟨g,SetwiseSylowNormalizer.normalizes_fixer s (g : G) hgbase,?_⟩
  have he := congrArg (fun p : Equiv.Perm (fixedPoints Q X) => (p U).val) hg
  change (g : G) • u = _ at he
  exact he.trans (congrArg Subtype.val hpU)

theorem one_lt_card_orbit {H X : Type*} [Group H] [MulAction H X] [Finite X]
    (u : X) (hu : u ∉ fixedPoints H X) : 1 < Nat.card (orbit H u) := by
  classical
  let _ := Fintype.ofFinite (orbit H u)
  have : Nonempty (orbit H u) := ⟨⟨u,mem_orbit_self u⟩⟩
  have hpos : 0 < Nat.card (orbit H u) := Nat.card_pos
  have hne : Nat.card (orbit H u) ≠ 1 := by
    intro he
    exact hu (mem_fixedPoints_iff_card_orbit_eq_one.mpr (by simpa using he))
  omega

end FiveTransitive.NormalizerSwappedOrbits

end CFSG

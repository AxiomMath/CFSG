module

public import CFSG.Monster.B.Geometry.Extension
public import CFSG.Monster.B.Geometry.Rigidity
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

section Companion

variable [Finite W] (hδ : IsWeylDistanceBuilding cs δ)
  (hcent : ∀ w : W, longest cs Set.univ * w = w * longest cs Set.univ)
  {c d : C} (hcd : δ c d = longest cs Set.univ)
include hδ hcd

variable (cs δ) in
@[expose] noncomputable def companion (c d x : C) : C :=
  oppChamber cs δ c d (longest cs Set.univ * δ c x)

omit hδ hcd in
theorem longest_mul_longest : longest cs Set.univ * longest cs Set.univ = (1 : W) :=
  isLongest_univ.mul_self

theorem dist_companion_right (x : C) : δ d (companion cs δ c d x) = δ c x := by
  have h := isApartmentMap_oppChamber hδ hcd (longest cs Set.univ)
    (longest cs Set.univ * δ c x)
  rw [oppChamber_longest hδ hcd, isLongest_univ.inv_eq, ← mul_assoc,
    longest_mul_longest, one_mul] at h
  exact h

theorem dist_companion_left (x : C) :
    δ (companion cs δ c d x) c = (δ c x)⁻¹ * longest cs Set.univ := by
  have h := isApartmentMap_oppChamber hδ hcd (longest cs Set.univ * δ c x) 1
  rw [oppChamber_one hδ hcd, mul_one, mul_inv_rev, isLongest_univ.inv_eq] at h
  exact h

theorem dist_left_companion (x : C) :
    δ c (companion cs δ c d x) = longest cs Set.univ * δ c x :=
  (oppChamber_spec hδ hcd _).1

include hcent in
theorem companion_opposite (x : C) : δ (companion cs δ c d x) x = longest cs Set.univ := by
  have h1 := dist_companion_left hδ hcd x
  have hlen := length_inv_mul_longest (cs := cs) (δ c x)
  have hval : (δ c x)⁻¹ * longest cs Set.univ * δ c x = longest cs Set.univ := by
    rw [mul_assoc, hcent, inv_mul_cancel_left]
  have h := dist_eq_mul_of_length_add hδ (x := companion cs δ c d x) (y := c) (z := x)
    (by rw [h1, hval, ← hlen])
  rw [h, h1, hval]

include hcent in
theorem opposite_companion (x : C) : δ x (companion cs δ c d x) = longest cs Set.univ := by
  rw [dist_inv hδ, companion_opposite hδ hcent hcd x, isLongest_univ.inv_eq]

include hcent in
theorem companion_mem (x : C) :
    oppChamber cs δ x (companion cs δ c d x) (δ x c) = c := by
  refine (eq_oppChamber hδ (opposite_companion hδ hcent hcd x) rfl ?_).symm
  rw [dist_inv hδ, dist_companion_left hδ hcd x, mul_inv_rev, inv_inv, isLongest_univ.inv_eq,
    dist_inv hδ c x, inv_inv, hcent]

include hcent in
theorem companion_step {x y : C} {i : ι} (hxy : δ x y = cs.simple i)
    (hlen : cs.length (δ c y) = cs.length (δ c x) + 1) :
    companion cs δ c d y =
      oppChamber cs δ x (companion cs δ c d x) (longest cs Set.univ * cs.simple i) := by
  have hcy : δ c y = δ c x * cs.simple i := by
    rcases (hδ.mul_simple c x y i hxy).1 with h | h
    · rw [h] at hlen
      omega
    · exact h
  have hval : (δ c y)⁻¹ * longest cs Set.univ * δ c x = cs.simple i * longest cs Set.univ := by
    rw [hcy, mul_inv_rev, cs.inv_simple, mul_assoc, mul_assoc, hcent, inv_mul_cancel_left]
  refine eq_oppChamber hδ (opposite_companion hδ hcent hcd x) ?_ ?_
  ·
    have h1 := dist_companion_left hδ hcd y
    have hl : cs.length ((δ c y)⁻¹ * longest cs Set.univ * δ c x) =
        cs.length ((δ c y)⁻¹ * longest cs Set.univ) + cs.length (δ c x) := by
      have h2 := length_inv_mul_longest (cs := cs) (δ c y)
      have h3 : cs.length (cs.simple i * longest cs Set.univ) + 1 =
          cs.length (longest cs Set.univ) := by
        have := isLongest_univ.length_mul_left (cs := cs) (x := cs.simple i)
          (by rw [cs.parabolic_univ]; trivial)
        rw [cs.length_simple] at this
        exact this
      rw [hval]
      omega
    have h4 := dist_eq_mul_of_length_add hδ (x := companion cs δ c d y) (y := c) (z := x)
      (by rw [h1]; exact hl)
    rw [dist_inv hδ, h4, h1, hval, mul_inv_rev, isLongest_univ.inv_eq, cs.inv_simple]
  ·
    have h := isApartmentMap_oppChamber hδ hcd (longest cs Set.univ * δ c y)
      (longest cs Set.univ * δ c x)
    change δ (companion cs δ c d y) (companion cs δ c d x) = _ at h
    have e1 : (longest cs Set.univ * δ c y)⁻¹ * (longest cs Set.univ * δ c x) =
        cs.simple i := by
      rw [hcy, mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_inv_rev, mul_assoc,
        inv_mul_cancel, mul_one, cs.inv_simple]
    have e2 : (longest cs Set.univ * cs.simple i)⁻¹ * longest cs Set.univ = cs.simple i := by
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, cs.inv_simple]
    rw [h, e1, e2]

end Companion

end CFSG.Monster.B.Geometry

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} {C' : Type*} {δ' : C' → C' → W}

variable (cs δ δ') in
@[expose] def IsGerm (c d : C) (c' d' : C') (x : C) (g : C → C') : Prop :=
  IsWeylIsometry δ δ' (foundation cs δ 2 x ∪ {companion cs δ c d x})
      (foundation cs δ' 2 (g x) ∪ {companion cs δ' c' d' (g x)}) g ∧
    δ' c' (g x) = δ c x

variable (cs δ δ') in
open _root_.Classical in
@[expose] noncomputable def extGerm (c d : C) (c' d' : C') (x : C) (g : C → C') : C → C' :=
  if h : ∃ Φ : C → C', IsWeylIsometry δ δ'
      (foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)))
      (foundation cs δ' 3 (g x) ∪ Set.range (oppChamber cs δ' (g x) (companion cs δ' c' d' (g x))))
      Φ ∧ Set.EqOn Φ g (foundation cs δ 2 x ∪ {companion cs δ c d x}) then h.choose else g

theorem foundation_two_subset_three (hδ : IsWeylDistanceBuilding cs δ) {x y : C} {i : ι}
    (hxy : δ x y = cs.simple i) :
    foundation cs δ 2 y ⊆ foundation cs δ 3 x := by
  intro u hu
  obtain ⟨I, hI, huI⟩ := mem_foundation_iff.mp hu
  have hyx : y ∈ residue cs δ (I ∪ {i}) x :=
    residue_mono Set.subset_union_right x ((mem_panel_iff hδ).mpr (Or.inr hxy))
  refine mem_foundation_iff.mpr ⟨I ∪ {i}, ?_, ?_⟩
  · calc (I ∪ {i}).encard ≤ I.encard + ({i} : Set ι).encard := Set.encard_union_le _ _
      _ ≤ 2 + 1 := by
        rw [Set.encard_singleton]
        exact add_le_add_left (by exact_mod_cast hI) 1
      _ = 3 := by norm_num
  · rw [← residue_eq_of_mem hδ hyx]
    exact residue_mono Set.subset_union_left y huI

section GermExt

variable [Finite W] (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
  (hcent : ∀ w : W, longest cs Set.univ * w = w * longest cs Set.univ)
  (hS : Nat.card ι = 4) (hext : Ext₃ cs δ δ')
  {c d : C} {c' d' : C'} (hcd : δ c d = longest cs Set.univ)
  (hcd' : δ' c' d' = longest cs Set.univ)
include hδ hδ' hcent hS hext hcd hcd'

theorem extGerm_spec {x : C} {g : C → C'} (hg : IsGerm cs δ δ' c d c' d' x g) :
    IsWeylIsometry δ δ'
      (foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)))
      (foundation cs δ' 3 (g x) ∪ Set.range (oppChamber cs δ' (g x) (companion cs δ' c' d' (g x))))
      (extGerm cs δ δ' c d c' d' x g) ∧
    Set.EqOn (extGerm cs δ δ' c d c' d' x g) g (foundation cs δ 2 x ∪ {companion cs δ c d x}) ∧
    (∀ Ψ : C → C', IsWeylIsometry δ δ'
        (foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)))
        (foundation cs δ' 3 (g x) ∪
          Set.range (oppChamber cs δ' (g x) (companion cs δ' c' d' (g x)))) Ψ →
      Set.EqOn Ψ g (foundation cs δ 2 x ∪ {companion cs δ c d x}) →
      Set.EqOn Ψ (extGerm cs δ δ' c d c' d' x g)
        (foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)))) ∧
    (∀ J : Set ι, J.encard ≤ 3 → IsTypeIso cs δ δ' (residue cs δ J x) (residue cs δ' J (g x))
      (extGerm cs δ δ' c d c' d' x g)) ∧
    ∀ u : W, extGerm cs δ δ' c d c' d' x g (oppChamber cs δ x (companion cs δ c d x) u) =
      oppChamber cs δ' (g x) (companion cs δ' c' d' (g x)) u := by
  have hx : x ∈ foundation cs δ 2 x ∪ {companion cs δ c d x} :=
    Or.inl (self_mem_foundation 2 x)
  have hgd : g (companion cs δ c d x) = companion cs δ' c' d' (g x) := by
    rcases hg.1.1.mapsTo (Or.inr rfl) with h | h
    · exfalso
      have h1 : δ' (g x) (g (companion cs δ c d x)) = longest cs Set.univ := by
        rw [hg.1.2 x hx _ (Or.inr rfl), opposite_companion hδ hcent hcd x]
      exact not_mem_foundation_two hδ' hS h1 h
    · exact h
  obtain ⟨-, -, Φ, hΦ, hΦφ, hΦu, hΦR, hΦA⟩ :=
    spherical_foundation_three_and_apartment_extension hδ hδ' hS hext
      (opposite_companion hδ hcent hcd x) (opposite_companion hδ' hcent hcd' (g x)) hg.1 rfl hgd
  have hex : ∃ Φ : C → C', IsWeylIsometry δ δ'
      (foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)))
      (foundation cs δ' 3 (g x) ∪ Set.range (oppChamber cs δ' (g x) (companion cs δ' c' d' (g x))))
      Φ ∧ Set.EqOn Φ g (foundation cs δ 2 x ∪ {companion cs δ c d x}) := ⟨Φ, hΦ, hΦφ⟩
  have hdef : extGerm cs δ δ' c d c' d' x g = hex.choose := by
    rw [extGerm, dite_eq_left hex]
  obtain ⟨hE, hEφ⟩ := hex.choose_spec
  rw [← hdef] at hE hEφ
  have heq := hΦu _ hE hEφ
  refine ⟨hE, hEφ, fun Ψ hΨ hΨφ => (hΦu Ψ hΨ hΨφ).trans heq.symm, fun J hJ => ?_, fun u => ?_⟩
  · have hsub : residue cs δ J x ⊆
        foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)) :=
      (residue_subset_foundation (by exact_mod_cast hJ) x).trans Set.subset_union_left
    refine ⟨?_, fun y hy z hz i => ?_⟩
    · exact (hΦR J hJ).1.congr (heq.symm.mono hsub)
    · rw [heq (hsub hy), heq (hsub hz)]
      exact (hΦR J hJ).2 y hy z hz i
  · rw [heq (Or.inr ⟨u, rfl⟩)]
    exact hΦA u


omit hext hcd' in
theorem IsGerm.map_companion {x : C} {g : C → C'} (hg : IsGerm cs δ δ' c d c' d' x g) :
    g (companion cs δ c d x) = companion cs δ' c' d' (g x) := by
  have hx : x ∈ foundation cs δ 2 x ∪ {companion cs δ c d x} :=
    Or.inl (self_mem_foundation 2 x)
  rcases hg.1.1.mapsTo (Or.inr rfl) with h | h
  · exfalso
    have h1 : δ' (g x) (g (companion cs δ c d x)) = longest cs Set.univ := by
      rw [hg.1.2 x hx _ (Or.inr rfl), opposite_companion hδ hcent hcd x]
    exact not_mem_foundation_two hδ' hS h1 h
  · exact h

theorem extGerm_between {x : C} {g : C → C'} (hg : IsGerm cs δ δ' c d c' d' x g) {e : C}
    (hmul : δ c (companion cs δ c d x) = δ c e * δ e (companion cs δ c d x))
    (hlen : cs.length (δ c (companion cs δ c d x)) =
      cs.length (δ c e) + cs.length (δ e (companion cs δ c d x))) :
    e ∈ Set.range (oppChamber cs δ x (companion cs δ c d x)) ∧
      extGerm cs δ δ' c d c' d' x g e = oppChamber cs δ' c' d' (δ c e) := by
  have hxd := opposite_companion hδ hcent hcd x
  have hap := isApartmentMap_oppChamber hδ hxd
  have hct : oppChamber cs δ x (companion cs δ c d x) (δ x c) = c := companion_mem hδ hcent hcd x
  have hdx : oppChamber cs δ x (companion cs δ c d x) (longest cs Set.univ) =
      companion cs δ c d x := oppChamber_longest hδ hxd
  have hcdx : δ c (companion cs δ c d x) = (δ x c)⁻¹ * longest cs Set.univ := by
    have h := hap (δ x c) (longest cs Set.univ)
    rwa [hct, hdx] at h
  have hlen' : cs.length ((δ c e)⁻¹ * δ c (companion cs δ c d x)) + cs.length (δ c e) =
      cs.length (δ c (companion cs δ c d x)) := by
    rw [hmul, inv_mul_cancel_left, ← hmul, hlen, add_comm]
  have he : e = oppChamber cs δ x (companion cs δ c d x) (δ x c * δ c e) := by
    refine eq_of_dist_eq_of_length_add hδ (x := c) (y := companion cs δ c d x) hlen' rfl
      ?_ ?_ ?_
    · rw [hmul, inv_mul_cancel_left]
    · have h := hap (δ x c) (δ x c * δ c e)
      rwa [hct, inv_mul_cancel_left] at h
    · have h := hap (δ x c * δ c e) (longest cs Set.univ)
      rw [hdx] at h
      rw [h, hcdx, mul_inv_rev, mul_assoc]
  refine ⟨⟨_, he.symm⟩, ?_⟩
  obtain ⟨-, -, -, -, hA⟩ := extGerm_spec hδ hδ' hcent hS hext hcd hcd' hg
  conv_lhs => rw [he]
  rw [hA]
  have hxd' := opposite_companion hδ' hcent hcd' (g x)
  have hap' := isApartmentMap_oppChamber hδ' hxd'
  have ht' : δ' (g x) c' = δ x c := by rw [dist_inv hδ', hg.2, ← dist_inv hδ]
  have hct' : oppChamber cs δ' (g x) (companion cs δ' c' d' (g x)) (δ x c) = c' := by
    rw [← ht']
    exact companion_mem hδ' hcent hcd' (g x)
  have hdx' : oppChamber cs δ' (g x) (companion cs δ' c' d' (g x)) (longest cs Set.univ) =
      companion cs δ' c' d' (g x) := oppChamber_longest hδ' hxd'
  have hcomm : (δ x c)⁻¹ * longest cs Set.univ = longest cs Set.univ * δ c x := by
    rw [dist_inv hδ c x, inv_inv, hcent]
  have hcdx' : δ' c' (companion cs δ' c' d' (g x)) = (δ x c)⁻¹ * longest cs Set.univ := by
    rw [dist_left_companion hδ' hcd', hg.2, hcomm]
  have hlen'' : cs.length ((δ c e)⁻¹ * δ' c' (companion cs δ' c' d' (g x))) +
      cs.length (δ c e) = cs.length (δ' c' (companion cs δ' c' d' (g x))) := by
    rw [hcdx', ← hcdx]
    exact hlen'
  refine eq_of_dist_eq_of_length_add hδ' (x := c') (y := companion cs δ' c' d' (g x)) hlen''
    ?_ ?_ ?_ ?_
  · have h := hap' (δ x c) (δ x c * δ c e)
    rwa [hct', inv_mul_cancel_left] at h
  · have h := hap' (δ x c * δ c e) (longest cs Set.univ)
    rw [hdx'] at h
    rw [h, hcdx', mul_inv_rev, mul_assoc]
  · exact (oppChamber_spec hδ' hcd' (δ c e)).1
  · have h1 := isApartmentMap_oppChamber hδ' hcd' (δ c e) (longest cs Set.univ * δ' c' (g x))
    change δ' (oppChamber cs δ' c' d' (δ c e)) (companion cs δ' c' d' (g x)) = _ at h1
    rw [h1, hcdx', hcomm, hg.2]

theorem extGerm_base {x : C} {g : C → C'} (hg : IsGerm cs δ δ' c d c' d' x g) :
    extGerm cs δ δ' c d c' d' x g c = c' := by
  have h := (extGerm_between hδ hδ' hcent hS hext hcd hcd' hg (e := c)
    (by rw [hδ.eq_one_self, one_mul]) (by rw [hδ.eq_one_self, cs.length_one, zero_add])).2
  rw [h, hδ.eq_one_self, oppChamber_one hδ' hcd']

theorem isGerm_extGerm {x y : C} {g : C → C'} (hg : IsGerm cs δ δ' c d c' d' x g) {i : ι}
    (hxy : δ x y = cs.simple i) (hlen : cs.length (δ c y) = cs.length (δ c x) + 1) :
    IsGerm cs δ δ' c d c' d' y (extGerm cs δ δ' c d c' d' x g) := by
  obtain ⟨hE, hEg, -, -, hA⟩ := extGerm_spec hδ hδ' hcent hS hext hcd hcd' hg
  set Φ := extGerm cs δ δ' c d c' d' x g
  set x' := g x
  have hΦx : Φ x = x' := hEg (Or.inl (self_mem_foundation 2 x))
  have hxdom : x ∈ foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)) :=
    Or.inl (self_mem_foundation 3 x)
  have hydom : y ∈ foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)) :=
    Or.inl (foundation_two_subset_three hδ hxy (self_mem_foundation 2 y))
  have hcdom : c ∈ foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)) :=
    Or.inr ⟨_, companion_mem hδ hcent hcd x⟩
  set y' := Φ y
  have hxy' : δ' x' y' = cs.simple i := by rw [← hΦx, hE.2 x hxdom y hydom, hxy]
  have hcy' : δ' c' y' = δ c y := by
    rw [← extGerm_base hδ hδ' hcent hS hext hcd hcd' hg, hE.2 c hcdom y hydom]
  have hlen' : cs.length (δ' c' y') = cs.length (δ' c' x') + 1 := by
    rw [hcy', hg.2, hlen]
  have hcomp : Φ (companion cs δ c d y) = companion cs δ' c' d' y' := by
    rw [companion_step hδ hcent hcd hxy hlen, hA, companion_step hδ' hcent hcd' hxy' hlen']
  have hcompdom : companion cs δ c d y ∈
      foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)) := by
    rw [companion_step hδ hcent hcd hxy hlen]
    exact Or.inr ⟨_, rfl⟩
  have hsub : foundation cs δ 2 y ∪ {companion cs δ c d y} ⊆
      foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x)) := by
    rintro u (hu | hu)
    · exact Or.inl (foundation_two_subset_three hδ hxy hu)
    · rw [Set.mem_singleton_iff.mp hu]
      exact hcompdom
  refine ⟨⟨⟨?_, hE.1.injOn.mono hsub, ?_⟩, fun u hu v hv => hE.2 u (hsub hu) v (hsub hv)⟩, hcy'⟩
  · rintro u (hu | hu)
    · obtain ⟨I, hI, huI⟩ := mem_foundation_iff.mp hu
      refine Or.inl (mem_foundation_iff.mpr ⟨I, hI, ?_⟩)
      exact hE.mem_residue hδ hδ' hydom (hsub (Or.inl hu)) huI
    · rw [Set.mem_singleton_iff.mp hu, hcomp]
      exact Or.inr rfl
  · rintro u' (hu' | hu')
    · obtain ⟨I, hI, huI⟩ := mem_foundation_iff.mp hu'
      have hu'dom : u' ∈ foundation cs δ' 3 x' ∪
          Set.range (oppChamber cs δ' x' (companion cs δ' c' d' x')) :=
        Or.inl (foundation_two_subset_three hδ' hxy' hu')
      obtain ⟨u, hu, rfl⟩ := hE.1.surjOn hu'dom
      rw [hE.mem_residue_iff hδ hδ' hydom hu] at huI
      exact ⟨u, Or.inl (mem_foundation_iff.mpr ⟨I, hI, huI⟩), rfl⟩
    · rw [Set.mem_singleton_iff.mp hu']
      exact ⟨_, Or.inr rfl, hcomp⟩

omit [Finite W] hδ hδ' hcent hS hext hcd hcd' in
theorem IsGerm.congr {x : C} {g₁ g₂ : C → C'} (hg : IsGerm cs δ δ' c d c' d' x g₁)
    (h : Set.EqOn g₁ g₂ (foundation cs δ 2 x ∪ {companion cs δ c d x})) :
    IsGerm cs δ δ' c d c' d' x g₂ := by
  have hx : g₁ x = g₂ x := h (Or.inl (self_mem_foundation 2 x))
  refine ⟨⟨?_, fun y hy z hz => ?_⟩, ?_⟩
  · rw [← hx]
    exact hg.1.1.congr h
  · rw [← h hy, ← h hz]
    exact hg.1.2 y hy z hz
  · rw [← hx]
    exact hg.2

theorem extGerm_congr {x : C} {g₁ g₂ : C → C'} (hg : IsGerm cs δ δ' c d c' d' x g₁)
    (h : Set.EqOn g₁ g₂ (foundation cs δ 2 x ∪ {companion cs δ c d x})) :
    Set.EqOn (extGerm cs δ δ' c d c' d' x g₁) (extGerm cs δ δ' c d c' d' x g₂)
      (foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x (companion cs δ c d x))) := by
  have hg₂ := hg.congr h
  have hx : g₁ x = g₂ x := h (Or.inl (self_mem_foundation 2 x))
  obtain ⟨hE₂, hEg₂, -, -, -⟩ := extGerm_spec hδ hδ' hcent hS hext hcd hcd' hg₂
  obtain ⟨-, -, huniq, -, -⟩ := extGerm_spec hδ hδ' hcent hS hext hcd hcd' hg
  rw [← hx] at hE₂
  exact (huniq _ hE₂ (hEg₂.trans h.symm)).symm

end GermExt

variable (cs δ) in
@[expose] def Ascending (c x : C) (γ : List (ι × C)) : Prop :=
  IsStrictGallery cs δ x γ ∧ cs.length (δ c (galleryEnd x γ)) = cs.length (δ c x) + γ.length

theorem length_dist_le_of_isStrictGallery (hδ : IsWeylDistanceBuilding cs δ) (c : C) {x : C}
    {γ : List (ι × C)} (hγ : IsStrictGallery cs δ x γ) :
    cs.length (δ c (galleryEnd x γ)) ≤ cs.length (δ c x) + γ.length := by
  induction γ generalizing x with
  | nil => simp
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    have h3 := ih h2
    have h4 : cs.length (δ c p.2) ≤ cs.length (δ c x) + 1 := by
      rcases (hδ.mul_simple c x p.2 p.1 h1).1 with h | h <;> rw [h]
      · omega
      · have := cs.length_mul_le (δ c x) (cs.simple p.1)
        rw [cs.length_simple] at this
        exact this
    simp only [galleryEnd_cons, List.length_cons] at h3 ⊢
    omega

theorem ascending_cons_iff (hδ : IsWeylDistanceBuilding cs δ) {c x : C} {p : ι × C}
    {γ : List (ι × C)} :
    Ascending cs δ c x (p :: γ) ↔ δ x p.2 = cs.simple p.1 ∧
      cs.length (δ c p.2) = cs.length (δ c x) + 1 ∧ Ascending cs δ c p.2 γ := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h4 := length_dist_le_of_isStrictGallery hδ c h2
    have h5 : cs.length (δ c p.2) ≤ cs.length (δ c x) + 1 := by
      rcases (hδ.mul_simple c x p.2 p.1 h1).1 with h | h <;> rw [h]
      · omega
      · have := cs.length_mul_le (δ c x) (cs.simple p.1)
        rw [cs.length_simple] at this
        exact this
    simp only [galleryEnd_cons, List.length_cons] at h3
    refine ⟨h1, by omega, h2, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h3⟩, ?_⟩
    simp only [galleryEnd_cons, List.length_cons]
    omega

theorem ascending_append_iff (hδ : IsWeylDistanceBuilding cs δ) {c x : C}
    {γ η : List (ι × C)} :
    Ascending cs δ c x (γ ++ η) ↔ Ascending cs δ c x γ ∧ Ascending cs δ c (galleryEnd x γ) η := by
  induction γ generalizing x with
  | nil =>
    simp only [List.nil_append, galleryEnd_nil]
    exact ⟨fun h => ⟨⟨trivial, by simp⟩, h⟩, fun h => h.2⟩
  | cons p γ ih =>
    rw [List.cons_append, ascending_cons_iff hδ, ascending_cons_iff hδ, ih]
    simp only [galleryEnd_cons]
    tauto

theorem ascending_of_isReduced (hδ : IsWeylDistanceBuilding cs δ) {c : C} {γ : List (ι × C)}
    (hγ : IsStrictGallery cs δ c γ) (hred : cs.IsReduced (galleryType γ)) :
    Ascending cs δ c c γ := by
  refine ⟨hγ, ?_⟩
  rw [hγ.dist_eq hδ hred, hred.eq, hδ.eq_one_self, cs.length_one, zero_add, length_galleryType]

variable (cs δ δ') in
@[expose] noncomputable def transport (c d : C) (c' d' : C') :
    C → (C → C') → List (ι × C) → (C → C')
  | _, g, [] => g
  | x, g, p :: γ => transport c d c' d' p.2 (extGerm cs δ δ' c d c' d' x g) γ

@[simp] theorem transport_nil (c d : C) (c' d' : C') (x : C) (g : C → C') :
    transport cs δ δ' c d c' d' x g [] = g := rfl

@[simp] theorem transport_cons (c d : C) (c' d' : C') (x : C) (g : C → C') (p : ι × C)
    (γ : List (ι × C)) :
    transport cs δ δ' c d c' d' x g (p :: γ) =
      transport cs δ δ' c d c' d' p.2 (extGerm cs δ δ' c d c' d' x g) γ := rfl

theorem transport_append (c d : C) (c' d' : C') (x : C) (g : C → C') (γ η : List (ι × C)) :
    transport cs δ δ' c d c' d' x g (γ ++ η) =
      transport cs δ δ' c d c' d' (galleryEnd x γ) (transport cs δ δ' c d c' d' x g γ) η := by
  induction γ generalizing x g with
  | nil => rfl
  | cons p γ ih => exact ih p.2 _

theorem transport_concat (c d : C) (c' d' : C') (x : C) (g : C → C') (γ : List (ι × C))
    (p : ι × C) :
    transport cs δ δ' c d c' d' x g (γ ++ [p]) =
      extGerm cs δ δ' c d c' d' (galleryEnd x γ) (transport cs δ δ' c d c' d' x g γ) := by
  rw [transport_append]
  rfl

section Transport

variable [Finite W] (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
  (hcent : ∀ w : W, longest cs Set.univ * w = w * longest cs Set.univ)
  (hS : Nat.card ι = 4) (hext : Ext₃ cs δ δ')
  {c d : C} {c' d' : C'} (hcd : δ c d = longest cs Set.univ)
  (hcd' : δ' c' d' = longest cs Set.univ)
include hδ hδ' hcent hS hext hcd hcd'

theorem isGerm_transport {x : C} {g : C → C'} (hg : IsGerm cs δ δ' c d c' d' x g)
    {γ : List (ι × C)} (hγ : Ascending cs δ c x γ) :
    IsGerm cs δ δ' c d c' d' (galleryEnd x γ) (transport cs δ δ' c d c' d' x g γ) := by
  induction γ generalizing x g with
  | nil => exact hg
  | cons p γ ih =>
    obtain ⟨h1, h2, h3⟩ := (ascending_cons_iff hδ).mp hγ
    exact ih (isGerm_extGerm hδ hδ' hcent hS hext hcd hcd' hg h1 h2) h3

theorem transport_congr {x : C} {g₁ g₂ : C → C'} (hg : IsGerm cs δ δ' c d c' d' x g₁)
    (h : Set.EqOn g₁ g₂ (foundation cs δ 2 x ∪ {companion cs δ c d x}))
    {γ : List (ι × C)} (hγ : Ascending cs δ c x γ) :
    Set.EqOn (transport cs δ δ' c d c' d' x g₁ γ) (transport cs δ δ' c d c' d' x g₂ γ)
      (foundation cs δ 2 (galleryEnd x γ) ∪ {companion cs δ c d (galleryEnd x γ)}) := by
  induction γ generalizing x g₁ g₂ with
  | nil => exact h
  | cons p γ ih =>
    obtain ⟨h1, h2, h3⟩ := (ascending_cons_iff hδ).mp hγ
    refine ih (isGerm_extGerm hδ hδ' hcent hS hext hcd hcd' hg h1 h2) ?_ h3
    have hE := extGerm_congr hδ hδ' hcent hS hext hcd hcd' hg h
    refine hE.mono ?_
    rintro u (hu | hu)
    · exact Or.inl (foundation_two_subset_three hδ h1 hu)
    · rw [Set.mem_singleton_iff.mp hu, companion_step hδ hcent hcd h1 h2]
      exact Or.inr ⟨_, rfl⟩

end Transport

end CFSG.Monster.B.Geometry

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} {C' : Type*} {δ' : C' → C' → W}

theorem Ascending.dist_eq (hδ : IsWeylDistanceBuilding cs δ) {c u : C} {γ : List (ι × C)}
    (hγ : Ascending cs δ c u γ) :
    δ c (galleryEnd u γ) = δ c u * cs.wordProd (galleryType γ) ∧
      cs.IsReduced (galleryType γ) := by
  induction γ using List.reverseRecOn with
  | nil => simp [CoxeterSystem.IsReduced]
  | append_singleton γ p ih =>
    have h := (ascending_append_iff hδ).mp hγ
    obtain ⟨h1, h2, -⟩ := (ascending_cons_iff hδ).mp h.2
    obtain ⟨ih1, ih2⟩ := ih h.1
    have hstep : δ c p.2 = δ c (galleryEnd u γ) * cs.simple p.1 := by
      rcases (hδ.mul_simple c _ p.2 p.1 h1).1 with h' | h'
      · rw [h'] at h2
        omega
      · exact h'
    have hlen := hγ.2
    simp only [galleryEnd_concat, List.length_append, List.length_singleton] at hlen
    refine ⟨?_, ?_⟩
    · rw [galleryEnd_concat, hstep, ih1, galleryType_append, cs.wordProd_append, mul_assoc]
      simp [galleryType]
    · rw [CoxeterSystem.IsReduced]
      have hle := cs.length_wordProd_le (galleryType (γ ++ [p]))
      have hge := cs.length_mul_le (δ c u) (cs.wordProd (galleryType (γ ++ [p])))
      have heq : δ c u * cs.wordProd (galleryType (γ ++ [p])) = δ c p.2 := by
        rw [hstep, ih1, galleryType_append, cs.wordProd_append, mul_assoc]
        simp [galleryType]
      rw [heq] at hge
      simp only [length_galleryType, List.length_append, List.length_singleton] at hle ⊢
      omega

theorem IsStrictGallery.end_mem_residue {K : Set ι} {x : C} {γ : List (ι × C)}
    (hγ : IsStrictGallery cs δ x γ) (hK : ∀ k ∈ galleryType γ, k ∈ K) :
    galleryEnd x γ ∈ residue cs δ K x :=
  mem_residue_iff.mpr ⟨γ, hγ, hK, rfl⟩

theorem exists_subset_pair_of_encard_le_two {I : Set ι} (hI : I.encard ≤ 2) (hne : I.Nonempty) :
    ∃ k l : ι, I ⊆ {k, l} := by
  obtain ⟨k, hk⟩ := hne
  by_cases hI1 : (I \ {k}).Nonempty
  · obtain ⟨l, hl⟩ := hI1
    refine ⟨k, l, fun m hm => ?_⟩
    by_cases hmk : m = k
    · exact Or.inl hmk
    · right
      have h2 : (I \ {k}).encard ≤ 1 := by
        have h3 := Set.encard_sdiff_singleton_add_one hk
        have h5 : (I \ {k}).encard + 1 ≤ 2 := h3 ▸ hI
        by_contra hcon
        push Not at hcon
        have h4 : (1 : ℕ∞) + 1 ≤ (I \ {k}).encard := Order.add_one_le_of_lt hcon
        have h6 : (1 : ℕ∞) + 1 + 1 ≤ 2 := (add_le_add_left h4 1).trans h5
        norm_num at h6
      exact Set.encard_le_one_iff.mp h2 m l ⟨hm, hmk⟩ hl
  · refine ⟨k, k, fun m hm => ?_⟩
    by_cases hmk : m = k
    · exact Or.inl hmk
    · exact absurd ⟨m, hm, hmk⟩ hI1

theorem encard_pair_le_two (i j : ι) : ({i, j} : Set ι).encard ≤ 2 := by
  refine (Set.encard_insert_le _ _).trans ?_
  rw [Set.encard_singleton]
  norm_num

section Braid

variable [Finite W] (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
  (hcent : ∀ w : W, longest cs Set.univ * w = w * longest cs Set.univ)
  (hS : Nat.card ι = 4) (hext : Ext₃ cs δ δ')
  {c d : C} {c' d' : C'} (hcd : δ c d = longest cs Set.univ)
  (hcd' : δ' c' d' = longest cs Set.univ)
include hδ hδ' hcent hS hext hcd hcd'

omit hδ' hS hext hcd' in
theorem companion_between {u : C} {γ : List (ι × C)} (hγ : Ascending cs δ c u γ) :
    δ c (companion cs δ c d u) = δ c (companion cs δ c d (galleryEnd u γ)) *
        δ (companion cs δ c d (galleryEnd u γ)) (companion cs δ c d u) ∧
      cs.length (δ c (companion cs δ c d u)) =
        cs.length (δ c (companion cs δ c d (galleryEnd u γ))) +
          cs.length (δ (companion cs δ c d (galleryEnd u γ)) (companion cs δ c d u)) := by
  obtain ⟨hdist, hred⟩ := hγ.dist_eq hδ
  have h1 := dist_left_companion hδ hcd (galleryEnd u γ)
  have h2 : δ (companion cs δ c d (galleryEnd u γ)) (companion cs δ c d u) =
      (cs.wordProd (galleryType γ))⁻¹ := by
    have h := isApartmentMap_oppChamber hδ hcd (longest cs Set.univ * δ c (galleryEnd u γ))
      (longest cs Set.univ * δ c u)
    change δ (companion cs δ c d (galleryEnd u γ)) (companion cs δ c d u) = _ at h
    rw [h, hdist, mul_inv_rev, mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc
      (longest cs Set.univ)⁻¹, isLongest_univ.inv_eq, longest_mul_longest, one_mul,
      inv_mul_cancel, mul_one]
  have h3 := dist_left_companion hδ hcd u
  refine ⟨by rw [h1, h2, h3, hdist, mul_assoc, mul_inv_cancel_right], ?_⟩
  rw [h1, h2, h3, cs.length_inv, hred.eq, length_galleryType]
  have hl1 := isLongest_univ.length_mul_left (cs := cs) (x := δ c (galleryEnd u γ))
    (by rw [cs.parabolic_univ]; trivial)
  have hl2 := isLongest_univ.length_mul_left (cs := cs) (x := δ c u)
    (by rw [cs.parabolic_univ]; trivial)
  rw [← hcent] at hl1 hl2
  have hl3 := hγ.2
  omega

theorem transport_eqOn_extGerm {u : C} {g : C → C'} (hg : IsGerm cs δ δ' c d c' d' u g)
    {i j : ι} {K : Set ι} (hK : {i, j} ⊆ K) (hK3 : K.ncard = 3 ∨ K = {i, j})
    {γ : List (ι × C)} (hγ : Ascending cs δ c u γ)
    (hγt : ∀ k ∈ galleryType γ, k ∈ ({i, j} : Set ι)) :
    Set.EqOn (transport cs δ δ' c d c' d' u g γ) (extGerm cs δ δ' c d c' d' u g)
      (foundation cs δ 2 (galleryEnd u γ) ∩ residue cs δ K u) := by
  obtain ⟨hE, hEg, -, hER, -⟩ := extGerm_spec hδ hδ' hcent hS hext hcd hcd' hg
  set Φ := extGerm cs δ δ' c d c' d' u g
  have hK3' : K.encard ≤ 3 := by
    rcases hK3 with h | rfl
    · have hKf : K.Finite := Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
      rw [← hKf.cast_ncard_eq, h]
      rfl
    · exact (encard_pair_le_two i j).trans (by norm_num)
  induction γ using List.reverseRecOn with
  | nil =>
    intro w hw
    exact (hEg (Or.inl hw.1)).symm
  | append_singleton γ p ih =>
    have hsplit := (ascending_append_iff hδ).mp hγ
    obtain ⟨hstep, hstepl, -⟩ := (ascending_cons_iff hδ).mp hsplit.2
    have hγt' : ∀ k ∈ galleryType γ, k ∈ ({i, j} : Set ι) := fun k hk =>
      hγt k (by simp [galleryType_append, hk])
    have IH := ih hsplit.1 hγt'
    set z := galleryEnd u γ
    set g₀ := transport cs δ δ' c d c' d' u g γ
    have hg₀ : IsGerm cs δ δ' c d c' d' z g₀ :=
      isGerm_transport hδ hδ' hcent hS hext hcd hcd' hg hsplit.1
    have htr : transport cs δ δ' c d c' d' u g (γ ++ [p]) = extGerm cs δ δ' c d c' d' z g₀ :=
      transport_concat _ _ _ _ u g γ p
    rw [htr, galleryEnd_concat]
    have hzR : z ∈ residue cs δ {i, j} u := hsplit.1.1.end_mem_residue hγt'
    have hzK : z ∈ residue cs δ K u := residue_mono hK u hzR
    obtain ⟨hEz, hEzg, -, hEzR, hEzA⟩ := extGerm_spec hδ hδ' hcent hS hext hcd hcd' hg₀
    have hRK : residue cs δ K z = residue cs δ K u := residue_eq_of_mem hδ hzK
    rcases hK3 with hK3 | rfl
    ·
      set z' := g₀ z
      have hz' : Φ z = z' := (IH ⟨self_mem_foundation 2 z, hzK⟩).symm
      have hxd := opposite_companion hδ hcent hcd z
      have hxd' := opposite_companion hδ' hcent hcd' z'
      set q := oppChamber cs δ z (companion cs δ c d z) (longest cs K)
      set q' := oppChamber cs δ' z' (companion cs δ' c' d' z') (longest cs K)
      have hq := isProjection_oppChamber_longest hδ hxd K
      have hq' := isProjection_oppChamber_longest hδ' hxd' K
      have hgd := hg₀.map_companion hδ hδ' hcent hS hcd
      classical
      let f : C → C' := fun w => if w = q then q' else g₀ w
      have hfF : ∀ w ∈ residueFoundation cs δ K z, f w = g₀ w := fun w hw =>
        ite_eq_right fun (h : w = q) =>
          oppChamber_longest_not_mem_residueFoundation hδ hxd hK3 (by subst h; exact hw)
      have hfq : f q = q' := ite_eq_left rfl
      have hloc := isWeylIsometry_localMap hδ hδ' hS hxd hxd' hg₀.1 rfl hgd hfF hfq
      have huniq := (hext K hK3 z q z' q' hq.1 hq'.1 (oppChamber_spec hδ hxd _).1
        (oppChamber_spec hδ' hxd' _).1 f hloc
        ((hfF z (mem_residueFoundation_iff.mpr ⟨∅, ⟨Set.empty_subset K, by simp⟩,
          self_mem_residue _ z⟩)).trans rfl) hfq).2
      have hΦz := hEzR K hK3'
      have hΦK : IsTypeIso cs δ δ' (residue cs δ K z) (residue cs δ' K z') Φ := by
        have h := hER K hK3'
        have hz'K : z' ∈ residue cs δ' K (g u) := by
          rw [← hz']
          exact h.1.mapsTo hzK
        rw [hRK, residue_eq_of_mem hδ' hz'K]
        exact h
      have hΦzf : Set.EqOn (extGerm cs δ δ' c d c' d' z g₀) f
          (residueFoundation cs δ K z ∪ {q}) := by
        rintro w (hw | hw)
        · rw [hfF w hw]
          exact hEzg (Or.inl (residueFoundation_subset_foundation K z hw))
        · rw [Set.mem_singleton_iff.mp hw, hfq]
          exact hEzA _
      have hΦf : Set.EqOn Φ f (residueFoundation cs δ K z ∪ {q}) := by
        rintro w (hw | hw)
        · rw [hfF w hw]
          refine (IH ⟨residueFoundation_subset_foundation K z hw, ?_⟩).symm
          rw [← hRK]
          exact residueFoundation_subset_residue K z hw
        · rw [Set.mem_singleton_iff.mp hw, hfq]
          obtain ⟨hmul, hlen⟩ := companion_between hδ hcent hcd hsplit.1
          obtain ⟨hdz, hΦdz⟩ := extGerm_between hδ hδ' hcent hS hext hcd hcd' hg hmul hlen
          have hΦdz' : Φ (companion cs δ c d z) =
              oppChamber cs δ' c' d' (δ c (companion cs δ c d z)) := hΦdz
          have hz'c : δ' c' z' = δ c z := hg₀.2
          have hcz : Φ (companion cs δ c d z) = companion cs δ' c' d' z' := by
            rw [hΦdz', dist_left_companion hδ hcd z, companion, hz'c]
          have hdom : ∀ w ∈ residue cs δ K z, w ∈ foundation cs δ 3 u ∪
              Set.range (oppChamber cs δ u (companion cs δ c d u)) := fun w hw =>
            Or.inl (residue_subset_foundation hK3' u (hRK ▸ hw))
          have hmap := hq.map hΦK.1 (fun w hw => hE.2 _ (Or.inr hdz) w (hdom w hw))
          rw [hcz] at hmap
          exact hmap.unique hq'
      have heq := huniq _ _ hΦz hΦK hΦzf hΦf
      intro w hw
      exact heq (hRK ▸ hw.2)
    ·
      intro w hw
      have hwz : w ∈ residue cs δ {i, j} z := by
        rw [residue_eq_of_mem hδ hzR]
        exact hw.2
      have hwF : w ∈ foundation cs δ 2 z :=
        residue_subset_foundation (encard_pair_le_two i j) z hwz
      rw [hEzg (Or.inl hwF)]
      exact IH ⟨hwF, hw.2⟩

omit hext in
theorem germ_eqOn_residue_pair (hrig' : Rig₂ cs δ') {y : C} {G₁ G₂ : C → C'}
    (h₁ : IsGerm cs δ δ' c d c' d' y G₁) (h₂ : IsGerm cs δ δ' c d c' d' y G₂)
    (hy : G₁ y = G₂ y) {k l : ι} (hkl : k ≠ l) (hk : Set.EqOn G₁ G₂ (panel cs δ k y))
    (hl : Set.EqOn G₁ G₂ (panel cs δ l y)) :
    Set.EqOn G₁ G₂ (residue cs δ {k, l} y) := by
  have : Nonempty C := ⟨y⟩
  set y' := G₂ y
  have hydom : y ∈ foundation cs δ 2 y ∪ {companion cs δ c d y} :=
    Or.inl (self_mem_foundation 2 y)
  have hsub : ∀ (J : Set ι) (x : C), J.encard ≤ 2 →
      residue cs δ J x ⊆ foundation cs δ 2 x ∪ {companion cs δ c d x} := fun J x hJ =>
    (residue_subset_foundation (by exact_mod_cast hJ) x).trans Set.subset_union_left
  have hsub' : ∀ (J : Set ι) (x : C'), J.encard ≤ 2 →
      residue cs δ' J x ⊆ foundation cs δ' 2 x ∪ {companion cs δ' c' d' x} := fun J x hJ =>
    (residue_subset_foundation (by exact_mod_cast hJ) x).trans Set.subset_union_left
  have hkl2 := encard_pair_le_two k l
  have hk1 : ({k} : Set ι).encard ≤ 2 := by rw [Set.encard_singleton]; norm_num
  have hl1 : ({l} : Set ι).encard ≤ 2 := by rw [Set.encard_singleton]; norm_num
  have hb₁ : Set.BijOn G₁ (residue cs δ {k, l} y) (residue cs δ' {k, l} y') :=
    h₁.1.bijOn_residue hδ hδ' hydom hy (hsub _ y hkl2) (hy ▸ hsub' _ (G₁ y) hkl2)
  have hb₂ : Set.BijOn G₂ (residue cs δ {k, l} y) (residue cs δ' {k, l} y') :=
    h₂.1.bijOn_residue hδ hδ' hydom rfl (hsub _ y hkl2) (hsub' _ y' hkl2)
  set G₂inv := Function.invFunOn G₂ (residue cs δ {k, l} y)
  have hinv : Set.InvOn G₂inv G₂ (residue cs δ {k, l} y) (residue cs δ' {k, l} y') :=
    hb₂.invOn_invFunOn
  have hbinv : Set.BijOn G₂inv (residue cs δ' {k, l} y') (residue cs δ {k, l} y) :=
    hinv.symm.bijOn hb₂.surjOn.mapsTo_invFunOn hb₂.mapsTo
  set θ : C' → C' := G₁ ∘ G₂inv
  have hθb : Set.BijOn θ (residue cs δ' {k, l} y') (residue cs δ' {k, l} y') := hb₁.comp hbinv
  have hθ : IsTypeIso cs δ' δ' (residue cs δ' {k, l} y') (residue cs δ' {k, l} y') θ := by
    refine ⟨hθb, fun a ha b hb i => ?_⟩
    have ha₀ := hbinv.mapsTo ha
    have hb₀ := hbinv.mapsTo hb
    change δ' (G₁ (G₂inv a)) (G₁ (G₂inv b)) = _ ↔ _
    rw [h₁.1.2 _ (hsub _ y hkl2 ha₀) _ (hsub _ y hkl2 hb₀),
      ← h₂.1.2 _ (hsub _ y hkl2 ha₀) _ (hsub _ y hkl2 hb₀), hinv.2 ha, hinv.2 hb]
  have hxd := opposite_companion hδ hcent hcd y
  have hxd' := opposite_companion hδ' hcent hcd' y'
  have hq := isProjection_oppChamber_longest hδ hxd {k, l}
  have hq' := isProjection_oppChamber_longest hδ' hxd' {k, l}
  have hproj : ∀ G : C → C', IsGerm cs δ δ' c d c' d' y G → G y = y' →
      Set.BijOn G (residue cs δ {k, l} y) (residue cs δ' {k, l} y') →
      G (oppChamber cs δ y (companion cs δ c d y) (longest cs {k, l})) =
        oppChamber cs δ' y' (companion cs δ' c' d' y') (longest cs {k, l}) := by
    intro G hG hGy hGb
    have hm := hq.map hGb (fun w hw => hG.1.2 _ (Or.inr rfl) w (hsub _ y hkl2 hw))
    rw [hG.map_companion hδ hδ' hcent hS hcd, hGy] at hm
    exact hm.unique hq'
  have hG₁b := hproj G₁ h₁ hy hb₁
  have hG₂b := hproj G₂ h₂ rfl hb₂
  have hθq : θ (oppChamber cs δ' y' (companion cs δ' c' d' y') (longest cs {k, l})) =
      oppChamber cs δ' y' (companion cs δ' c' d' y') (longest cs {k, l}) := by
    change G₁ (G₂inv _) = _
    have hinvb : G₂inv (oppChamber cs δ' y' (companion cs δ' c' d' y') (longest cs {k, l})) =
        oppChamber cs δ y (companion cs δ c d y) (longest cs {k, l}) := by
      rw [← hG₂b]
      exact hinv.1 hq.1
    rw [hinvb, hG₁b]
  have hpanel : ∀ m ∈ ({k, l} : Set ι), Set.EqOn G₁ G₂ (panel cs δ m y) →
      ∀ a ∈ panel cs δ' m y', θ a = a := by
    intro m hm hGm a ha
    have hm1 : ({m} : Set ι).encard ≤ 2 := by rw [Set.encard_singleton]; norm_num
    have hbm : Set.BijOn G₂ (panel cs δ m y) (panel cs δ' m y') :=
      h₂.1.bijOn_residue hδ hδ' hydom rfl (hsub _ y hm1) (hsub' _ y' hm1)
    obtain ⟨a₀, ha₀, rfl⟩ := hbm.surjOn ha
    have ha₀R : a₀ ∈ residue cs δ {k, l} y :=
      residue_mono (Set.singleton_subset_iff.mpr hm) y ha₀
    change G₁ (G₂inv (G₂ a₀)) = G₂ a₀
    rw [hinv.1 ha₀R]
    exact hGm ha₀
  have hfix := hrig' k l hkl y' _ hq'.1 (oppChamber_spec hδ' hxd' _).1 θ hθ hθq (by
    rintro a (ha | ha)
    · exact hpanel k (by simp) hk a ha
    · exact hpanel l (by simp) hl a ha)
  intro w hw
  have := hfix (G₂ w) (hb₂.mapsTo hw)
  change G₁ (G₂inv (G₂ w)) = G₂ w at this
  rwa [hinv.1 hw] at this

omit hext in
theorem germ_eqOn_of_panels (hrig' : Rig₂ cs δ') {y : C} {G₁ G₂ : C → C'}
    (h₁ : IsGerm cs δ δ' c d c' d' y G₁) (h₂ : IsGerm cs δ δ' c d c' d' y G₂)
    (hpan : ∀ k, Set.EqOn G₁ G₂ (panel cs δ k y)) :
    Set.EqOn G₁ G₂ (foundation cs δ 2 y ∪ {companion cs δ c d y}) := by
  obtain ⟨k₀⟩ : Nonempty ι := (Nat.card_pos_iff.mp (by rw [hS]; norm_num)).1
  have hy : G₁ y = G₂ y := hpan k₀ (self_mem_residue _ y)
  rintro w (hw | hw)
  · obtain ⟨I, hI, hwI⟩ := mem_foundation_iff.mp hw
    rcases I.eq_empty_or_nonempty with rfl | hne
    · rw [mem_residue_iff_mem_parabolic hδ, cs.parabolic_empty, Subgroup.mem_bot,
        hδ.eq_one_iff] at hwI
      rw [← hwI, hy]
    obtain ⟨k, l, hkl⟩ := exists_subset_pair_of_encard_le_two (by exact_mod_cast hI) hne
    have hwkl : w ∈ residue cs δ {k, l} y := residue_mono hkl y hwI
    by_cases hkl' : k = l
    · subst hkl'
      rw [Set.pair_eq_singleton] at hwkl
      exact hpan k hwkl
    · exact germ_eqOn_residue_pair hδ hδ' hcent hS hcd hcd' hrig' h₁ h₂ hy hkl' (hpan k)
        (hpan l) hwkl
  · rw [Set.mem_singleton_iff.mp hw, h₁.map_companion hδ hδ' hcent hS hcd,
      h₂.map_companion hδ hδ' hcent hS hcd, hy]

theorem transport_eqOn_of_pair (hrig' : Rig₂ cs δ') {u : C} {g : C → C'}
    (hg : IsGerm cs δ δ' c d c' d' u g) {i j : ι} (hij : i ≠ j) {η η' : List (ι × C)}
    (hη : Ascending cs δ c u η) (hη' : Ascending cs δ c u η')
    (ht : ∀ k ∈ galleryType η, k ∈ ({i, j} : Set ι))
    (ht' : ∀ k ∈ galleryType η', k ∈ ({i, j} : Set ι))
    (hend : galleryEnd u η' = galleryEnd u η) :
    Set.EqOn (transport cs δ δ' c d c' d' u g η) (transport cs δ δ' c d c' d' u g η')
      (foundation cs δ 2 (galleryEnd u η) ∪ {companion cs δ c d (galleryEnd u η)}) := by
  have h₁ := isGerm_transport hδ hδ' hcent hS hext hcd hcd' hg hη
  have h₂ := isGerm_transport hδ hδ' hcent hS hext hcd hcd' hg hη'
  rw [hend] at h₂
  refine germ_eqOn_of_panels hδ hδ' hcent hS hcd hcd' hrig' h₁ h₂ fun k => ?_
  have hyR : galleryEnd u η ∈ residue cs δ {i, j} u := hη.1.end_mem_residue ht
  set K : Set ι := insert k {i, j}
  have hK : {i, j} ⊆ K := Set.subset_insert _ _
  have hK3 : K.ncard = 3 ∨ K = {i, j} := by
    by_cases hk : k ∈ ({i, j} : Set ι)
    · exact Or.inr (Set.insert_eq_of_mem hk)
    · left
      rw [Set.ncard_insert_of_notMem hk, Set.ncard_pair hij]
  have hE₁ := transport_eqOn_extGerm hδ hδ' hcent hS hext hcd hcd' hg hK hK3 hη ht
  have hE₂ := transport_eqOn_extGerm hδ hδ' hcent hS hext hcd hcd' hg hK hK3 hη' ht'
  rw [hend] at hE₂
  intro w hw
  have hk1 : ({k} : Set ι).encard ≤ 2 := by rw [Set.encard_singleton]; norm_num
  have hwF : w ∈ foundation cs δ 2 (galleryEnd u η) :=
    residue_subset_foundation (by exact_mod_cast hk1) _ hw
  have hwK : w ∈ residue cs δ K u := by
    rw [← residue_eq_of_mem hδ (residue_mono hK u hyR)]
    exact residue_mono (Set.singleton_subset_iff.mpr (Set.mem_insert k _)) _ hw
  rw [hE₁ ⟨hwF, hwK⟩, hE₂ ⟨hwF, hwK⟩]

end Braid

theorem mem_pair_of_mem_alternatingWord {i j k : ι} {m : ℕ}
    (hk : k ∈ alternatingWord i j m) : k ∈ ({i, j} : Set ι) := by
  induction m generalizing i j with
  | zero => simp [alternatingWord] at hk
  | succ m ih =>
    rw [alternatingWord_succ, List.concat_eq_append, List.mem_append] at hk
    rcases hk with hk | hk
    · rcases ih hk with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rw [List.mem_singleton.mp hk]
      exact Or.inr rfl

theorem exists_eq_concat_braidWord {i j : ι} (hM : M i j ≠ 0) :
    ∃ ω : List ι, braidWord M i j = ω ++ [j] := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hM
  refine ⟨alternatingWord j i m, ?_⟩
  rw [braidWord, hm, alternatingWord_succ, List.concat_eq_append]

section Indep

variable [Finite W] (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
  (hcent : ∀ w : W, longest cs Set.univ * w = w * longest cs Set.univ)
  (hS : Nat.card ι = 4) (hext : Ext₃ cs δ δ')
  {c d : C} {c' d' : C'} (hcd : δ c d = longest cs Set.univ)
  (hcd' : δ' c' d' = longest cs Set.univ) (hrig' : Rig₂ cs δ')
  {φ : C → C'} (hφ : IsGerm cs δ δ' c d c' d' c φ)
include hδ hδ' hcent hS hext hcd hcd' hrig' hφ

omit hrig' in
theorem transport_concat_eqOn {α₁ α₂ : List (ι × C)} {p₁ : ι × C}
    (hα₁ : Ascending cs δ c c α₁)
    (hγ₁ : Ascending cs δ c c (α₁ ++ [p₁])) (hz : galleryEnd c α₁ = galleryEnd c α₂)
    (hIH : Set.EqOn (transport cs δ δ' c d c' d' c φ α₁) (transport cs δ δ' c d c' d' c φ α₂)
      (foundation cs δ 2 (galleryEnd c α₁) ∪ {companion cs δ c d (galleryEnd c α₁)})) :
    Set.EqOn (transport cs δ δ' c d c' d' c φ (α₁ ++ [p₁]))
      (transport cs δ δ' c d c' d' c φ (α₂ ++ [p₁]))
      (foundation cs δ 2 p₁.2 ∪ {companion cs δ c d p₁.2}) := by
  rw [transport_concat, transport_concat, ← hz]
  have hg := isGerm_transport hδ hδ' hcent hS hext hcd hcd' hφ hα₁
  have hE := extGerm_congr hδ hδ' hcent hS hext hcd hcd' hg hIH
  obtain ⟨h1, h2, -⟩ := (ascending_cons_iff hδ).mp ((ascending_append_iff hδ).mp hγ₁).2
  refine hE.mono ?_
  rintro u (hu | hu)
  · exact Or.inl (foundation_two_subset_three hδ h1 hu)
  · rw [Set.mem_singleton_iff.mp hu, companion_step hδ hcent hcd h1 h2]
    exact Or.inr ⟨_, rfl⟩

theorem transport_indep :
    ∀ γ₁ γ₂ : List (ι × C), Ascending cs δ c c γ₁ → Ascending cs δ c c γ₂ →
      galleryEnd c γ₁ = galleryEnd c γ₂ →
      Set.EqOn (transport cs δ δ' c d c' d' c φ γ₁) (transport cs δ δ' c d c' d' c φ γ₂)
        (foundation cs δ 2 (galleryEnd c γ₁) ∪ {companion cs δ c d (galleryEnd c γ₁)}) := by
  suffices H : ∀ n : ℕ, ∀ γ₁ γ₂ : List (ι × C), Ascending cs δ c c γ₁ →
      Ascending cs δ c c γ₂ → galleryEnd c γ₁ = galleryEnd c γ₂ → γ₁.length = n →
      Set.EqOn (transport cs δ δ' c d c' d' c φ γ₁) (transport cs δ δ' c d c' d' c φ γ₂)
        (foundation cs δ 2 (galleryEnd c γ₁) ∪ {companion cs δ c d (galleryEnd c γ₁)}) from
    fun γ₁ γ₂ h₁ h₂ he => H _ γ₁ γ₂ h₁ h₂ he rfl
  have hlen : ∀ γ : List (ι × C), Ascending cs δ c c γ →
      γ.length = cs.length (δ c (galleryEnd c γ)) := fun γ h => by
    rw [h.2, hδ.eq_one_self, cs.length_one, zero_add]
  intro n
  induction n with
  | zero =>
    intro γ₁ γ₂ h₁ h₂ he hn
    have hn₂ : γ₂.length = 0 := by rw [hlen γ₂ h₂, ← he, ← hlen γ₁ h₁, hn]
    rw [List.length_eq_zero_iff.mp hn, List.length_eq_zero_iff.mp hn₂]
    exact Set.eqOn_refl _ _
  | succ n ih =>
    have same : ∀ γ₁ γ₂ : List (ι × C), Ascending cs δ c c γ₁ → Ascending cs δ c c γ₂ →
        galleryEnd c γ₁ = galleryEnd c γ₂ → γ₁.length = n + 1 →
        (galleryType γ₁).getLast? = (galleryType γ₂).getLast? →
        Set.EqOn (transport cs δ δ' c d c' d' c φ γ₁) (transport cs δ δ' c d c' d' c φ γ₂)
          (foundation cs δ 2 (galleryEnd c γ₁) ∪ {companion cs δ c d (galleryEnd c γ₁)}) := by
      intro γ₁ γ₂ h₁ h₂ he hn hl
      have hn₂ : γ₂.length = n + 1 := by rw [hlen γ₂ h₂, ← he, ← hlen γ₁ h₁, hn]
      obtain rfl | ⟨α₁, p₁, rfl⟩ := List.eq_nil_or_concat' γ₁
      · simp at hn
      obtain rfl | ⟨α₂, p₂, rfl⟩ := List.eq_nil_or_concat' γ₂
      · simp at hn₂
      have hp : p₁ = p₂ := by
        simp only [galleryType_append, galleryType_cons, galleryType_nil,
          List.getLast?_append, List.getLast?_singleton, Option.some_or,
          Option.some.injEq] at hl
        exact Prod.ext hl (by simpa using he)
      subst hp
      have hs₁ := (ascending_append_iff hδ).mp h₁
      have hs₂ := (ascending_append_iff hδ).mp h₂
      obtain ⟨hz₁x, hl₁, -⟩ := (ascending_cons_iff hδ).mp hs₁.2
      obtain ⟨hz₂x, hl₂, -⟩ := (ascending_cons_iff hδ).mp hs₂.2
      have hz : galleryEnd c α₁ = galleryEnd c α₂ := by
        have hd₁ : δ c p₁.2 = δ c (galleryEnd c α₁) * cs.simple p₁.1 := by
          rcases (hδ.mul_simple c _ p₁.2 p₁.1 hz₁x).1 with h | h
          · rw [h] at hl₁; omega
          · exact h
        have hd₂ : δ c p₁.2 = δ c (galleryEnd c α₂) * cs.simple p₁.1 := by
          rcases (hδ.mul_simple c _ p₁.2 p₁.1 hz₂x).1 with h | h
          · rw [h] at hl₂; omega
          · exact h
        have hd : δ c (galleryEnd c α₁) = δ c (galleryEnd c α₂) := by
          have := hd₁.symm.trans hd₂
          exact mul_right_cancel this
        by_contra hne
        have h12 := dist_eq_simple_of_eq_simple hδ hz₁x hz₂x hne
        have hl : cs.length (δ c (galleryEnd c α₁) * cs.simple p₁.1) =
            cs.length (δ c (galleryEnd c α₁)) + 1 := by rw [← hd₁]; exact hl₁
        have := (hδ.mul_simple c _ _ p₁.1 h12).2 hl
        rw [← hd] at this
        have h0 := congrArg cs.length this
        omega
      have hn' : α₁.length = n := by simpa using hn
      have IH := ih α₁ α₂ hs₁.1 hs₂.1 hz hn'
      have := transport_concat_eqOn hδ hδ' hcent hS hext hcd hcd' hφ hs₁.1 h₁ hz IH
      simpa using this
    intro γ₁ γ₂ h₁ h₂ he hn
    have hn₂ : γ₂.length = n + 1 := by rw [hlen γ₂ h₂, ← he, ← hlen γ₁ h₁, hn]
    obtain rfl | ⟨α₁, p₁, rfl⟩ := List.eq_nil_or_concat' γ₁
    · simp at hn
    obtain rfl | ⟨α₂, p₂, rfl⟩ := List.eq_nil_or_concat' γ₂
    · simp at hn₂
    by_cases hij : p₁.1 = p₂.1
    · exact same _ _ h₁ h₂ he hn (by simp [galleryType, hij])
    obtain ⟨x, hx⟩ : ∃ x, galleryEnd c (α₁ ++ [p₁]) = x := ⟨_, rfl⟩
    rw [hx] at he ⊢
    have hs₁ := (ascending_append_iff hδ).mp h₁
    have hs₂ := (ascending_append_iff hδ).mp h₂
    obtain ⟨hz₁x, hl₁, -⟩ := (ascending_cons_iff hδ).mp hs₁.2
    obtain ⟨hz₂x, hl₂, -⟩ := (ascending_cons_iff hδ).mp hs₂.2
    have hx₁ : p₁.2 = x := by rw [← hx, galleryEnd_concat]
    have hx₂ : p₂.2 = x := by rw [he, galleryEnd_concat]
    have hdesc : ∀ (α : List (ι × C)) (p : ι × C), p.2 = x →
        δ (galleryEnd c α) p.2 = cs.simple p.1 →
        cs.length (δ c p.2) = cs.length (δ c (galleryEnd c α)) + 1 →
        cs.IsLeftDescent (δ c x)⁻¹ p.1 := by
      intro α p hpx hstep hstepl
      have hd : δ c p.2 = δ c (galleryEnd c α) * cs.simple p.1 := by
        rcases (hδ.mul_simple c _ p.2 p.1 hstep).1 with h | h
        · rw [h] at hstepl; omega
        · exact h
      rw [cs.isLeftDescent_inv_iff, IsRightDescent, ← hpx, hd, mul_assoc,
        cs.simple_mul_simple_self, mul_one]
      rw [hd] at hstepl
      omega
    have hdi := hdesc α₁ p₁ hx₁ hz₁x hl₁
    have hdj := hdesc α₂ p₂ hx₂ hz₂x hl₂
    obtain ⟨wJ, hwJ⟩ : ∃ wJ, longest cs ({p₁.1, p₂.1} : Set ι) = wJ := ⟨_, rfl⟩
    have hJl : IsLongest cs {p₁.1, p₂.1} wJ := hwJ ▸ isLongest_of_finite _
    have hdJ : ∀ k ∈ ({p₁.1, p₂.1} : Set ι), cs.IsLeftDescent (δ c x)⁻¹ k := by
      intro k hk
      rcases hk with rfl | hk
      · exact hdi
      · rw [Set.mem_singleton_iff.mp hk]
        exact hdj
    have hlJ := length_longest_mul_of_forall_isLeftDescent hJl hdJ
    obtain ⟨v, hv_def⟩ : ∃ v, δ c x * wJ = v := ⟨_, rfl⟩
    have hv : cs.length v + cs.length wJ = cs.length (δ c x) := by
      have h1 : cs.length v = cs.length (wJ * (δ c x)⁻¹) := by
        rw [← hv_def, ← cs.length_inv, mul_inv_rev, hJl.inv_eq]
      rw [h1, ← cs.length_inv (δ c x)]
      exact hlJ
    have hvw : v⁻¹ * δ c x = wJ := by
      rw [← hv_def, mul_inv_rev, hJl.inv_eq, mul_assoc, inv_mul_cancel, mul_one]
    obtain ⟨u, hcu, hux⟩ := exists_dist_eq_of_length_add hδ (x := c) (y := x) rfl
      (u := v) (by rw [hvw, add_comm]; exact hv)
    rw [hvw] at hux
    obtain ⟨β₀, hβ₀, hβ₀p⟩ := cs.exists_isReduced v
    obtain ⟨β, hβ, hβt, hβe⟩ := exists_strictGallery hδ hβ₀ (hβ₀p.symm.trans hcu.symm)
    have hMfin : ∀ a b : ι, M a b ≠ 0 := fun a b h => by
      have h1 := cs.orderOf_simple_mul_simple a b
      rw [h] at h1
      exact (orderOf_pos (cs.simple a * cs.simple b)).ne' h1
    have hbw : ∀ a b : ι, a ≠ b → ({a, b} : Set ι) = {p₁.1, p₂.1} →
        cs.IsReduced (braidWord M a b) ∧ cs.wordProd (braidWord M a b) = δ u x := by
      intro a b hab hJ'
      obtain ⟨hL, hR, -⟩ := isLongest_braidWord (cs := cs) hab (hMfin a b)
      rw [hJ'] at hL
      exact ⟨hR, by rw [hux, hL.unique hJl]⟩
    obtain ⟨hRi, hPi⟩ := hbw p₂.1 p₁.1 (Ne.symm hij) (Set.pair_comm _ _)
    obtain ⟨hRj, hPj⟩ := hbw p₁.1 p₂.1 hij rfl
    obtain ⟨ηi, hηi, hηit, hηie⟩ := exists_strictGallery hδ hRi hPi
    obtain ⟨ηj, hηj, hηjt, hηje⟩ := exists_strictGallery hδ hRj hPj
    have hasc : ∀ η : List (ι × C), IsStrictGallery cs δ u η → galleryEnd u η = x →
        η.length = cs.length wJ → Ascending cs δ c c (β ++ η) := by
      intro η hη hηe hηl
      refine ⟨(isStrictGallery_append _ _ _).mpr ⟨hβ, hβe ▸ hη⟩, ?_⟩
      rw [galleryEnd_append, hβe, hηe, hδ.eq_one_self, cs.length_one, zero_add,
        List.length_append, hηl, ← hv, ← length_galleryType, hβt, ← hβ₀.eq, ← hβ₀p]
    have hli : ηi.length = cs.length wJ := by
      rw [← length_galleryType, hηit, ← hRi.eq, hPi, hux]
    have hlj : ηj.length = cs.length wJ := by
      rw [← length_galleryType, hηjt, ← hRj.eq, hPj, hux]
    have hγi := hasc ηi hηi hηie hli
    have hγj := hasc ηj hηj hηje hlj
    have heᵢ : galleryEnd c (β ++ ηi) = x := by rw [galleryEnd_append, hβe, hηie]
    have heⱼ : galleryEnd c (β ++ ηj) = x := by rw [galleryEnd_append, hβe, hηje]
    have hlast : ∀ (η : List (ι × C)) (a b : ι), galleryType η = braidWord M a b →
        (galleryType (β ++ η)).getLast? = some b := by
      intro η a b ht
      obtain ⟨ω, hω⟩ := exists_eq_concat_braidWord (M := M) (hMfin a b)
      rw [galleryType_append, ht, hω, ← List.append_assoc]
      simp
    have hnᵢ : (β ++ ηi).length = n + 1 := by
      rw [hlen _ hγi, heᵢ, ← hx, ← hlen _ h₁, hn]
    have hnⱼ : (β ++ ηj).length = n + 1 := by
      rw [hlen _ hγj, heⱼ, ← hx, ← hlen _ h₁, hn]
    have e1 := same (α₁ ++ [p₁]) (β ++ ηi) h₁ hγi (by rw [hx, heᵢ]) hn
      (by rw [hlast ηi p₂.1 p₁.1 hηit]; simp [galleryType])
    have e2 := same (α₂ ++ [p₂]) (β ++ ηj) h₂ hγj (by rw [← he, heⱼ]) hn₂
      (by rw [hlast ηj p₁.1 p₂.1 hηjt]; simp [galleryType])
    rw [hx] at e1
    rw [← he] at e2
    have e3 : Set.EqOn (transport cs δ δ' c d c' d' c φ (β ++ ηi))
        (transport cs δ δ' c d c' d' c φ (β ++ ηj))
        (foundation cs δ 2 x ∪ {companion cs δ c d x}) := by
      rw [transport_append, transport_append]
      have hβa := ((ascending_append_iff hδ).mp hγi).1
      have hg := isGerm_transport hδ hδ' hcent hS hext hcd hcd' hφ hβa
      have hai := ((ascending_append_iff hδ).mp hγi).2
      have haj := ((ascending_append_iff hδ).mp hγj).2
      rw [hβe] at hg hai haj ⊢
      have hti : ∀ k ∈ galleryType ηi, k ∈ ({p₁.1, p₂.1} : Set ι) := fun k hk => by
        rw [hηit] at hk
        rw [Set.pair_comm]
        exact mem_pair_of_mem_alternatingWord hk
      have htj : ∀ k ∈ galleryType ηj, k ∈ ({p₁.1, p₂.1} : Set ι) := fun k hk => by
        rw [hηjt] at hk
        exact mem_pair_of_mem_alternatingWord hk
      have := transport_eqOn_of_pair hδ hδ' hcent hS hext hcd hcd' hrig' hg hij hai haj hti htj
        (hηje.trans hηie.symm)
      rwa [hηie] at this
    intro w hw
    rw [e1 hw, e3 hw, ← e2 hw]

end Indep

theorem exists_ascending (hδ : IsWeylDistanceBuilding cs δ) (c x : C) :
    ∃ γ : List (ι × C), Ascending cs δ c c γ ∧ galleryEnd c γ = x := by
  obtain ⟨ω, hω, hωp⟩ := cs.exists_isReduced (δ c x)
  obtain ⟨γ, hγ, hγt, hγe⟩ := exists_strictGallery hδ hω hωp.symm
  exact ⟨γ, ascending_of_isReduced hδ hγ (hγt ▸ hω), hγe⟩

variable (cs δ) in
open _root_.Classical in
@[expose] noncomputable def chosenGallery (c x : C) : List (ι × C) :=
  if h : ∃ γ : List (ι × C), Ascending cs δ c c γ ∧ galleryEnd c γ = x then h.choose else []

theorem chosenGallery_spec (hδ : IsWeylDistanceBuilding cs δ) (c x : C) :
    Ascending cs δ c c (chosenGallery cs δ c x) ∧ galleryEnd c (chosenGallery cs δ c x) = x := by
  have h := exists_ascending hδ c x
  rw [chosenGallery, dite_eq_left h]
  exact h.choose_spec

variable (cs δ δ') in
@[expose] noncomputable def germAt (c d : C) (c' d' : C') (φ : C → C') (x : C) : C → C' :=
  transport cs δ δ' c d c' d' c φ (chosenGallery cs δ c x)

section Global

variable [Finite W] (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
  (hcent : ∀ w : W, longest cs Set.univ * w = w * longest cs Set.univ)
  (hS : Nat.card ι = 4) (hext : Ext₃ cs δ δ')
  {c d : C} {c' d' : C'} (hcd : δ c d = longest cs Set.univ)
  (hcd' : δ' c' d' = longest cs Set.univ) (hrig' : Rig₂ cs δ')
  {φ : C → C'} (hφ : IsGerm cs δ δ' c d c' d' c φ)
include hδ hδ' hcent hS hext hcd hcd' hrig' hφ

omit hrig' in
theorem isGerm_germAt (x : C) : IsGerm cs δ δ' c d c' d' x (germAt cs δ δ' c d c' d' φ x) := by
  have h := isGerm_transport hδ hδ' hcent hS hext hcd hcd' hφ (chosenGallery_spec hδ c x).1
  rwa [(chosenGallery_spec hδ c x).2] at h

theorem transport_eqOn_germAt {γ : List (ι × C)} (hγ : Ascending cs δ c c γ) {x : C}
    (hx : galleryEnd c γ = x) :
    Set.EqOn (transport cs δ δ' c d c' d' c φ γ) (germAt cs δ δ' c d c' d' φ x)
      (foundation cs δ 2 x ∪ {companion cs δ c d x}) := by
  have h := transport_indep hδ hδ' hcent hS hext hcd hcd' hrig' hφ γ (chosenGallery cs δ c x) hγ
    (chosenGallery_spec hδ c x).1 (hx.trans (chosenGallery_spec hδ c x).2.symm)
  rwa [hx] at h

theorem germAt_eqOn_extGerm {z x : C} {i : ι} (hzx : δ z x = cs.simple i)
    (hlen : cs.length (δ c x) = cs.length (δ c z) + 1) :
    Set.EqOn (germAt cs δ δ' c d c' d' φ x)
      (extGerm cs δ δ' c d c' d' z (germAt cs δ δ' c d c' d' φ z))
      (foundation cs δ 2 x ∪ {companion cs δ c d x}) := by
  obtain ⟨hγ, hγe⟩ := chosenGallery_spec hδ c z
  have hasc : Ascending cs δ c c (chosenGallery cs δ c z ++ [(i, x)]) := by
    refine (ascending_append_iff hδ).mpr ⟨hγ, (ascending_cons_iff hδ).mpr ⟨?_, ?_, ⟨trivial, by
      simp⟩⟩⟩
    · rw [hγe]; exact hzx
    · rw [hγe]; exact hlen
  have h1 := transport_eqOn_germAt hδ hδ' hcent hS hext hcd hcd' hrig' hφ hasc (x := x) (by simp)
  rw [transport_concat, hγe] at h1
  exact fun w hw => (h1 hw).symm

theorem germAt_eqOn_inter {x y : C} {i : ι} (hxy : δ x y = cs.simple i) :
    Set.EqOn (germAt cs δ δ' c d c' d' φ x) (germAt cs δ δ' c d c' d' φ y)
      (foundation cs δ 2 x ∩ foundation cs δ 2 y) := by
  have hyx := hδ.symm_of_eq_simple hxy
  have hgx := isGerm_germAt hδ hδ' hcent hS hext hcd hcd' hφ x
  have hgy := isGerm_germAt hδ hδ' hcent hS hext hcd hcd' hφ y
  rcases cs.length_mul_simple (δ c x) i with h | h
  ·
    have hcy : δ c y = δ c x * cs.simple i := (hδ.mul_simple c x y i hxy).2 h
    have hl : cs.length (δ c y) = cs.length (δ c x) + 1 := by rw [hcy, h]
    have e := germAt_eqOn_extGerm hδ hδ' hcent hS hext hcd hcd' hrig' hφ hxy hl
    obtain ⟨-, hE, -, -, -⟩ := extGerm_spec hδ hδ' hcent hS hext hcd hcd' hgx
    intro w hw
    rw [e (Or.inl hw.2), hE (Or.inl hw.1)]
  · rcases (hδ.mul_simple c x y i hxy).1 with hcy | hcy
    ·
      obtain ⟨z, hxz, hcz⟩ := hδ.exists_simple c x i
      have hzx := hδ.symm_of_eq_simple hxz
      have hlx : cs.length (δ c x) = cs.length (δ c z) + 1 := by rw [hcz]; omega
      have hly : cs.length (δ c y) = cs.length (δ c z) + 1 := by rw [hcy, hcz]; omega
      have hzy : δ z y = cs.simple i := by
        refine dist_eq_simple_of_eq_simple hδ hzx hyx ?_
        rintro rfl
        rw [hcz] at hcy
        have := congrArg cs.length hcy
        omega
      have ex := germAt_eqOn_extGerm hδ hδ' hcent hS hext hcd hcd' hrig' hφ hzx hlx
      have ey := germAt_eqOn_extGerm hδ hδ' hcent hS hext hcd hcd' hrig' hφ hzy hly
      intro w hw
      rw [ex (Or.inl hw.1), ey (Or.inl hw.2)]
    ·
      have hl : cs.length (δ c x) = cs.length (δ c y) + 1 := by
        rw [hcy]; omega
      have e := germAt_eqOn_extGerm hδ hδ' hcent hS hext hcd hcd' hrig' hφ hyx hl
      obtain ⟨-, hE, -, -, -⟩ := extGerm_spec hδ hδ' hcent hS hext hcd hcd' hgy
      intro w hw
      rw [e (Or.inl hw.1), hE (Or.inl hw.2)]

theorem germAt_self_eq {x w : C} (hw : w ∈ foundation cs δ 2 x) :
    germAt cs δ δ' c d c' d' φ w w = germAt cs δ δ' c d c' d' φ x w := by
  obtain ⟨I, hI, hwI⟩ := mem_foundation_iff.mp hw
  obtain ⟨γ, hγ, hγt, rfl⟩ := mem_residue_iff.mp hwI
  have key : ∀ (γ : List (ι × C)) (z : C), IsStrictGallery cs δ z γ →
      (∀ k ∈ galleryType γ, k ∈ I) → ∀ v ∈ residue cs δ I z,
        germAt cs δ δ' c d c' d' φ z v = germAt cs δ δ' c d c' d' φ (galleryEnd z γ) v := by
    intro γ
    induction γ with
    | nil => intro z _ _ v _; rfl
    | cons p γ ih =>
      intro z hγ hγt v hv
      obtain ⟨h1, h2⟩ := hγ
      have hp : p.1 ∈ I := hγt p.1 (by simp)
      have hpz : p.2 ∈ residue cs δ I z := Relation.ReflTransGen.single ⟨p.1, hp, h1⟩
      have hvp : v ∈ residue cs δ I p.2 := by rw [residue_eq_of_mem hδ hpz]; exact hv
      have hvz : v ∈ foundation cs δ 2 z := residue_subset_foundation (by exact_mod_cast hI) z hv
      have hvp' : v ∈ foundation cs δ 2 p.2 :=
        residue_subset_foundation (by exact_mod_cast hI) p.2 hvp
      rw [germAt_eqOn_inter hδ hδ' hcent hS hext hcd hcd' hrig' hφ h1 ⟨hvz, hvp'⟩]
      exact ih p.2 h2 (fun k hk => hγt k (by simp [hk])) v hvp
  have hend : galleryEnd x γ ∈ residue cs δ I x := hγ.end_mem_residue hγt
  exact (key γ x hγ hγt _ hend).symm

end Global

theorem companion_self [Finite W] (hδ : IsWeylDistanceBuilding cs δ) {c d : C}
    (hcd : δ c d = longest cs Set.univ) : companion cs δ c d c = d := by
  rw [companion, hδ.eq_one_self, mul_one, oppChamber_longest hδ hcd]

theorem oppChamber_companion [Finite W] (hδ : IsWeylDistanceBuilding cs δ)
    (hcent : ∀ w : W, longest cs Set.univ * w = w * longest cs Set.univ) {c d : C}
    (hcd : δ c d = longest cs Set.univ) (v t : W) :
    oppChamber cs δ (oppChamber cs δ c d v) (companion cs δ c d (oppChamber cs δ c d v)) t =
      oppChamber cs δ c d (v * t) := by
  have hap := isApartmentMap_oppChamber hδ hcd
  have hcomp : companion cs δ c d (oppChamber cs δ c d v) =
      oppChamber cs δ c d (longest cs Set.univ * v) := by
    rw [companion, (oppChamber_spec hδ hcd v).1]
  refine (eq_oppChamber hδ (opposite_companion hδ hcent hcd _) ?_ ?_).symm
  · rw [hap, inv_mul_cancel_left]
  · rw [hcomp, hap, mul_inv_rev, mul_assoc, ← mul_assoc v⁻¹, ← hcent, mul_assoc,
      inv_mul_cancel, mul_one]

theorem global_extension_of_rank_three_opposition [Finite W]
    (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
    (hS : Nat.card ι = 4)
    (hcent : ∀ w : W, longest cs Set.univ * w = w * longest cs Set.univ)
    (hext : Ext₃ cs δ δ') (hrig : Rig₂ cs δ) (hrig' : Rig₂ cs δ') {c d : C} {c' d' : C'}
    (hcd : δ c d = longest cs Set.univ) (hcd' : δ' c' d' = longest cs Set.univ) {φ : C → C'}
    (hφ : IsWeylIsometry δ δ' (foundation cs δ 2 c ∪ {d}) (foundation cs δ' 2 c' ∪ {d'}) φ)
    (hφc : φ c = c') (hφd : φ d = d') :
    ∃ F : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F ∧
      Set.EqOn F φ (foundation cs δ 2 c ∪ {d}) ∧
      ∀ F' : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F' →
        Set.EqOn F' φ (foundation cs δ 2 c ∪ {d}) → F' = F := by
  have hφg : IsGerm cs δ δ' c d c' d' c φ := by
    refine ⟨?_, by rw [hφc, hδ.eq_one_self, hδ'.eq_one_self]⟩
    rw [companion_self hδ hcd, hφc, companion_self hδ' hcd']
    exact hφ
  obtain ⟨F, hF⟩ : ∃ F : C → C', ∀ x, F x = germAt cs δ δ' c d c' d' φ x x :=
    ⟨_, fun _ => rfl⟩
  have hG := isGerm_germAt hδ hδ' hcent hS hext hcd hcd' hφg
  have hFG : ∀ x, ∀ w ∈ foundation cs δ 2 x, F w = germAt cs δ δ' c d c' d' φ x w :=
    fun x w hw => by
      rw [hF]
      exact germAt_self_eq hδ hδ' hcent hS hext hcd hcd' hrig' hφg hw
  have hpanel : ∀ (x : C) (i : ι), panel cs δ i x ⊆ foundation cs δ 2 x := fun x i =>
    residue_subset_foundation (by rw [Set.encard_singleton]; norm_num) x
  have hadj : ∀ x y i, δ x y = cs.simple i → δ' (F x) (F y) = cs.simple i := by
    intro x y i hxy
    have hy : y ∈ panel cs δ i x := (mem_panel_iff hδ).mpr (Or.inr hxy)
    rw [hFG x x (self_mem_foundation 2 x), hFG x y (hpanel x i hy),
      (hG x).1.2 x (Or.inl (self_mem_foundation 2 x)) y (Or.inl (hpanel x i hy)), hxy]
  have hdist : ∀ x y, δ' (F x) (F y) = δ x y := fun x y =>
    dist_map_eq hδ hδ' (J := Set.univ) (a := x) (fun y _ z _ i h => hadj y z i h)
      (self_mem_residue _ x) (by rw [residue_univ hδ]; trivial)
  have hinj : Function.Injective F := fun x y h => by
    have := hdist x y
    rw [h, hδ'.eq_one_self, eq_comm, hδ.eq_one_iff] at this
    exact this
  have hsurj : Function.Surjective F := by
    intro y'
    have hy' : y' ∈ residue cs δ' Set.univ (F c) := by rw [residue_univ hδ']; trivial
    induction hy' with
    | refl => exact ⟨c, rfl⟩
    | @tail a' b' _ hab ih =>
      obtain ⟨x, rfl⟩ := ih
      obtain ⟨i, -, hi⟩ := hab
      rw [hF] at hi
      have hb : b' ∈ panel cs δ' i (germAt cs δ δ' c d c' d' φ x x) :=
        (mem_panel_iff hδ').mpr (Or.inr hi)
      have hbij := (hG x).1.bijOn_residue hδ hδ' (Or.inl (self_mem_foundation 2 x)) rfl
        ((hpanel x i).trans Set.subset_union_left)
        ((residue_subset_foundation (by rw [Set.encard_singleton]; norm_num) _).trans
          Set.subset_union_left)
      obtain ⟨y, hy, rfl⟩ := hbij.surjOn hb
      exact ⟨y, (hFG x y (hpanel x i hy))⟩
  have hFiso : IsTypeIso cs δ δ' Set.univ Set.univ F :=
    ⟨Set.bijOn_univ.mpr ⟨hinj, hsurj⟩, fun x _ y _ i => by rw [hdist]⟩
  have hGc : Set.EqOn φ (germAt cs δ δ' c d c' d' φ c)
      (foundation cs δ 2 c ∪ {companion cs δ c d c}) :=
    transport_eqOn_germAt hδ hδ' hcent hS hext hcd hcd' hrig' hφg (γ := [])
      ⟨trivial, by simp⟩ rfl
  have hFc : ∀ w ∈ foundation cs δ 2 c, F w = φ w := fun w hw =>
    (hFG c w hw).trans (hGc (Or.inl hw)).symm
  have hA : ∀ ω : List ι, cs.IsReduced ω →
      F (oppChamber cs δ c d (cs.wordProd ω)) = oppChamber cs δ' c' d' (cs.wordProd ω) := by
    intro ω hω
    induction ω using List.reverseRecOn with
    | nil =>
      rw [cs.wordProd_nil, oppChamber_one hδ hcd, oppChamber_one hδ' hcd',
        hFc c (self_mem_foundation 2 c), hφc]
    | append_singleton ω i ih =>
      have hred := isReduced_of_isReduced_concat hω
      have IH := ih hred
      have hv : cs.wordProd (ω ++ [i]) = cs.wordProd ω * cs.simple i := by
        rw [cs.wordProd_append, cs.wordProd_singleton]
      rw [hv]
      have hxy : δ (oppChamber cs δ c d (cs.wordProd ω))
          (oppChamber cs δ c d (cs.wordProd ω * cs.simple i)) = cs.simple i := by
        rw [isApartmentMap_oppChamber hδ hcd, inv_mul_cancel_left]
      have hlen : cs.length (δ c (oppChamber cs δ c d (cs.wordProd ω * cs.simple i))) =
          cs.length (δ c (oppChamber cs δ c d (cs.wordProd ω))) + 1 := by
        rw [(oppChamber_spec hδ hcd _).1, (oppChamber_spec hδ hcd _).1]
        exact length_mul_simple_of_isReduced_concat hω
      have e := germAt_eqOn_extGerm hδ hδ' hcent hS hext hcd hcd' hrig' hφg hxy hlen
      obtain ⟨-, -, -, -, hext'⟩ := extGerm_spec hδ hδ' hcent hS hext hcd hcd'
        (hG (oppChamber cs δ c d (cs.wordProd ω)))
      have hy := oppChamber_companion hδ hcent hcd (cs.wordProd ω) (cs.simple i)
      rw [hF, e (Or.inl (self_mem_foundation 2 _))]
      conv_lhs => rw [← hy]
      rw [hext', ← hF, IH, oppChamber_companion hδ' hcent hcd' (cs.wordProd ω) (cs.simple i)]
  have hFd : F d = d' := by
    obtain ⟨ω, hω, hωp⟩ := cs.exists_isReduced (longest cs Set.univ)
    have h := hA ω hω
    rw [← hωp, oppChamber_longest hδ hcd, oppChamber_longest hδ' hcd'] at h
    exact h
  have hFφ : Set.EqOn F φ (foundation cs δ 2 c ∪ {d}) := by
    rintro w (hw | hw)
    · exact hFc w hw
    · rw [Set.mem_singleton_iff.mp hw, hFd, hφd]
  refine ⟨F, hFiso, hFφ, fun F' hF' hF'φ => ?_⟩
  refine ((spherical_building_panel_opposite_rigidity hδ hrig hcd (δ' := δ')).2 F' F hF' hFiso
    ?_ ?_)
  · rw [hF'φ (Or.inr rfl), hFφ (Or.inr rfl)]
  · intro i y hy
    rw [hF'φ (Or.inl (hpanel c i hy)), hFφ (Or.inl (hpanel c i hy))]

end CFSG.Monster.B.Geometry

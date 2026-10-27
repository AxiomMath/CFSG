module

public import CFSG.Monster.B.Geometry.Gate

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

section

variable (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem isTypeIso_residue_of_mem_typeAut {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ) {x : C}
    (hgx : g x = x) (J : Set ι) :
    IsTypeIso cs δ δ (residue cs δ J x) (residue cs δ J x) g := by
  have hginv : g⁻¹ ∈ typeAut cs δ := inv_mem hg
  have hgx' : g⁻¹ x = x := by rw [Equiv.Perm.inv_eq_iff_eq, hgx]
  have hmaps : ∀ h ∈ typeAut cs δ, h x = x → ∀ y ∈ residue cs δ J x, h y ∈ residue cs δ J x := by
    intro h hh hhx y hy
    rw [mem_residue_iff_mem_parabolic hδ] at hy ⊢
    rw [← hhx, dist_typeAut hδ hh]
    exact hy
  refine ⟨⟨hmaps g hg hgx, g.injective.injOn, fun y hy => ⟨g⁻¹ y,
    hmaps g⁻¹ hginv hgx' y hy, by simp⟩⟩, fun y _ z _ i => hg y z i⟩

variable [Finite W]

theorem fix_residue_pair (hrig : Rig₂ cs δ) {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ)
    {x z : C} (hxz : δ x z = longest cs Set.univ) (hgz : g z = z)
    (hE₁ : ∀ i, ∀ y ∈ panel cs δ i x, g y = y) {i j : ι} (hij : i ≠ j) :
    ∀ y ∈ residue cs δ {i, j} x, g y = y := by
  have hgx : g x = x := hE₁ i x (self_mem_residue _ x)
  have hiso := isTypeIso_residue_of_mem_typeAut hδ hg hgx {i, j}
  set p := oppChamber cs δ x z (longest cs {i, j})
  have hproj := isProjection_oppChamber_longest hδ hxz {i, j}
  have hgp : g p = p := by
    have h := hproj.map hiso.1 (fun q _ => dist_typeAut hδ hg z q)
    rw [hgz] at h
    exact h.unique hproj
  refine hrig i j hij x p hproj.1 (oppChamber_spec hδ hxz _).1 g hiso hgp ?_
  rintro y (hy | hy)
  · exact hE₁ i y hy
  · exact hE₁ j y hy

theorem fix_oppChamber {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ) {x z : C}
    (hxz : δ x z = longest cs Set.univ) (hgx : g x = x) (hgz : g z = z) (u : W) :
    g (oppChamber cs δ x z u) = oppChamber cs δ x z u := by
  obtain ⟨h1, h2⟩ := oppChamber_spec hδ hxz u
  refine eq_oppChamber hδ hxz ?_ ?_
  · rw [← hgx, dist_typeAut hδ hg, hgx, h1]
  · rw [← hgz, dist_typeAut hδ hg, hgz, h2]

theorem propagate (hrig : Rig₂ cs δ) {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ) {x z : C}
    (hxz : δ x z = longest cs Set.univ) (hgz : g z = z)
    (hE₁ : ∀ i, ∀ y ∈ panel cs δ i x, g y = y) {y : C} {i : ι} (hy : δ x y = cs.simple i) :
    (∀ j, ∀ w ∈ panel cs δ j y, g w = w) ∧ ∃ z', δ y z' = longest cs Set.univ ∧ g z' = z' := by
  have hyP : y ∈ panel cs δ i x := (mem_panel_iff hδ).mpr (Or.inr hy)
  have hgx : g x = x := hE₁ i x (self_mem_residue _ x)
  refine ⟨fun j w hw => ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji
      rw [panel, residue_eq_of_mem hδ hyP] at hw
      exact hE₁ j w hw
    · have hyR : y ∈ residue cs δ {i, j} x :=
        residue_mono (by simp) x hyP
      have hwR : w ∈ residue cs δ {i, j} x := by
        rw [← residue_eq_of_mem hδ hyR]
        exact residue_mono (by simp) y hw
      exact fix_residue_pair hδ hrig hg hxz hgz hE₁ (Ne.symm hji) w hwR
  · by_cases hya : y = oppChamber cs δ x z (cs.simple i)
    · refine ⟨oppChamber cs δ x z (cs.simple i * longest cs Set.univ), ?_,
        fix_oppChamber hδ hg hxz hgx hgz _⟩
      rw [hya, isApartmentMap_oppChamber hδ hxz, inv_mul_cancel_left]
    · exact ⟨z, dist_eq_longest_of_mem_panel hδ hxz hyP hya, hgz⟩

theorem eq_one_of_fix_panels_opposite (hrig : Rig₂ cs δ) {c d : C}
    (hcd : δ c d = longest cs Set.univ) {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ)
    (hgd : g d = d) (hgc : ∀ i, ∀ y ∈ panel cs δ i c, g y = y) : g = 1 := by
  have key : ∀ y : C, g y = y ∧ (∀ j, ∀ w ∈ panel cs δ j y, g w = w) ∧
      ∃ z', δ y z' = longest cs Set.univ ∧ g z' = z' := by
    intro y
    have hy : y ∈ residue cs δ Set.univ c := by rw [residue_univ hδ]; trivial
    induction hy with
    | refl =>
      refine ⟨?_, hgc, d, hcd, hgd⟩
      by_cases hne : Nonempty ι
      · obtain ⟨i⟩ := hne
        exact hgc i c (self_mem_residue _ c)
      ·
        have hu : (Set.univ : Set ι) = ∅ := Set.univ_eq_empty_iff.mpr (not_nonempty_iff.mp hne)
        have hW : ∀ w : W, w = 1 := by
          intro w
          have h := cs.parabolic_univ
          rw [hu, cs.parabolic_empty] at h
          have : w ∈ (⊥ : Subgroup W) := h ▸ Subgroup.mem_top w
          exact Subgroup.mem_bot.mp this
        exact (hδ.eq_one_iff (g c) c).mp (hW _)
    | @tail b y' _ hby ih =>
      obtain ⟨-, hE, z, hbz, hgz⟩ := ih
      obtain ⟨i, -, hi⟩ := hby
      obtain ⟨hE', hz'⟩ := propagate hδ hrig hg hbz hgz hE hi
      refine ⟨?_, hE', hz'⟩
      exact hE i y' ((mem_panel_iff hδ).mpr (Or.inr hi))
  ext y
  exact (key y).1

end

theorem spherical_building_panel_opposite_rigidity [Finite W]
    (hδ : IsWeylDistanceBuilding cs δ) (hrig : Rig₂ cs δ) {c d : C}
    (hcd : δ c d = longest cs Set.univ) {C' : Type*} {δ' : C' → C' → W} :
    (∀ g ∈ typeAut cs δ, g d = d → (∀ i, ∀ y ∈ panel cs δ i c, g y = y) → g = 1) ∧
    ∀ f₁ f₂ : C → C', IsTypeIso cs δ δ' Set.univ Set.univ f₁ →
      IsTypeIso cs δ δ' Set.univ Set.univ f₂ → f₁ d = f₂ d →
        (∀ i, ∀ y ∈ panel cs δ i c, f₁ y = f₂ y) → f₁ = f₂ := by
  refine ⟨fun g hg hgd hgc => eq_one_of_fix_panels_opposite hδ hrig hcd hg hgd hgc, ?_⟩
  intro f₁ f₂ h₁ h₂ hd hc
  have hb₁ : Function.Bijective f₁ := Set.bijOn_univ.mp h₁.1
  have hb₂ : Function.Bijective f₂ := Set.bijOn_univ.mp h₂.1
  set e₁ := Equiv.ofBijective f₁ hb₁
  set e₂ := Equiv.ofBijective f₂ hb₂
  set g : Equiv.Perm C := e₁.trans e₂.symm
  have hge : ∀ x, f₂ (g x) = f₁ x := fun x => by
    change e₂ (e₂.symm (e₁ x)) = f₁ x
    rw [Equiv.apply_symm_apply]
    rfl
  have hg : g ∈ typeAut cs δ := by
    intro x y i
    rw [← h₂.2 (g x) trivial (g y) trivial i, hge, hge]
    exact h₁.2 x trivial y trivial i
  have hfix : ∀ x, f₁ x = f₂ x → g x = x := fun x hx => hb₂.1 (by rw [hge, hx])
  have h1 := eq_one_of_fix_panels_opposite hδ hrig hcd hg (hfix d hd)
    (fun i y hy => hfix y (hc i y hy))
  funext x
  rw [← hge x, h1]
  rfl

end CFSG.Monster.B.Geometry

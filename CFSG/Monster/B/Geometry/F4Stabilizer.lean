module

public import CFSG.Monster.B.Geometry.PlaneModel
public import CFSG.Monster.B.Geometry.QuadrangleModel
public import CFSG.LieType.Chevalley.BraidWalk
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.Monster.B.Geometry.Rigidity

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

section Generic

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

variable (cs δ) in
@[expose] def pairStab (c d : C) : Subgroup (Equiv.Perm C) where
  carrier := {g | g ∈ typeAut cs δ ∧ g c = c ∧ g d = d}
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1, by simp [hh.2.1, hg.2.1], by simp [hh.2.2, hg.2.2]⟩
  one_mem' := ⟨one_mem _, rfl, rfl⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, by
    rw [Equiv.Perm.inv_eq_iff_eq]; exact hg.2.1.symm, by
    rw [Equiv.Perm.inv_eq_iff_eq]; exact hg.2.2.symm⟩

theorem mem_pairStab {c d : C} {g : Equiv.Perm C} :
    g ∈ pairStab cs δ c d ↔ g ∈ typeAut cs δ ∧ g c = c ∧ g d = d :=
  Iff.rfl

variable (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem mem_residue_iff_of_mem_typeAut {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ) {c : C}
    (hgc : g c = c) (J : Set ι) (y : C) :
    g y ∈ residue cs δ J c ↔ y ∈ residue cs δ J c := by
  rw [mem_residue_iff_mem_parabolic hδ, mem_residue_iff_mem_parabolic hδ, ← hgc,
    dist_typeAut hδ hg, hgc]

@[expose] noncomputable def pairStabRestrict (J : Set ι) (c d : C) :
    pairStab cs δ c d →* Equiv.Perm (residue cs δ J c) where
  toFun t := t.1.subtypePerm fun y => mem_residue_iff_of_mem_typeAut hδ t.2.1 t.2.2.1 J y
  map_one' := rfl
  map_mul' _ _ := rfl

theorem pairStabRestrict_apply (J : Set ι) {c d : C} (t : pairStab cs δ c d)
    (y : residue cs δ J c) : ((pairStabRestrict hδ J c d t y : residue cs δ J c) : C) = t.1 y :=
  rfl

theorem pairStabRestrict_mem (J : Set ι) {c d p : C}
    (hp : IsProjection cs δ (residue cs δ J c) d p) (t : pairStab cs δ c d) :
    pairStabRestrict hδ J c d t ∈
      residueStab cs δ (residue cs δ J c) ⟨c, self_mem_residue J c⟩ ⟨p, hp.1⟩ := by
  obtain ⟨t, ht, htc, htd⟩ := t
  refine ⟨fun y z i => ?_, Subtype.ext htc, Subtype.ext ?_⟩
  · exact ht y z i
  · have hiso := isTypeIso_residue_of_mem_typeAut hδ ht htc J
    have h := hp.map hiso.1 (fun q _ => dist_typeAut hδ ht d q)
    rw [htd] at h
    exact h.unique hp

end Generic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

instance neZero_rank_F4 : NeZero Tag.F4.rank := ⟨by decide⟩

theorem f4M01 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 0 1 = 3 := by
  simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    RootWalk.coxeterOrder_eq_braidLength]
  decide

theorem f4M10 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 1 0 = 3 := by
  simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    RootWalk.coxeterOrder_eq_braidLength]
  decide

theorem f4M12 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 1 2 = 4 := by
  simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    RootWalk.coxeterOrder_eq_braidLength]
  decide

theorem f4M23 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 2 3 = 3 := by
  simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    RootWalk.coxeterOrder_eq_braidLength]
  decide

theorem f4M32 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 3 2 = 3 := by
  simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    RootWalk.coxeterOrder_eq_braidLength]
  decide

theorem fin_f4_pairs : ∀ i j : Fin Tag.F4.rank, i ≠ j →
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨
      (i = 3 ∧ j = 2) ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
        (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by
  decide

theorem f4M_commute
    (i j : Fin Tag.F4.rank) (hij : i ≠ j) (h01 : (i, j) ≠ (0, 1))
    (h10 : (i, j) ≠ (1, 0)) (h12 : (i, j) ≠ (1, 2)) (h21 : (i, j) ≠ (2, 1))
    (h23 : (i, j) ≠ (2, 3)) (h32 : (i, j) ≠ (3, 2)) :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) i j = 2 := by
  rcases fin_f4_pairs i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals first
    | exact absurd rfl ‹_›
    | simp only [CFSG.LieType.RootSystem.coxeterMatrix,
          TauCeti.coxeterMatrixOfCartanMatrix_apply, RootWalk.coxeterOrder_eq_braidLength]
      decide

theorem fin_f4_cases : ∀ i : Fin Tag.F4.rank, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide

variable {C : Type*} {δ : C → C → WeylGroup .F4} (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
  {k₂ k₄ : Type*} [Field k₂] [Field k₄]
  (h12 : ∀ x, IsPlaneFlagResidue (coxeterSystem .F4) δ k₂ 0 1 x)
  (h34 : ∀ x, IsPlaneFlagResidue (coxeterSystem .F4) δ k₄ 2 3 x)
  (h23 : ∀ x, IsQuadrangleFlagResidue (coxeterSystem .F4) δ 1 2 x)
include hδ h12 h34 h23

theorem rig₂_f4 : Rig₂ (coxeterSystem .F4) δ := by
  intro i j hij a b hb hab g hg hgb hfix
  by_cases h01 : (i, j) = (0, 1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h01
    exact (h12 a).fix hδ hij f4M01 hb hab hg hgb hfix
  by_cases h10 : (i, j) = (1, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h10
    exact (h12 a).swap.fix hδ hij f4M10 hb hab hg hgb hfix
  by_cases h23' : (i, j) = (2, 3)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h23'
    exact (h34 a).fix hδ hij f4M23 hb hab hg hgb hfix
  by_cases h32 : (i, j) = (3, 2)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h32
    exact (h34 a).swap.fix hδ hij f4M32 hb hab hg hgb hfix
  by_cases h12' : (i, j) = (1, 2)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h12'
    exact (h23 a).fix hδ hij f4M12 hb hab hg hgb fun y hy => hfix y (Or.inr hy)
  by_cases h21 : (i, j) = (2, 1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h21
    rw [Set.pair_comm] at hb hab hg ⊢
    exact (h23 a).fix hδ hij.symm f4M12 hb hab hg hgb fun y hy => hfix y (Or.inl hy)
  exact fix_residue_of_commute hδ hij (f4M_commute i j hij h01 h10 h12' h21 h23' h32) hg hfix

theorem eq_one_of_fix_residue_f4 (hk₂ : Nat.card k₂ = 2) {c d : C}
    (hcd : δ c d = longest (coxeterSystem .F4) Set.univ) {t : Equiv.Perm C}
    (ht : t ∈ typeAut (coxeterSystem .F4) δ) (htc : t c = c) (htd : t d = d)
    (hR : ∀ y ∈ residue (coxeterSystem .F4) δ {2, 3} c, t y = y) : t = 1 := by
  have hrig := rig₂_f4 hδ h12 h34 h23
  have hq : ∀ J : Set (Fin Tag.F4.rank),
      oppChamber (coxeterSystem .F4) δ c d (longest (coxeterSystem .F4) J) ∈
        residue (coxeterSystem .F4) δ J c ∧
      δ c (oppChamber (coxeterSystem .F4) δ c d (longest (coxeterSystem .F4) J)) =
        longest (coxeterSystem .F4) J ∧
      t (oppChamber (coxeterSystem .F4) δ c d (longest (coxeterSystem .F4) J)) =
        oppChamber (coxeterSystem .F4) δ c d (longest (coxeterSystem .F4) J) := fun J =>
    ⟨(isProjection_oppChamber_longest hδ hcd J).1, (oppChamber_spec hδ hcd _).1,
      fix_oppChamber hδ ht hcd htc htd _⟩
  have hpanel : ∀ (i : Fin Tag.F4.rank) (J : Set (Fin Tag.F4.rank)), i ∈ J →
      panel (coxeterSystem .F4) δ i c ⊆ residue (coxeterSystem .F4) δ J c := fun i J hi =>
    residue_mono (Set.singleton_subset_iff.mpr hi) c
  have hR12 : ∀ y ∈ residue (coxeterSystem .F4) δ {1, 2} c, t y = y := by
    obtain ⟨h1, h2, h3⟩ := hq {1, 2}
    exact (h23 c).fix hδ (by decide) f4M12 h1 h2
      (isTypeIso_residue_of_mem_typeAut hδ ht htc _) h3
      fun y hy => hR y (hpanel 2 {2, 3} (by simp) hy)
  have hR01 : ∀ y ∈ residue (coxeterSystem .F4) δ {0, 1} c, t y = y := by
    obtain ⟨h1, h2, h3⟩ := hq {0, 1}
    exact (h12 c).fix_of_card_two hδ hk₂ (by decide) f4M01 h1 h2
      (isTypeIso_residue_of_mem_typeAut hδ ht htc _) htc h3
  refine eq_one_of_fix_panels_opposite hδ hrig hcd ht htd fun i y hy => ?_
  rcases fin_f4_cases i with rfl | rfl | rfl | rfl
  · exact hR01 y (hpanel 0 {0, 1} (by simp) hy)
  · exact hR01 y (hpanel 1 {0, 1} (by simp) hy)
  · exact hR y (hpanel 2 {2, 3} (by simp) hy)
  · exact hR y (hpanel 3 {2, 3} (by simp) hy)

theorem F4_opposite_pair_automorphism_stabilizer_bound (hk₂ : Nat.card k₂ = 2)
    (hk₄ : Nat.card k₄ = 4) {c d p : C} (hcd : δ c d = longest (coxeterSystem .F4) Set.univ)
    (hp : IsProjection (coxeterSystem .F4) δ (residue (coxeterSystem .F4) δ {2, 3} c) d p) :
    ∃ ρ : pairStab (coxeterSystem .F4) δ c d →*
        residueStab (coxeterSystem .F4) δ (residue (coxeterSystem .F4) δ {2, 3} c)
          ⟨c, self_mem_residue _ c⟩ ⟨p, hp.1⟩,
      (∀ t y, (((ρ t).1 y : residue (coxeterSystem .F4) δ {2, 3} c) : C) = t.1 y) ∧
      Function.Injective ρ ∧
      Nat.card (residueStab (coxeterSystem .F4) δ (residue (coxeterSystem .F4) δ {2, 3} c)
        ⟨c, self_mem_residue _ c⟩ ⟨p, hp.1⟩) = 18 ∧
      Nat.card (pairStab (coxeterSystem .F4) δ c d) ∣ 18 := by
  let ρ := (pairStabRestrict hδ {2, 3} c d).codRestrict _ (pairStabRestrict_mem hδ {2, 3} hp)
  have hρ : ∀ t y, (((ρ t).1 y : residue (coxeterSystem .F4) δ {2, 3} c) : C) = t.1 y :=
    fun _ _ => rfl
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : ∀ y ∈ residue (coxeterSystem .F4) δ {2, 3} c, t.1 y = y := fun y hy => by
      have := congrArg (fun g : residueStab (coxeterSystem .F4) δ _ _ _ =>
        ((g.1 ⟨y, hy⟩ : residue (coxeterSystem .F4) δ {2, 3} c) : C)) ht
      simpa [hρ] using this
    exact Subtype.ext (eq_one_of_fix_residue_f4 hδ h12 h34 h23 hk₂ hcd t.2.1 t.2.2.1 t.2.2.2 h1)
  have hpq : p = oppChamber (coxeterSystem .F4) δ c d (longest (coxeterSystem .F4) {2, 3}) :=
    hp.unique (isProjection_oppChamber_longest hδ hcd {2, 3})
  have hcp : δ c p = longest (coxeterSystem .F4) {2, 3} := by
    rw [hpq]
    exact (oppChamber_spec hδ hcd _).1
  have hcard : Nat.card (residueStab (coxeterSystem .F4) δ (residue (coxeterSystem .F4) δ {2, 3} c)
      ⟨c, self_mem_residue _ c⟩ ⟨p, hp.1⟩) = 18 := by
    rw [(h34 c).nat_card_residueStab hδ (by decide) f4M23 _ _ hcp,
      nat_card_planeOppStab_of_card_four hk₄]
  refine ⟨ρ, hρ, hinj, hcard, ?_⟩
  rw [← hcard]
  exact Subgroup.card_dvd_of_injective ρ hinj

end CFSG.Monster.B.Geometry

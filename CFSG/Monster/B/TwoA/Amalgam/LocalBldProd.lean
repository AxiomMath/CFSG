module

public import CFSG.Monster.B.TwoA.Amalgam.LocalBld

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Geometry
  CFSG.LieType.Chevalley.CosetBuilding

section IncFlag

variable {Pt Ln : Type*} (inc : Pt → Ln → Prop)

abbrev IncFlag : Type _ := {p : Pt × Ln // inc p.1 p.2}

variable (Z : Type*) (a b z : Fin 4)

@[expose] def incProduct : ChamberSystem (Fin 4) (IncFlag inc × Z) :=
  ChamberSystem.ofThree a b z (fun p q => p.1.1.2 = q.1.1.2 ∧ p.2 = q.2)
    (fun p q => p.1.1.1 = q.1.1.1 ∧ p.2 = q.2) (fun p q => p.1 = q.1)
    ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩
    ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩
    ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

variable {inc Z a b z}

theorem incProduct_adj_a :
    (incProduct inc Z a b z).adj a = fun p q => p.1.1.2 = q.1.1.2 ∧ p.2 = q.2 :=
  ChamberSystem.ofThree_adj₁

theorem incProduct_adj_b (hab : a ≠ b) :
    (incProduct inc Z a b z).adj b = fun p q => p.1.1.1 = q.1.1.1 ∧ p.2 = q.2 :=
  ChamberSystem.ofThree_adj₂ hab.symm

theorem incProduct_adj_z (haz : a ≠ z) (hbz : b ≠ z) :
    (incProduct inc Z a b z).adj z = fun p q => p.1 = q.1 :=
  ChamberSystem.ofThree_adj₃ haz.symm hbz.symm

theorem incProduct_plane_gallery (hab : a ≠ b) (hinc : ∀ x x' : Pt, ∃ L, inc x L ∧ inc x' L)
    (u u' : IncFlag inc) (t : Z) :
    ∃ γ : List (Fin 4 × (IncFlag inc × Z)), (incProduct inc Z a b z).IsGallery (u, t) γ ∧
      (∀ j ∈ galleryType γ, j ∈ ({a, b} : Set (Fin 4))) ∧ galleryEnd (u, t) γ = (u', t) := by
  obtain ⟨L, h1, h2⟩ := hinc u.1.1 u'.1.1
  let w₁ : IncFlag inc := ⟨(u.1.1, L), h1⟩
  let w₂ : IncFlag inc := ⟨(u'.1.1, L), h2⟩
  refine ⟨[(b, (w₁, t)), (a, (w₂, t)), (b, (u', t))], ?_, ?_, rfl⟩
  · refine ⟨?_, ?_, ?_, trivial⟩
    · rw [incProduct_adj_b hab]
      exact ⟨rfl, rfl⟩
    · rw [incProduct_adj_a]
      exact ⟨rfl, rfl⟩
    · rw [incProduct_adj_b hab]
      exact ⟨rfl, rfl⟩
  · intro j hj
    simp only [galleryType, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp

theorem incProduct_gallery (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
    (hinc : ∀ x x' : Pt, ∃ L, inc x L ∧ inc x' L) (x y : IncFlag inc × Z) :
    ∃ γ : List (Fin 4 × (IncFlag inc × Z)), (incProduct inc Z a b z).IsGallery x γ ∧
      (∀ j ∈ galleryType γ, j ∈ ({a, b, z} : Set (Fin 4))) ∧ galleryEnd x γ = y := by
  obtain ⟨γ, h1, h2, h3⟩ := incProduct_plane_gallery (z := z) hab hinc x.1 y.1 y.2
  refine ⟨(z, (x.1, y.2)) :: γ, ⟨?_, h1⟩, ?_, ?_⟩
  · rw [incProduct_adj_z haz hbz]
  · intro j hj
    simp only [galleryType, List.map_cons, List.mem_cons] at hj
    rcases hj with rfl | hj
    · simp
    · rcases h2 j hj with rfl | rfl <;> simp
  · rw [galleryEnd_cons, h3]

end IncFlag

section Residue

variable {Pt Ln : Type*} {inc : Pt → Ln → Prop} {Z : Type*} {a b z : Fin 4} {i : Fin 4}
  {φ : Pc i → IncFlag inc × Z} (hφ : IsFlagModel (incProduct inc Z a b z) φ)
  (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
  (hJ : ∀ j : Fin 4, j ≠ i ↔ j = a ∨ j = b ∨ j = z)
  (hinc : ∀ x x' : Pt, ∃ L, inc x L ∧ inc x' L)
include hφ hab haz hbz hJ hinc

omit hφ in
theorem incProduct_conn (x₀ x : IncFlag inc × Z) :
    ∃ γ : List (Fin 4 × (IncFlag inc × Z)), (incProduct inc Z a b z).IsGallery x₀ γ ∧
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ i}) ∧ galleryEnd x₀ γ = x := by
  obtain ⟨γ, h1, h2, h3⟩ := incProduct_gallery hab haz hbz hinc x₀ x
  refine ⟨γ, h1, fun j hj => ?_, h3⟩
  have := h2 j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  exact (hJ j).mpr this

omit hab haz hbz hJ hinc in
@[expose] def sliceChamber (u : IncFlag inc) : Chamber := flagChamber hφ (u, (φ 1).2)

omit haz hbz hJ hinc in
theorem flagChamber_slice_eq {u : IncFlag inc} {γ : List (Fin 4 × Chamber)}
    (hi : ∀ j ∈ ({a, b} : Set (Fin 4)), j ≠ i)
    (hγ : cosetCS.IsGallery (flagChamber hφ (u, (φ 1).2)) γ)
    (hγJ : ∀ j ∈ galleryType γ, j ∈ ({a, b} : Set (Fin 4))) :
    ∃ u', flagChamber hφ (u', (φ 1).2) = galleryEnd (flagChamber hφ (u, (φ 1).2)) γ := by
  induction γ generalizing u with
  | nil => exact ⟨u, rfl⟩
  | cons p γ ih =>
    have hp : p.1 ∈ ({a, b} : Set (Fin 4)) := hγJ p.1 (by simp [galleryType])
    obtain ⟨c, hc⟩ := exists_flagChamber_of_adj hφ (hi p.1 hp) _ hγ.1
    have hadj := (chamberAdj_flagChamber_iff hφ (hi p.1 hp) _ c).mp (hc ▸ hγ.1)
    have hc2 : c.2 = (φ 1).2 := by
      rcases hp with hp | hp
      · rw [hp, incProduct_adj_a] at hadj
        exact hadj.2.symm
      · rw [Set.mem_singleton_iff.mp hp, incProduct_adj_b hab] at hadj
        exact hadj.2.symm
    have hc' : flagChamber hφ (c.1, (φ 1).2) = p.2 := by
      rw [← hc2]
      exact hc
    rw [galleryEnd_cons]
    have hγ2 : cosetCS.IsGallery (flagChamber hφ (c.1, (φ 1).2)) γ := hc' ▸ hγ.2
    obtain ⟨u', hu'⟩ := ih hγ2 fun j hj => hγJ j (by simp [galleryType] at hj ⊢; tauto)
    exact ⟨u', hu'.trans (by rw [hc'])⟩

omit haz hbz in
theorem bijOn_slice :
    Set.BijOn (sliceChamber hφ) Set.univ (cosetCS.residue {a, b} baseChamber) := by
  have hi : ∀ j ∈ ({a, b} : Set (Fin 4)), j ≠ i := by
    intro j hj
    rcases hj with rfl | hj
    · exact (hJ _).mpr (Or.inl rfl)
    · exact (hJ _).mpr (Or.inr (Or.inl (Set.mem_singleton_iff.mp hj)))
  have hbase : flagChamber hφ ((φ 1).1, (φ 1).2) = baseChamber := flagChamber_one hφ
  refine ⟨fun u _ => ?_, fun u _ u' _ h => ?_, fun c hc => ?_⟩
  · obtain ⟨γ, h1, h2, h3⟩ := incProduct_plane_gallery (z := z) hab hinc (φ 1).1 u (φ 1).2
    have := flagChamber_mem_residue hφ hi h1 h2
    rw [h3, hbase] at this
    exact this
  · exact congrArg Prod.fst (flagChamber_injective hφ h)
  · obtain ⟨γ, hγ, hγJ, rfl⟩ := hc
    rw [← hbase] at hγ ⊢
    obtain ⟨u', hu'⟩ := flagChamber_slice_eq hφ hab hi hγ hγJ
    exact ⟨u', Set.mem_univ _, hu'⟩

theorem isResidueBuilding_of_incProduct {M : CoxeterMatrix (Fin 4)} {W : Type*} [Group W]
    {cs : CoxeterSystem M W} (hMaz : M a z = 2) (hMbz : M b z = 2)
    (hZ : ∀ t : Z, ∃ t', t' ≠ t) (hplane : cosetCS.IsResidueBuilding cs {a, b} baseChamber) :
    cosetCS.IsResidueBuilding cs {j | j ≠ i} baseChamber := by
  obtain ⟨δab, hBab, hadjab⟩ := hplane
  have hs := bijOn_slice hφ hab hJ hinc
  have hai : a ≠ i := (hJ a).mpr (Or.inl rfl)
  have hbi : b ≠ i := (hJ b).mpr (Or.inr (Or.inl rfl))
  have hzi : z ≠ i := (hJ z).mpr (Or.inr (Or.inr rfl))
  set δP : IncFlag inc → IncFlag inc → W :=
    fun u v => δab (sliceChamber hφ u) (sliceChamber hφ v) with hδP
  have hBP : IsBuildingOn cs δP {a, b} Set.univ := hBab.comap hs
  have hPadj : ∀ (u v : IncFlag inc) (j : Fin 4), j ∈ ({a, b} : Set (Fin 4)) →
      ((δP u v = 1 ∨ δP u v = cs.simple j) ↔
        (incProduct inc Z a b z).adj j (u, (φ 1).2) (v, (φ 1).2)) := by
    intro u v j hj
    have hji : j ≠ i := by
      rcases hj with rfl | hj
      · exact hai
      · rw [Set.mem_singleton_iff.mp hj]
        exact hbi
    exact (hadjab _ (hs.mapsTo (Set.mem_univ u)) _ (hs.mapsTo (Set.mem_univ v)) j hj).symm.trans
      (chamberAdj_flagChamber_iff hφ hji _ _)
  have hz : z ∉ ({a, b} : Set (Fin 4)) := by
    rintro (h | h)
    · exact haz h.symm
    · exact hbz (Set.mem_singleton_iff.mp h).symm
  have hM : ∀ j ∈ ({a, b} : Set (Fin 4)), M j z = 2 := by
    intro j hj
    rcases hj with rfl | hj
    · exact hMaz
    · rw [Set.mem_singleton_iff.mp hj]
      exact hMbz
  have hprod := hBP.prodRankOne hz hM hZ
  have hset : insert z ({a, b} : Set (Fin 4)) = {j | j ≠ i} := by
    ext j
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    rw [hJ j]
    tauto
  rw [hset, Set.univ_prod_univ] at hprod
  refine isResidueBuilding_of_flagModel hφ hprod (fun x y j hj => ?_)
    (incProduct_conn hab haz hbz hJ hinc (φ 1))
  rcases (hJ j).mp hj with rfl | rfl | rfl
  · rw [prodRankOneDist_adj_iff hBP hz (Set.mem_univ _) (Set.mem_univ _) (Or.inl rfl),
      hPadj _ _ _ (Or.inl rfl), incProduct_adj_a]
    simp
  · rw [prodRankOneDist_adj_iff hBP hz (Set.mem_univ _) (Set.mem_univ _) (Or.inr rfl),
      hPadj _ _ _ (Or.inr rfl), incProduct_adj_b hab]
    simp
  · rw [prodRankOneDist_adj_z_iff hBP hz (Set.mem_univ _) (Set.mem_univ _),
      incProduct_adj_z haz hbz]

end Residue

end CFSG.Monster.B.TwoA.Amalgam

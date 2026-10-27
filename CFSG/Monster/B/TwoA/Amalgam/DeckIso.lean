module

public import CFSG.Monster.B.Geometry.ChamberCoverAction

public section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

section Generic

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {D : Type*} {δ : D → D → W}

theorem eq_simple_iff_adj (hδ : IsWeylDistanceBuilding cs δ) {Y : ChamberSystem ι D}
    (hadj : ∀ i A B, Y.adj i A B ↔ δ A B = 1 ∨ δ A B = cs.simple i) (i : ι) (A B : D) :
    δ A B = cs.simple i ↔ Y.adj i A B ∧ A ≠ B := by
  constructor
  · intro h
    exact ⟨(hadj i A B).2 (Or.inr h), fun e =>
      CoxeterSystem.simple_ne_one cs i (h.symm.trans ((hδ.eq_one_iff A B).2 e))⟩
  · rintro ⟨h, hne⟩
    rcases (hadj i A B).1 h with h1 | h1
    · exact absurd ((hδ.eq_one_iff A B).1 h1) hne
    · exact h1

theorem typeAut_le_of_adj (hδ : IsWeylDistanceBuilding cs δ) {Y : ChamberSystem ι D}
    (hadj : ∀ i A B, Y.adj i A B ↔ δ A B = 1 ∨ δ A B = cs.simple i) :
    Y.typeAut ≤ CFSG.Monster.B.Geometry.typeAut cs δ := by
  intro g hg
  refine (CFSG.Monster.B.Geometry.mem_typeAut cs δ).2 fun x y i => ?_
  rw [eq_simple_iff_adj hδ hadj, eq_simple_iff_adj hδ hadj, (ChamberSystem.mem_typeAut.1 hg) i x y,
    g.injective.ne_iff]

theorem isWeylDistanceBuilding_equiv (hδ : IsWeylDistanceBuilding cs δ) {D' : Type*}
    (e : D ≃ D') : IsWeylDistanceBuilding cs (fun x y : D' => δ (e.symm x) (e.symm y)) where
  nonempty := by
    obtain ⟨x⟩ := hδ.nonempty
    exact ⟨e x⟩
  eq_one_iff x y := (hδ.eq_one_iff _ _).trans e.symm.injective.eq_iff
  mul_simple x y z i h := hδ.mul_simple _ _ _ i h
  exists_simple x y i := by
    obtain ⟨z, hz⟩ := hδ.exists_simple (e.symm x) (e.symm y) i
    exact ⟨e z, by simpa using hz⟩

end Generic

section Cover

variable {I C : Type*} {X : ChamberSystem I C} {c₀ : C}

theorem coverProj_injective_of_pi2_eq_bot (hK : X.pi2 c₀ = ⊥) :
    Function.Injective (X.coverProj c₀) := by
  intro d d' h
  obtain ⟨z, hz, rfl⟩ := ChamberSystem.exists_ker_smul_eq h
  have hz1 : z = 1 := by
    have hz' : z ∈ X.pi2 c₀ := hz
    rw [hK, Subgroup.mem_bot] at hz'
    exact hz'
  rw [hz1, one_smul]

theorem coverProj_bijective_of_pi2_eq_bot (hX : X.Connected) (hK : X.pi2 c₀ = ⊥) :
    Function.Bijective (X.coverProj c₀) :=
  ⟨coverProj_injective_of_pi2_eq_bot hK, ChamberSystem.coverProj_surjective hX⟩

theorem adj_iff_of_pi2_eq_bot (hK : X.pi2 c₀ = ⊥) (i : I) (A B : X.Cover c₀) :
    (X.universalCover c₀).adj i A B ↔ X.adj i (X.coverProj c₀ A) (X.coverProj c₀ B) := by
  refine ⟨ChamberSystem.isMorphism_coverProj i A B, fun h => ?_⟩
  have hB : X.coverProj c₀ B ∈ X.residue {i} (X.coverProj c₀ A) :=
    ChamberSystem.mem_residue_singleton.2 h
  obtain ⟨B', hB', hBB'⟩ := (ChamberSystem.bijOn_coverProj_panel i A).surjOn hB
  have hBeq : B' = B := coverProj_injective_of_pi2_eq_bot hK hBB'
  rw [← hBeq]
  exact ChamberSystem.mem_residue_singleton.1 hB'

theorem exists_building_of_pi2_eq_bot {M : CoxeterMatrix I} {W : Type*} [Group W]
    {cs : CoxeterSystem M W} (hX : X.Connected) (hK : X.pi2 c₀ = ⊥)
    {δ : X.Cover c₀ → X.Cover c₀ → W} (hδ : IsWeylDistanceBuilding cs δ)
    (hadj : ∀ i A B, (X.universalCover c₀).adj i A B ↔ δ A B = 1 ∨ δ A B = cs.simple i) :
    ∃ δX : C → C → W, IsWeylDistanceBuilding cs δX ∧
      ∀ i x y, X.adj i x y ↔ δX x y = 1 ∨ δX x y = cs.simple i := by
  set e := Equiv.ofBijective _ (coverProj_bijective_of_pi2_eq_bot hX hK) with he
  refine ⟨fun x y => δ (e.symm x) (e.symm y), isWeylDistanceBuilding_equiv hδ e,
    fun i x y => ?_⟩
  rw [← hadj, adj_iff_of_pi2_eq_bot hK]
  simp only [he, Equiv.ofBijective_apply_symm_apply]

theorem natCard_eq_of_pi2_eq_bot (hX : X.Connected) (hK : X.pi2 c₀ = ⊥) :
    Nat.card C = Nat.card (X.Cover c₀) :=
  (Nat.card_congr (Equiv.ofBijective _ (coverProj_bijective_of_pi2_eq_bot hX hK))).symm

end Cover

end CFSG.Monster.B.TwoA.Amalgam

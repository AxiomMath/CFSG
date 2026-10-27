module

public import CFSG.Monster.B.Geometry.ChamberSystem

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

namespace ChamberSystem

variable {X : ChamberSystem ι C}

theorem residue_eq_of_adj_iff (hδ : IsWeylDistanceBuilding cs δ)
    (hadj : ∀ i x y, X.adj i x y ↔ δ x y = 1 ∨ δ x y = cs.simple i) (J : Set ι) (x : C) :
    X.residue J x = CFSG.LieType.Chevalley.CosetBuilding.residue cs δ J x := by
  ext y
  constructor
  · rintro ⟨γ, hγ, hJ, rfl⟩
    induction γ generalizing x with
    | nil => exact Relation.ReflTransGen.refl
    | cons p γ ih =>
      obtain ⟨h1, h2⟩ := hγ
      have hrest := ih p.2 h2 (fun i hi => hJ i (by simp [hi]))
      rw [galleryEnd_cons]
      rcases (hadj p.1 x p.2).mp h1 with h | h
      · rw [(hδ.eq_one_iff x p.2).mp h]
        exact hrest
      · exact Relation.ReflTransGen.head ⟨p.1, hJ p.1 (by simp), h⟩ hrest
  · intro h
    induction h with
    | refl => exact X.self_mem_residue J x
    | @tail b c _ hbc ih =>
      obtain ⟨i, hi, he⟩ := hbc
      exact mem_residue_trans ih (X.residue_mono (Set.singleton_subset_iff.mpr hi) b
        (mem_residue_singleton.mpr ((hadj i b c).mpr (Or.inr he))))

end ChamberSystem

end CFSG.Monster.B.Geometry

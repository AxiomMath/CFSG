module

public import CFSG.Quasithin.EmptyFaithful.S153NDef

public section

namespace CFSG.Quasithin.S153N

variable {W : Type} [CommGroup W]

theorem relIndex_stabAt_eq_ncard (Γ : Subgroup (MulAut W)) (w : W) :
    (stabAt Γ w).relIndex Γ = ((fun g : MulAut W => g w) '' (Γ : Set (MulAut W))).ncard := by
  have h1 : (stabAt Γ w).subgroupOf Γ = MulAction.stabilizer ↥Γ w := by
    ext g
    rw [Subgroup.mem_subgroupOf, mem_stabAt, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  rw [Subgroup.relIndex, h1, MulAction.index_stabilizer]
  congr 1
  ext x
  simp [MulAction.mem_orbit_iff]

theorem image_eq_of_stabAt_sup {Γ J : Subgroup (MulAut W)} {w : W} (hJΓ : J ≤ Γ)
    (hJn : (J.subgroupOf Γ).Normal) (hsup : Γ = J ⊔ stabAt Γ w) :
    (fun g : MulAut W => g w) '' (Γ : Set (MulAut W)) =
      (fun g : MulAut W => g w) '' (J : Set (MulAut W)) := by
  refine le_antisymm ?_ (Set.image_mono hJΓ)
  rintro _ ⟨g, hg, rfl⟩
  have h1 : (J ⊔ stabAt Γ w).subgroupOf Γ = J.subgroupOf Γ ⊔ (stabAt Γ w).subgroupOf Γ :=
    Subgroup.subgroupOf_sup hJΓ (stabAt_le Γ w)
  rw [← hsup, Subgroup.subgroupOf_self] at h1
  have hmem : (⟨g, hg⟩ : ↥Γ) ∈ J.subgroupOf Γ ⊔ (stabAt Γ w).subgroupOf Γ := by
    rw [← h1]
    exact Subgroup.mem_top _
  have := hJn
  obtain ⟨j, hj, d, hd, hjd⟩ := Subgroup.mem_sup_of_normal_left.1 hmem
  refine ⟨(j : MulAut W), hj, ?_⟩
  have hdw : (d : MulAut W) w = w := hd.2
  have h2 := congrArg (fun x : ↥Γ => (x : MulAut W) w) hjd
  simp only at h2
  show (j : MulAut W) w = g w
  rw [← h2]
  show (j : MulAut W) w = ((j : MulAut W) * (d : MulAut W)) w
  rw [MulAut.mul_apply, hdw]

end CFSG.Quasithin.S153N

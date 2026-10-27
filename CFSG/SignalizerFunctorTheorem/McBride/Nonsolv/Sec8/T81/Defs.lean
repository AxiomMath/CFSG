module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

variable {G : Type*} [Group G]

@[expose] def zL (θ : G → Subgroup G) (Z B L : Subgroup G) : Subgroup G :=
  Z ⊓ ⨅ K ∈ lcal (thetaOf θ B), ⨅ (_ : K ≠ L), Subgroup.centralizer (K : Set G)

@[expose] def mL (θ : G → Subgroup G) (Z B L : Subgroup G) : Subgroup G :=
  L ⊔ zL θ Z B L

@[expose] def mAll (θ : G → Subgroup G) (Z B : Subgroup G) : Subgroup G :=
  ⨆ L ∈ lcal (thetaOf θ B), mL θ Z B L

@[expose] def mFam (θ : G → Subgroup G) (Z B : Subgroup G) : Set (Subgroup G) :=
  {Y | ∃ L ∈ lcal (thetaOf θ B), Y = mL θ Z B L}

theorem mem_zL_iff {θ : G → Subgroup G} {Z B L : Subgroup G} {z : G} :
    z ∈ zL θ Z B L ↔ z ∈ Z ∧ ∀ K ∈ lcal (thetaOf θ B), K ≠ L → ∀ y ∈ K, y * z = z * y := by
  simp only [zL, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => forall₂_congr fun K _ => ?_
  constructor
  · intro h hKL y hy
    exact (h hKL) y hy
  · intro h hKL y hy
    exact h hKL y hy

theorem le_mL (θ : G → Subgroup G) (Z B L : Subgroup G) : L ≤ mL θ Z B L := le_sup_left

theorem zL_le_mL (θ : G → Subgroup G) (Z B L : Subgroup G) : zL θ Z B L ≤ mL θ Z B L :=
  le_sup_right

theorem zL_le (θ : G → Subgroup G) (Z B L : Subgroup G) : zL θ Z B L ≤ Z := inf_le_left

theorem mL_le_mAll {θ : G → Subgroup G} {Z B L : Subgroup G} (hL : L ∈ lcal (thetaOf θ B)) :
    mL θ Z B L ≤ mAll θ Z B :=
  le_iSup₂_of_le L hL le_rfl

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

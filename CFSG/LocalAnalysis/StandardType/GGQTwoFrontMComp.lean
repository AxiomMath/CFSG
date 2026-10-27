module

public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem qTwoFrontM_comp_false {R : Type} [Group R] {L D J : Subgroup G} {y : G} (hyD : y ∈ D)
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) (φ : ↥L →* R)
    (hφ : φ.ker ≤ Subgroup.center ↥L) {a : ↥L}
    (ha : ∀ l : ↥L, y * (l : G) * y⁻¹ = ((a * l * a⁻¹ : ↥L) : G))
    (hsol : Group.IsSolvable ↥(Subgroup.centralizer ({φ a} : Set R))) : False := by
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hJD : J ≤ Subgroup.centralizer (D : Set G) := hJ.1.trans inf_le_right
  let ψ : ↥J →* R := φ.comp (Subgroup.inclusion hJL)
  have hcomm : ∀ j : ↥J, φ a * ψ j = ψ j * φ a := by
    intro j
    set l : ↥L := Subgroup.inclusion hJL j with hl
    have hyj : y * (j : G) = (j : G) * y :=
      (Subgroup.mem_centralizer_iff.mp (hJD j.2)) y hyD
    have hcy : y * (j : G) * y⁻¹ = (j : G) := by
      rw [hyj, mul_assoc, mul_inv_cancel, mul_one]
    have hconjG : ((a * l * a⁻¹ : ↥L) : G) = (j : G) := by
      rw [← ha l, hl, Subgroup.coe_inclusion]
      exact hcy
    have hconjL : a * l * a⁻¹ = l := by
      apply Subtype.ext
      rw [hconjG, hl, Subgroup.coe_inclusion]
    have hphiconj : φ a * φ l * (φ a)⁻¹ = φ l := by
      simpa only [map_mul, map_inv] using congrArg φ hconjL
    have hlψ : ψ j = φ l := rfl
    rw [hlψ]
    calc φ a * φ l = (φ a * φ l * (φ a)⁻¹) * φ a := by group
      _ = φ l * φ a := by rw [hphiconj]
  have hrange_le : ψ.range ≤ Subgroup.centralizer ({φ a} : Set R) := by
    rintro _ ⟨j, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hcomm j
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({φ a} : Set R)) := hsol
  have hrange_solv : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hrange_le)
      (Subgroup.inclusion_injective hrange_le)
  have hker_solv : Group.IsSolvable ↥ψ.ker := by
    refine Group.isSolvable_of_comm (fun p q => ?_)
    have hp : Subgroup.inclusion hJL (p : ↥J) ∈ Subgroup.center ↥L :=
      hφ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp p.2))
    apply Subtype.ext
    apply Subgroup.inclusion_injective hJL
    change Subgroup.inclusion hJL ((p : ↥J) * (q : ↥J)) =
      Subgroup.inclusion hJL ((q : ↥J) * (p : ↥J))
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hp (Subgroup.inclusion hJL (q : ↥J))).symm
  haveI : Group.IsSolvable ↥ψ.ker := hker_solv
  haveI : Group.IsSolvable ↥ψ.range := hrange_solv
  have hker_eq : ψ.rangeRestrict.ker = ψ.ker := by
    ext j
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  have hsJ : Group.IsSolvable ↥J :=
    Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict (by
      rw [hker_eq, Subgroup.range_subtype])
  haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2.toNontrivial
  haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
  exact (Group.IsPerfect.not_isSolvable ↥J) hsJ

end CFSG.StandardType.QTwo

end

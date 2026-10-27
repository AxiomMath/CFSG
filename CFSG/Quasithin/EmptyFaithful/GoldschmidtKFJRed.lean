module

public import CFSG.Quasithin.EmptyFaithful.SBd18Out
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.ComponentClassification

theorem not_isSolvable_fixedSub_of_quotient {K : Type} [Group K] (u : MulAut K)
    (h : ¬ Group.IsSolvable ↥(SBd18.fixedSub (PerfectAutomorphisms.centerQuotientHom K u))) :
    ¬ Group.IsSolvable ↥(SBd18.fixedSub u) := by
  intro hsolv
  apply h
  let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  let ū := PerfectAutomorphisms.centerQuotientHom K u
  let D : Subgroup K := (SBd18.fixedSub ū).comap π
  have hπu : ∀ x : K, π (u x) = ū (π x) := fun x =>
    (CentralCover.centerQuotientHom_apply_mk K u x).symm
  have hD : ∀ d : K, d ∈ D ↔ ū (π d) = π d := fun d => SBd18.mem_fixedSub
  have hmem : ∀ d : D, (u d * (d : K)⁻¹ : K) ∈ Subgroup.center K := fun d => by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (u d * (d : K)⁻¹) = 1
    rw [map_mul, map_inv, hπu, (hD d).mp d.2, mul_inv_cancel]
  let ζ : D →* Subgroup.center K :=
    { toFun := fun d => ⟨u d * (d : K)⁻¹, hmem d⟩
      map_one' := by
        apply Subtype.ext
        change u (1 : K) * (1 : K)⁻¹ = 1
        simp
      map_mul' := fun d e => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hmem e)
        change u ((d : K) * e) * ((d : K) * e)⁻¹ =
          (u d * (d : K)⁻¹) * (u e * (e : K)⁻¹)
        calc u ((d : K) * e) * ((d : K) * e)⁻¹
            = u d * (u e * (e : K)⁻¹) * (d : K)⁻¹ := by rw [map_mul]; group
          _ = u d * (d : K)⁻¹ * (u e * (e : K)⁻¹) := by
              rw [hc (u d)]
              calc u e * (e : K)⁻¹ * u d * (d : K)⁻¹
                  = (u e * (e : K)⁻¹) * (u d * (d : K)⁻¹) := by group
                _ = u d * (d : K)⁻¹ * (u e * (e : K)⁻¹) := (hc (u d * (d : K)⁻¹)).symm }
  have hle : SBd18.fixedSub u ≤ D := fun x hx => by
    rw [hD, ← hπu, SBd18.mem_fixedSub.mp hx]
  have hker : ζ.ker ≤ (Subgroup.inclusion hle).range := fun d hd => by
    have h1 := congrArg Subtype.val ((MonoidHom.mem_ker).mp hd)
    change u d * (d : K)⁻¹ = 1 at h1
    exact ⟨⟨d, SBd18.mem_fixedSub.mpr (mul_inv_eq_one.mp h1)⟩, rfl⟩
  have : Group.IsSolvable (Subgroup.center K) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  have : Group.IsSolvable D := Group.isSolvable_of_ker_le_range _ ζ hker
  let f : D →* ↥(SBd18.fixedSub ū) :=
    { toFun := fun d => ⟨π d, SBd18.mem_fixedSub.mpr ((hD d).mp d.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun d e => by
        apply Subtype.ext
        simp }
  refine Group.isSolvable_of_surjective (f := f) fun q => ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) q.1
  exact ⟨⟨x, (hD x).mpr (by rw [hx]; exact SBd18.mem_fixedSub.mp q.2)⟩, Subtype.ext hx⟩

end CFSG.Quasithin.SBd19F

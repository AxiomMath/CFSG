module

public import CFSG.Quasithin.EmptyFaithful.SBd18Out
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.ComponentClassification CFSG.Open

variable {K : Type} [Group K]

@[expose] noncomputable def fixedPre (u : MulAut K) : Subgroup K :=
  (SBd18.fixedSub (PerfectAutomorphisms.centerQuotientHom K u)).comap
    (QuotientGroup.mk' (Subgroup.center K))

theorem mem_fixedPre {u : MulAut K} {d : K} :
    d ∈ fixedPre u ↔ PerfectAutomorphisms.centerQuotientHom K u (d : K ⧸ Subgroup.center K) =
      (d : K ⧸ Subgroup.center K) :=
  Iff.rfl

theorem fixedSub_le_fixedPre (u : MulAut K) : SBd18.fixedSub u ≤ fixedPre u := fun x hx => by
  rw [mem_fixedPre, CentralCover.centerQuotientHom_apply_mk K u x, SBd18.mem_fixedSub.mp hx]

theorem normal_fixedSub_comap (u : MulAut K) :
    ((SBd18.fixedSub u).subgroupOf (fixedPre u)).Normal := by
  let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hπu : ∀ x : K, π (u x) = PerfectAutomorphisms.centerQuotientHom K u (π x) := fun x =>
    (CentralCover.centerQuotientHom_apply_mk K u x).symm
  have hmem : ∀ d : fixedPre u, (u d * (d : K)⁻¹ : K) ∈ Subgroup.center K := fun d => by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (u d * (d : K)⁻¹) = 1
    have hd : PerfectAutomorphisms.centerQuotientHom K u (π d) = π d := mem_fixedPre.mp d.2
    rw [map_mul, map_inv, hπu, hd, mul_inv_cancel]
  let ζ : fixedPre u →* Subgroup.center K :=
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
  have hker : ζ.ker = (SBd18.fixedSub u).subgroupOf (fixedPre u) := by
    ext d
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, SBd18.mem_fixedSub]
    constructor
    · intro h
      have h1 := congrArg Subtype.val h
      change u d * (d : K)⁻¹ = 1 at h1
      exact mul_inv_eq_one.mp h1
    · intro h
      apply Subtype.ext
      change u d * (d : K)⁻¹ = 1
      rw [h, mul_inv_cancel]
  rw [← hker]
  exact MonoidHom.normal_ker ζ

theorem map_fixedPre (u : MulAut K) :
    (fixedPre u).map (QuotientGroup.mk' (Subgroup.center K)) =
      SBd18.fixedSub (PerfectAutomorphisms.centerQuotientHom K u) :=
  Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem isSubnormal_map_fixedSub (u : MulAut K) {L : Subgroup K}
    (hL : IsSubnormal L (SBd18.fixedSub u)) :
    IsSubnormal (L.map (QuotientGroup.mk' (Subgroup.center K)))
      (SBd18.fixedSub (PerfectAutomorphisms.centerQuotientHom K u)) := by
  have h1 : IsSubnormal L (fixedPre u) :=
    A3.subnormal_trans hL
      (A3.subnormal_of_normal (fixedSub_le_fixedPre u) (normal_fixedSub_comap u))
  have h2 := A3.subnormal_map (QuotientGroup.mk' (Subgroup.center K)) h1
  rwa [map_fixedPre] at h2

end CFSG.Quasithin.SBd19F

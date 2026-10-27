module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixQuasi
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.StandardType

variable {L R : Type*} [Group L] [Group R]

theorem ggQ2s08rN_comm_comap_quasisimple {π : L →* R} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center L) (S : Subgroup R) (hS : ⁅S, S⁆ = S)
    (hSq : CFSG.Assembly.IsQuasisimple ↥S) :
    CFSG.Assembly.IsQuasisimple ↥(⁅S.comap π, S.comap π⁆) := by
  set Q : Subgroup L := ⁅S.comap π, S.comap π⁆
  have hQperf : ⁅Q, Q⁆ = Q := ggQ2s08r6_comm_comap_perfect hπ hker S hS
  have hperf : commutator ↥Q = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : L) ∈ ⁅Q, Q⁆ := by rw [hQperf]; exact x.2
    rw [← Subgroup.map_subtype_commutator Q] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  have hmap : Q.map π = S := ggQ2s08r6_map_comm_comap hπ S hS
  let f : ↥Q →* ↥S :=
    { toFun := fun x =>
        ⟨π (x : L), Subgroup.mem_comap.mp (Subgroup.commutator_le_self (S.comap π) x.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [map_mul] }
  have hf : Function.Surjective f := by
    intro s
    have hs : (s : R) ∈ Q.map π := by rw [hmap]; exact s.2
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨x, hx⟩, Subtype.ext hxπ⟩
  have hkerf : f.ker ≤ Subgroup.center ↥Q := by
    intro q hq
    have hq' : (q : L) ∈ π.ker := MonoidHom.mem_ker.mpr (Subtype.ext_iff.mp hq)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using Subgroup.mem_center_iff.mp (hker hq') (y : L)
  have hQp : Group.IsPerfect ↥Q := ⟨hperf⟩
  have hc : Subgroup.center ↥Q = ((QuotientGroup.mk' (Subgroup.center ↥S)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hQp f hf hkerf]
  let e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥S ⧸ Subgroup.center ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))
  have : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
  exact ⟨hperf, (MulEquiv.isSimpleGroup_congr e).mpr this⟩

end CFSG.StandardType

end

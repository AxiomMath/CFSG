module

public import CFSG.Quasithin.EmptyFaithful.T1521SU3Zc
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBasic

public section

namespace CFSG.Quasithin.U31521

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] noncomputable def conjAut (L : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (L : Set G)) : MulAut ↥L :=
  CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt.conjAct
    (E := Subgroup.normalizer (L : Set G)) (X := L) le_rfl ⟨g, hg⟩

theorem coe_conjAut_apply (L : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) : ((conjAut L g hg x : ↥L) : G) = g * (x : G) * g⁻¹ := rfl

variable [Finite G]

theorem centralizes_center_of_sq_mem_centralizer {L R : Subgroup G}
    {n : ℕ} (hn : 2 ≤ n) (hL : IsPSU 3 2 n ↥L) (hR : IsSylowTwoOf R L) {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgR : g ∈ Subgroup.normalizer (R : Set G))
    (hg2 : g ^ 2 ∈ Subgroup.centralizer (L : Set G)) {z : G} (hz : z ∈ R)
    (hzc : ∀ y ∈ R, z * y = y * z) : g * z * g⁻¹ = z := by
  have hzL : z ∈ L := hR.1 hz
  let R' : Sylow 2 ↥L := A4.toSylow hR
  have hR'mem : ∀ x : ↥L, x ∈ (R' : Subgroup ↥L) ↔ (x : G) ∈ R := fun x => Iff.rfl
  set β : MulAut ↥L := conjAut L g hgL with hβ
  have hβstab : β ∈ autStab (R' : Subgroup ↥L) := by
    rw [mem_autStab]
    intro x
    rw [hR'mem, hR'mem, hβ, coe_conjAut_apply]
    exact (Subgroup.mem_normalizer_iff.mp hgR (x : G)).symm
  have hβ2 : β ^ 2 = 1 := by
    ext x
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, hβ, coe_conjAut_apply, coe_conjAut_apply]
    have h1 : g * (g * (x : G) * g⁻¹) * g⁻¹ = (g * g) * (x : G) * (g * g)⁻¹ := by group
    rw [h1]
    have := Subgroup.mem_centralizer_iff.mp (by rwa [pow_two] at hg2) (x : G) x.2
    calc (g * g) * (x : G) * (g * g)⁻¹ = (x : G) * (g * g) * (g * g)⁻¹ := by rw [this]
      _ = (x : G) := by group
  have key := centralizes_center_of_sq_eq_one hn hL R' hβstab hβ2 (u := ⟨z, hzL⟩)
    ((hR'mem _).2 hz) (fun y hy => Subtype.ext (hzc (y : G) ((hR'mem y).1 hy)))
  have := congrArg (fun x : ↥L => (x : G)) key
  simpa [hβ, coe_conjAut_apply] using this

end CFSG.Quasithin.U31521

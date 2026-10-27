module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinSylowNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
open scoped Pointwise
namespace CFSG.GorensteinWalter
noncomputable section
universe u

/-- Sylow conjugacy inside the centralizer produces an inverting normalizer element. -/
public theorem firstCase_klein_sylow_normalizer_inverter
    {G : Type u} [Group G] [Finite G]
    {x y : G} (hy : IsInvolution y)
    (hyInv : y * x * y⁻¹ = x⁻¹)
    (Q : Sylow 2 (Subgroup.centralizer ({x} : Set G))) :
    ∃ n : G, n ∈ Subgroup.normalizer
        (((Q : Subgroup (Subgroup.centralizer ({x} : Set G))).map
          (Subgroup.centralizer ({x} : Set G)).subtype : Subgroup G) : Set G) ∧
      n * x * n⁻¹ = x⁻¹ := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyNormC : y ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hcomm : Commute x z :=
        (Subgroup.mem_centralizer_iff.mp hz x (by simp))
      have hc := hcomm.conj y
      have hc' : Commute x⁻¹ (y*z*y⁻¹) := by simpa [hyInv] using hc
      have hc'' := hc'.inv_left
      have hc''' : Commute x (y*z*y⁻¹) := by simpa using hc''
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : q = x := by simpa using hq
      subst q
      exact hc'''.eq
    · intro hz
      have hcomm : Commute x (y*z*y⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hz x (by simp))
      have hc := hcomm.conj y
      have hcy : y * (y*z*y⁻¹) * y⁻¹ = z := by
        calc
          y * (y*z*y⁻¹) * y⁻¹ = (y*y) * z * (y*y) := by rw [hyinv]; group
          _ = z := by simp [hy2]
      have hc' : Commute z x⁻¹ := by
        simpa only [hcy, hyInv] using hc.symm
      have hc'' := hc'.inv_right
      have hc''' : Commute z x := by simpa using hc''
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : q = x := by simpa using hq
      subst q
      exact hc'''.eq.symm
  let α : C ≃* C :=
    { toFun := fun z => ⟨y * (z : G) * y⁻¹,
        (Subgroup.mem_normalizer_iff.mp hyNormC (z : G)).1 z.2⟩
      invFun := fun z => ⟨y * (z : G) * y⁻¹,
        (Subgroup.mem_normalizer_iff.mp hyNormC (z : G)).1 z.2⟩
      left_inv := by
        intro z
        ext
        calc
          y * (y * (z : G) * y⁻¹) * y⁻¹ = (y*y) * z * (y⁻¹*y⁻¹) := by group
          _ = z := by simp [hy2, hyinv]
      right_inv := by
        intro z
        ext
        calc
          y * (y * (z : G) * y⁻¹) * y⁻¹ = (y*y) * z * (y⁻¹*y⁻¹) := by group
          _ = z := by simp [hy2, hyinv]
      map_mul' := by
        intro a b
        ext
        simp [MulAut.conj_apply] }
  have hαsurj : Function.Surjective α := by
    intro z
    refine ⟨α z, ?_⟩
    apply Subtype.ext
    calc
      y * (y * (z : G) * y⁻¹) * y⁻¹ = (y*y) * z * (y⁻¹*y⁻¹) := by group
      _ = z := by simp [hy2, hyinv]
  let Q' : Sylow 2 C := Sylow.mapSurjective (f := α.toMonoidHom) hαsurj Q
  obtain ⟨d, hd⟩ := @MulAction.IsPretransitive.exists_smul_eq C (Sylow 2 C)
      inferInstance inferInstance Q' Q
  have hmap : (Q' : Subgroup C).map (MulAut.conj d).toMonoidHom =
      (Q : Subgroup C) := by
    have h := congrArg (fun R : Sylow 2 C => (R : Subgroup C)) hd
    rw [Sylow.coe_subgroup_smul] at h
    have hsmul : MulAut.conj d • (Q' : Subgroup C) =
        (Q' : Subgroup C).map (MulAut.conj d).toMonoidHom := by
      ext z
      rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
      constructor <;> rintro ⟨g, hg, hz⟩ <;>
        exact ⟨g, hg, by simpa [MulAut.smul_def] using hz⟩
    rw [hsmul] at h
    exact h
  let n : G := (d : G) * y
  let QG : Subgroup G := (Q : Subgroup C).map C.subtype
  have hQGnorm : Subgroup.map (MulAut.conj n).toMonoidHom QG ≤ QG := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨z0, hz0, hz⟩
    rcases Subgroup.mem_map.mp hz0 with ⟨q, hq, hzq⟩
    have hq' : α q ∈ (Q' : Subgroup C) := by
      exact Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    have hdq : (MulAut.conj d) (α q) ∈ (Q : Subgroup C) := by
      have hm : (MulAut.conj d) (α q) ∈
          (Q' : Subgroup C).map (MulAut.conj d).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨α q, hq', rfl⟩
      rw [hmap] at hm
      exact hm
    have hdqG : (d : G) * (y * (q : G) * y⁻¹) * (d : G)⁻¹ ∈ QG := by
      exact Subgroup.mem_map.mpr ⟨(⟨(MulAut.conj d) (α q), hdq⟩ : Q),
        hdq, rfl⟩
    rw [← hz, ← hzq]
    simpa [QG, n, α, MulAut.conj_apply] using hdqG
  have hQGcard : Nat.card QG = Nat.card (Q : Subgroup C) := by
    exact (Nat.card_congr (Subgroup.equivMapOfInjective
      (Q : Subgroup C) C.subtype C.subtype_injective).toEquiv).symm
  have hQGmapEq : Subgroup.map (MulAut.conj n).toMonoidHom QG = QG := by
    apply Subgroup.eq_of_le_of_card_ge hQGnorm
    rw [Subgroup.card_map_of_injective (K := QG) (MulAut.conj n).injective]
  have hnNorm : n ∈ Subgroup.normalizer (QG : Set G) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).2 hQGmapEq
  refine ⟨n, hnNorm, ?_⟩
  have hdx : Commute (d : G) x :=
    (Subgroup.mem_centralizer_iff.mp d.2 x (by simp)).symm
  calc
    n * x * n⁻¹ = (d : G) * (y*x*y⁻¹) * (d : G)⁻¹ := by simp [n]; group
    _ = (d : G) * x⁻¹ * (d : G)⁻¹ := by rw [hyInv]
    _ = x⁻¹ := by
      rw [hdx.inv_right.eq]
      simp

end
end CFSG.GorensteinWalter

module

public import CFSG.Quasithin.Vol2.Ch11SecA15GO
public import CFSG.GH74.Uniqueness.SU.SU2Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.GH74.Uniqueness.SU.SU2
open scoped Pointwise

variable {G : Type} [Group G]

namespace OnanData

variable {Z Y T V₁ C : Subgroup G} {d : G}

@[expose] noncomputable def ystar (D : OnanData Z Y T V₁ C d) (y : ↥Y) : ↥(onanX Z Y D.YZ) :=
  ⟨onanRho Z Y D.YZ y, ⟨y, rfl⟩⟩

theorem ystar_surj (D : OnanData Z Y T V₁ C d) (x : ↥(onanX Z Y D.YZ)) :
    ∃ y : ↥Y, D.ystar y = x := by
  obtain ⟨y, hy⟩ := x.2
  exact ⟨y, Subtype.ext hy⟩

theorem mem_smul_iff (D : OnanData Z Y T V₁ C d) (y : ↥Y) {W : Subgroup G} (hW : W ≤ Z)
    (u : ↥Z) :
    u ∈ D.ystar y • W.subgroupOf Z ↔ (u : G) ∈ W.map (MulAut.conj (y : G)).toMonoidHom := by
  refine (Subgroup.mem_smul_pointwise_iff_exists _ _ _).trans ?_
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    change _ = ((onanRho Z Y D.YZ y b : ↥Z) : G)
    rw [onanRho_apply_coe]
    rfl
  · rintro ⟨w, hw, hwu⟩
    refine ⟨⟨w, hW hw⟩, hw, Subtype.ext ?_⟩
    change ((onanRho Z Y D.YZ y ⟨w, hW hw⟩ : ↥Z) : G) = u
    rw [onanRho_apply_coe, ← hwu]
    rfl

theorem smul_eq (D : OnanData Z Y T V₁ C d) (y : ↥Y) {W : Subgroup G} (hW : W ≤ Z) :
    D.ystar y • W.subgroupOf Z = (W.map (MulAut.conj (y : G)).toMonoidHom).subgroupOf Z := by
  ext u
  rw [D.mem_smul_iff y hW, Subgroup.mem_subgroupOf]

theorem map_conj_le (D : OnanData Z Y T V₁ C d) (y : ↥Y) {W : Subgroup G} (hW : W ≤ Z) :
    W.map (MulAut.conj (y : G)).toMonoidHom ≤ Z := by
  rintro _ ⟨w, hw, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (D.YZ y.2) w).mp (hW hw)

theorem smul_eq_iff (D : OnanData Z Y T V₁ C d) (y : ↥Y) :
    D.ystar y • C.subgroupOf Z = C.subgroupOf Z ↔
      C.map (MulAut.conj (y : G)).toMonoidHom = C := by
  rw [D.smul_eq y D.CZ, Subgroup.subgroupOf_inj, inf_eq_left.mpr (D.map_conj_le y D.CZ),
    inf_eq_left.mpr D.CZ]

theorem fixSub_eq [Finite G] (D : OnanData Z Y T V₁ C d) :
    fixSub ↥Z (Subgroup.zpowers D.dstar) = C.subgroupOf Z := by
  ext u
  rw [mem_fixSub, Subgroup.mem_subgroupOf]
  constructor
  · intro hu
    have h1 := hu D.dstar (Subgroup.mem_zpowers _)
    rw [← D.conj_eq_iff u.2]
    have := congrArg Subtype.val h1
    change ((onanRho Z Y D.YZ ⟨d, D.dY⟩ u : ↥Z) : G) = u at this
    rwa [onanRho_apply_coe] at this
  · intro hu y hy
    obtain ⟨k, rfl⟩ := exists_pow_of_mem_zpowers hy
    apply Subtype.ext
    change (((D.dstar ^ k : ↥(onanX Z Y D.YZ)) : MulAut ↥Z) u : G) = u
    rw [dstar_pow_apply_coe]
    exact pow_conj_eq_of_conj_eq ((D.conj_eq_iff u.2).mpr hu) k

end OnanData

end CFSG.Quasithin.Vol2.Ch11.SecA

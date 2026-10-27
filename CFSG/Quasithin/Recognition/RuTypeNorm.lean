module

public import CFSG.Quasithin.Recognition.RuTypeSetting

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type*} [Group G]

namespace RuData

variable (R : RuData G)

@[expose] noncomputable def conjBy (g : SL(3, ZMod 2)) : RuData G where
  L := R.L
  T := R.T
  one := R.one
  two := R.two
  θ := (MulAut.conj g⁻¹).toMonoidHom.comp R.θ
  θ_surj := (MulAut.conj g⁻¹).surjective.comp R.θ_surj
  θ_ker := by
    rw [← R.θ_ker]
    ext x
    simp [MonoidHom.mem_ker]
  ψV := R.ψV.trans (SL3.natEquiv g⁻¹)
  ψV_equiv := fun l v w h => by
    have e := R.ψV_equiv l v w h
    apply Multiplicative.toAdd.injective
    simp only [MulEquiv.trans_apply, SL3.natEquiv_apply, toAdd_ofAdd, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, e]
    rw [SL3.natAct3_mul, SL3.natAct3_mul, ← SL3.natAct3_mul g g⁻¹, mul_inv_cancel,
      SL3.natAct3_one]
  χ := (SL3.stHom g⁻¹).comp R.χ
  χ_ker := by
    rw [← R.χ_ker]
    ext s
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · intro h
      apply SL3.stHom_injective g⁻¹
      rw [h, map_one]
    · intro h
      rw [h, map_one]
  χ_trace := fun s => by
    have := R.χ_trace s
    unfold IsTraceZero at this ⊢
    simp only [MonoidHom.coe_comp, Function.comp_apply, SL3.stHom_apply, SL3.trace_stAct]
    exact this
  χ_surj := fun A hA => by
    obtain ⟨s, hs⟩ := R.χ_surj (stAct g A) (by
      unfold IsTraceZero at hA ⊢
      rw [SL3.trace_stAct, hA])
    refine ⟨s, ?_⟩
    apply Multiplicative.toAdd.injective
    simp only [MonoidHom.coe_comp, Function.comp_apply, SL3.stHom_apply, hs, toAdd_ofAdd]
    rw [← SL3.stAct_mul, inv_mul_cancel, SL3.stAct_one]
  χ_equiv := fun l s t h => by
    have e := R.χ_equiv l s t h
    apply Multiplicative.toAdd.injective
    simp only [MonoidHom.coe_comp, Function.comp_apply, SL3.stHom_apply, e, toAdd_ofAdd,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [SL3.stAct_mul, SL3.stAct_mul, ← SL3.stAct_mul g g⁻¹, mul_inv_cancel, SL3.stAct_one]
  σ5 := R.σ5
  σ5_surj := R.σ5_surj
  σ5_ker := R.σ5_ker
  φ := R.φ
  φ_surj := R.φ_surj
  φ_ker := R.φ_ker
  ψU := R.ψU
  ψU_surj := R.ψU_surj
  ψU_ker := R.ψU_ker
  ψU_equiv := R.ψU_equiv

end RuData

structure RuDataN (G : Type*) [Group G] extends RuData G where
  hP0 : ((T : Subgroup G).subgroupOf L).map θ = SL3.P0

namespace RuData

variable [Finite G] (R : RuData G)

theorem card_θT : Nat.card (((R.T : Subgroup G).subgroupOf R.L).map R.θ) = 8 := by
  have h := R.card_θTL
  rwa [R.TL_eq] at h

@[expose] noncomputable def normalize : RuDataN G :=
  let g := (SL3.exists_conj_eq_P0 R.card_θT).choose
  { R.conjBy g with
    hP0 := by
      have hg := (SL3.exists_conj_eq_P0 R.card_θT).choose_spec
      show (((R.T : Subgroup G).subgroupOf R.L).map
        ((MulAut.conj g⁻¹).toMonoidHom.comp R.θ)) = SL3.P0
      rw [← Subgroup.map_map, hg, Subgroup.map_map]
      have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ :=
        MonoidHom.ext fun x => by
          simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
            MulAut.conj_apply, MonoidHom.id_apply]
          group
      rw [this, Subgroup.map_id] }

end RuData

end CFSG.Quasithin.RuType

module

public import CFSG.Quasithin.Recognition.RuTypeNorm
public import CFSG.Quasithin.Recognition.RuTypeSigma

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] def sigmaEquiv (g : SigmaL2F4) :
    Multiplicative (Fin 2 → F4) ≃* Multiplicative (Fin 2 → F4) where
  toFun v := Multiplicative.ofAdd (sigmaAct g (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd (sigmaAct g⁻¹ (Multiplicative.toAdd v))
  left_inv v := by
    simp only [toAdd_ofAdd]
    rw [← Sigma.sigmaAct_mul, inv_mul_cancel, Sigma.sigmaAct_one]
    rfl
  right_inv v := by
    simp only [toAdd_ofAdd]
    rw [← Sigma.sigmaAct_mul, mul_inv_cancel, Sigma.sigmaAct_one]
    rfl
  map_mul' v w := by
    simp only [toAdd_mul, Sigma.sigmaAct_add]
    rfl

theorem sigmaEquiv_apply (g : SigmaL2F4) (v : Multiplicative (Fin 2 → F4)) :
    Multiplicative.toAdd (sigmaEquiv g v) = sigmaAct g (Multiplicative.toAdd v) := rfl

namespace RuData

variable (R : RuData G)

@[expose] noncomputable def conjByS (g : SigmaL2F4) : RuData G :=
  { R with
    φ := (MulAut.conj g⁻¹).toMonoidHom.comp R.φ
    φ_surj := (MulAut.conj g⁻¹).surjective.comp R.φ_surj
    φ_ker := by
      rw [← R.φ_ker]
      ext x
      simp [MonoidHom.mem_ker]
    ψU := (sigmaEquiv g⁻¹).toMonoidHom.comp R.ψU
    ψU_surj := (sigmaEquiv g⁻¹).surjective.comp R.ψU_surj
    ψU_ker := by
      rw [← R.ψU_ker]
      ext x
      simp [MonoidHom.mem_ker]
    ψU_equiv := fun h u u' e => by
      have := R.ψU_equiv h u u' e
      apply Multiplicative.toAdd.injective
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        sigmaEquiv_apply, this, toAdd_ofAdd, MulAut.conj_apply, inv_inv]
      rw [Sigma.sigmaAct_mul, Sigma.sigmaAct_mul, ← Sigma.sigmaAct_mul g g⁻¹, mul_inv_cancel,
        Sigma.sigmaAct_one] }

end RuData

structure RuDataM (G : Type*) [Group G] extends RuDataN G where
  hSP0 : ((T : Subgroup G).subgroupOf (ruH T)).map φ = Sigma.SP0

namespace RuDataN

variable (N : RuDataN G)

omit [Group G] in
theorem Q_le_T [Group G] [Finite G] (N : RuDataN G) : ruQ N.T ≤ (N.T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pCore 2 (ruH N.T)).Normal := pCore_normal 2
  have hTp : IsPGroup 2 ((N.T : Subgroup G).subgroupOf (ruH N.T)) :=
    N.T.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe N.toRuData.T_le_H).symm
  have hidx : ¬ 2 ∣ ((N.T : Subgroup G).subgroupOf (ruH N.T)).index := by
    intro h
    have h1 := Subgroup.relIndex_mul_index N.toRuData.T_le_H
    have h2 := (N.T).not_dvd_index
    apply h2
    rw [← h1]
    exact dvd_mul_of_dvd_left h _
  let P : Sylow 2 (ruH N.T) := hTp.toSylow hidx
  have hle : pCore 2 (ruH N.T) ≤ (P : Subgroup (ruH N.T)) :=
    (pCore_isPGroup (G := ruH N.T) 2).le_sylow_of_normal P
  have h := Subgroup.map_mono (f := (ruH N.T).subtype) hle
  have e : ((P : Subgroup (ruH N.T))).map (ruH N.T).subtype = (N.T : Subgroup G) :=
    Subgroup.map_subgroupOf_eq_of_le N.toRuData.T_le_H
  rw [e] at h
  exact h

variable [Finite G]

theorem card_φT : Nat.card (((N.T : Subgroup G).subgroupOf (ruH N.T)).map N.φ) = 8 := by
  have h1 := Subgroup.relIndex_ker (K := (N.T : Subgroup G).subgroupOf (ruH N.T)) N.φ
  have h2 := Subgroup.relIndex_mul_card N.φ.ker ((N.T : Subgroup G).subgroupOf (ruH N.T))
  have hker : N.φ.ker ≤ (N.T : Subgroup G).subgroupOf (ruH N.T) := by
    rw [N.φ_ker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact N.Q_le_T hx
  have hT : Nat.card (N.T : Subgroup G) = 2 ^ 14 := by
    rw [← N.toRuData.TL_eq, N.toRuData.card_TL]
  rw [inf_eq_left.mpr hker, h1, N.φ_ker, card_subgroupOf_of_le (pCoreOf_le 2 _),
    N.toRuData.card_Q, card_subgroupOf_of_le N.toRuData.T_le_H, hT] at h2
  omega

@[expose] noncomputable def normalizeS : RuDataM G :=
  let g := (Sigma.exists_conj_eq_SP0 N.card_φT).choose
  { toRuDataN := { N.toRuData.conjByS g with hP0 := N.hP0 }
    hSP0 := by
      have hg := (Sigma.exists_conj_eq_SP0 N.card_φT).choose_spec
      show (((N.T : Subgroup G).subgroupOf (ruH N.T)).map
        ((MulAut.conj g⁻¹).toMonoidHom.comp N.φ)) = Sigma.SP0
      rw [← Subgroup.map_map, hg, Subgroup.map_map]
      have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ :=
        MonoidHom.ext fun x => by
          simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
            MulAut.conj_apply, MonoidHom.id_apply]
          group
      rw [this, Subgroup.map_id] }

end RuDataN

theorem nonempty_ruDataM {G : Type*} [Group G] [Finite G] (h : IsTypeRu G) :
    Nonempty (RuDataM G) := by
  obtain ⟨R⟩ := nonempty_ruData h
  exact ⟨R.normalize.normalizeS⟩

end CFSG.Quasithin.RuType

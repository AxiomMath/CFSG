module

public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.RankThree.PartOne.LSTD.Model

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def permSU (hU : UnitaryFieldData 2 f K) :
    Equiv.Perm (Fin 5) →* ↥(unitarySU 2 f K 5) :=
  (permGL (n := 5) (K := K)).codRestrict _ (permGL_mem_unitarySU hU)

@[simp] theorem coe_permSU (hU : UnitaryFieldData 2 f K) (σ : Equiv.Perm (Fin 5)) :
    ((permSU hU σ : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) = permGL σ := rfl

@[expose] noncomputable def Wmodel (hU : UnitaryFieldData 2 f K) :
    Equiv.Perm (Fin 5) →* StatedProj (unitarySU 2 f K 5) :=
  (projU K f).comp (permSU hU)

theorem Wmodel_apply (hU : UnitaryFieldData 2 f K) (σ : Equiv.Perm (Fin 5)) :
    Wmodel hU σ = projU K f (permSU hU σ) := rfl

section Normalizer

variable (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)

include h5 in
theorem conj_torusBar_le (σ : Equiv.Perm (Fin 5)) {x : StatedProj (unitarySU 2 f K 5)}
    (hx : x ∈ torusBar K f) : Wmodel hU σ * x * (Wmodel hU σ)⁻¹ ∈ torusBar K f := by
  obtain ⟨v, hv, rfl⟩ := (mem_torusBar_iff hU h5).mp hx
  have hy : v ∘ σ.symm ∈ torusVec 5 5 K := torusVec_comp σ.symm hv
  refine (mem_torusBar_iff hU h5).mpr ⟨v ∘ σ.symm, hy, ?_⟩
  rw [Wmodel_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, coe_permSU, coe_tSU, coe_tSU,
    permGL_conj_diagU]

include h5 in
theorem Wmodel_mem_normalizer (σ : Equiv.Perm (Fin 5)) :
    Wmodel hU σ ∈ Subgroup.normalizer (torusBar K f : Set (StatedProj (unitarySU 2 f K 5))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_torusBar_le hU h5 σ hx, fun hx => ?_⟩
  have h1 := conj_torusBar_le hU h5 σ⁻¹ hx
  have : Wmodel hU σ⁻¹ * (Wmodel hU σ * x * (Wmodel hU σ)⁻¹) * (Wmodel hU σ⁻¹)⁻¹ = x := by
    rw [map_inv, inv_inv]
    group
  rwa [this] at h1

end Normalizer

section Conj

variable (hU : UnitaryFieldData 2 f K)

theorem map_conj_Bk (σ : Equiv.Perm (Fin 5)) {a b : Fin 5} (hab : a ≠ b) :
    (Bk hU hab).map (MulAut.conj (permSU hU σ)).toMonoidHom = Bk hU (σ.injective.ne hab) := by
  have hmap := map_blk_coordPerm hU σ hab
  have hconj : ∀ g : ↥(unitarySU 2 f K 5),
      ((MulAut.conj (permSU hU σ) g : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) =
        coordPerm K σ (g : GL (Fin 5) K) := by
    intro g
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, coe_permSU,
      permGL_conj_eq_coordPerm]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_Bk_iff, MulEquiv.coe_toMonoidHom, hconj]
    rw [← hmap]
    exact ⟨_, (mem_Bk_iff hU hab).mp hy, rfl⟩
  · intro hx
    have hx' : (x : GL (Fin 5) K) ∈ (blk hU hab).map (coordPerm K σ).toMonoidHom := by
      rw [hmap]
      exact hx
    obtain ⟨g, hg, hgx⟩ := hx'
    refine ⟨⟨g, blk_le_unitarySU hab hg⟩, hg, ?_⟩
    apply Subtype.ext
    rw [MulEquiv.coe_toMonoidHom, hconj]
    exact hgx

theorem Jfun_equiv_model (σ : Equiv.Perm (Fin 5)) (a b : Fin 5) :
    Jfun hU (σ a) (σ b) = conjBy (Wmodel hU σ) (Jfun hU a b) := by
  by_cases hab : a = b
  · subst hab
    have : Jfun hU (σ a) (σ a) = ⊥ := by simp [Jfun]
    rw [this]
    have h2 : Jfun hU a a = ⊥ := by simp [Jfun]
    rw [h2]
    unfold conjBy
    exact (Subgroup.map_bot _).symm
  · rw [Jfun_of_ne hU (σ.injective.ne hab), Jfun_of_ne hU hab, ← map_conj_Bk hU σ hab]
    unfold conjBy
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1

end Conj

section Model

variable (hU : UnitaryFieldData 2 f K)

noncomputable def mapEquivOfInjOn {A B : Type} [Group A] [Group B] (H : Subgroup A) (φ : A →* B)
    (h : Function.Injective (φ.comp H.subtype)) : ↥H ≃* ↥(H.map φ) :=
  (MonoidHom.ofInjective h).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

theorem Jfun_model (hf : 2 ≤ f) {a b : Fin 5} (hab : a ≠ b) :
    StatedClassicalModel ↥(Jfun hU a b) .PSL 2 2 f := by
  have hmodel := (blk_model hU hf hab).2.2
  let e1 : ↥(blk hU hab) ≃* ↥(Bk hU hab) :=
    (Subgroup.subgroupOfEquivOfLe (blk_le_unitarySU hab)).symm
  let e2 : ↥(Bk hU hab) ≃* ↥((Bk hU hab).map (projU K f)) :=
    mapEquivOfInjOn _ _ (projU_injOn_Bk hU hab)
  exact Equivariance.statedClassicalModel_of_mulEquiv
    (e1.trans (e2.trans (MulEquiv.subgroupCongr (Jfun_of_ne hU hab).symm))) hmodel

end Model

end CFSG.RankThree.PartOne.LSTD

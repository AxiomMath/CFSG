module

public import CFSG.Quasithin.Recognition.HSTypeSetting
public import CFSG.Quasithin.EmptyFaithful.S14113bFStar
import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open

variable {G : Type*} [Group G]

theorem fitting_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.ComponentClassification.Fitting.subgroup A).map e.toMonoidHom =
      CFSG.ComponentClassification.Fitting.subgroup B :=
  CFSG.WholeGroup.fittingSubgroup_map_mulEquiv e

theorem generalizedFitting_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.ComponentClassification.GeneralizedFitting.subgroup A).map e.toMonoidHom =
      CFSG.ComponentClassification.GeneralizedFitting.subgroup B := by
  simp only [CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup]
  rw [Subgroup.map_sup, fitting_map_equiv e, CFSG.ComponentClassification.Layer.equiv_invariant e]

theorem quasithinGenFitting_map_mulEquiv (σ : G ≃* G) (Y : Subgroup G) :
    quasithinGenFitting (Y.map σ.toMonoidHom) = (quasithinGenFitting Y).map σ.toMonoidHom := by
  rw [CFSG.Quasithin.quasithinGenFitting_eq_map_subtype,
    CFSG.Quasithin.quasithinGenFitting_eq_map_subtype]
  set e := Y.equivMapOfInjective σ.toMonoidHom σ.injective
  rw [← generalizedFitting_map_equiv e, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem centralizer_map_mulEquiv (σ : G ≃* G) (z : G) :
    Subgroup.centralizer ({σ z} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map σ.toMonoidHom := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨σ.symm x, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp⟩
    apply σ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hx]
  · rintro ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hy
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]

theorem normalizer_map_mulEquiv (σ : G ≃* G) (V : Subgroup G) :
    Subgroup.normalizer ((V.map σ.toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (V : Set G)).map σ.toMonoidHom :=
  (Subgroup.map_normalizer_eq_of_bijective V σ.bijective).symm

@[expose] noncomputable def mapEquivOfEq (σ : G ≃* G) {Y Y' : Subgroup G}
    (hY : Y' = Y.map σ.toMonoidHom) :
    ↥Y ≃* ↥Y' :=
  (Y.equivMapOfInjective σ.toMonoidHom σ.injective).trans (MulEquiv.subgroupCongr hY.symm)

theorem coe_mapEquivOfEq (σ : G ≃* G) {Y Y' : Subgroup G} (hY : Y' = Y.map σ.toMonoidHom)
    (y : ↥Y) : (mapEquivOfEq σ hY y : G) = σ y := rfl

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem map_mulEquiv (h : HSSetting z V) (σ : G ≃* G) :
    HSSetting (σ z) (V.map σ.toMonoidHom) := by
  have hC := centralizer_map_mulEquiv σ z
  have hN := normalizer_map_mulEquiv σ V
  have hQ : quasithinGenFitting (Subgroup.centralizer ({σ z} : Set G)) =
      (quasithinGenFitting (Subgroup.centralizer ({z} : Set G))).map σ.toMonoidHom := by
    rw [hC, quasithinGenFitting_map_mulEquiv]
  have hP : quasithinGenFitting (Subgroup.normalizer ((V.map σ.toMonoidHom : Subgroup G) :
      Set G)) = (quasithinGenFitting (Subgroup.normalizer (V : Set G))).map σ.toMonoidHom := by
    rw [hN, quasithinGenFitting_map_mulEquiv]
  refine
    { orderOf_z := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_z
      elem := ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      card_V := by
        rw [Subgroup.card_map_of_injective σ.injective]
        exact h.card_V
      one := ⟨?_, ?_⟩
      two := ⟨?_, ?_, ?_⟩ }
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul]
    exact congrArg σ (congrArg Subtype.val
      (h.elem.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, h.elem.2 x' hx', map_one]
  · obtain ⟨e⟩ := h.one.fstar
    exact ⟨(mapEquivOfEq σ hQ).symm.trans e⟩
  · obtain ⟨φ, hφ, hker⟩ := h.one.quot
    set e := mapEquivOfEq σ hC
    refine ⟨φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, ?_⟩
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hQ, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨_, hx, ?_⟩
      have := coe_mapEquivOfEq σ hC (e.symm x)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    · rintro ⟨y, hy, hyx⟩
      have h1 : ((e.symm x : ↥(Subgroup.centralizer ({z} : Set G))) : G) = y := by
        apply σ.injective
        rw [← coe_mapEquivOfEq σ hC, MulEquiv.apply_symm_apply]
        exact hyx.symm
      simpa only [MulEquiv.coe_toMonoidHom, h1] using hy
  · rw [hQ]
    exact Subgroup.map_mono h.two.le
  · obtain ⟨e⟩ := h.two.fstar
    exact ⟨(mapEquivOfEq σ hP).symm.trans e⟩
  · obtain ⟨θ, hθ, hker⟩ := h.two.quot
    set e := mapEquivOfEq σ hN
    refine ⟨θ.comp e.symm.toMonoidHom, hθ.comp e.symm.surjective, ?_⟩
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hP, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨_, hx, ?_⟩
      have := coe_mapEquivOfEq σ hN (e.symm x)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    · rintro ⟨y, hy, hyx⟩
      have h1 : ((e.symm x : ↥(Subgroup.normalizer (V : Set G))) : G) = y := by
        apply σ.injective
        rw [← coe_mapEquivOfEq σ hN, MulEquiv.apply_symm_apply]
        exact hyx.symm
      simpa only [MulEquiv.coe_toMonoidHom, h1] using hy

theorem conj (h : HSSetting z V) (g : G) :
    HSSetting (g * z * g⁻¹) (V.map (MulAut.conj g).toMonoidHom) := by
  have := h.map_mulEquiv (MulAut.conj g)
  simpa [MulAut.conj_apply] using this

end HSSetting

theorem hsQ_conj (z g : G) :
    hsQ (g * z * g⁻¹) = (hsQ z).map (MulAut.conj g).toMonoidHom := by
  have h1 := centralizer_map_mulEquiv (MulAut.conj g) z
  simp only [MulAut.conj_apply] at h1
  show quasithinGenFitting (Subgroup.centralizer ({g * z * g⁻¹} : Set G)) = _
  rw [h1, quasithinGenFitting_map_mulEquiv]

theorem mem_map_conj_iff {Y : Subgroup G} {g x : G} :
    x ∈ Y.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Y := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

end CFSG.Quasithin.HSType

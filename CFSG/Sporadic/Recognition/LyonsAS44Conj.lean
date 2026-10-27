module

public import CFSG.Sporadic.Recognition.LyonsAS44ConjPerm
public import CFSG.Sporadic.Recognition.LyonsAS44DeltaGen
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.Frattini
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section Conj

variable {G : Type*} [Group G]

@[expose] def deltaGen (x : G) (T : Subgroup G) : Subgroup G :=
  closure {w : G | w ∈ T ∧ IsConj x w}

theorem isConj_conj_iff {x w c : G} : IsConj x (c * w * c⁻¹) ↔ IsConj x w := by
  constructor
  · intro h
    have : IsConj (c * w * c⁻¹) w := isConj_iff.2 ⟨c⁻¹, by group⟩
    exact h.trans this
  · intro h
    exact h.trans (isConj_iff.2 ⟨c, rfl⟩)

theorem deltaGen_conjSub (x : G) (T : Subgroup G) (c : G) :
    deltaGen x (conjSub c T) = conjSub c (deltaGen x T) := by
  unfold deltaGen
  refine Eq.trans ?_ (MonoidHom.map_closure (MulAut.conj c).toMonoidHom _).symm
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, mem_conjSub_iff]
  constructor
  · rintro ⟨hy, hxy⟩
    refine ⟨c⁻¹ * y * c, ⟨hy, ?_⟩, ?_⟩
    · have : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
      rw [this] at hxy
      exact isConj_conj_iff.1 hxy
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨w, ⟨hw, hxw⟩, rfl⟩
    refine ⟨?_, isConj_conj_iff.2 hxw⟩
    simpa [MulAut.conj_apply, mul_assoc] using hw

theorem deltaIn_conjSub (x : G) (T : Subgroup G) (c : G) :
    deltaIn x (conjSub c T) = (conjSub c) '' (deltaIn x T) := by
  ext B
  rw [mem_deltaIn_iff, Set.mem_image]
  constructor
  · rintro ⟨w, hw, hwT, rfl⟩
    refine ⟨zpowers (c⁻¹ * w * c), mem_deltaIn_iff.2 ⟨c⁻¹ * w * c, ?_, ?_, rfl⟩, ?_⟩
    · have : w = c * (c⁻¹ * w * c) * c⁻¹ := by group
      rw [this] at hw
      exact isConj_conj_iff.1 hw
    · exact mem_conjSub_iff.1 hwT
    · rw [conjSub_zpowers]
      congr 1
      group
  · rintro ⟨B', hB', rfl⟩
    obtain ⟨w, hw, hwT, rfl⟩ := mem_deltaIn_iff.1 hB'
    refine ⟨c * w * c⁻¹, isConj_conj_iff.2 hw, ?_, conjSub_zpowers c w⟩
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hwT

theorem card_conjSub (B : Subgroup G) (c : G) : Nat.card ↥(conjSub c B) = Nat.card ↥B :=
  Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem inf_centralizer_conjSub (R : Subgroup G) (c : G) :
    conjSub c R ⊓ centralizer ((conjSub c R : Subgroup G) : Set G) =
      conjSub c (R ⊓ centralizer (R : Set G)) := by
  ext g
  simp only [Subgroup.mem_inf, mem_conjSub_iff, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hg, hc⟩
    refine ⟨hg, fun h hh => ?_⟩
    have e1 : c⁻¹ * (c * h * c⁻¹) * c = h := by group
    have h3 := hc (c * h * c⁻¹) (by rw [e1]; exact hh)
    have h4 := congrArg (fun z => c⁻¹ * z * c) h3
    have e3 : c⁻¹ * (c * h * c⁻¹ * g) * c = h * (c⁻¹ * g * c) := by group
    have e4 : c⁻¹ * (g * (c * h * c⁻¹)) * c = (c⁻¹ * g * c) * h := by group
    simp only [e3, e4] at h4
    exact h4
  · rintro ⟨hg, hc⟩
    refine ⟨hg, fun h hh => ?_⟩
    have h3 := hc _ hh
    have h4 := congrArg (fun z => c * z * c⁻¹) h3
    have e3 : c * (c⁻¹ * h * c * (c⁻¹ * g * c)) * c⁻¹ = h * g := by group
    have e4 : c * (c⁻¹ * g * c * (c⁻¹ * h * c)) * c⁻¹ = g * h := by group
    simp only [e3, e4] at h4
    exact h4

theorem frattini_map_mulEquiv {R R' : Type*} [Group R] [Group R'] (e : R ≃* R') :
    frattini R' = (frattini R).map e.toMonoidHom := by
  apply le_antisymm
  · have h := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective
    intro y hy
    refine ⟨e.symm y, h hy, by simp⟩
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective e.surjective

theorem map_frattini_conjSub (R : Subgroup G) (c : G) :
    (frattini ↥(conjSub c R)).map (conjSub c R).subtype =
      conjSub c ((frattini ↥R).map R.subtype) := by
  let e : ↥R ≃* ↥(conjSub c R) :=
    Subgroup.equivMapOfInjective R (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  rw [frattini_map_mulEquiv e, Subgroup.map_map]
  have : (conjSub c R).subtype.comp e.toMonoidHom =
      (MulAut.conj c).toMonoidHom.comp R.subtype := by
    ext r
    rfl
  rw [this, ← Subgroup.map_map]
  rfl

@[expose] def Lemma45 (x : G) (T : Subgroup G) : Prop :=
  ∃ R E : Subgroup G, R ≤ T ∧ R ⊔ deltaGen x T = T ∧ Nat.card ↥R = 3 ^ 6 ∧ E ≤ R ∧
    Nat.card ↥E = 9 ∧ R ⊓ centralizer (R : Set G) = E ∧ ⁅R, R⁆ = E ∧
    (frattini ↥R).map R.subtype = E ∧ (∀ r ∈ R, r ^ 3 ∈ E) ∧
    (∀ g ∈ T, orderOf g = 3 → g ∈ R ∨ g ∈ deltaGen x T) ∧
    ∃ u v : G, IsConj x u ∧ IsConj x v ∧ zpowers u ≠ zpowers v ∧ E = closure {u, v} ∧
      deltaIn x R = {zpowers u, zpowers v}

theorem Lemma45.conj {x : G} {T : Subgroup G} (h : Lemma45 x T) (c : G) :
    Lemma45 x (conjSub c T) := by
  obtain ⟨R, E, hRT, hsup, hR, hER, hE, hcent, hcomm, hfr, hcube, hord, u, v, hu, hv, huv, hEuv,
    hδ⟩ := h
  refine ⟨conjSub c R, conjSub c E, Subgroup.map_mono hRT, ?_, by rw [card_conjSub, hR],
    Subgroup.map_mono hER, by rw [card_conjSub, hE], ?_, ?_, ?_, ?_, ?_,
    c * u * c⁻¹, c * v * c⁻¹, isConj_conj_iff.2 hu, isConj_conj_iff.2 hv, ?_, ?_, ?_⟩
  · rw [deltaGen_conjSub, conjSub, conjSub, conjSub, ← Subgroup.map_sup, hsup]
  · rw [inf_centralizer_conjSub, hcent]
  · rw [conjSub, ← Subgroup.map_commutator, hcomm]
    rfl
  · rw [map_frattini_conjSub, hfr]
  · intro r hr
    rw [mem_conjSub_iff] at hr
    rw [mem_conjSub_iff]
    have := hcube _ hr
    have e : c⁻¹ * r ^ 3 * c = (c⁻¹ * r * c) ^ 3 := by
      rw [show c⁻¹ * r * c = c⁻¹ * r * c⁻¹⁻¹ by simp, conj_pow]
      simp
    rw [e]
    exact this
  · intro g hg hg3
    rw [mem_conjSub_iff] at hg
    have hord' : orderOf (c⁻¹ * g * c) = 3 := by
      have := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective g
      simpa [MulAut.conj_apply, hg3] using this
    rw [deltaGen_conjSub, mem_conjSub_iff, mem_conjSub_iff]
    exact hord _ hg hord'
  · intro h
    apply huv
    have h' := congrArg (conjSub c⁻¹) (by simpa [conjSub_zpowers] using h :
      conjSub c (zpowers u) = conjSub c (zpowers v))
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h'
  · rw [hEuv, conjSub, MonoidHom.map_closure, Set.image_pair]
    rfl
  · rw [deltaIn_conjSub, hδ, Set.image_pair, conjSub_zpowers, conjSub_zpowers]

end Conj

end CFSG.Sporadic.Recognition.LyonsSims

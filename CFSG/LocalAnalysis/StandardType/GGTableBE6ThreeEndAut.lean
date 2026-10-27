module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace E6ThreeEnd

section General

variable {R R' : Type*} [Group R] [Group R']

@[expose] def AutEndNode (A : Subgroup (MulAut R)) : Prop :=
  ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
    ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)

theorem congr_apply' (e : R ≃* R') (a : MulAut R) (x : R) :
    MulAut.congr e a (e x) = e (a x) := by
  simp [MulAut.congr]

theorem ggFix_congr (e : R ≃* R') (a : MulAut R) :
    ggFix (MulAut.congr e a) = (ggFix a).map e.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [mem_ggFix, congr_apply']
  constructor
  · intro h
    exact ⟨x, mem_ggFix.mpr (e.injective h), rfl⟩
  · rintro ⟨x', hx', hxx'⟩
    have hx : x' = x := e.injective hxx'
    subst hx
    rw [mem_ggFix.mp hx']

theorem ggFix_conj (t : R) :
    ggFix (MulAut.conj t) = Subgroup.centralizer ({t} : Set R) := by
  ext x
  rw [mem_ggFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  · intro h
    rw [← h]
    group

theorem congr_conj (e : R ≃* R') (t : R) :
    MulAut.congr e (MulAut.conj t) = MulAut.conj (e t) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [congr_apply', MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem AutEndNode.map (e : R ≃* R') {A : Subgroup (MulAut R)} (h : AutEndNode A) :
    AutEndNode (A.map (MulAut.congr e).toMonoidHom) := by
  obtain ⟨a, haA, ha1, hcomp, hcent⟩ := h
  have hF : ggFix (MulAut.congr e a) = (ggFix a).map e.toMonoidHom := ggFix_congr e a
  have hL : LargeEvenLayer (ggFix (MulAut.congr e a)) =
      (LargeEvenLayer (ggFix a)).map e.toMonoidHom := by
    rw [hF, largeEvenLayer_map_of_injective _ e.injective]
  refine ⟨MulAut.congr e a, ⟨a, haA, rfl⟩, fun h1 => ha1 ?_, ?_, ?_⟩
  · apply (MulAut.congr e).injective
    rw [h1, map_one]
  · rw [hL, hF]
    exact isComponentOf_map_of_injective _ e.injective hcomp
  · rintro _ ⟨a', ha', rfl⟩
    rw [hL]
    constructor
    · intro hj
      have h2 : ∀ j ∈ LargeEvenLayer (ggFix a), a' j = j := by
        intro j hj'
        apply e.injective
        rw [← congr_apply']
        exact hj (e j) ⟨j, hj', rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hcent a' ha').mp h2)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_zpow, hk]
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hk' : a ^ k = a' := (MulAut.congr e).injective (by rw [map_zpow]; exact hk)
      have h2 := (hcent a' ha').mpr (Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩)
      rintro _ ⟨j, hj, rfl⟩
      change MulAut.congr e a' (e j) = e j
      rw [congr_apply', h2 j hj]

theorem map_congr_symm_map_congr (e : R ≃* R') (A : Subgroup (MulAut R)) :
    (A.map (MulAut.congr e).toMonoidHom).map (MulAut.congr e.symm).toMonoidHom = A := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A
  ext φ x
  simp [MulAut.congr]

end General

theorem ggEndNodeAut_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : TableBUD.GGEndNodeAut p r R' I') :
    TableBUD.GGEndNodeAut p r R I := by
  intro A hA hAI hr h3
  set A' := A.map (MulAut.congr e).toMonoidHom with hA'
  have hcard : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hA'ab : IsElemAbelian p A' := TableB.isElemAbelian_map hA _
  have h1 : AutEndNode A' := h A' hA'ab (by
    rintro _ ⟨φ, hφ, rfl⟩
    exact hI φ (hAI φ hφ)) (hcard ▸ hr) (hcard ▸ h3)
  have h2 := h1.map e.symm
  rw [hA', map_congr_symm_map_congr] at h2
  exact h2

end E6ThreeEnd

end CFSG.StandardType

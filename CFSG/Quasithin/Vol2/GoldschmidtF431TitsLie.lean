module

public import CFSG.Quasithin.Recognition.F4Local

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open

universe u v

section Defs

variable {Mb : Type u} [Group Mb]

@[expose] def InvStep (T M1 M2 : Subgroup Mb) (i j : Mb) : Prop :=
  i ∈ T ∧ j ∈ T ∧ ∃ c : Mb, (c ∈ M1 ∨ c ∈ M2) ∧ j = c * i * c⁻¹

structure F431LieI (T M1 M2 : Subgroup Mb) (z t : Mb) : Prop where
  sylow : IsSylowTwoOf T ⊤
  T_le₁ : T ≤ M1
  T_le₂ : T ≤ M2
  z_mem : z ∈ T
  t_mem : t ∈ T
  hz : orderOf z = 2
  ht : orderOf t = 2
  not_conj : ¬ IsConj z t
  classes : ∀ x : Mb, orderOf x = 2 → IsConj z x ∨ IsConj t x
  cent_z : Subgroup.centralizer ({z} : Set Mb) = M1
  cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2
  center_T : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ M1 ⊓ M2, m * z * m⁻¹ = w
  inv_chain : ∀ i ∈ T, orderOf i = 2 →
    Relation.ReflTransGen (InvStep T M1 M2) z i ∨ Relation.ReflTransGen (InvStep T M1 M2) t i

end Defs

section Fusion

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M]
  {T M1 M2 : Subgroup Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem InvStep.isConj_amalgamMap (C : F431Comp M1 M2 b1 b2) (hT1 : T ≤ M1) (hT2 : T ≤ M2)
    {i j : Mb} (h : InvStep T M1 M2 i j) :
    IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  obtain ⟨hi, hj, c, hc, rfl⟩ := h
  rcases hc with hc | hc
  · have hi1 : i ∈ M1 := hT1 hi
    have hj1 : c * i * c⁻¹ ∈ M1 := hT1 hj
    have e : (⟨c * i * c⁻¹, hj1⟩ : M1) = ⟨c, hc⟩ * ⟨i, hi1⟩ * ⟨c, hc⟩⁻¹ := rfl
    rw [amalgamMap_of_mem₁ b1 b2 hi1, amalgamMap_of_mem₁ b1 b2 hj1, e, map_mul, map_mul,
      map_inv]
    exact isConj_iff.mpr ⟨b1 ⟨c, hc⟩, rfl⟩
  · have hi2 : i ∈ M2 := hT2 hi
    have hj2 : c * i * c⁻¹ ∈ M2 := hT2 hj
    have e : (⟨c * i * c⁻¹, hj2⟩ : M2) = ⟨c, hc⟩ * ⟨i, hi2⟩ * ⟨c, hc⟩⁻¹ := rfl
    rw [amalgamMap_of_mem₂ b1 b2 C.agree hi2, amalgamMap_of_mem₂ b1 b2 C.agree hj2, e, map_mul,
      map_mul, map_inv]
    exact isConj_iff.mpr ⟨b2 ⟨c, hc⟩, rfl⟩

theorem InvStep.isConj {i j : Mb} (h : InvStep T M1 M2 i j) : IsConj i j := by
  obtain ⟨-, -, c, -, rfl⟩ := h
  exact isConj_iff.mpr ⟨c, rfl⟩

theorem reflTransGen_isConj_amalgamMap (C : F431Comp M1 M2 b1 b2) (hT1 : T ≤ M1) (hT2 : T ≤ M2)
    {i j : Mb} (h : Relation.ReflTransGen (InvStep T M1 M2) i j) :
    IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  induction h with
  | refl => exact IsConj.refl _
  | tail _ hs ih => exact ih.trans (hs.isConj_amalgamMap C hT1 hT2)

theorem reflTransGen_isConj {i j : Mb} (h : Relation.ReflTransGen (InvStep T M1 M2) i j) :
    IsConj i j := by
  induction h with
  | refl => exact IsConj.refl _
  | tail _ hs ih => exact ih.trans hs.isConj

theorem F431LieI.fusion_forward (D : F431LieI T M1 M2 z t) (C : F431Comp M1 M2 b1 b2) {i j : Mb}
    (hi : i ∈ T) (hj : j ∈ T) (hio : orderOf i = 2) (hjo : orderOf j = 2) (hij : IsConj i j) :
    IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  have key : ∀ {a b : Mb}, Relation.ReflTransGen (InvStep T M1 M2) a b →
      IsConj (amalgamMap b1 b2 a) (amalgamMap b1 b2 b) := fun h =>
    reflTransGen_isConj_amalgamMap C D.T_le₁ D.T_le₂ h
  rcases D.inv_chain i hi hio with hzi | hti <;> rcases D.inv_chain j hj hjo with hzj | htj
  · exact (key hzi).symm.trans (key hzj)
  · exfalso
    exact D.not_conj ((reflTransGen_isConj hzi).trans (hij.trans (reflTransGen_isConj htj).symm))
  · exfalso
    exact D.not_conj ((reflTransGen_isConj hzj).trans (hij.symm.trans
      (reflTransGen_isConj hti).symm))
  · exact (key hti).symm.trans (key htj)

theorem F431LieI.lemma_F435 (D : F431LieI T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
    (hnc : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t)) {i j : Mb} (hi : i ∈ T)
    (hj : j ∈ T) (hio : orderOf i = 2) (hjo : orderOf j = 2) :
    IsConj i j ↔ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  refine ⟨D.fusion_forward C hi hj hio hjo, fun h => ?_⟩
  rcases D.classes i hio with hzi | hti <;> rcases D.classes j hjo with hzj | htj
  · exact hzi.symm.trans hzj
  · exfalso
    apply hnc
    exact ((D.fusion_forward C D.z_mem hi D.hz hio hzi).trans h).trans
      (D.fusion_forward C hj D.t_mem hjo D.ht htj.symm)
  · exfalso
    apply hnc
    exact ((D.fusion_forward C D.z_mem hj D.hz hjo hzj).trans h.symm).trans
      (D.fusion_forward C hi D.t_mem hio D.ht hti.symm)
  · exact hti.symm.trans htj

end Fusion

end CFSG.Quasithin

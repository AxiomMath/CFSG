module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.TwoLocalAt

open scoped commutatorElement

private lemma commutatorElement_mul_center_left {G : Type*} [Group G] {x y z : G}
    (hz : z ∈ Subgroup.center G) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hc : ⁅z, y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz y).symm
  rw [hc, mul_one]
  group

private lemma commutatorElement_mul_center_right {G : Type*} [Group G] {x y w : G}
    (hw : w ∈ Subgroup.center G) : ⁅x, y * w⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hc : ⁅x, w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hw x)
  rw [hc, mul_one]
  group

private lemma commutatorElement_mul_center {G : Type*} [Group G] {x y z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) :
    ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_center_left hz, commutatorElement_mul_center_right hw]

private theorem eq_of_central_displacement_hom_aux {G H : Type*} [Group G] [Group H]
    (f g : G →* H) (h : ∀ x, (g x)⁻¹ * f x ∈ Subgroup.center H)
    (hperf : commutator G = ⊤) : f = g := by
  have hfg : ∀ x, f x = g x * ((g x)⁻¹ * f x) := fun x => by group
  have hle : commutator G ≤ f.eqLocus g := by
    rw [commutator_def G, Subgroup.commutator_le]
    intro a _ b _
    show f ⁅a, b⁆ = g ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement, hfg a, hfg b]
    exact commutatorElement_mul_center (h a) (h b)
  rw [hperf] at hle
  ext x
  exact hle (Subgroup.mem_top x)

private lemma ker_stable {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (a : MulAut L') {z : L'} (hz : z ∈ ψ.ker) :
    a z ∈ ψ.ker := by
  have hzc : z ∈ Subgroup.center L' := hker hz
  have hazc : a z ∈ Subgroup.center L' := MulEquivClass.apply_mem_center a hzc
  have hcent : ψ (a z) ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff] at hazc ⊢
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    rw [← map_mul, ← map_mul, hazc l]
  show ψ (a z) = 1
  simpa [hZ] using hcent

private noncomputable def inducedHom {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (a : MulAut L') : R →* R :=
  MonoidHom.liftOfSurjective ψ hψ
    ⟨ψ.comp a.toMonoidHom, fun z hz => ker_stable ψ hψ hker hZ a hz⟩

private lemma inducedHom_apply {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (a : MulAut L') (l : L') :
    inducedHom ψ hψ hker hZ a (ψ l) = ψ (a l) := by
  simp [inducedHom]

private lemma inducedHom_leftInverse {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (a : MulAut L') (r : R) :
    inducedHom ψ hψ hker hZ a⁻¹ (inducedHom ψ hψ hker hZ a r) = r := by
  obtain ⟨l, rfl⟩ := hψ r
  rw [inducedHom_apply, inducedHom_apply]
  simp

private lemma inducedHom_rightInverse {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (a : MulAut L') (r : R) :
    inducedHom ψ hψ hker hZ a (inducedHom ψ hψ hker hZ a⁻¹ r) = r := by
  obtain ⟨l, rfl⟩ := hψ r
  rw [inducedHom_apply, inducedHom_apply]
  simp

private lemma inducedHom_bijective {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (a : MulAut L') :
    Function.Bijective (inducedHom ψ hψ hker hZ a) := by
  constructor
  · intro x y hxy
    calc
      x = inducedHom ψ hψ hker hZ a⁻¹ (inducedHom ψ hψ hker hZ a x) :=
        (inducedHom_leftInverse ψ hψ hker hZ a x).symm
      _ = inducedHom ψ hψ hker hZ a⁻¹ (inducedHom ψ hψ hker hZ a y) := by rw [hxy]
      _ = y := inducedHom_leftInverse ψ hψ hker hZ a y
  · intro y
    exact ⟨inducedHom ψ hψ hker hZ a⁻¹ y,
      inducedHom_rightInverse ψ hψ hker hZ a y⟩

private noncomputable def inducedAut {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (a : MulAut L') : MulAut R :=
  MulEquiv.ofBijective (inducedHom ψ hψ hker hZ a) (inducedHom_bijective ψ hψ hker hZ a)

private lemma inducedAut_apply {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (a : MulAut L') (l : L') :
    inducedAut ψ hψ hker hZ a (ψ l) = ψ (a l) := by
  rw [inducedAut, MulEquiv.ofBijective_apply, inducedHom_apply]

private noncomputable def inducedAutHom {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) : MulAut L' →* MulAut R :=
  MonoidHom.mk' (inducedAut ψ hψ hker hZ) (by
    intro a b
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    simp [inducedAut_apply, MulAut.mul_apply])

private lemma inducedAutHom_apply {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (a : MulAut L') (l : L') :
    inducedAutHom ψ hψ hker hZ a (ψ l) = ψ (a l) := by
  simp [inducedAutHom, inducedAut_apply]

theorem exists_inducedAut {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (hperf : commutator L' = ⊤) :
    ∃ Θ : MulAut L' →* MulAut R, Function.Injective Θ ∧
      ∀ (a : MulAut L') (l : L'), Θ a (ψ l) = ψ (a l) := by
  refine ⟨inducedAutHom ψ hψ hker hZ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    have hdis : ∀ x, ((MonoidHom.id L') x)⁻¹ * a.toMonoidHom x ∈ Subgroup.center L' := by
      intro x
      have hx : ψ (x⁻¹ * a x) = 1 := by
        have h' : ψ (a x) = ψ x := by
          have h := congrArg (fun f : MulAut R => f (ψ x)) ha
          simpa [inducedAutHom_apply] using h
        simp [h']
      exact hker (show x⁻¹ * a x ∈ ψ.ker from hx)
    have heq : a.toMonoidHom = MonoidHom.id L' :=
      eq_of_central_displacement_hom_aux a.toMonoidHom (MonoidHom.id L') hdis hperf
    ext x
    simpa using congrArg (fun f : L' →* L' => f x) heq
  · intro a l
    exact inducedAutHom_apply ψ hψ hker hZ a l

end CFSG.StandardType.TwoLocalAt

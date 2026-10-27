module

public import CFSG.LocalAnalysis.StandardType.PhanEDMCoxeterW0
public import CFSG.LocalAnalysis.StandardType.PhanEGatePair

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Gate

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} {w₀ : W} {t : C → C}

structure IsFlipInvolution (cs : CoxeterSystem M W) (δ : C → C → W) (w₀ : W) (t : C → C) :
    Prop where
  invol : ∀ x, t (t x) = x
  dist : ∀ x y, δ (t x) (t y) = w₀ * δ x y * w₀

@[expose] def flipType (cs : CoxeterSystem M W) (w₀ : W) (J : Set ι) : Set ι :=
  {k | ∃ j ∈ J, w₀ * cs.simple j * w₀ = cs.simple k}

@[expose] def flipCore (cs : CoxeterSystem M W) (δ : C → C → W) (t : C → C) (J : Set ι) (a : C) :
    Set C :=
  projSet cs δ J a (t '' residue cs δ J a)

variable {J : Set ι} {a x x' : C}

private theorem p9uGF_simple_conj_mem_flipType {i : ι} (hi : i ∈ J)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀) :
    ∃ k ∈ flipType cs w₀ J, w₀ * cs.simple i * w₀ = cs.simple k := by
  obtain ⟨k, hk⟩ := CoxeterSystem.exists_simple_conj_w0 cs w₀ hw i
  exact ⟨k, ⟨i, hi, hk⟩, hk⟩

private theorem p9uGF_image_mem (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) {y : C} (hy : y ∈ residue cs δ J a) :
    t y ∈ residue cs δ (flipType cs w₀ J) (t a) := by
  induction hy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨i, hi, hδi⟩ := hbc
    obtain ⟨k, hk, hk'⟩ := p9uGF_simple_conj_mem_flipType (J := J) (w₀ := w₀) hi hw
    exact Relation.ReflTransGen.tail ih ⟨k, hk, by rw [ht.dist, hδi, hk']⟩

private theorem p9uGF_image_mem' (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) {z : C}
    (hz : z ∈ residue cs δ (flipType cs w₀ J) (t a)) : t z ∈ residue cs δ J a := by
  have hw2 : w₀ * w₀ = 1 := CoxeterSystem.w0_mul_self cs w₀ hw
  induction hz with
  | refl =>
    rw [ht.invol a]
    exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨k, hk, hδk⟩ := hbc
    obtain ⟨j, hj, hj'⟩ := hk
    refine Relation.ReflTransGen.tail ih ⟨j, hj, ?_⟩
    rw [ht.dist, hδk, ← hj']
    calc w₀ * (w₀ * cs.simple j * w₀) * w₀ = (w₀ * w₀) * cs.simple j * (w₀ * w₀) := by group
      _ = cs.simple j := by rw [hw2]; group

theorem image_residue_flip (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (J : Set ι) (a : C) :
    t '' residue cs δ J a = residue cs δ (flipType cs w₀ J) (t a) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact p9uGF_image_mem (J := J) (a := a) hw ht hy
  · intro hz
    exact ⟨t z, p9uGF_image_mem' (J := J) (a := a) hw ht hz, ht.invol z⟩

theorem t_resProj_of_image (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) {J K : Set ι} {a b : C}
    (h : t '' residue cs δ J a = residue cs δ K b) (y : C) :
    t (resProj cs δ J a y) = resProj cs δ K b (t y) := by
  have hproj := isProjection_resProj hB J a y
  have hproj' : IsProjection cs δ (t '' residue cs δ J a) (t y)
      (t (resProj cs δ J a y)) := by
    refine ⟨⟨resProj cs δ J a y, hproj.1, rfl⟩, ?_⟩
    rintro q' ⟨q, hq, rfl⟩ hne
    have hqp : q ≠ resProj cs δ J a y := fun h' => hne (by rw [h'])
    have hlt := hproj.2 q hq hqp
    rw [ht.dist, ht.dist]
    rw [CoxeterSystem.length_w0_conj cs w₀ hw (δ y (resProj cs δ J a y)),
      CoxeterSystem.length_w0_conj cs w₀ hw (δ y q)]
    exact hlt
  rw [h] at hproj'
  exact (resProj_eq hB hproj').symm

theorem t_resProj (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (J : Set ι) (a y : C) :
    t (resProj cs δ J a y) = resProj cs δ (flipType cs w₀ J) (t a) (t y) :=
  t_resProj_of_image hB hw ht (image_residue_flip hw ht J a) y

theorem image_residue_flip_flip (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (J : Set ι) (a : C) :
    t '' residue cs δ (flipType cs w₀ J) (t a) = residue cs δ J a := by
  ext z
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact p9uGF_image_mem' (J := J) (a := a) hw ht hz
  · intro hz
    exact ⟨t z, p9uGF_image_mem (J := J) (a := a) hw ht hz, ht.invol z⟩

theorem t_flipCore (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (J : Set ι) (a : C) :
    t '' flipCore cs δ t J a =
      projSet cs δ (flipType cs w₀ J) (t a) (residue cs δ J a) := by
  unfold flipCore projSet
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr ?_
  intro y _
  show t (resProj cs δ J a (t y)) = resProj cs δ (flipType cs w₀ J) (t a) y
  rw [t_resProj hB hw ht J a (t y), ht.invol y]

end CFSG.ClassicalInvolution.Phan.PhanE.Gate

end

module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.RingTheory.SimpleModule.Basic

public section

namespace CFSG.Quasithin.SqModel

open scoped Matrix

variable {F : Type} [Field F] {d : ℕ}

def addClosureSubring (s : Set (Matrix (Fin d) (Fin d) F))
    (h1 : (1 : Matrix (Fin d) (Fin d) F) ∈ s) (hmul : ∀ A ∈ s, ∀ B ∈ s, A * B ∈ s) :
    Subring (Matrix (Fin d) (Fin d) F) where
  carrier := AddSubgroup.closure s
  zero_mem' := zero_mem _
  one_mem' := AddSubgroup.subset_closure h1
  add_mem' := add_mem
  neg_mem' := neg_mem
  mul_mem' {a b} ha hb := by
    induction hb using AddSubgroup.closure_induction with
    | mem y hy =>
      induction ha using AddSubgroup.closure_induction with
      | mem x hx => exact AddSubgroup.subset_closure (hmul x hx y hy)
      | zero => simp
      | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
      | neg x _ hx => rw [neg_mul]; exact neg_mem hx
    | zero => simp
    | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy

theorem closure_eq_top_of_irr_of_comm (hd : 0 < d) {s : Set (Matrix (Fin d) (Fin d) F)}
    (h1 : (1 : Matrix (Fin d) (Fin d) F) ∈ s) (hmul : ∀ A ∈ s, ∀ B ∈ s, A * B ∈ s)
    (hirr : ∀ W : AddSubgroup (Fin d → F), (∀ A ∈ s, ∀ w ∈ W, A.mulVec w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcomm : ∀ φ : (Fin d → F) →+ (Fin d → F),
      (∀ A ∈ s, ∀ w, φ (A.mulVec w) = A.mulVec (φ w)) → ∃ c : F, ∀ w, φ w = c • w) :
    AddSubgroup.closure s = ⊤ := by
  classical
  let R := addClosureSubring s h1 hmul
  have hRs : ∀ A (hA : A ∈ s) (w : Fin d → F),
      (⟨A, AddSubgroup.subset_closure hA⟩ : R) • w = A.mulVec w := fun A hA w => rfl
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (Fin d → F) := inferInstance
  have : IsSimpleModule R (Fin d → F) := by
    rw [isSimpleModule_iff]
    refine ⟨fun N => ?_⟩
    have hN : ∀ A ∈ s, ∀ w ∈ N.toAddSubgroup, A.mulVec w ∈ N.toAddSubgroup := by
      intro A hA w hw
      have := N.smul_mem (⟨A, AddSubgroup.subset_closure hA⟩ : R) hw
      rwa [hRs A hA] at this
    rcases hirr _ hN with h | h
    · left
      ext w
      have := congrArg (fun W : AddSubgroup (Fin d → F) => w ∈ W) h
      simpa using this
    · right
      ext w
      have := congrArg (fun W : AddSubgroup (Fin d → F) => w ∈ W) h
      simpa using this
  have hscal : ∀ φ : Module.End R (Fin d → F), ∃ c : F, ∀ w, φ w = c • w := by
    intro φ
    refine hcomm φ.toAddMonoidHom fun A hA w => ?_
    have := φ.map_smul (⟨A, AddSubgroup.subset_closure hA⟩ : R) w
    rwa [hRs A hA, hRs A hA] at this
  have hdens : ∀ A : Matrix (Fin d) (Fin d) F, A ∈ AddSubgroup.closure s := by
    intro A
    let f : Module.End (Module.End R (Fin d → F)) (Fin d → F) :=
      { toFun := fun w => A.mulVec w
        map_add' := fun x y => Matrix.mulVec_add A x y
        map_smul' := fun φ w => by
          obtain ⟨c, hc⟩ := hscal φ
          have h1 : (φ • w) = c • w := hc w
          show A.mulVec (φ • w) = φ • A.mulVec w
          rw [h1]
          have h2 : φ • A.mulVec w = c • A.mulVec w := hc _
          rw [h2, Matrix.mulVec_smul] }
    obtain ⟨r, hr⟩ := jacobson_density f (Finset.univ.image fun i : Fin d => (Pi.single i 1 :
      Fin d → F))
    have hcol : A = (r : Matrix (Fin d) (Fin d) F) := by
      ext i j
      have := hr (Pi.single j 1) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      have h2 : A.mulVec (Pi.single j 1) = (r : Matrix (Fin d) (Fin d) F).mulVec (Pi.single j 1) :=
        this
      have h3 := congrFun h2 i
      simpa [Matrix.mulVec_single_one] using h3
    rw [hcol]
    exact r.2
  exact top_unique fun A _ => hdens A

end CFSG.Quasithin.SqModel

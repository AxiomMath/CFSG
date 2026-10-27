module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Geometry.ChamberSystem

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

section Restrict

variable {I C : Type}

@[expose] def _root_.CFSG.Monster.B.Geometry.ChamberSystem.restrict (X : ChamberSystem I C)
    (A : Set C) : ChamberSystem I A where
  adj i y z := X.adj i y.1 z.1
  equivalence i := ⟨fun y => X.adj_refl i y.1, fun h => X.adj_symm h,
    fun h h' => X.adj_trans h h'⟩

end Restrict

section Prod

variable {I J C D : Type}

@[expose] def _root_.CFSG.Monster.B.Geometry.ChamberSystem.prod (X : ChamberSystem I C)
    (Y : ChamberSystem J D) : ChamberSystem (I ⊕ J) (C × D) where
  adj i x y := match i with
    | .inl i => X.adj i x.1 y.1 ∧ x.2 = y.2
    | .inr j => x.1 = y.1 ∧ Y.adj j x.2 y.2
  equivalence i := by
    cases i with
    | inl i =>
      exact ⟨fun x => ⟨X.adj_refl i x.1, rfl⟩, fun h => ⟨X.adj_symm h.1, h.2.symm⟩,
        fun h h' => ⟨X.adj_trans h.1 h'.1, h.2.trans h'.2⟩⟩
    | inr j =>
      exact ⟨fun x => ⟨rfl, Y.adj_refl j x.2⟩, fun h => ⟨h.1.symm, Y.adj_symm h.2⟩,
        fun h h' => ⟨h.1.trans h'.1, Y.adj_trans h.2 h'.2⟩⟩

end Prod

structure ChamberIso {I I' C D : Type} (X : ChamberSystem I C) (Y : ChamberSystem I' D) where
  e : I ≃ I'
  Φ : C ≃ D
  adj_iff : ∀ (i : I) (x y : C), X.adj i x y ↔ Y.adj (e i) (Φ x) (Φ y)

namespace ChamberIso

variable {I I' C D : Type} {X : ChamberSystem I C} {Y : ChamberSystem I' D}

def symm (h : ChamberIso X Y) : ChamberIso Y X where
  e := h.e.symm
  Φ := h.Φ.symm
  adj_iff := by
    intro i x y
    have h' := h.adj_iff (h.e.symm i) (h.Φ.symm x) (h.Φ.symm y)
    simpa using h'.symm

private def pls_relabel (h : ChamberIso X Y) (γ : List (I × C)) : List (I' × D) :=
  γ.map fun p => (h.e p.1, h.Φ p.2)

@[simp] private theorem pls_relabel_nil (h : ChamberIso X Y) :
    pls_relabel h ([] : List (I × C)) = [] := rfl

private theorem pls_relabel_append (h : ChamberIso X Y) (γ η : List (I × C)) :
    pls_relabel h (γ ++ η) = pls_relabel h γ ++ pls_relabel h η :=
  List.map_append ..

private theorem pls_galleryEnd_relabel (h : ChamberIso X Y) (x : C) (γ : List (I × C)) :
    galleryEnd (h.Φ x) (pls_relabel h γ) = h.Φ (galleryEnd x γ) := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih =>
    show galleryEnd (h.Φ p.2) (pls_relabel h γ) = h.Φ (galleryEnd p.2 γ)
    exact ih p.2

private theorem pls_galleryType_relabel (h : ChamberIso X Y) (γ : List (I × C)) :
    galleryType (pls_relabel h γ) = (galleryType γ).map h.e := by
  induction γ with
  | nil => rfl
  | cons p γ ih =>
    change h.e p.1 :: galleryType (pls_relabel h γ) = h.e p.1 :: (galleryType γ).map h.e
    rw [ih]

private theorem pls_isGallery_relabel (h : ChamberIso X Y) {x : C} {γ : List (I × C)}
    (hγ : X.IsGallery x γ) : Y.IsGallery (h.Φ x) (pls_relabel h γ) := by
  induction γ generalizing x with
  | nil => trivial
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    exact ⟨(h.adj_iff p.1 x p.2).mp h1, ih h2⟩

private theorem pls_elemMove_relabel (h : ChamberIso X Y) {x : C} {γ γ' : List (I × C)}
    (hm : X.ElemMove x γ γ') :
    Y.ElemMove (h.Φ x) (pls_relabel h γ) (pls_relabel h γ') := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := hm
  simp only [pls_relabel_append]
  refine ElemMove.mk (pls_relabel h γ₁) (pls_relabel h η) (pls_relabel h η')
    (pls_relabel h γ₂) (h.e '' J) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [h.e.injective.encard_image J]
    exact hJ
  · rw [pls_galleryEnd_relabel]
    exact pls_isGallery_relabel h hη
  · rw [pls_galleryEnd_relabel]
    exact pls_isGallery_relabel h hη'
  · intro i hi
    rw [pls_galleryType_relabel, List.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact ⟨j, hηJ j hj, rfl⟩
  · intro i hi
    rw [pls_galleryType_relabel, List.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact ⟨j, hη'J j hj, rfl⟩
  · rw [pls_galleryEnd_relabel, pls_galleryEnd_relabel, pls_galleryEnd_relabel]
    exact congrArg h.Φ hend

private theorem pls_twoHomotopic_relabel (h : ChamberIso X Y) {x : C} {γ γ' : List (I × C)}
    (hm : X.TwoHomotopic x γ γ') :
    Y.TwoHomotopic (h.Φ x) (pls_relabel h γ) (pls_relabel h γ') := by
  induction hm with
  | rel a b hab => exact TwoHomotopic.of_elemMove (pls_elemMove_relabel h hab)
  | refl => exact TwoHomotopic.refl _
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ih ih' => exact ih.trans ih'

private theorem pls_relabel_symm_relabel (h : ChamberIso X Y) (γ : List (I' × D)) :
    pls_relabel h (pls_relabel h.symm γ) = γ := by
  induction γ with
  | nil => rfl
  | cons p γ ih =>
    change (h.e ((h.symm).e p.1), h.Φ ((h.symm).Φ p.2)) ::
        pls_relabel h (pls_relabel h.symm γ) = p :: γ
    rw [show (h.symm).e = h.e.symm from rfl, show (h.symm).Φ = h.Φ.symm from rfl,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, ih]

private theorem pls_connected (h : ChamberIso X Y) (hX : X.Connected) : Y.Connected := by
  intro u v
  obtain ⟨γ, hγ, hend⟩ := hX (h.Φ.symm u) (h.Φ.symm v)
  refine ⟨pls_relabel h γ, ?_, ?_⟩
  · simpa using pls_isGallery_relabel h hγ
  · have h4 : galleryEnd (h.Φ (h.Φ.symm u)) (pls_relabel h γ) = h.Φ (h.Φ.symm v) := by
      rw [pls_galleryEnd_relabel, hend]
    simpa using h4

private theorem pls_simplyTwoConnected (h : ChamberIso X Y) (hX : X.SimplyTwoConnected) :
    Y.SimplyTwoConnected := by
  intro u γ hγ hend
  have h1 : X.IsGallery (h.Φ.symm u) (pls_relabel h.symm γ) :=
    pls_isGallery_relabel h.symm hγ
  have h2 : galleryEnd (h.Φ.symm u) (pls_relabel h.symm γ) = h.Φ.symm u := by
    have h2' := pls_galleryEnd_relabel h.symm u γ
    rw [hend] at h2'
    exact h2'
  have h3 : Y.TwoHomotopic (h.Φ (h.Φ.symm u)) (pls_relabel h (pls_relabel h.symm γ)) [] :=
    pls_twoHomotopic_relabel h (hX _ _ h1 h2)
  rw [pls_relabel_symm_relabel] at h3
  simpa using h3

theorem connected_iff (h : ChamberIso X Y) : X.Connected ↔ Y.Connected :=
  ⟨pls_connected h, pls_connected h.symm⟩

theorem simplyTwoConnected_iff (h : ChamberIso X Y) :
    X.SimplyTwoConnected ↔ Y.SimplyTwoConnected :=
  ⟨pls_simplyTwoConnected h, pls_simplyTwoConnected h.symm⟩

end ChamberIso

end CFSG.ClassicalInvolution.Phan.PhanE

end

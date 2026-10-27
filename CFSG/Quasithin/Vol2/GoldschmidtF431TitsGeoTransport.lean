module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoPtLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLnLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Iso

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Quasithin.H13.F431.F45

universe u u' v v'

variable {X : Type u} {X' : Type u'} [Group X] [Group X'] {V : Type v} {V' : Type v'}
  [MulAction X V] [MulAction X' V'] {Γ : SimpleGraph V} {Γ' : SimpleGraph V'}

structure EqData (Φ : X →* X') (e : V' ≃ V) (Γ : SimpleGraph V) (Γ' : SimpleGraph V') : Prop where
  surj : Function.Surjective Φ
  smul : ∀ (y : X) (v : V'), e (Φ y • v) = y • e v
  adj : ∀ u v, Γ'.Adj u v ↔ Γ.Adj (e u) (e v)

namespace EqData

variable {Φ : X →* X'} {e : V' ≃ V} (E : EqData Φ e Γ Γ')

include E

theorem smul_eq_iff (y : X) (v w : V') : Φ y • v = w ↔ y • e v = e w := by
  rw [← E.smul y v]
  exact e.injective.eq_iff.symm

theorem dist (u v : V') : Γ'.dist u v = Γ.dist (e u) (e v) :=
  (iso_dist (G := Γ') (H := Γ) ⟨e, fun {a b} => (E.adj a b).symm⟩ u v).symm

theorem ncard_neighborSet (a : V') :
    (Γ'.neighborSet a).ncard = (Γ.neighborSet (e a)).ncard := by
  have h : Γ.neighborSet (e a) = e '' Γ'.neighborSet a :=
    neighborSet_iso (G := Γ') (H := Γ) ⟨e, fun {a b} => (E.adj a b).symm⟩ a
  rw [h, Set.ncard_image_of_injective _ e.injective]

end EqData

namespace PtLoc

variable {Φ : X →* X'} {e : V' ≃ V} {a b₀ w₀ : V'}

theorem transport (E : EqData Φ e Γ Γ') (L : PtLoc X Γ (e a) (e b₀) (e w₀)) :
    PtLoc X' Γ' a b₀ w₀ where
  dist := by rw [E.dist]; exact L.dist
  adj := (E.adj _ _).2 L.adj
  orb b hb := by
    obtain ⟨g, h1, h2⟩ := L.orb (e b) (by rw [← E.dist]; exact hb)
    exact ⟨Φ g, (E.smul_eq_iff g a a).2 h1, (E.smul_eq_iff g b₀ b).2 h2⟩
  trans u hu := by
    obtain ⟨k, h1, h2, h3⟩ := L.trans (e u) ((E.adj _ _).1 hu)
    exact ⟨Φ k, (E.smul_eq_iff k a a).2 h1, (E.smul_eq_iff k b₀ b₀).2 h2,
      (E.smul_eq_iff k w₀ u).2 h3⟩
  moves u hu := by
    obtain ⟨k, h1, h2, h3, w, hw, hkw⟩ := L.moves (e u) ((E.adj _ _).1 hu)
    refine ⟨Φ k, (E.smul_eq_iff k a a).2 h1, (E.smul_eq_iff k b₀ b₀).2 h2,
      (E.smul_eq_iff k u u).2 h3, e.symm w, (E.adj _ _).2 (by simpa using hw), fun hcon => hkw ?_⟩
    have := (E.smul_eq_iff k (e.symm w) (e.symm w)).1 hcon
    simpa using this
  exact := by
    obtain ⟨k, h1, h2, h3, y₀, hy₀, hky, hun⟩ := L.exact
    refine ⟨Φ k, (E.smul_eq_iff k a a).2 h1, (E.smul_eq_iff k b₀ b₀).2 h2,
      (E.smul_eq_iff k w₀ w₀).2 h3, e.symm y₀, (E.adj _ _).2 (by simpa using hy₀),
      (E.smul_eq_iff k _ _).2 (by simpa using hky), fun y hy hfy => ?_⟩
    have := hun (e y) ((E.adj _ _).1 hy) ((E.smul_eq_iff k y y).1 hfy)
    rw [← this]
    simp

end PtLoc

namespace LnLoc

variable {Φ : X →* X'} {e : V' ≃ V} {a b₇ b₁ b₂ : V'}

theorem transport (E : EqData Φ e Γ Γ') (L : LnLoc X Γ (e a) (e b₇) (e b₁) (e b₂)) :
    LnLoc X' Γ' a b₇ b₁ b₂ where
  card := by rw [E.ncard_neighborSet]; exact L.card
  orb7 b hb := by
    obtain ⟨g, h1, h2⟩ := L.orb7 (e b) (by rw [← E.dist]; exact hb)
    exact ⟨Φ g, (E.smul_eq_iff g a a).2 h1, (E.smul_eq_iff g b₇ b).2 h2⟩
  orb8 b hb := by
    rcases L.orb8 (e b) (by rw [← E.dist]; exact hb) with ⟨g, h1, h2⟩ | ⟨g, h1, h2⟩
    · exact Or.inl ⟨Φ g, (E.smul_eq_iff g a a).2 h1, (E.smul_eq_iff g b₁ b).2 h2⟩
    · exact Or.inr ⟨Φ g, (E.smul_eq_iff g a a).2 h1, (E.smul_eq_iff g b₂ b).2 h2⟩
  moves1 u hu := by
    obtain ⟨k, h1, h2, h3, w, hw, hkw⟩ := L.moves1 (e u) ((E.adj _ _).1 hu)
    refine ⟨Φ k, (E.smul_eq_iff k a a).2 h1, (E.smul_eq_iff k b₁ b₁).2 h2,
      (E.smul_eq_iff k u u).2 h3, e.symm w, (E.adj _ _).2 (by simpa using hw), fun hcon => hkw ?_⟩
    have := (E.smul_eq_iff k (e.symm w) (e.symm w)).1 hcon
    simpa using this
  moves2 u hu := by
    obtain ⟨k, h1, h2, h3, w, hw, hkw⟩ := L.moves2 (e u) ((E.adj _ _).1 hu)
    refine ⟨Φ k, (E.smul_eq_iff k a a).2 h1, (E.smul_eq_iff k b₂ b₂).2 h2,
      (E.smul_eq_iff k u u).2 h3, e.symm w, (E.adj _ _).2 (by simpa using hw), fun hcon => hkw ?_⟩
    have := (E.smul_eq_iff k (e.symm w) (e.symm w)).1 hcon
    simpa using this

end LnLoc

namespace AffLab

variable {Φ : X →* X'} {e : V' ≃ V} {a : V'} {lab : ZMod 5 → V}

theorem transport (E : EqData Φ e Γ Γ') (A : AffLab X Γ (e a) lab) :
    AffLab X' Γ' a (fun i => e.symm (lab i)) where
  inj i j h := A.inj (e.symm.injective h)
  adj i := (E.adj _ _).2 (by simpa using A.adj i)
  surj u hu := by
    obtain ⟨i, hi⟩ := A.surj (e u) ((E.adj _ _).1 hu)
    exact ⟨i, by simp [hi]⟩
  aff g' hg' := by
    obtain ⟨y, rfl⟩ := E.surj g'
    obtain ⟨α, β, hα, h⟩ := A.aff y ((E.smul_eq_iff y a a).1 hg')
    refine ⟨α, β, hα, fun i => ?_⟩
    apply e.injective
    rw [E.smul]
    simpa using h i

end AffLab

end CFSG.Quasithin.TitsGeo

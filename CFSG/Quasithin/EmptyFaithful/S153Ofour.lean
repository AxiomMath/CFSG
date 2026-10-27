module

public import CFSG.Quasithin.EmptyFaithful.S153Setup
public import CFSG.Quasithin.EmptyFaithful.S153QuadClass
public import CFSG.Quasithin.EmptyFaithful.S153OrthStruct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem exists_ofourStruct_of_plusType {W : Type*} [CommGroup W] {q : W → ZMod 2}
    (hexp : ∀ w : W, w * w = 1) (hcard : Nat.card W = 16) (hq : IsQuadraticFormOn q)
    (hn : IsNondegQuadratic q) (hp : IsPlusType q) :
    ∃ (L₁ L₂ : Subgroup (MulAut W)) (t : MulAut W),
      OfourStruct (orthogonalGroupOf q) L₁ L₂ t ∧
        ∀ w : W, q w = 1 ↔ (w ∈ commV L₁ ∨ w ∈ commV L₂) ∧ w ≠ 1 := by
  have hfin : Finite W := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨U₁, U₂, hinf, hsup, φ₁, φ₂, hqe⟩ :=
    S153.exists_decomposition_of_plusType hexp hcard hq hn hp
  have hq' : q = S1417.quadOf hinf hsup φ₁ φ₂ := funext hqe
  obtain ⟨L₁, L₂, t, hS, hc₁, hc₂⟩ := S153.exists_ofourStruct hinf hsup φ₁ φ₂
  refine ⟨L₁, L₂, t, ?_, fun w => ?_⟩
  · rw [hq']
    exact hS
  · rw [hq', S1417.quadOf_eq_one_iff hinf hsup φ₁ φ₂, hc₁, hc₂]

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem exists_ofourStruct (h : Hyp153 G T Mc M) :
    ∃ (q : IntMod (VZ T M) h.elemAbelian → ZMod 2)
      (L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) h.elemAbelian)))
      (t : MulAut (IntMod (VZ T M) h.elemAbelian)),
      IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧ IsPlusType q ∧
        autI h.elemAbelian M = orthogonalGroupOf q ∧
        OfourStruct (autI h.elemAbelian M) L₁ L₂ t ∧
        ∀ w, q w = 1 ↔ (w ∈ commV L₁ ∨ w ∈ commV L₂) ∧ w ≠ 1 := by
  obtain ⟨hcard, q, hq1, hq2, hq3, hq4⟩ := h.ofour
  have hX : autI h.elemAbelian M = orthogonalGroupOf q := hq4
  have hexp : ∀ w : IntMod (VZ T M) h.elemAbelian, w * w = 1 := fun w => by
    rw [← pow_two]
    exact IntMod.sq_eq_one w
  obtain ⟨L₁, L₂, t, hS, hnonsing⟩ := exists_ofourStruct_of_plusType (W := IntMod (VZ T M) h.elemAbelian)
    (q := q) hexp hcard hq1 hq2 hq3
  refine ⟨q, L₁, L₂, t, hq1, hq2, hq3, hX, ?_, hnonsing⟩
  rw [hX]
  exact hS

end Hyp153

end CFSG.Quasithin

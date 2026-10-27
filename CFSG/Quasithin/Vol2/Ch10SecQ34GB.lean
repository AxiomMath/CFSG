module

public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

noncomputable abbrev tau32 : ↥(StatedSL 3 (ZMod 2)) := B5.trvSL (0 : Fin 3) 1 (by decide) 1

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {I : Subgroup V}
  {π : ↥(StatedSL 3 (ZMod 2)) →* ↥H}

theorem commutator_tau (hD : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H I ⊥ π) :
    ∃ f ∈ I, f * f = 1 ∧ ∀ u ∈ I,
      ((π tau32 : ↥H) : MulAut V) u * u⁻¹ = 1 ∨ ((π tau32 : ↥H) : MulAut V) u * u⁻¹ = f := by
  obtain ⟨e, he⟩ := B5.exists_linModel hD
  set f : ↥I := e.symm (Multiplicative.ofAdd (Pi.single 0 1)) with hf
  refine ⟨f, f.2, ?_, fun u hu => ?_⟩
  · have h : e (f * f) = 1 := by
      rw [map_mul, hf, MulEquiv.apply_symm_apply, ← ofAdd_add, ← Pi.single_add,
        show (1 : ZMod 2) + 1 = 0 from by decide, Pi.single_zero, ofAdd_zero]
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  · have hτu : ((π tau32 : ↥H) : MulAut V) u ∈ I := hD.2.2.2.1 (π tau32) u hu
    have h1 := he tau32 ⟨u, hu⟩ hτu
    rw [B5.natAct_trvSL] at h1
    set x := Multiplicative.toAdd (e ⟨u, hu⟩) with hx
    have h2 : e ⟨((π tau32 : ↥H) : MulAut V) u * u⁻¹, I.mul_mem hτu (I.inv_mem hu)⟩ =
        Multiplicative.ofAdd (Pi.single 0 (x 1)) := by
      have : (⟨((π tau32 : ↥H) : MulAut V) u * u⁻¹, I.mul_mem hτu (I.inv_mem hu)⟩ : ↥I) =
          ⟨((π tau32 : ↥H) : MulAut V) u, hτu⟩ * (⟨u, hu⟩ : ↥I)⁻¹ := rfl
      rw [this, map_mul, map_inv, h1, one_mul]
      show Multiplicative.ofAdd (x + Pi.single 0 (x 1)) * (Multiplicative.ofAdd x)⁻¹ = _
      rw [← ofAdd_neg, ← ofAdd_add]
      congr 1
      abel
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (x 1) with h0 | h0
    · left
      rw [h0, Pi.single_zero, ofAdd_zero] at h2
      have := e.injective (h2.trans (map_one e).symm)
      exact congrArg Subtype.val this
    · right
      rw [h0] at h2
      have := e.injective (h2.trans (MulEquiv.apply_symm_apply e _).symm)
      exact congrArg Subtype.val this

theorem exists_tau_ne (hD : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H I ⊥ π) :
    ∃ u ∈ I, ((π tau32 : ↥H) : MulAut V) u ≠ u := by
  obtain ⟨e, he⟩ := B5.exists_linModel hD
  set u : ↥I := e.symm (Multiplicative.ofAdd (Pi.single 1 1)) with hu
  refine ⟨u, u.2, fun h => ?_⟩
  have hτu : ((π tau32 : ↥H) : MulAut V) u ∈ I := hD.2.2.2.1 (π tau32) u u.2
  have h1 := he tau32 u hτu
  have h2 : (⟨((π tau32 : ↥H) : MulAut V) u, hτu⟩ : ↥I) = u := Subtype.ext h
  rw [h2, B5.natAct_trvSL, hu, MulEquiv.apply_symm_apply] at h1
  have h3 := congrFun (congrArg Multiplicative.toAdd h1) 0
  simp at h3

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

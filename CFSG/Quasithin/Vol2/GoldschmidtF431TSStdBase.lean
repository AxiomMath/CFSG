module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431NFTI

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.NF
open scoped commutatorElement

section Equiv

variable {D C : Type} [Group D] [Group C] (ε : D ≃* C)

theorem mem_map_equiv_iff {S : Subgroup D} {x : D} : ε x ∈ S.map ε.toMonoidHom ↔ x ∈ S := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem mem_iff_of_map_eq {S : Subgroup D} {S' : Subgroup C} (h : S.map ε.toMonoidHom = S')
    {x : D} : ε x ∈ S' ↔ x ∈ S := by
  rw [← h]
  exact mem_map_equiv_iff ε

theorem mem_symm_iff_of_map_eq {S : Subgroup D} {S' : Subgroup C} (h : S.map ε.toMonoidHom = S')
    {y : C} : ε.symm y ∈ S ↔ y ∈ S' := by
  have := mem_iff_of_map_eq ε h (x := ε.symm y)
  simpa using this.symm

theorem congr_mem_autStab {S : Subgroup D} {S' : Subgroup C} (h : S.map ε.toMonoidHom = S')
    {φ : MulAut D} (hφ : φ ∈ autStab S) : MulAut.congr ε φ ∈ autStab S' := by
  intro y
  have := hφ (ε.symm y)
  rw [← mem_iff_of_map_eq ε h, ← mem_iff_of_map_eq ε h] at this
  simpa using this

theorem map_centralizer_singleton (x : D) :
    (Subgroup.centralizer ({x} : Set D)).map ε.toMonoidHom =
      Subgroup.centralizer ({ε x} : Set C) := by
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hd' : d ∈ Subgroup.centralizer ({x} : Set D) := hd
    rw [Subgroup.mem_centralizer_singleton_iff] at hd'
    show ε d ∈ Subgroup.centralizer ({ε x} : Set C)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hd']
  · intro hy
    refine ⟨ε.symm y, ?_, by simp⟩
    have hy' : y ∈ Subgroup.centralizer ({ε x} : Set C) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy'
    show ε.symm y ∈ Subgroup.centralizer ({x} : Set D)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply ε.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy'

end Equiv

section Generic

variable {D C : Type} [Group D] [Group C] (ε : D ≃* C)

theorem map_symm_eq_of_map_eq {S : Subgroup D} {S' : Subgroup C}
    (h : S.map ε.toMonoidHom = S') : S'.map ε.symm.toMonoidHom = S := by
  rw [← h, Subgroup.map_map]
  ext x
  simp

theorem map_cj_equiv (c : D) (H : Subgroup D) :
    (cj c H).map ε.toMonoidHom = cj (ε c) (H.map ε.toMonoidHom) := by
  ext y
  rw [mem_cj]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_inv, ← map_mul, ← map_mul]
    refine ⟨c⁻¹ * x * c, mem_cj.mp hx, ?_⟩
    simp
  · rintro ⟨x, hx, hxy⟩
    refine ⟨c * x * c⁻¹, ?_, ?_⟩
    · show c * x * c⁻¹ ∈ cj c H
      rw [mem_cj]
      have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
      rw [e]
      exact hx
    · have hxy' : ε x = (ε c)⁻¹ * y * ε c := hxy
      show ε (c * x * c⁻¹) = y
      rw [map_mul, map_mul, map_inv, hxy']
      group

theorem not_solvable_map_equiv {X : Subgroup D} (h : ¬ Group.IsSolvable ↥X) :
    ¬ Group.IsSolvable ↥(X.map ε.toMonoidHom) := fun _hs =>
  h (Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective X ε.toMonoidHom ε.injective).toMonoidHom)
    (Subgroup.equivMapOfInjective X ε.toMonoidHom ε.injective).injective)

theorem solvable_map_equiv {X : Subgroup D} (h : Group.IsSolvable ↥X) :
    Group.IsSolvable ↥(X.map ε.toMonoidHom) :=
  Group.isSolvable_of_surjective
    (f := (Subgroup.equivMapOfInjective X ε.toMonoidHom ε.injective).toMonoidHom)
    (Subgroup.equivMapOfInjective X ε.toMonoidHom ε.injective).surjective

theorem map_inf_centralizer_equiv (L V : Subgroup D) :
    L.map ε.toMonoidHom ⊓ Subgroup.centralizer ((V.map ε.toMonoidHom : Subgroup C) : Set C) =
      (L ⊓ Subgroup.centralizer (V : Set D)).map ε.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨⟨l, hl, rfl⟩, hx⟩
    refine ⟨l, ⟨hl, ?_⟩, rfl⟩
    show l ∈ Subgroup.centralizer (V : Set D)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := Subgroup.mem_centralizer_iff.mp hx (ε v) ⟨v, hv, rfl⟩
    exact ε.injective (by simpa [map_mul] using this)
  · rintro ⟨l, ⟨hl, hc⟩, rfl⟩
    refine ⟨⟨l, hl, rfl⟩, ?_⟩
    show ε l ∈ Subgroup.centralizer ((V.map ε.toMonoidHom : Subgroup C) : Set C)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc v hv
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg _ this

end Generic

section Transport

variable {D C : Type} [Group D] [Group C] (ε : D ≃* C)

theorem mem_map_symm_iff {S : Subgroup C} {x : D} : x ∈ S.map ε.symm.toMonoidHom ↔ ε x ∈ S := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem centralizer_le_transport {R : Subgroup D} {R' : Subgroup C}
    (hR : R.map ε.toMonoidHom = R') (w : C) :
    Subgroup.centralizer ({ε.symm w} : Set D) ≤ R ↔ Subgroup.centralizer ({w} : Set C) ≤ R' := by
  have hc := map_centralizer_singleton ε (ε.symm w)
  rw [MulEquiv.apply_symm_apply] at hc
  constructor
  · intro h y hy
    rw [← hc] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    exact (mem_iff_of_map_eq ε hR).mpr (h hd)
  · intro h d hd
    have h1 : ε d ∈ Subgroup.centralizer ({w} : Set C) := by
      rw [← hc]
      exact Subgroup.mem_map_of_mem _ hd
    exact (mem_iff_of_map_eq ε hR).mp (h h1)


end Transport

section Above

variable {D C : Type} [Group D] [Group C] (A : LieAmalgamExt D) (ε : D ≃* C)

theorem above_of_std {U P P' : Subgroup C}
    (habove : ∀ B : Subgroup C, Subgroup.normalizer (U : Set C) ≤ B → B ≠ ⊤ → B ≤ P ∨ B ≤ P')
    {Q Q' : Subgroup D} (hQP : Q.map ε.toMonoidHom = P) (hQP' : Q'.map ε.toMonoidHom = P')
    (hU : A.TD.map ε.toMonoidHom = U) :
    ∀ X : Subgroup D, Subgroup.normalizer (A.TD : Set D) ≤ X → X ≠ ⊤ → X ≤ Q ∨ X ≤ Q' := by
  intro X hX hne
  have hN : Subgroup.normalizer (U : Set C) ≤ X.map ε.toMonoidHom := by
    rw [← hU, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hX
  have hne' : X.map ε.toMonoidHom ≠ ⊤ := by
    intro h
    apply hne
    rw [eq_top_iff]
    intro x _
    have : ε x ∈ X.map ε.toMonoidHom := by rw [h]; trivial
    exact (mem_map_equiv_iff ε).mp this
  rcases habove _ hN hne' with h | h
  · left
    intro x hx
    exact (mem_iff_of_map_eq ε hQP).mp (h (Subgroup.mem_map_of_mem _ hx))
  · right
    intro x hx
    exact (mem_iff_of_map_eq ε hQP').mp (h (Subgroup.mem_map_of_mem _ hx))

end Above
end CFSG.Quasithin.H13.F431.Lift

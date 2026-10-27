module

import CFSG.Quasithin.Background.FFC4Zmod
import CFSG.CGT.Timmesfeld75.TransvectionBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16t3_natural_normal_form {n : ℕ} {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (h : BinaryNaturalSL H U Z n 1) :
    Z ≤ U ∧ (∀ h' : ↥H, ∀ u ∈ U, (h' : MulAut W) u ∈ U) ∧
      (∀ h' : ↥H, ∀ z ∈ Z, (h' : MulAut W) z ∈ Z) ∧
      ∃ (π : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* ↥H)
        (β : ↥U →* Multiplicative (Fin n → ZMod 2)),
        Function.Injective π ∧ Function.Surjective π ∧ Function.Surjective β ∧
        (∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z) ∧
        ∀ (s : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥U)
          (hu : ((π s : ↥H) : MulAut W) (u : W) ∈ U),
          β ⟨((π s : ↥H) : MulAut W) (u : W), hu⟩ =
            Multiplicative.ofAdd ((s : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
              (Multiplicative.toAdd (β u))) := by
  obtain ⟨π₂, hπ₂⟩ := FFC.BinaryNaturalSL.exists_zmod h
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ₂
  obtain ⟨hπ₂surj, hZU, -, hUinv, hZinv, -, -, -⟩ := hπ₂
  let π : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* ↥H :=
    π₂.comp (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)).toMonoidHom
  have hEq : ∀ (s : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥U)
      (hu : ((π s : ↥H) : MulAut W) (u : W) ∈ U),
      f ⟨((π s : ↥H) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd ((s : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
          (Multiplicative.toAdd (f u))) := by
    intro s u hu
    have h1 := hfe
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2) s) u hu
    simp only [natAct, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe] at h1
    exact h1
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmat : (x : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec = id := by
      funext v
      obtain ⟨u, hu⟩ := hfs (Multiplicative.ofAdd v)
      have hu' : ((π x : ↥H) : MulAut W) (u : W) ∈ U := by
        rw [hx]
        simpa using u.2
      have h1 := hEq x u hu'
      have hval : ((π x : ↥H) : MulAut W) (u : W) = (u : W) := by
        rw [hx]
        simp
      have hl : (⟨((π x : ↥H) : MulAut W) (u : W), hu'⟩ : ↥U) = u :=
        Subtype.ext hval
      rw [hl, hu] at h1
      rw [toAdd_ofAdd] at h1
      simpa using (Multiplicative.ofAdd.injective h1).symm
    have h1 : Matrix.toLin' (x : Matrix (Fin n) (Fin n) (ZMod 2)) =
        Matrix.toLin' (1 : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      rw [Matrix.toLin'_one]
      exact LinearMap.ext fun v => by
        rw [Matrix.toLin'_apply]
        simpa using congrFun hmat v
    exact Subtype.ext (Matrix.toLin'.injective h1)
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨x, hx⟩ := hπ₂surj y
    obtain ⟨s, hs⟩ :=
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)).surjective x
    refine ⟨s, ?_⟩
    show π₂ ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)) s) = y
    rw [hs]
    exact hx
  exact ⟨hZU, hUinv, hZinv, π, f, hπinj, hπsurj, hfs, hfk, hEq⟩

theorem s16t3_sl_of_linearEquiv {n : ℕ}
    (s : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), orderOf g = orderOf s ∧
      ∀ v : Fin n → ZMod 2, (g : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v = s v := by
  obtain ⟨g, hg⟩ := CFSG.CGT.Timmesfeld75.exists_sl_of_linearEquiv s
  refine ⟨g, ?_, fun v => hg v⟩
  have hlin : Matrix.SpecialLinearGroup.toLin' g = s := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro v
    rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap, Matrix.toLin'_apply]
    exact hg v
  rw [← hlin]
  exact (orderOf_injective (Matrix.SpecialLinearGroup.toLin' (n := Fin n) (R := ZMod 2))
    (Matrix.SpecialLinearGroup.toLin'_injective (n := Fin n) (R := ZMod 2)) g).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

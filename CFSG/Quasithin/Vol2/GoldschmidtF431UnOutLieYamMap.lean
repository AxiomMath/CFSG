module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin

public section

namespace CFSG.Quasithin.H13.F431.Un.OL

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.Sec53F.Yam
open CFSG.QuasithinUnique.Setup.Layer (isSylowTwoOf_map_mulEquiv)

section Map

variable {C C' : Type} [Group C] [Group C'] (e : C ≃* C')

def subOrderIso : Subgroup C ≃o Subgroup C' where
  toFun := Subgroup.map e.toMonoidHom
  invFun := Subgroup.map e.symm.toMonoidHom
  left_inv M := by
    rw [Subgroup.map_map]
    ext x
    simp
  right_inv M := by
    rw [Subgroup.map_map]
    ext x
    simp
  map_rel_iff' := Subgroup.map_le_map_iff_of_injective e.injective

theorem isCoatom_map {M : Subgroup C} (hM : IsCoatom M) : IsCoatom (M.map e.toMonoidHom) :=
  (OrderIso.isCoatom_iff (subOrderIso e) M).2 hM

theorem isTwoLocal_map {M : Subgroup C} (hM : IsTwoLocal M) : IsTwoLocal (M.map e.toMonoidHom) := by
  obtain ⟨R, hR1, hR2, rfl⟩ := hM
  refine ⟨R.map e.toMonoidHom, fun h => hR1 ?_, ?_, (Subgroup.map_equiv_normalizer_eq R e)⟩
  · exact Subgroup.map_injective e.injective (by rw [h, Subgroup.map_bot])
  · exact hR2.of_equiv (R.equivMapOfInjective e.toMonoidHom e.injective)

theorem yamStd_map {U P₀ P₁ : Subgroup C} (S : YamStd C U P₀ P₁) :
    YamStd C' (U.map e.toMonoidHom) (P₀.map e.toMonoidHom) (P₁.map e.toMonoidHom) where
  sylow := by
    have h := (isSylowTwoOf_map_mulEquiv e).2 S.sylow
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at h
  no_normal R hR hp := by
    have hN : (R.map e.symm.toMonoidHom).Normal := hR.map e.symm.toMonoidHom e.symm.surjective
    have h0 := S.no_normal _ hN (hp.of_equiv (R.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective))
    have : R = (R.map e.symm.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map]
      ext x
      simp
    rw [this, h0, Subgroup.map_bot]
  ne h := S.ne (Subgroup.map_injective e.injective h)
  le₀ := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono S.le₀
  le₁ := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono S.le₁
  coatom₀ := isCoatom_map e S.coatom₀
  coatom₁ := isCoatom_map e S.coatom₁
  above A hA hAt := by
    set A₀ := A.map e.symm.toMonoidHom with hA₀
    have hAA : A = A₀.map e.toMonoidHom := by
      rw [hA₀, Subgroup.map_map]
      ext x
      simp
    have h1 : Subgroup.normalizer (U : Set C) ≤ A₀ := by
      intro x hx
      have : e x ∈ Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup C') : Set C') := by
        rw [← Subgroup.map_equiv_normalizer_eq U e]
        exact ⟨x, hx, rfl⟩
      exact ⟨e x, hA this, by simp⟩
    have h2 : A₀ ≠ ⊤ := fun h => hAt (by
      rw [hAA, h, Subgroup.map_top_of_surjective _ e.surjective])
    rcases S.above A₀ h1 h2 with h | h
    · left
      rw [hAA]
      exact Subgroup.map_mono h
    · right
      rw [hAA]
      exact Subgroup.map_mono h
  twoLoc₀ := isTwoLocal_map e S.twoLoc₀
  twoLoc₁ := isTwoLocal_map e S.twoLoc₁

end Map

theorem yamStd_swap {C : Type} [Group C] {U P₀ P₁ : Subgroup C} (S : YamStd C U P₀ P₁) :
    YamStd C U P₁ P₀ where
  sylow := S.sylow
  no_normal := S.no_normal
  ne := S.ne.symm
  le₀ := S.le₁
  le₁ := S.le₀
  coatom₀ := S.coatom₁
  coatom₁ := S.coatom₀
  above A hA hAt := (S.above A hA hAt).symm
  twoLoc₀ := S.twoLoc₁
  twoLoc₁ := S.twoLoc₀

end CFSG.Quasithin.H13.F431.Un.OL

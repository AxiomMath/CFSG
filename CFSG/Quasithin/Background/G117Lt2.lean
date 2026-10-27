module

public import CFSG.Quasithin.Background.G117Lt1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace G117

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem field_eq_zero_or_one_of_card_two {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2)
    (y : F) : y = 0 ∨ y = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_contra h
  push Not at h
  have h3 : ({0, 1, y} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h.1.symm, zero_ne_one]),
      Finset.card_pair (Ne.symm h.2)]
  have := Finset.card_le_univ ({0, 1, y} : Finset F)
  rw [← Nat.card_eq_fintype_card, hF] at this
  omega

section Faithful

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}
  (h108 : G108Hyp B Γ v₁ W X X₀ L)

include h108

theorem eq_one_of_fixes_irr (hE11 : E11Stmt) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I) (hhom : Homogeneous (normalClosure Γ L))
    (hH : Invariant (normalClosure Γ L) I)
    (hend : EndIsField (restrictRange (normalClosure Γ L) I hH) 1) {c : GLV V}
    (hcH : ∀ h ∈ normalClosure Γ L, h * c = c * h)
    (hfix : ∀ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J → conjSub c J = J) :
    c = 1 := by
  obtain ⟨D⟩ := hE11 V (normalClosure Γ L) I hhom hI h108.fixedSpace_H h108.sSup_isIrr
  obtain ⟨e⟩ := hend
  have hF2 : Nat.card D.F = 2 := by
    have h1 : Nat.card D.F = Nat.card ↥(endOn (normalClosure Γ L) I) :=
      (Nat.card_congr D.endEquiv.toEquiv).symm
    rw [h1, endOn_eq_endCommutant hH, Nat.card_congr e.toEquiv, GaloisField.card 2 1 one_ne_zero]
    norm_num
  let cc : ↥(Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) :=
    ⟨c, Subgroup.mem_centralizer_iff.2 hcH⟩
  have hθ : D.θ cc = 1 := by
    refine LinearEquiv.ext fun u => ?_
    by_cases hu : u = 0
    · subst hu
      simp
    · let p : Projectivization D.F D.U := Projectivization.mk D.F u hu
      have hp := D.θ_acts cc (D.ψ.symm p).1 (D.ψ.symm p).2
      obtain ⟨hJ', hψ⟩ := hp
      have e1 : conjSub c (D.ψ.symm p).1 = (D.ψ.symm p).1 := hfix _ (D.ψ.symm p).2
      have e2 : (⟨conjSub c (D.ψ.symm p).1, hJ'⟩ : {J : Submodule (ZMod 2) V //
          IrrPlus (normalClosure Γ L) J}) = D.ψ.symm p := Subtype.ext e1
      have e3 : D.θ cc • p = p := by
        have := hψ
        rw [e2, Equiv.apply_symm_apply] at this
        exact this.symm
      have e4 : D.θ cc • p = Projectivization.mk D.F (D.θ cc u) (by simpa using hu) :=
        Projectivization.smul_mk _ hu
      rw [e4] at e3
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).1 e3
      have ha1 : a = 1 := by
        rcases field_eq_zero_or_one_of_card_two hF2 (a : D.F) with h0 | h1
        · exact absurd h0 a.ne_zero
        · exact Units.ext h1
      rw [ha1, one_smul] at ha
      simpa using ha.symm
  have : cc = 1 := D.θ.injective (by rw [hθ, map_one])
  exact congrArg Subtype.val this

end Faithful

end G117

end G11

end CFSG.Quasithin

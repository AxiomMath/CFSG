module

public import CFSG.Quasithin.Background.G10FifteenOuter

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem caseOne_ii (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) :
    ∃ x ∈ X, conjSub x I ≠ I ∧ IsCompl I (conjSub x I) ∧
      ¬ HIso (normalClosure Γ L) I (conjSub x I) ∧
      ∃ (i : V) (hi : i ∈ I ⊓ perp B v₁), i ≠ 0 ∧ I ⊓ W = Submodule.span (ZMod 2) {i} ∧
        v₁ = i + x i ∧
        (fixedSpace X = Submodule.span (ZMod 2) {v₁} →
          fixedSpace (stabilizerOf X I) ⊓ I = Submodule.span (ZMod 2) {i}) ∧
        (∀ y ∈ stabilizerOf X I, (∀ h ∈ normalClosure Γ L, y * h = h * y) → y = 1) ∧
        FaithfulOn (stabilizerOf X I) I ∧
        FullTransvections (stabilizerOf X I) (I ⊓ perp B v₁) i hi := by
  obtain ⟨i, hi, hi0, hv, hY⟩ := hyp.exists_i h10 hI hfix hx hne
  refine ⟨x, hx, hne, hyp.isCompl_sup_conj h10 h11 h12 hI hfix hx hne,
    fun h => hne (hfix x hx h), i, hi, hi0, hyp.inf_W_eq_span h11 h12 hI hfix hx hne hi hi0 hv,
    hv, fun hfs => hyp.fixedSpace_stabilizerOf_inf hI hfix hx hne hi.1 hi0 hv hY hfs,
    fun y hy hc => hyp.centralizer_X_eq_one h10 h11 h12 hI hfix hx hne hy.1 hc,
    hyp.faithfulOn_stabilizerOf h10 h11 h12 hI hfix hx hne,
    hyp.fullTransvections hI hfix hx hne hi hv⟩

theorem caseTwo_isotropic (hOut : OuterGLInput) (h10 : G1010Concl Γ v₁ X L)
    (h11 : G1011Concl Γ v₁ X L) (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) (hiso : Isotropic B I) :
    (¬ Homogeneous (normalClosure Γ L) ∧ ¬ SelfDual (normalClosure Γ L) I ∧
        FaithfulOn (normalClosure Γ L) I ∧ Isotropic B I ∧
        ∀ x ∈ X, conjSub x I ≠ I → IsDualOf (normalClosure Γ L) I (conjSub x I)) ∧
      (¬ AutAll (normalClosure Γ L) I ∨ Module.finrank (ZMod 2) I = 4) :=
  ⟨hyp.caseII h10 h11 h12 hI hfix hx hne hiso,
    hyp.three_of_isotropic hOut h10 h11 h12 hI hfix hx hne hiso⟩


theorem fix_conj {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) :
    ∀ z ∈ X, HIso (normalClosure Γ L) (conjSub x I) (conjSub z (conjSub x I)) →
      conjSub z (conjSub x I) = conjSub x I := by
  intro z hz hiso
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hirr' : IsIrr (normalClosure Γ L) (conjSub x I) :=
    hirr.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  rcases hyp.conj_mem_pair hI hfix hx hne hz (Or.inr rfl :
      conjSub x I = I ∨ conjSub x I = conjSub x I) with h | h
  · exfalso
    rw [h] at hiso
    exact hne (hfix x hx (hiso_symm hirr'.1 hirr.1 hiso))
  · exact h

theorem conj_conj_ne {I : Submodule (ZMod 2) V} {x : GLV V} (hx : x ∈ X)
    (hne : conjSub x I ≠ I) : conjSub x (conjSub x I) ≠ conjSub x I := by
  rw [conjSub_conjSub_of_sq (hyp.X_sq x hx)]
  exact fun h => hne h.symm

end G108Hyp

end G11

end CFSG.Quasithin

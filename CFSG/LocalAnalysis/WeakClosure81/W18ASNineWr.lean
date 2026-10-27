module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineSym
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineSp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

private def piFinSuccMulEquiv (L : Type) [Group L] (m : ℕ) :
    (Fin (m + 1) → L) ≃* L × (Fin m → L) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv p := by simp
  map_mul' _ _ := rfl

private def kerFstMulEquiv (A B : Type) [Group A] [Group B] :
    ↥(MonoidHom.fst A B).ker ≃* B where
  toFun x := x.1.2
  invFun b := ⟨(1, b), MonoidHom.mem_ker.mpr rfl⟩
  left_inv x := by
    obtain ⟨⟨a, b⟩, hx⟩ := x
    have ha : a = 1 := hx
    subst ha
    rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

namespace NoSocle185Factor

theorem prod {A B : Type} [Group A] [Group B] (hA : NoSocle185Factor A)
    (hB : NoSocle185Factor B) : NoSocle185Factor (A × B) :=
  of_normal (MonoidHom.fst A B).ker (of_mulEquiv (kerFstMulEquiv A B).symm hB)
    (of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.fst A B)
      fun a => ⟨(a, 1), rfl⟩).symm hA)

theorem pi_fin {L : Type} [Group L] (hL : NoSocle185Factor L) (m : ℕ) :
    NoSocle185Factor (Fin m → L) := by
  induction m with
  | zero => exact of_commute fun a b => Subsingleton.elim _ _
  | succ m ih => exact of_mulEquiv (piFinSuccMulEquiv L m).symm (hL.prod ih)

end NoSocle185Factor

theorem noSocle185Factor_pi_sl2 (hO : LieOrderFormulasInput) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (m : ℕ) :
    NoSocle185Factor (Fin m → Matrix.SpecialLinearGroup (Fin 2) F) :=
  (noSocle185Factor_sl2 hO hF).pi_fin m

theorem noSocle185Factor_wreathSym (hO : LieOrderFormulasInput) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (m : ℕ) :
    NoSocle185Factor (WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m) := by
  refine NoSocle185Factor.of_normal
    (SemidirectProduct.rightHom : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m →*
      Equiv.Perm (Fin m)).ker ?_ ?_
  · exact NoSocle185Factor.of_mulEquiv
      ((MonoidHom.ofInjective SemidirectProduct.inl_injective).trans
        (MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom))
      (noSocle185Factor_pi_sl2 hO hF m)
  · exact NoSocle185Factor.of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective SemidirectProduct.rightHom
        SemidirectProduct.rightHom_surjective).symm (noSocle185Factor_perm hO m)

theorem noSocle185Factor_of_isL2WrSymGp (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {n m : ℕ} (h : IsL2WrSymGp Y n m) : NoSocle185Factor Y := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact (noSocle185Factor_wreathSym hO hF m).of_mulEquiv e.symm

end CFSG.LocalAnalysis.WeakClosure81

end

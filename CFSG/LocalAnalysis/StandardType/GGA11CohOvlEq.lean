module

public import CFSG.LocalAnalysis.StandardType.GGA11CohDefs
public import CFSG.LocalAnalysis.StandardType.GGA11CohWsub
public import CFSG.LocalAnalysis.StandardType.GGA11CohOvlComp
public import CFSG.LocalAnalysis.StandardType.GGA11CohCompEq

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

theorem a11OverlapEqInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (φ₃ : SL 9 →* G) (f n : Fin 4 → G), A11GlueHyp φ₃ f n →
      ∀ l m : Fin 4, l ≠ m → Ovl φ₃ n l m = Ovl φ₃ n m l := by
  intro G _ _ φ₃ f n hhyp l m hlm
  have hpair : ∀ l m : Fin 4, l ≠ m → ∃ k : Fin 4, k ≠ l ∧ k ≠ m := by decide
  obtain ⟨k, hkl, hkm⟩ := hpair l m hlm
  have hA := a11OvlCompInput_holds a11WsubInput_holds G φ₃ f n hhyp l m hlm
  have hA' := a11OvlCompInput_holds a11WsubInput_holds G φ₃ f n hhyp m l hlm.symm
  have hfkA : f k ∈ Ovl φ₃ n l m := hA.2.2 k hkl hkm
  have hfkA' : f k ∈ Ovl φ₃ n m l := hA'.2.2 k hkm hkl
  have hfk1 : f k ≠ 1 := by
    have hk7 : orderOf (f k) = 7 := hhyp.2.2.2.1 k
    intro h
    rw [h, orderOf_one] at hk7
    omega
  refine a11CompEqInput_holds G (Subgroup.centralizer ({f l, f m} : Set G))
    (Ovl φ₃ n l m) (Ovl φ₃ n m l) (f k) hA.1 ?_ hfkA hfkA' hfk1 hA.2.1
  simpa only [Set.pair_comm] using hA'.1

end CFSG.StandardType.A11

end

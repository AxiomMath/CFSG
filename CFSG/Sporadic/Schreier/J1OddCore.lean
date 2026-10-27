module

public import CFSG.Sporadic.Schreier.MathieuOddCoreTransport
public import CFSG.Foundations.Basic
public import CFSG.Sporadic.Schreier.J1Centralizer

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint

theorem ctugs_j1_involution_centralizer_odd_core_free
    {G : Type*} [Group G] [Finite G]
    (hG : Nonempty (G ≃* NativeSporadic.J1)) (t : G) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) = 120 ∧
      CFSG.piCore {q : Nat.Primes | q.val ≠ 2} (Subgroup.centralizer ({t} : Set G)) = ⊥ ∧
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) = ⊥ ∧
      CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  obtain ⟨ψ⟩ := hG
  set θ : G ≃* j1P := ψ.trans j1PermEquiv
  have hP : ∀ s : j1P, orderOf s = 2 →
      CFSG.oddCore (Subgroup.centralizer ({s} : Set j1P)) = ⊥ :=
    inner_oddCore_eq_bot j1P fun u hu ho => ⟨15, 3,
      (j1P_involution_centralizer u hu ho).1.trans (by norm_num),
      (j1P_involution_centralizer u hu ho).2.1⟩
  have hodd := inner_of_equiv θ hP t ht
  have hcard : Nat.card (Subgroup.centralizer ({t} : Set G)) = 120 := by
    have hu : ((θ t : j1P) : Equiv.Perm (Fin 3080)) ∈ j1P := (θ t).2
    have hou : orderOf ((θ t : j1P) : Equiv.Perm (Fin 3080)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact ht
    rw [← (j1P_involution_centralizer _ hu hou).1, ← map_centralizer_subtype,
      Subgroup.card_map_of_injective j1P.subtype_injective, ← map_centralizer_equiv,
      Subgroup.card_map_of_injective θ.injective]
  refine ⟨hcard, ?_, ?_, hodd⟩
  · rw [← CFSG.oddCore_eq_piCore _]
    exact hodd
  · rw [CFSG.pPrimeCore_eq_piCore _ 2, ← CFSG.oddCore_eq_piCore _]
    exact hodd

end CFSG.Sporadic.Schreier

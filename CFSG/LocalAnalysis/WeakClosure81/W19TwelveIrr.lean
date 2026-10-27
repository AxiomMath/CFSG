module

public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveAbs
public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveComm
public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveEnd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem gap1912E0_of_gap1912 (c : MinCex193 D V₀ V p X) (h2 : Nat.card ↥V₀ = 2)
    (h12 : Gap1912 D V₀ V X) : Gap1912E0 D V₀ V X := by
  intro I hI hnot
  have hIZ : I ≤ Z193 D V := hI.1
  have hMH : X ⊔ D.T ≤ D.M := c.hyp.le_M
  have hA : IsElemAbelian 2 (CFSG.Quasithin.conjClosure I (X ⊔ D.T)) :=
    isElemAbelian_conjClosure (IsElemAbelian.mono c.isElemAbelian_Z193 hIZ) (h12 I hI)
  have hIH : I ≤ X ⊔ D.T := (hIZ.trans c.Z193_le_T).trans le_sup_right
  have hV₀H : ∀ h ∈ X ⊔ D.T, ∀ v ∈ V₀, h * v = v * h := by
    intro h hh v hv
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (c.commutator_V₀_eq_bot h2 hMH)
    exact (Subgroup.mem_centralizer_iff.1 (hle hv)) h hh
  have hFn : X ⊔ D.T ≤ normalizer (V₀ : Set G) := hMH.trans c.setting.pair.le_normalizer₀
  have hOn : ∀ h ∈ X ⊔ D.T, ∀ o ∈ pCoreOf 2 (X ⊔ D.T), h⁻¹ * o * h ∈ pCoreOf 2 (X ⊔ D.T) := by
    intro h hh o ho
    have := (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ D.T) ((X ⊔ D.T).inv_mem hh)) o).1 ho
    simpa using this
  have hIO : ∀ a ∈ I, ∀ o ∈ pCoreOf 2 (X ⊔ D.T), ⁅a, o⁆ ∈ V₀ := by
    intro a ha o ho
    have hoT : o ∈ D.T := Hyp193.pCoreOf_le_T c.hyp ho
    exact commutator_mem_of_card_four hI.2.1 h2 hI.2.2.1
      (hI.2.2.2.1 (c.T_le_normalizer_Z193 hoT)) (hFn (Subgroup.mem_sup_right hoT)) a ha
  have hOE : ∀ o ∈ pCoreOf 2 (X ⊔ D.T), ∀ e ∈ CFSG.Quasithin.conjClosure I (X ⊔ D.T),
      ⁅e, o⁆ ∈ V₀ := fun o ho e he =>
    commutator_mem_of_mem_conjClosure hIH hOn hV₀H hIO e he o ho
  have hXE : ¬ ⁅X, CFSG.Quasithin.conjClosure I (X ⊔ D.T)⁆ ≤ V₀ := hnot
  exact exists_irreducible_constituent c.hyp.prime c.hyp.odd hA le_sup_left
    (c.hyp.pCoreOf_le_T.trans le_sup_right) (CFSG.Quasithin.le_normalizer_conjClosure I _)
    (hI.2.2.1.trans (CFSG.Quasithin.le_conjClosure I _)) hV₀H c.le_normalizer_sup_pCoreOf hOE
    c.hyp.isPGroup hXE

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end

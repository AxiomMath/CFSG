module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Count
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_exists_noncyclic_le_preBarSub {M V₀ V E : Subgroup G} (hV : IsElemAbelian 2 V)
    {p : ℕ} (hp : p.Prime) (hEM : E ≤ M) (hMs : M ≤ stabTil V₀ V) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 3) {K : Subgroup (MulAut (Vtil V₀ V hV))}
    (hKM : K ≤ Mbar M V₀ V hV) (hpK : p ∣ Nat.card K)
    (hM3 : ¬ p ^ 3 ∣ Nat.card (Mbar M V₀ V hV))
    (hN : barSub V₀ V hV E ≤ normalizer (K : Set (MulAut (Vtil V₀ V hV)))) :
    ∃ B : Subgroup G, B ≤ E ∧ B ≤ preBarSub M V₀ V hV K ∧ IsElemAbelian p B ∧
      ¬ IsCyclic ↥B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEst : E ≤ stabTil V₀ V := hEM.trans hMs
  let Q' : Subgroup (MulAut (Vtil V₀ V hV)) := K ⊓ barSub V₀ V hV E
  have hQ' : Q' ≤ barSub V₀ V hV E := inf_le_right
  have hrel : K.relIndex (barSub V₀ V hV E) ≤ p ^ (2 - 1) :=
    c23_relIndex_le_of_card hp (barSub_mono V₀ V hV hEM) hKM
      ((hE.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)).isPGroup hN
      (a := 1) (b := 2) (by simpa using hpK) (by simpa using hM3)
  have hrel' : K.relIndex (barSub V₀ V hV E) ≤ p := by simpa using hrel
  have hcardP : Nat.card (barSub V₀ V hV E) =
      K.relIndex (barSub V₀ V hV E) * Nat.card Q' :=
    (Subgroup.relIndex_mul_card (H := K) (K := barSub V₀ V hV E)).symm
  have hPle : Nat.card (barSub V₀ V hV E) ≤ p * Nat.card Q' := by
    rw [hcardP]
    exact Nat.mul_le_mul_right _ hrel'
  have hid := s16c7_card_mul_card_preBarSub hV hEst (Q := Q') hQ'
  rw [hEcard] at hid
  have hle : p ^ 3 * Nat.card Q' ≤ Nat.card (preBarSub E V₀ V hV Q') *
      (p * Nat.card Q') := by
    calc p ^ 3 * Nat.card Q'
        = Nat.card (preBarSub E V₀ V hV Q') * Nat.card (barSub V₀ V hV E) := hid
      _ ≤ Nat.card (preBarSub E V₀ V hV Q') * (p * Nat.card Q') :=
          Nat.mul_le_mul_left _ hPle
  have hBcard : p ^ 2 ≤ Nat.card (preBarSub E V₀ V hV Q') := by
    have hQ'pos : 0 < Nat.card Q' := Nat.card_pos
    have h1 : p ^ 3 ≤ Nat.card (preBarSub E V₀ V hV Q') * p :=
      Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_assoc] using hle) hQ'pos
    have hp3eq : p ^ 3 = p ^ 2 * p := by ring
    rw [hp3eq] at h1
    exact Nat.le_of_mul_le_mul_right h1 hp.pos
  have hBE : preBarSub E V₀ V hV Q' ≤ E := inf_le_left
  have hBel : IsElemAbelian p (preBarSub E V₀ V hV Q') := hE.mono hBE
  refine ⟨preBarSub E V₀ V hV Q', hBE, ?_, hBel, ?_⟩
  · intro g hg
    obtain ⟨hgE, hgst, hgQ'⟩ := (mem_preBarSub E V₀ V hV Q').1 hg
    exact (mem_preBarSub M V₀ V hV K).2 ⟨hEM hgE, hgst, (Subgroup.mem_inf.1 hgQ').1⟩
  · exact s16c7_not_isCyclic_of_elemAbelian hp hBel hBcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Sylow
public import CFSG.Quasithin.AppendixH.H9.H93.PsiBridge
public import CFSG.Quasithin.AppendixH.H9.H93.JThompson.ImgPermSubgroups
public import CFSG.Quasithin.AppendixH.H9.H93.JThompson.SylowStabilizerOrder
public import CFSG.Quasithin.AppendixH.H9.H93.JThompson.ThompsonJUnique

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem thompsonJ_Sylow_facts (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {T : Subgroup (MulAut (PairN 4))} (hT : IsSylowIn 2 T (Mg 4)) :
    thompsonJ (T ⊓ stabSub (V1n 4)) ≤ Lg 4 ∧
      IsElemAbelian2 (thompsonJ (T ⊓ stabSub (V1n 4))) ∧
      Nat.card (thompsonJ (T ⊓ stabSub (V1n 4))) = 16 := by
  have hT₁L : T ⊓ stabSub (V1n 4) ≤ Lg 4 := by
    rw [inf_stabSub_V1n_eq_inf_Lg hT]
    exact inf_le_right
  have hT₁M : T ⊓ stabSub (V1n 4) ≤ Mg 4 := hT₁L.trans Lg_le_Mg
  have hc : Nat.card ↥(T ⊓ stabSub (V1n 4)) = 64 := card_inf_stabSub_V1n_of_isSylowIn hT
  have hPA : imgPermOf ψ (T ⊓ stabSub (V1n 4)) ≤ alternatingGroup (Fin 8) :=
    (le_Lg_iff_imgPermOf_le_alt ψ hT₁M).1 hT₁L
  have hPc : Nat.card ↥(imgPermOf ψ (T ⊓ stabSub (V1n 4))) = 64 :=
    (card_imgPermOf ψ hT₁M).trans hc
  obtain ⟨E₀, hE₀P, hE₀ab, hE₀c, hE₀max⟩ := exists_unique_e16_of_card_sixtyfour hPA hPc
  obtain ⟨J₀, hJ₀M, hJ₀E⟩ := exists_le_Mg_imgPermOf_eq ψ E₀
  have hJ₀T : J₀ ≤ T ⊓ stabSub (V1n 4) :=
    le_of_imgPermOf_le ψ hJ₀M (by rw [hJ₀E]; exact hE₀P)
  have hJ₀ab2 : IsElemAbelian2 J₀ :=
    (isElemAbelian2_iff_imgPermOf ψ hJ₀M).2 (by rw [hJ₀E]; exact hE₀ab)
  have hJ₀c : Nat.card ↥J₀ = 16 := by
    rw [← card_imgPermOf ψ hJ₀M, hJ₀E, hE₀c]
  have hJ₀ab : IsElemAbelian 2 J₀ := isElemAbelian_two_iff_isElemAb2.2 hJ₀ab2
  have hJ : thompsonJ (T ⊓ stabSub (V1n 4)) = J₀ := by
    refine thompsonJ_eq_of_unique_max hJ₀T hJ₀ab ?_ ?_
    · intro B hBT hB
      have hBM : B ≤ Mg 4 := hBT.trans hT₁M
      have hB2 : IsElemAbelian2 B := isElemAbelian_two_iff_isElemAb2.1 hB
      have hBab : IsElemAb2 (imgPermOf ψ B) := (isElemAbelian2_iff_imgPermOf ψ hBM).1 hB2
      rw [hJ₀c, ← card_imgPermOf ψ hBM]
      exact (hE₀max _ (imgPermOf_mono ψ hBT) hBab).1
    · intro B hBT hB hBc
      have hBM : B ≤ Mg 4 := hBT.trans hT₁M
      have hB2 : IsElemAbelian2 B := isElemAbelian_two_iff_isElemAb2.1 hB
      have hBab : IsElemAb2 (imgPermOf ψ B) := (isElemAbelian2_iff_imgPermOf ψ hBM).1 hB2
      have h16 : Nat.card ↥(imgPermOf ψ B) = 16 := by
        rw [card_imgPermOf ψ hBM, hBc, hJ₀c]
      exact eq_of_imgPermOf_eq ψ hBM hJ₀M
        (((hE₀max _ (imgPermOf_mono ψ hBT) hBab).2 h16).trans hJ₀E.symm)
  have key : ∀ A : Subgroup (MulAut (PairN 4)), A = J₀ →
      A ≤ Lg 4 ∧ IsElemAbelian2 A ∧ Nat.card ↥A = 16 := by
    rintro A rfl
    exact ⟨hJ₀T.trans hT₁L, hJ₀ab2, hJ₀c⟩
  exact key _ hJ

end CFSG.ASVolI.ChH

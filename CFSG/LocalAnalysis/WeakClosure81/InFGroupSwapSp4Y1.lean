module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4FactE
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Act
import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4G0

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

open Subgroup CFSG.Open CFSG.Quasithin

variable {Q : Type} [Group Q] [Finite Q] {L T P₀ P₁ : Subgroup Q} {n : ℕ}
  {F : Type} [Field F] [Finite F] {w : F × F → Q}

private theorem map_conj_pCoreOf_perfectCore_eq {P P' : Subgroup Q} {t : Q}
    (hP : P.map (MulAut.conj t).toMonoidHom = P') :
    (pCoreOf 2 (perfectCore P)).map (MulAut.conj t).toMonoidHom =
      pCoreOf 2 (perfectCore P') := by
  rw [← CFSG.ASVolI.ChH.pCoreOf_map_of_injective 2 (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective (perfectCore P), CFSG.Quasithin.map_perfectCore, hP]

theorem stab_of_commute (h : Setting L T P₀ P₁ n w) {A : Subgroup Q} (hAT : A ≤ T)
    (hA2 : IsElemAbelian 2 A) (hAS : ∀ a ∈ A, P₀.map (MulAut.conj a).toMonoidHom = P₀)
    (hcard : 2 ^ n < Nat.card ↥A) {t : Q} (ht : t ∈ T) (htA : ∀ a ∈ A, t * a = a * t) :
    P₀.map (MulAut.conj t).toMonoidHom = P₀ := by
  rcases map_conj_eq_or h ht with ⟨h0, -⟩ | ⟨h0, h1⟩
  · exact h0
  · exfalso
    have hR0 := map_conj_pCoreOf_perfectCore_eq (P := P₀) (P' := P₁) h0
    have hR1 := map_conj_pCoreOf_perfectCore_eq (P := P₁) (P' := P₀) h1
    have hBt : ∀ b ∈ A ⊓ L, t * b = b * t := fun b hb => htA b hb.1
    have hBin : A ⊓ L ≤ pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁) := by
      have hB2 : IsElemAbelian 2 (A ⊓ L) := hA2.mono inf_le_left
      have hBmem : A ⊓ L ≤ T ⊓ L := le_inf (le_trans inf_le_left hAT) inf_le_right
      have hmap : (A ⊓ L).map (MulAut.conj t).toMonoidHom = A ⊓ L := by
        have htN : t ∈ Subgroup.normalizer ((A ⊓ L : Subgroup Q) : Set Q) :=
          Subgroup.centralizer_le_normalizer _
            (Subgroup.mem_centralizer_iff.mpr fun b hb => (hBt b hb).symm)
        simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp htN
      rcases le_or_le_of_isElemAbelian h hBmem hB2 with hB | hB
      · refine le_inf hB ?_
        calc A ⊓ L = (A ⊓ L).map (MulAut.conj t).toMonoidHom := hmap.symm
          _ ≤ (pCoreOf 2 (perfectCore P₀)).map (MulAut.conj t).toMonoidHom :=
            Subgroup.map_mono hB
          _ = pCoreOf 2 (perfectCore P₁) := hR0
      · refine le_inf ?_ hB
        calc A ⊓ L = (A ⊓ L).map (MulAut.conj t).toMonoidHom := hmap.symm
          _ ≤ (pCoreOf 2 (perfectCore P₁)).map (MulAut.conj t).toMonoidHom :=
            Subgroup.map_mono hB
          _ = pCoreOf 2 (perfectCore P₀) := hR1
    have hcardB : Nat.card ↥(A ⊓ L) ≤ 2 ^ n := card_le_of_swap h ht h0 hBin hBt
    have hAle : ¬ A ≤ L := by
      intro hAL
      rw [inf_eq_left.mpr hAL] at hcardB
      exact (not_le.mpr hcard) hcardB
    obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAle
    have hBa : ∀ b ∈ A ⊓ L, a * b = b * a := fun b hb => hA2.comm haA hb.1
    have hcardB2 : Nat.card ↥(A ⊓ L) ≤ 2 ^ (n / 2) :=
      card_le_of_stab h (hAT haA) haL (hAS a haA) ht h0 hBin hBa hBt
    have hcardA : Nat.card ↥A ≤ 2 * 2 ^ (n / 2) :=
      (h.out A hAT hA2).trans (Nat.mul_le_mul_left 2 hcardB2)
    have h2 : 2 * 2 ^ (n / 2) = 2 ^ (n / 2 + 1) := by
      rw [pow_succ]
      exact Nat.mul_comm _ _
    have hn : 2 ≤ n := h.two_le
    have h3 : 2 ^ (n / 2 + 1) ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by
        have hdiv := Nat.div_lt_self (n := n) (k := 2) (by omega) (by norm_num)
        omega)
    exact (not_le.mpr hcard) (hcardA.trans (h2.le.trans h3))

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

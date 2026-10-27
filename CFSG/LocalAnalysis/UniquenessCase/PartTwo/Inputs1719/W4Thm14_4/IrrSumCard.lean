module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ye
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81

private theorem card_eq_of_le_sup_of_inf_eq_bot {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {A B I : Subgroup W}
    (hAstab : StableUnder X A) (hBstab : StableUnder X B)
    (hBirr : ∀ J, StableUnder X J → J ≤ B → J = ⊥ ∨ J = B)
    (hdisjAB : A ⊓ B = ⊥) (hIA : I ⊓ A = ⊥)
    (hI : IsIrrOn X I ⊥) (hIle : I ≤ A ⊔ B) :
    Nat.card ↥I = Nat.card ↥B := by
  have hC : (I ⊔ A) ⊓ B = ⊥ ∨ (I ⊔ A) ⊓ B = B :=
    hBirr _ (stableUnder_inf (stableUnder_sup hI.2.1 hAstab) hBstab) inf_le_right
  have hcard : ∀ U V : Subgroup W, U ⊓ V = ⊥ →
      Nat.card ↥(U ⊔ V) = Nat.card ↥U * Nat.card ↥V := fun U V h =>
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U V
      (by rw [CommGroup.normalizer_eq_top]; exact le_top) (disjoint_iff.mpr h)
  have hcardIA := hcard I A hIA
  have hcardAB := hcard A B hdisjAB
  rcases hC with hC | hC
  ·
    have hcardIAB := hcard (I ⊔ A) B hC
    have hsup_eq : (I ⊔ A) ⊔ B = A ⊔ B := by
      rw [sup_assoc, sup_eq_right.mpr hIle]
    have hI1 : Nat.card ↥I = 1 := by
      have hh : Nat.card ↥I * (Nat.card ↥A * Nat.card ↥B) = Nat.card ↥A * Nat.card ↥B := by
        rw [← Nat.mul_assoc, ← hcardIA, ← hcardIAB, hsup_eq, hcardAB]
      exact Nat.mul_right_cancel (Nat.mul_pos Nat.card_pos Nat.card_pos)
        (by rw [Nat.one_mul]; exact hh)
    exact absurd (Subgroup.eq_bot_of_card_eq I hI1) hI.1.ne'
  ·
    have hsup_eq : I ⊔ A = A ⊔ B :=
      le_antisymm (sup_le hIle le_sup_left) (sup_le le_sup_right (hC ▸ inf_le_left))
    have hh : Nat.card ↥A * Nat.card ↥I = Nat.card ↥A * Nat.card ↥B := by
      rw [mul_comm (Nat.card ↥A), ← hcardIA, hsup_eq, hcardAB, mul_comm]
    exact Nat.mul_left_cancel Nat.card_pos hh

private theorem exists_card_eq_card_of_le_iSup {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} :
    ∀ {n : ℕ} (M : Fin n → Subgroup W),
      (∀ i, M i ⊓ (⊥ ⊔ ⨆ (j : Fin n) (_ : j ≠ i), M j) ≤ ⊥) →
      (∀ i, IsIrrOn X (M i) ⊥) →
      ∀ {I : Subgroup W}, IsIrrOn X I ⊥ → I ≤ ⨆ i, M i →
      ∃ i, Nat.card ↥I = Nat.card ↥(M i) := by
  intro n
  induction n with
  | zero =>
      intro M hind hirr I hI hIle
      have hbot : I = ⊥ := le_bot_iff.mp (by simpa using hIle)
      exact absurd hbot hI.1.ne'
  | succ n ih =>
      intro M hind hirr I hI hIle
      classical
      set A : Subgroup W := ⨆ i : Fin n, M i.castSucc with hA
      set B : Subgroup W := M (Fin.last n) with hB
      have hAstab : StableUnder X A := by
        rw [hA]
        exact stableUnder_iSup fun i => (hirr i.castSucc).2.1
      have hBstab : StableUnder X B := by
        rw [hB]
        exact (hirr (Fin.last n)).2.1
      have hsplit : (⨆ i : Fin (n + 1), M i) = A ⊔ B := by
        rw [hA, hB]
        refine le_antisymm (iSup_le fun i => ?_)
          (sup_le (iSup_le fun i => le_iSup M _) (le_iSup M _))
        refine Fin.lastCases ?_ ?_ i
        · exact le_sup_right
        · intro j
          exact le_sup_of_le_left (le_iSup (fun i : Fin n => M i.castSucc) j)
      have hIle' : I ≤ A ⊔ B := hsplit ▸ hIle
      by_cases hIA : I ≤ A
      ·
        have hind' : ∀ i : Fin n, M i.castSucc ⊓
            (⊥ ⊔ ⨆ (j : Fin n) (_ : j ≠ i), M j.castSucc) ≤ ⊥ := by
          intro i
          refine le_trans (inf_le_inf le_rfl ?_) (hind i.castSucc)
          refine sup_le bot_le ?_
          refine iSup_le fun j => iSup_le fun hji => ?_
          exact le_sup_of_le_right (le_iSup₂_of_le
            (f := fun (k : Fin (n + 1)) (_ : k ≠ i.castSucc) => M k)
            j.castSucc (fun h => hji (Fin.castSucc_inj.mp h)) le_rfl)
        obtain ⟨i, hi⟩ := ih (fun i : Fin n => M i.castSucc) hind'
          (fun i => hirr i.castSucc) hI hIA
        exact ⟨i.castSucc, hi⟩
      ·
        have hIA' : I ⊓ A = ⊥ := by
          have hstable : StableUnder X (I ⊓ A) := stableUnder_inf hI.2.1 hAstab
          rcases hI.2.2.2 (I ⊓ A) hstable bot_le inf_le_left with h | h
          · exact h
          · exact absurd (h ▸ inf_le_right) hIA
        have hIR : ∀ J, StableUnder X J → J ≤ B → J = ⊥ ∨ J = B := by
          intro J hJ hle
          rw [hB] at hle
          exact (hirr (Fin.last n)).2.2.2 J hJ bot_le hle
        have hle : A ≤ ⊥ ⊔ ⨆ (j : Fin (n + 1)) (_ : j ≠ Fin.last n), M j := by
          rw [hA]
          refine iSup_le fun i => ?_
          exact le_sup_of_le_right (le_iSup₂_of_le
            (f := fun (k : Fin (n + 1)) (_ : k ≠ Fin.last n) => M k)
            i.castSucc (Fin.castSucc_ne_last i) le_rfl)
        have hdisjAB : A ⊓ B = ⊥ := by
          refine le_bot_iff.mp ?_
          rw [inf_comm]
          refine le_trans (inf_le_inf le_rfl hle) ?_
          rw [hB]
          exact hind (Fin.last n)
        have hIB := card_eq_of_le_sup_of_inf_eq_bot hAstab hBstab hIR hdisjAB hIA' hI hIle'
        rw [hB] at hIB
        exact ⟨Fin.last n, hIB⟩

theorem exists_card_eq_of_isIrrOn {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {n : ℕ} (M : Fin n → Subgroup W)
    (hind : ∀ i, M i ⊓ (⊥ ⊔ ⨆ (j : Fin n) (_ : j ≠ i), M j) ≤ ⊥)
    (hsup : (⊥ ⊔ ⨆ i, M i) = ⊤) (hirr : ∀ i, IsIrrOn X (M i) ⊥) {I : Subgroup W}
    (hI : IsIrrOn X I ⊥) : ∃ i, Nat.card ↥I = Nat.card ↥(M i) := by
  have hIle : I ≤ ⨆ i, M i := by
    have h : I ≤ ⊥ ⊔ ⨆ i, M i := hsup.symm ▸ le_top
    simpa using h
  exact exists_card_eq_card_of_le_iSup M hind hirr hI hIle

theorem card_eq_prod_of_indep {W : Type} [CommGroup W] [Finite W] {n : ℕ}
    (M : Fin n → Subgroup W) (hind : ∀ i, M i ⊓ (⊥ ⊔ ⨆ (j : Fin n) (_ : j ≠ i), M j) ≤ ⊥)
    (hsup : (⊥ ⊔ ⨆ i, M i) = ⊤) : Nat.card W = ∏ i, Nat.card ↥(M i) := by
  have hiSup : (⨆ i, M i) = ⊤ := by simpa using hsup
  have hindI : iSupIndep M := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, ← le_bot_iff]
    simpa using hind i
  have hcomm : Pairwise fun i j : Fin n => ∀ x y : W, x ∈ M i → y ∈ M j → Commute x y :=
    fun _ _ _ x y _ _ => mul_comm x y
  rw [← Subgroup.card_top (G := W), ← hiSup]
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.P22y.card_iSup_of_iSupIndep hcomm hindI

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

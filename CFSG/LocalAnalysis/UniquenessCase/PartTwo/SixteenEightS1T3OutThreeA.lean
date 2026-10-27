module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCJ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

theorem s16t3_eq_of_iso_of_card_quot_three (helem : ∀ w : W, w * w = 1)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hcomm : commSub ⊤ L = ⊤)
    (hsum : SumOfNatShape L (⊤ : Subgroup W) (fixV L) 3)
    (hcard : Nat.card {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) // XMod.IsIrr ↥L Y} = 3)
    {Y Y' : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))} (hY : XMod.IsIrr ↥L Y)
    (hY' : XMod.IsIrr ↥L Y') (hiso : XMod.Iso ↥L Y' Y) : Y' = Y := by
  classical
  have hQ : ∀ q : W ⧸ modFix L (⊤ : Subgroup W), q ^ 2 = 1 := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, pow_two, helem w, QuotientGroup.mk_one]
  obtain ⟨I, hnat, hS, hind, htop⟩ := s16t3_quot_summands (L := L) hq hsum
  let S : Fin 3 → Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) :=
    fun i => tilde L (⊤ : Subgroup W) (I i)
  have hS' : ∀ i, XMod.IsIrr ↥(⊤ : Subgroup ↥L) (S i) :=
    fun i => (s16t3_isIrr_top_iff (S i)).2 (hS i)
  have hE : ∀ i, Nat.card (Module.End ↥(XMod.opRing ↥(⊤ : Subgroup ↥L)
      (W ⧸ modFix L (⊤ : Subgroup W))) ↥(XMod.toSubmod (hS' i).1)) = 2 :=
    fun i => s16t3_card_end_eq_two_of_endUnits (hS' i)
      (s16t3_endUnitsTrivial_tilde (L := L) hq (hnat i))
  have hn : ∀ i, Nat.card {J : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
      XMod.IsIrr ↥(⊤ : Subgroup ↥L) J ∧ XMod.Iso ↥(⊤ : Subgroup ↥L) J (S i)} =
      2 ^ (Nat.card {k : Fin 3 // XMod.Iso ↥(⊤ : Subgroup ↥L) (S k) (S i)}) - 1 :=
    fun i => s16t3_card_iso_type hQ (hS' i)
      (s16t3_isotypicOfLength_isoComp hS' hind htop (hS' i)) (hE i)
  have hYtop : XMod.IsIrr ↥(⊤ : Subgroup ↥L) Y := (s16t3_isIrr_top_iff Y).2 hY
  have hY'top : XMod.IsIrr ↥(⊤ : Subgroup ↥L) Y' := (s16t3_isIrr_top_iff Y').2 hY'
  have hisotop : XMod.Iso ↥(⊤ : Subgroup ↥L) Y' Y := (s16t3_iso_top_iff Y' Y).2 hiso
  have hex : ∀ Z : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)),
      XMod.IsIrr ↥(⊤ : Subgroup ↥L) Z → ∃ i, XMod.Iso ↥(⊤ : Subgroup ↥L) Z (S i) :=
    fun Z hZ => CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup (S := S) hS' hZ
      (by rw [htop]; exact le_top)
  obtain ⟨i, hi⟩ := hex Y hYtop
  by_contra hne
  let A := {J : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
      XMod.IsIrr ↥(⊤ : Subgroup ↥L) J ∧ XMod.Iso ↥(⊤ : Subgroup ↥L) J (S i)}
  let B := {Z : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
      XMod.IsIrr ↥(⊤ : Subgroup ↥L) Z}
  let c : ℕ := Nat.card {k : Fin 3 // XMod.Iso ↥(⊤ : Subgroup ↥L) (S k) (S i)}
  have hAcard : Nat.card A = 2 ^ c - 1 := hn i
  have h2A : 2 ≤ Nat.card A := by
    haveI : Nontrivial A :=
      ⟨⟨Y, hYtop, hi⟩, ⟨Y', hY'top, hisotop.trans hi⟩,
        fun h => hne (Subtype.ext_iff.mp h).symm⟩
    have h := Finite.one_lt_card (α := A)
    omega
  have hAB : Nat.card A ≤ Nat.card B :=
    Nat.card_le_card_of_injective (fun J : A => (⟨J.1, J.2.1⟩ : B))
      (fun _ _ hab => Subtype.ext (congrArg (fun J : B => J.1) hab))
  have hBcard : Nat.card B = 3 := by
    have h := s16t3_card_irr_top (A := ↥L) (Q := W ⧸ modFix L (⊤ : Subgroup W))
    change Nat.card {Z : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
      XMod.IsIrr ↥(⊤ : Subgroup ↥L) Z} = 3
    rw [h]
    exact hcard
  have hc2 : c = 2 := by
    have h2c : 2 ≤ 2 ^ c - 1 := by rw [← hAcard]; exact h2A
    have h3c : 2 ^ c - 1 ≤ 3 := by
      rw [← hAcard]
      exact le_trans hAB (le_of_eq hBcard)
    have h1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    have hge2 : 2 ≤ c := by
      have hlt : 2 ^ 1 < 2 ^ c := by
        rw [Nat.pow_one]
        have h : 3 ≤ 2 ^ c := by omega
        omega
      have := (Nat.pow_lt_pow_iff_right (show (1 : ℕ) < 2 by norm_num)).1 hlt
      omega
    have hle2 : c ≤ 2 := by
      have hle4 : 2 ^ c ≤ 2 ^ 2 := by
        show 2 ^ c ≤ 4
        omega
      exact (Nat.pow_le_pow_iff_right (show (1 : ℕ) < 2 by norm_num)).1 hle4
    omega
  have hA3 : Nat.card A = 3 := by rw [hAcard, hc2]; norm_num
  have hall : ∀ Z : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)),
      XMod.IsIrr ↥(⊤ : Subgroup ↥L) Z → XMod.Iso ↥(⊤ : Subgroup ↥L) Z (S i) := by
    intro Z hZ
    by_contra hZi
    have hlt := Finite.card_subtype_lt
      (p := fun Z' : B => XMod.Iso ↥(⊤ : Subgroup ↥L) Z'.1 (S i))
      (x := (⟨Z, hZ⟩ : B)) hZi
    have heq : Nat.card {Z' : B // XMod.Iso ↥(⊤ : Subgroup ↥L) Z'.1 (S i)} =
        Nat.card A :=
      Nat.card_congr
        { toFun := fun Z' => ⟨Z'.1.1, Z'.1.2, Z'.2⟩
          invFun := fun J => ⟨⟨J.1, J.2.1⟩, J.2.2⟩
          left_inv := fun Z' => rfl
          right_inv := fun J => rfl }
    rw [heq, hBcard, hA3] at hlt
    exact absurd hlt (lt_irrefl 3)
  have hci3 : Nat.card {k : Fin 3 // XMod.Iso ↥(⊤ : Subgroup ↥L) (S k) (S i)} = 3 := by
    have hcard' : Nat.card {k : Fin 3 // XMod.Iso ↥(⊤ : Subgroup ↥L) (S k) (S i)} =
        Nat.card (Fin 3) :=
      Nat.card_congr
        { toFun := fun k => k.1
          invFun := fun k => ⟨k, hall (S k) (hS' k)⟩
          left_inv := fun k => rfl
          right_inv := fun k => rfl }
    rw [hcard']
    simp
  have hc3 : c = 3 := hci3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

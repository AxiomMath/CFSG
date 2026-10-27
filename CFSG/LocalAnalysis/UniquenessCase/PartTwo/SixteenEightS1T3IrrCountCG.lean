module

public import CFSG.Quasithin.Background.SmithD39TwoSocle
public import CFSG.Quasithin.Background.SmithD39TwoMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem s16t3_isotypicOfLength_isoComp [Finite Q] {Λ : Subgroup Γ} {ι : Type*} [Finite ι]
    {S : ι → Subgroup Q} (hS : ∀ i, XMod.IsIrr ↥Λ (S i)) (hind : iSupIndep S)
    (htop : (⨆ i, S i) = ⊤) {Y : Subgroup Q} (hY : XMod.IsIrr ↥Λ Y) :
    IsotypicOfLength ↥Λ (isoComp ↥Λ Y) Y (Nat.card {i : ι // XMod.Iso ↥Λ (S i) Y}) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  set T : Finset ι := Finset.univ.filter (fun i => XMod.Iso ↥Λ (S i) Y) with hT
  set P : Subgroup Q := ⨆ i ∈ T, S i with hP
  set R : Subgroup Q := ⨆ i : {i : ι // i ∉ T}, S i.1 with hR
  have hmemT : ∀ i : ι, i ∈ T ↔ XMod.Iso ↥Λ (S i) Y := by
    intro i
    simp [hT]
  have hP_le : P ≤ isoComp ↥Λ Y := by
    rw [hP]
    refine iSup₂_le fun i hi => ?_
    rw [hT] at hi
    exact le_isoComp (hS i) (Finset.mem_filter.1 hi).2
  have hRinv : XMod.IsInv ↥Λ R := by
    rw [hR]
    exact XMod.isInv_iSup fun i => (hS i.1).1
  have hYR : isoComp ↥Λ Y ⊓ R = ⊥ := by
    by_contra hne
    have hinv : XMod.IsInv ↥Λ (isoComp ↥Λ Y ⊓ R) := (isInv_isoComp Y).inf hRinv
    obtain ⟨J, hJle, hJ⟩ := CFSG.Quasithin.SmithD391.exists_isIrr_le hinv hne
    have hJY : XMod.Iso ↥Λ J Y := by
      obtain ⟨J', hJ'⟩ := CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup
        (S := fun J' : {J' : Subgroup Q // XMod.IsIrr ↥Λ J' ∧ XMod.Iso ↥Λ J' Y} =>
          (J' : Subgroup Q)) (fun J' => J'.2.1) hJ (hJle.trans inf_le_left)
      exact hJ'.trans J'.2.2
    obtain ⟨i, hJi⟩ := CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup
      (S := fun i : {i : ι // i ∉ T} => S i.1) (fun i => hS i.1) hJ
      (by rw [← hR]; exact hJle.trans inf_le_right)
    exact i.2 ((hmemT i.1).2 ((XMod.Iso.symm hJ.1 hJi).trans hJY))
  have hPR_sup : P ⊔ R = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun i => ?_
    by_cases hi : i ∈ T
    · refine le_trans ?_ le_sup_left
      rw [hP]
      exact le_iSup₂ (f := fun i (_ : i ∈ T) => S i) i hi
    · refine le_trans ?_ le_sup_right
      rw [hR]
      exact le_iSup (fun j : {j : ι // j ∉ T} => S j.1) ⟨i, hi⟩
  have hiso : isoComp ↥Λ Y = P := by
    have hmod : isoComp ↥Λ Y ⊓ (P ⊔ R) = P := by
      rw [inf_comm, sup_inf_assoc_of_le R hP_le, inf_comm, hYR, sup_bot_eq]
    have h1 : isoComp ↥Λ Y = isoComp ↥Λ Y ⊓ (P ⊔ R) := by rw [hPR_sup, inf_top_eq]
    exact h1.trans hmod
  have hrk_eq : ∀ i ∈ T, rk ↥(S i) = rk ↥Y := by
    intro i hi
    rw [hT] at hi
    obtain ⟨φ, _⟩ := (Finset.mem_filter.1 hi).2
    unfold rk
    rw [Nat.card_congr φ.toEquiv]
  have hrkP : rk ↥P = ∑ i ∈ T, rk ↥(S i) := by
    rw [hP]
    exact rk_iSup_biSup_eq_sum S hind T
  have hsum_eq : ∑ i ∈ T, rk ↥(S i) = T.card * rk ↥Y := by
    rw [Finset.sum_congr rfl (fun i hi => hrk_eq i hi), Finset.sum_const, smul_eq_mul]
  have hTcard : T.card = Nat.card {i : ι // XMod.Iso ↥Λ (S i) Y} := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_of_subtype T fun i => by simp [hT]).symm
  exact ⟨isInv_isoComp Y, le_rfl, by rw [hiso, hrkP, hsum_eq, hTcard]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

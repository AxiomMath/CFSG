module

public import CFSG.Timmesfeld.ARS.LinearRel
public import CFSG.Timmesfeld.ARS.Sec5Count

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Linear

structure IsRootFrame (R : Set (Subgroup G)) (N : ℕ) (X : Fin N → Fin N → Subgroup G) :
    Prop where
  mem : ∀ i j, i ≠ j → X i j ∈ R
  opposite : ∀ i j, i ≠ j → Opposite (X i j) (X j i)
  commuting : ∀ i j k l, i ≠ j → k ≠ l → i ≠ l → k ≠ j → Commuting (X i j) (X k l)
  special : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → Special R (X i j) (X j k) ∧ ⁅X i j, X j k⁆ = X i k
  iSup_eq_top : (⨆ i, ⨆ j, ⨆ (_ : i ≠ j), X i j) = ⊤

section Span

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
  {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ)
include hR hiso hnd hΩ hΔ

theorem IsFrame.card_iSup_row {n : ℕ} {P : Fin n → Set (Subgroup G)} {Q : Fin n → Subgroup G}
    (hfr : IsFrame R Δ P Q) {E : Subgroup G} (hE : E ∈ R) (i₀ : Fin n)
    (X : Fin n → Subgroup G) (hX : ∀ j, j ≠ i₀ → X j ∈ P i₀ ∧ X j ∈ dualPoint R Δ (Q j)) :
    Nat.card ↥(⨆ j ∈ (Finset.univ : Finset (Fin n)).erase i₀, X j) = Nat.card E ^ (n - 1) := by
  have h := (card_iSup_eq_pow hR hiso hnd hΩ hΔ (hfr.isPoint i₀) hE X P
    ((Finset.univ : Finset (Fin n)).erase i₀) (fun j hj => (hX j (Finset.ne_of_mem_erase hj)).1)
    (fun j _ => hfr.isPoint j) fun j hj k _ => by
      rw [hfr.le_stabSet_iff_of_mem (hX j (Finset.ne_of_mem_erase hj)).2 k]
      exact ne_comm).1
  rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h

theorem IsFrame.card_iSup_col {n : ℕ} {P : Fin n → Set (Subgroup G)} {Q : Fin n → Subgroup G}
    (hfr : IsFrame R Δ P Q) {E : Subgroup G} (hE : E ∈ R) (j₀ : Fin n)
    (X : Fin n → Subgroup G) (hX : ∀ i, i ≠ j₀ → X i ∈ P i ∧ X i ∈ dualPoint R Δ (Q j₀)) :
    Nat.card ↥(⨆ i ∈ (Finset.univ : Finset (Fin n)).erase j₀, X i) = Nat.card E ^ (n - 1) := by
  have hC₀ := hfr.mem j₀
  have hΔ' := isTI_dualPoint hR hiso hnd hΩ hΔ hC₀
  have hD : ∀ k, IsPoint (dualPoint R Δ (Q j₀)) (dualPoint R Δ (Q k)) := fun k =>
    (isPoint_dualPoint_iff hR hC₀).2 ⟨Q k, hfr.mem k, rfl⟩
  have h := (card_iSup_eq_pow hR hiso hnd hΩ hΔ' (hD j₀) hE X (fun k => dualPoint R Δ (Q k))
    ((Finset.univ : Finset (Fin n)).erase j₀) (fun i hi => (hX i (Finset.ne_of_mem_erase hi)).2)
    (fun k _ => hD k) fun i hi k _ =>
      hfr.le_stabSet_dualPoint_iff_of_mem hR hiso hnd hΩ hΔ
        (hX i (Finset.ne_of_mem_erase hi)).1 k).1
  rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h

theorem IsFrame.exists_members {n : ℕ} {P : Fin n → Set (Subgroup G)} {Q : Fin n → Subgroup G}
    (hfr : IsFrame R Δ P Q) :
    ∃ X : Fin n → Fin n → Subgroup G,
      ∀ i j, i ≠ j → X i j ∈ P i ∧ X i j ∈ dualPoint R Δ (Q j) := by
  have hex : ∀ i j, ∃ X, i ≠ j → X ∈ P i ∧ X ∈ dualPoint R Δ (Q j) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨⊥, fun h => absurd hij h⟩
    · obtain ⟨X, hX1, hX2⟩ := hfr.exists_mem hR hiso hnd hΩ hΔ hij
      exact ⟨X, fun _ => ⟨hX1, hX2⟩⟩
  choose X hX using hex
  exact ⟨X, hX⟩

theorem IsFrame.pow_le_card_gen {n : ℕ} {P : Fin n → Set (Subgroup G)} {Q : Fin n → Subgroup G}
    (hfr : IsFrame R Δ P Q) {E : Subgroup G} (hE : E ∈ R) (i : Fin n) :
    Nat.card E ^ (n - 1) ≤ Nat.card ↥(gen (P i)) ∧
      Nat.card E ^ (n - 1) ≤ Nat.card ↥(gen (dualPoint R Δ (Q i))) := by
  obtain ⟨X, hX⟩ := hfr.exists_members hR hiso hnd hΩ hΔ
  refine ⟨?_, ?_⟩
  · rw [← hfr.card_iSup_row hR hiso hnd hΩ hΔ hE i (X i) fun j hj => hX i j (Ne.symm hj)]
    exact Subgroup.card_le_of_le (iSup₂_le fun j hj =>
      le_gen (hX i j (Ne.symm (Finset.ne_of_mem_erase hj))).1)
  · rw [← hfr.card_iSup_col hR hiso hnd hΩ hΔ hE i (fun k => X k i) fun k hk => hX k i hk]
    exact Subgroup.card_le_of_le
      (iSup₂_le fun j hj => le_gen (hX j i (Finset.ne_of_mem_erase hj)).2)

theorem pow_le_card_gen_dualPoint {E : Subgroup G} (hE : E ∈ R) {C : Subgroup G} (hC : C ∈ R)
    {k : ℕ} (hk : Nat.card E ^ k = Nat.card ↥(gen (dualPoint R Δ C))) :
    Nat.card E ^ k ≤ Nat.card ↥(gen Δ) := by
  obtain ⟨P, Q, hfr⟩ := exists_isFrame hR hiso hnd hΩ hΔ hE hC (k + 1) (Nat.succ_pos k)
    (by simp [hk])
  have := (hfr.pow_le_card_gen hR hiso hnd hΩ hΔ hE 0).1
  rwa [Nat.add_sub_cancel, (hfr.isPoint 0).card_gen] at this

theorem card_gen_dualPoint_eq {C : Subgroup G} (hC : C ∈ R) :
    Nat.card ↥(gen (dualPoint R Δ C)) = Nat.card ↥(gen Δ) := by
  obtain ⟨A, hA, -⟩ := hΔ.2.1
  have hAR := hΔ.1 hA
  have hq := one_lt_card_of_mem hR hAR
  obtain ⟨m, hm⟩ := Sec5.exists_card_gen_eq_pow hR hiso hnd hΩ hΔ.isWeakTI hA
  have hΔ' := isTI_dualPoint hR hiso hnd hΩ hΔ hC
  obtain ⟨B, hB, -⟩ := hΔ'.2.1
  obtain ⟨m', hm'⟩ := Sec5.exists_card_gen_eq_pow hR hiso hnd hΩ hΔ'.isWeakTI hB
  rw [hR.card_eq hB.1 hAR] at hm'
  have h1 := pow_le_card_gen_dualPoint hR hiso hnd hΩ hΔ hAR hC hm'.symm
  obtain ⟨Pc, hPc, hCPc⟩ := exists_isPoint_mem hR hΔ hC
  have hdd := dualPoint_dualPoint hR hiso hnd hΩ hΔ hC hPc hCPc
  have h2 := pow_le_card_gen_dualPoint hR hiso hnd hΩ hΔ' hAR hC (k := m)
    (by rw [hdd, hPc.card_gen, hm])
  rw [hm] at h1
  rw [hm'] at h2
  rw [hm', hm, le_antisymm ((Nat.pow_le_pow_iff_right hq).1 h2)
    ((Nat.pow_le_pow_iff_right hq).1 h1)]

theorem exists_isRootFrame {m : ℕ} {A : Subgroup G} (hA : A ∈ Δ)
    (hm : Nat.card ↥(gen Δ) = Nat.card A ^ m) :
    2 ≤ m ∧ ∃ X : Fin (m + 1) → Fin (m + 1) → Subgroup G, IsRootFrame R (m + 1) X := by
  have hAR := hΔ.1 hA
  have hq := one_lt_card_of_mem hR hAR
  have hm2 : 2 ≤ m := by
    obtain ⟨B, hB, C, hC, hBC⟩ := hΔ.2.1
    have hBR := hΔ.1 hB
    have hCR := hΔ.1 hC
    have hcard : Nat.card A ^ 2 ≤ Nat.card ↥(gen Δ) := by
      calc Nat.card A ^ 2 = Nat.card B * Nat.card C := by
            rw [hR.card_eq hBR hAR, hR.card_eq hCR hAR, sq]
        _ ≤ Nat.card ↥(B ⊔ C) := card_mul_card_le_card_sup (inf_eq_bot hR hiso hBR hCR hBC)
        _ ≤ Nat.card ↥(gen Δ) := Subgroup.card_le_of_le (sup_le (le_gen hB) (le_gen hC))
    rw [hm] at hcard
    exact (Nat.pow_le_pow_iff_right hq).1 hcard
  refine ⟨hm2, ?_⟩
  obtain ⟨P, Q, hfr⟩ := exists_isFrame hR hiso hnd hΩ hΔ hAR hAR (m + 1) (Nat.succ_pos m) (by
    rw [Nat.add_sub_cancel, card_gen_dualPoint_eq hR hiso hnd hΩ hΔ hAR, hm])
  obtain ⟨X, hX⟩ := hfr.exists_members hR hiso hnd hΩ hΔ
  refine ⟨X, ⟨fun i j hij => (hX i j hij).2.1, fun i j hij => ?_, fun i j k l hij hkl hil hkj => ?_,
    fun i j k hij hjk hik => ?_, ?_⟩⟩
  · exact hfr.opposite hR hiso hnd hΩ hΔ (hX i j hij).1 (hX i j hij).2 (hX j i (Ne.symm hij)).1
      (hX j i (Ne.symm hij)).2
  · exact hfr.commuting hR hiso hnd hΩ hΔ (hX i j hij).1 (hX i j hij).2 (hX k l hkl).1
      (hX k l hkl).2 hil hkj
  · exact hfr.special hR hiso hnd hΩ hΔ (hX i j hij).1 (hX i j hij).2 (hX j k hjk).1
      (hX j k hjk).2 (hX i k hik).1 (hX i k hik).2 hik
  ·
    set L := ⨆ i, ⨆ j, ⨆ (_ : i ≠ j), X i j with hL
    have hXL : ∀ i j, i ≠ j → X i j ≤ L := fun i j hij =>
      le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le hij le_rfl))
    set i0 : Fin (m + 1) := 0
    set i1 : Fin (m + 1) := 1
    have h01 : i0 ≠ i1 := by
      simp only [i0, i1, ne_eq, Fin.zero_eq_one_iff]
      omega
    have hrow : gen (P i0) ≤ L := by
      have hcard := hfr.card_iSup_row hR hiso hnd hΩ hΔ hAR i0 (X i0)
        fun j hj => hX i0 j (Ne.symm hj)
      have hle : (⨆ j ∈ (Finset.univ : Finset (Fin (m + 1))).erase i0, X i0 j) ≤ gen (P i0) :=
        iSup₂_le fun j hj => le_gen (hX i0 j (Ne.symm (Finset.ne_of_mem_erase hj))).1
      have heq := Subgroup.eq_of_le_of_card_ge hle (by
        rw [hcard, (hfr.isPoint i0).card_gen, hm, Nat.add_sub_cancel])
      rw [← heq]
      exact iSup₂_le fun j hj => hXL i0 j (Ne.symm (Finset.ne_of_mem_erase hj))
    have hcol : gen (dualPoint R Δ (Q i1)) ≤ L := by
      have hcard := hfr.card_iSup_col hR hiso hnd hΩ hΔ hAR i1 (fun k => X k i1)
        fun k hk => hX k i1 hk
      have hle : (⨆ k ∈ (Finset.univ : Finset (Fin (m + 1))).erase i1, X k i1) ≤
          gen (dualPoint R Δ (Q i1)) :=
        iSup₂_le fun k hk => le_gen (hX k i1 (Finset.ne_of_mem_erase hk)).2
      have heq := Subgroup.eq_of_le_of_card_ge hle (by
        rw [hcard, card_gen_dualPoint_eq hR hiso hnd hΩ hΔ (hfr.mem i1), hm, Nat.add_sub_cancel])
      rw [← heq]
      exact iSup₂_le fun k hk => hXL k i1 (Finset.ne_of_mem_erase hk)
    have hA' := hX i0 i1 h01
    have hA₀ := hX i1 i0 (Ne.symm h01)
    have hopp := hfr.opposite hR hiso hnd hΩ hΔ hA'.1 hA'.2 hA₀.1 hA₀.2
    have hΛ : gen (lambdaSet R (X i0 i1)) ≤ L := by
      refine gen_le fun B hB => ?_
      rcases mem_or_mem_dualPoint hR hiso hnd hΩ hΔ (hfr.isPoint i0) hA'.1 hB with h | h
      · exact (le_gen h).trans hrow
      · rw [dualPoint_eq_of_mem hA'.2] at h
        exact (le_gen h).trans hcol
    rw [eq_top_iff, ← gen_lambdaSet_sup_eq_top_of hR hiso hnd hA'.2.1 ⟨hA₀.2.1, hopp⟩]
    exact sup_le hΛ (hXL i1 i0 (Ne.symm h01))

end Span

end Linear

end CFSG.Timmesfeld.ARS

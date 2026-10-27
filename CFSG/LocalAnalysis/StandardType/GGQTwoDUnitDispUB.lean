module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU
public import CFSG.LocalAnalysis.StandardType.GGFrameTBSUDvdModel

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem qtwoDB36_inner_le_primeFormD {K : Type} [Field K] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) :
    CFSG.ComponentClassification.OuterAutomorphisms.inner
        (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ≤
      primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  intro α hα
  obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ α).1 hα
  rw [primeFormD]
  exact ⟨⟨s, s.2.1⟩,
    (congrArg (primeFormConjHom h _) (Subtype.ext rfl)).trans hs.symm⟩

private theorem qtwoDB36_hAI {K : Type} [Field K] {s : ℕ} (h : UnitaryFieldData 2 1 K)
    (hd1 : 1 ≤ s) {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin s) K 2)}
    {A : Subgroup (MulAut L')} (hAinn : A ≤ (MulAut.conj : L' →* MulAut L').range) :
    ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin s) K 2))
        (LargeEvenGUSet (Fin s) K 2), ∀ l : L', x (ψ l) = ψ (a l) := by
  intro a ha
  obtain ⟨l, hl⟩ := hAinn ha
  have hmem : MulAut.conj (ψ l) ∈ InndiagSU.inndiagU h (d := s) (n := 1) hd1 := by
    rw [InndiagSU.inndiagU, Subgroup.mem_comap]
    refine qtwoDB36_inner_le_primeFormD (d := s) (n := 1) h ?_
    have h1 : MulAut.conj (ψ l) ∈
        (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin s) K 2) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin s) K 2))).range := ⟨ψ l, rfl⟩
    rw [InndiagSU.range_conj_eq_comap_inner h (d := s) (n := 1) hd1] at h1
    exact Subgroup.mem_comap.mp h1
  refine ⟨MulAut.conj (ψ l),
    InndiagSU.mem_conjImage_of_mem_inndiagU h (d := s) (n := 1) hmem, fun y => ?_⟩
  rw [← hl, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem qtwoDB36_aut_card
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) {s : ℕ}
    (hs : 7 ≤ s) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin s) K 2)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAinn : A ≤ (MulAut.conj : L' →* MulAut L').range)
    (hcard : 3 ^ (s / 3 + 2) ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = s.factorial := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by
    rw [hK]
    norm_num
  have h : UnitaryFieldData 2 1 K := TableBU.unitaryFieldData_of_card hK' le_rfl
  have hp : (3 : ℕ).Prime := by norm_num
  have hp2 : 3 ≠ 2 := by norm_num
  have hd1 : 1 ≤ s := by omega
  have hAI := qtwoDB36_hAI (s := s) (ψ := ψ) h hd1 hAinn
  by_cases h3 : 3 ∣ s
  · have hdn : (s, 1) ≠ (6, 1) := by
      intro he
      have := congrArg Prod.fst he
      omega
    obtain ⟨S, Θ, Φ, hS, hΘ, hk, hinj, hrg, hΦ, hW⟩ :=
      exists_udPermHom (n := 1) (d := s) (p := 3) hK' le_rfl hdn (by omega) hp
        (by norm_num) h3 hψ hker hperf hA hAI hcard hsc
    have hcardAut : Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) =
        Nat.card (Equiv.Perm (Fin s)) := by
      rw [← hrg]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hcardAut, Nat.card_perm, Nat.card_fin]
  · have hpd : ¬ 3 ∣ s := h3
    have hd3 : 3 ≤ s := by omega
    have hdq : (s, 2 ^ 1) ≠ (3, 2) := by
      intro he
      have := congrArg Prod.fst he
      omega
    have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin s) K (2 ^ 1))) = ⊥ :=
      TableBUE.center_proj_eq_bot hK' hd3 hdq
    have hIp : ∀ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin s) K (2 ^ 1)))
        (LargeEvenGUSet (Fin s) K (2 ^ 1)), φ ^ 3 = 1 →
          φ ∈ Set.range (MulAut.conj :
            LargeEvenProj (LargeEvenSUGroup (Fin s) K (2 ^ 1)) →*
              MulAut (LargeEvenProj (LargeEvenSUGroup (Fin s) K (2 ^ 1)))) :=
      fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK' le_rfl hd3 hdq hp (by norm_num)
        hpd φ hφ hφp
    have hcp := StdSubRestU.ggCenterPrime_unitary hK' le_rfl hd3 hdq hp hp2 hpd
    have hT := UModel.ggTorusPermEltSC_unitary (n := 1) (d := s) (p := 3) hK' le_rfl hd1
      hp hp2 (by norm_num) hpd
    have hSC := ggTorusAutCardSC_of_permEltSC (p := 3) (d := s) hp hp2 hd1 hZ hIp hcp hT
    have h27 : 3 ^ 3 ≤ Nat.card A :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ s / 3 + 2)) hcard
    exact (hSC L' ψ hψ hker hperf A hA hAI h27 hsc).2

end CFSG.StandardType.QTwo

end

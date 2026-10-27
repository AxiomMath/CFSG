module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAction
import CFSG.LocalAnalysis.UniquenessCase.UC1K327Core
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGThreeRankExtremal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

private theorem centralizer_map_mk'_pPrimeCore {X : Type} [Group X] [Finite X] (a : X)
    (hB : IsPGroup 3 (Subgroup.zpowers a)) :
    (Subgroup.centralizer ({a} : Set X)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) =
      Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
          Set (X ⧸ CFSG.pPrimeCore 3 X)) := by
  have hOcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 X)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := X)
  have hOnotdvd : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hOcop
  have h := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3)
    (N := CFSG.pPrimeCore 3 X) hOnotdvd (Q := Subgroup.zpowers a) hB
  have hz1 : Subgroup.centralizer (Subgroup.zpowers a : Set X) =
      Subgroup.centralizer ({a} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hz2 : Subgroup.centralizer
      (Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a) :
        Set (X ⧸ CFSG.pPrimeCore 3 X)) =
      Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
          Set (X ⧸ CFSG.pPrimeCore 3 X)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [MonoidHom.map_zpowers, hz1, hz2] at h
  exact h.symm

private theorem balance_quotient_pPrimeCore {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (hA : CFSG.Open.IsElemAbelian 3 A)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X,
      W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X))) :
    ∀ aq ∈ A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)), aq ≠ 1 →
      ∀ Wq : Subgroup (X ⧸ CFSG.pPrimeCore 3 X),
      Wq ≤ Subgroup.centralizer ({aq} : Set (X ⧸ CFSG.pPrimeCore 3 X)) →
      A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤
        Subgroup.normalizer (Wq : Set (X ⧸ CFSG.pPrimeCore 3 X)) →
      Nat.Coprime (Nat.card Wq) 3 →
      Wq ≤ CFSG.Open.relPPrimeCore 3
        (Subgroup.centralizer ({aq} : Set (X ⧸ CFSG.pPrimeCore 3 X))) := by
  let O : Subgroup X := CFSG.pPrimeCore 3 X
  let π : X →* X ⧸ O := QuotientGroup.mk' O
  have hOcop : Nat.Coprime 3 (Nat.card O) := by
    dsimp [O]; exact CFSG.pPrimeCore_coprime_card (p := 3) (G := X)
  have hker : Nat.Coprime (Nat.card π.ker) 3 := by
    rw [show π.ker = O from QuotientGroup.ker_mk' O]
    exact hOcop.symm
  intro aq haq haq1 Wq hWqC hWqN hWqcop
  obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp haq
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact haq1 (map_one π)
  have hB : IsPGroup 3 (Subgroup.zpowers a) :=
    hA.isPGroup.to_le (Subgroup.zpowers_le.mpr haA)
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  let W₀ : Subgroup X := Wq.comap π ⊓ C
  have hCmap' : C.map π =
      Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
          Set (X ⧸ CFSG.pPrimeCore 3 X)) := by
    simpa [C, O, π] using centralizer_map_mk'_pPrimeCore (X := X) a hB
  have hWqC' : Wq ≤ C.map π := by
    simpa [hCmap'] using hWqC
  have hW₀map : W₀.map π = Wq :=
    CFSG.LocalAnalysis.GorensteinLyons.SteinbergCG.map_comap_inf_of_le_map
      (f := π) (B := C) (S := Wq) hWqC'
  have hAcomap : A ≤ Subgroup.normalizer (Wq.comap π : Set X) :=
    (Subgroup.map_le_iff_le_comap.mp hWqN).trans (Subgroup.le_normalizer_comap π)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩)
  have hAW₀ : A ≤ Subgroup.normalizer (W₀ : Set X) := by
    have hACnorm : A ≤ Subgroup.normalizer (C : Set X) := by
      simpa [C] using hAC.trans Subgroup.le_normalizer
    exact (le_inf hAcomap hACnorm).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcopComap : Nat.Coprime 3 (Nat.card (Wq.comap π)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.coprime_comap_of_coprime_kernel 3 π
      (QuotientGroup.mk'_surjective O) hker.symm Wq hWqcop.symm
  have hcopW₀ : Nat.Coprime (Nat.card W₀) 3 :=
    (Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le (inf_le_left : W₀ ≤ Wq.comap π)) hcopComap).symm
  have hW₀C : W₀ ≤ C := inf_le_right
  have hW₀Y : W₀ ≤ CFSG.Open.relPPrimeCore 3 C :=
    hbal a haA ha1 W₀ (by simpa [W₀, C] using hW₀C) (by simpa [W₀] using hAW₀) hcopW₀
  rw [← hW₀map]
  refine (Subgroup.map_mono hW₀Y).trans ?_
  rw [CoprimeImage.relPPrimeCore_map_of_coprime_ker π hker C, hCmap']

theorem le_pPrimeCore_of_kFactE27Signalizer (hStar : KFactE27Signalizer)
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {P A : Subgroup X}
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hP : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X)))
    {W : Subgroup X} (hAW : A ≤ Subgroup.normalizer (W : Set X))
    (hW : Nat.Coprime (Nat.card W) 3) : W ≤ CFSG.pPrimeCore 3 X := by
  classical
  let O : Subgroup X := CFSG.pPrimeCore 3 X
  let π : X →* X ⧸ O := QuotientGroup.mk' O
  have hcore : CFSG.pPrimeCore 3 (X ⧸ O) = ⊥ := by
    dsimp [O]; exact CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hHyp : UC22.InS3.UC327.Hyp327 (X ⧸ O) (P.map π) (A.map π) := by
    simpa [O, π] using UC22.InS3.UC327.hyp_quotient hX
  have hOnotdvd : ¬ 3 ∣ Nat.card O := by
    dsimp [O]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := X))
  have hker : Nat.Coprime (Nat.card π.ker) 3 := by
    rw [show π.ker = O from QuotientGroup.ker_mk' O]
    dsimp [O]
    exact (CFSG.pPrimeCore_coprime_card (p := 3) (G := X)).symm
  have hinjP : Function.Injective (π.comp P.subtype) := by
    simpa [O, π] using
      CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3)
        (N := O) hOnotdvd hX.sylow.isPGroup
  have hrangeP : (π.comp P.subtype).range = P.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eP : ↥P ≃* ↥(P.map π) :=
    (MonoidHom.ofInjective hinjP).trans (MulEquiv.subgroupCongr hrangeP)
  have hEquiv : Nonempty (↥(P.map π) ≃* UC22.InS3.UC326.ZWr 1) := by
    obtain ⟨e⟩ := hP
    exact ⟨eP.symm.trans e⟩
  have hbalq := balance_quotient_pPrimeCore (X := X) (A := A) hX.elem hbal
  have hmapbot : W.map π = ⊥ :=
    hStar (X ⧸ O) (P.map π) (A.map π) (hK.quotient O) hHyp hEquiv hcore hbalq (W.map π)
      (CoprimeImage.map_le_normalizer_map π hAW)
      (Nat.Coprime.of_dvd_left (Subgroup.card_map_dvd W π) hW)
  have hle : W ≤ π.ker := (Subgroup.map_eq_bot_iff W).mp hmapbot
  rw [show π.ker = O from QuotientGroup.ker_mk' O] at hle
  exact hle

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

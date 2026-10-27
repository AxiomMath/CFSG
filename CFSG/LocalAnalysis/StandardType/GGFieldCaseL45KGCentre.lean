module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXProper
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Certs


theorem largeEvenLabelAll_centerPrime_omegaPlus {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : 4 ≤ lab.rank) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime p R :=
  largeEvenLabelAll_omegaPlus ht h4 fun _ _ _ _ _ =>
    CorFourTwoOpen.ggCenterPrime_omegaPlus hp hp2 (by omega)

theorem coprime_card_center_of_marking_omegaPlus {H : Type} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hmk : LargeEvenMarking H (fun lab _ _ _ _ _ => lab.tag = .D ∧ 4 ≤ lab.rank)) :
    Nat.Coprime p (Nat.card (Subgroup.center H)) := by
  have hM := largeEvenMarking_and_labelAll (S := fun lab => lab.tag = .D ∧ 4 ≤ lab.rank)
    (P' := fun R _ _ _ => GGCenterPrime p R)
    (fun _ _ hS => largeEvenLabelAll_centerPrime_omegaPlus hS.1 hS.2 hp hp2)
    (fun _ _ _ _ _ _ h => h) hmk
  obtain ⟨hperf, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, -, hZ⟩ := largeEvenRawDatum_exists hraw
  set ψ : H →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H)) with hψ
  have hsurj : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center H := by
    intro x hx
    have h1 : θ (QuotientGroup.mk' (Subgroup.center H) x) = 1 := hx
    rw [map_eq_one_iff θ θ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (hZ H ψ hsurj hker hperf)

theorem ggD4CentreThreeInput_holds : GGD4CentreThreeInput := by
  intro H _ _ hmk
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmk
  exact coprime_card_center_of_marking_omegaPlus Nat.prime_three (by norm_num)
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, ht, h4⟩ => ⟨hs, hna, θ, ht, h4.ge⟩) hraw⟩

theorem ggL45CyclicD4Input_of_enlarge' (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (hgr : GGNbrGraphInput) (hKG : GGD4FieldEnlargeEInput) :
    GGL45CyclicD4Input :=
  ggL45CyclicD4Input_of_enlarge hraw hiso hcent hgr hKG ggD4CentreThreeInput_holds

end Certs

end CFSG.StandardType

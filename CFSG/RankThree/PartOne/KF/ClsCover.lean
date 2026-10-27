module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.RankThree.PerfectCover Subgroup

universe u v w

section Card

variable {S : Type u} [Group S] [Finite S]

omit [Finite S] in
theorem card_hopfCover (hS : Group.IsPerfect S) :
    Nat.card (HopfCover S) = Nat.card S * Nat.card (hopfMultiplier S) := by
  have : Group.IsPerfect S := hS
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (hopfMultiplier S)
  have hq : Nat.card (HopfCover S ⧸ hopfMultiplier S) = Nat.card S :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (hopfCoverMap S)
      (hopfCoverMap_surjective (S := S))).toEquiv
  rw [hq] at h
  exact h

end Card

section Universal

variable {S : Type u} [Group S] [Finite S] {E : Type v} [Group E] [Finite E]
  {L : Type w} [Group L] [Finite L]

omit [Finite E] [Finite L] in
theorem exists_hom_of_card_multiplier_eq (hS : Group.IsPerfect S) (hE : Group.IsPerfect E)
    (π : E →* S) (hπ : Function.Surjective π) (hπc : π.ker ≤ Subgroup.center E)
    (hcard : Nat.card (hopfMultiplier S) = Nat.card π.ker)
    (p : L →* S) (hp : Function.Surjective p) (hpc : p.ker ≤ Subgroup.center L) :
    ∃ ρ : E →* L, p.comp ρ = π ∧ (Group.IsPerfect L → Function.Surjective ρ) := by
  have : Group.IsPerfect S := hS
  have : Group.IsPerfect E := hE
  have : Finite (HopfCover S) := finite_hopfCover hS
  have hEsurj : Function.Surjective (hopfLift π hπ hπc) := hopfLift_surjective π hπ hπc
  have hcardE : Nat.card E = Nat.card S * Nat.card π.ker := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    have hq : Nat.card (E ⧸ π.ker) = Nat.card S :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv
    rw [hq] at h
    exact h
  have hbij : Function.Bijective (hopfLift π hπ hπc) := by
    refine hEsurj.bijective_of_nat_card_le ?_
    rw [card_hopfCover hS, hcard, hcardE]
  let e : HopfCover S ≃* E := MulEquiv.ofBijective (hopfLift π hπ hπc) hbij
  refine ⟨(hopfLift p hp hpc).comp e.symm.toMonoidHom, ?_, fun hL => ?_⟩
  · refine MonoidHom.ext fun x => ?_
    have h1 := congrArg (fun f : HopfCover S →* S => f (e.symm x)) (comp_hopfLift p hp hpc)
    have h2 := congrArg (fun f : HopfCover S →* S => f (e.symm x)) (comp_hopfLift π hπ hπc)
    have h3 : hopfLift π hπ hπc (e.symm x) = x := e.apply_symm_apply x
    simp only [MonoidHom.comp_apply] at h1 h2
    calc p ((hopfLift p hp hpc).comp e.symm.toMonoidHom x)
        = hopfCoverMap S (e.symm x) := h1
      _ = π (hopfLift π hπ hπc (e.symm x)) := h2.symm
      _ = π x := by rw [h3]
  · have : Group.IsPerfect L := hL
    exact (hopfLift_surjective p hp hpc).comp e.symm.surjective

end Universal

end CFSG.RankThree.PartOne.KFU

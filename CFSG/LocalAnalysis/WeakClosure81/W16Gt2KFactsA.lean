module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelOvergroupHolds
public import CFSG.StronglyEmbedded.BenderCentre
public import CFSG.CGT.Timmesfeld75.ListWCSzU3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsSz)
open Subgroup

theorem kFacts_card_L2 :
    ∀ (X : Type) [Group X] (n : ℕ), 1 ≤ n → IsL2 X n → Nat.card X = 2 ^ n * (4 ^ n - 1) :=
  fun _ _ _ hn h => CFSG.Quasithin.H13.card_of_lieModel_L2 hn h

theorem kFacts_card_Sz :
    ∀ (X : Type) [Group X] (n : ℕ), IsSz X n →
      Nat.card X = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) :=
  fun _ _ _ h => CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.card_of_isSz_two_pow h

theorem kFacts_card_SzGp :
    ∀ (X : Type) [Group X] (n : ℕ), SevenK.IsSzGp X n →
      Nat.card X = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) :=
  fun _ _ _ h => CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.card_of_isSz_two_pow
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))

theorem kFacts_card_PSU2 :
    ∀ (X : Type) [Group X] (n : ℕ), 1 ≤ n → IsPSUGp X 2 n → Nat.card X = 2 ^ n * (4 ^ n - 1) := by
  intro X _ n _ h
  have hadm := CFSG.Blueprint.LieModel.admissible h
  exact absurd hadm.2.2.1 (by decide)

private theorem card_center_sylow_isSzGp {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : SevenK.IsSzGp Y n) (P : Sylow 2 Y) :
    Nat.card (Subgroup.center (P : Subgroup Y)) = 2 ^ n := by
  have hL : CFSG.Blueprint.LieModel Y .twistedB2 0 2 n :=
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hY⟩))
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ := CFSG.CGT.Timmesfeld75.exists_sz_of_lieModel hL
  let e' : Y ≃* CFSG.Theory.Comparator.SzModel a :=
    e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a).symm)
  have h := CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_sz ha e' P
  rw [← CFSG.StronglyEmbedded.BenderCentre.map_center_eq P,
    Subgroup.card_map_of_injective (P : Subgroup Y).subtype_injective] at h
  exact h

private theorem exists_sylow_quotient_card_center {X : Type} [Group X] [Finite X]
    (hodd : Odd (Nat.card (Subgroup.center X))) (P : Sylow 2 X) :
    ∃ Q : Sylow 2 (X ⧸ Subgroup.center X),
      Nat.card (Subgroup.center (P : Subgroup X)) =
        Nat.card (Subgroup.center (Q : Subgroup (X ⧸ Subgroup.center X))) := by
  set π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) with hπ
  let Q : Sylow 2 (X ⧸ Subgroup.center X) := Sylow.mapSurjective (f := π)
    (QuotientGroup.mk'_surjective _) P
  have hQ : (Q : Subgroup (X ⧸ Subgroup.center X)) = (P : Subgroup X).map π :=
    Sylow.coe_mapSurjective (f := π) (QuotientGroup.mk'_surjective _) P
  have hinj : Function.Injective (π.comp (P : Subgroup X).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : (x : X) ∈ Subgroup.center X := by
      have := hx
      simpa [hπ, QuotientGroup.eq_one_iff] using this
    obtain ⟨k, hk⟩ := P.isPGroup' x
    have h1 : orderOf (x : X) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hk
    have h2 : orderOf (x : X) ∣ Nat.card (Subgroup.center X) := by
      have := orderOf_dvd_natCard (⟨x, hxZ⟩ : Subgroup.center X)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (Subgroup.center X)) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff] at h3
    exact Subtype.ext h3
  refine ⟨Q, ?_⟩
  rw [hQ]
  have e : (P : Subgroup X) ≃* (P : Subgroup X).map π :=
    (MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]))
  exact Nat.card_congr (Subgroup.centerCongr e).toEquiv

private theorem card_eq_card_center_of_forall_mem {X : Type} [Group X] {T W : Subgroup X}
    (hW : ∀ x : X, x ∈ W ↔ x ∈ T ∧ ∀ y ∈ T, x * y = y * x) :
    Nat.card W = Nat.card (Subgroup.center T) := by
  have hmap : (Subgroup.center T).map T.subtype = W := by
    ext x
    rw [hW x]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, fun y hy => ?_⟩
      have := Subgroup.mem_center_iff.mp hz ⟨y, hy⟩
      exact congrArg Subtype.val this.symm
    · rintro ⟨hxT, hx⟩
      refine ⟨⟨x, hxT⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
      exact Subtype.ext (hx y y.2).symm
  rw [← hmap, Subgroup.card_map_of_injective T.subtype_injective]

theorem kFacts_card_suzukiRoot :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (W : Subgroup X),
      Odd (Nat.card (Subgroup.center X)) → SevenK.IsSzGp (X ⧸ Subgroup.center X) n →
        IsSuzukiRootGroup X W → Nat.card W = 2 ^ n := by
  intro X _ _ n W hodd hSz hW
  obtain ⟨T, hT⟩ := hW
  obtain ⟨Q, hQ⟩ := exists_sylow_quotient_card_center hodd T
  rw [card_eq_card_center_of_forall_mem (T := (T : Subgroup X)) hT, hQ]
  exact card_center_sylow_isSzGp hSz Q

end CFSG.LocalAnalysis.WeakClosure81

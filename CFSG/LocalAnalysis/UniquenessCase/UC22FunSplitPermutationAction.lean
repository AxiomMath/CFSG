module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationFrattini
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Kernel
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutation
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutation168
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
import CFSG.GroupTheory.PermutingProducts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F14

open Subgroup CFSG.ComponentClassification.AS81.Sec2
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)
open CFSG.GroupTheory.PermSylowTwo
open scoped Pointwise

theorem le_conjSetStab_of_mapsTo_conj {X : Type} [Group X]
    {Δ : Set (Subgroup X)} {H : Subgroup X}
    (hH : ∀ g ∈ H, Set.MapsTo (Subgroup.map (MulAut.conj g).toMonoidHom) Δ Δ) :
    H ≤ conjSetStab Δ := by
  apply le_conjSetStab
  intro g hg J hJ
  simpa only [rightConjugate, inv_inv] using hH g⁻¹ (H.inv_mem hg) hJ

theorem sylow_le_conjSetStab_funSet {X : Type} [Group X] [Finite X]
    {𝔉 : ∀ {Y : Type} [Group Y], Subgroup Y → Subgroup Y → Prop}
    (hconj : ∀ (g : X) {K : Subgroup X},
      𝔉 ⊤ K → 𝔉 ⊤ (K.map (MulAut.conj g).toMonoidHom)) (P : Sylow 2 X) :
    (P : Subgroup X) ≤ conjSetStab (FunSet 𝔉 X (P : Subgroup X)) :=
  le_conjSetStab_of_mapsTo_conj fun _g hg _ hJ =>
    mem_funSet_map_conj_of_mem_normalizer hconj (Subgroup.le_normalizer hg) hJ

theorem le_normalizer_of_conjPermHom_map_eq_bot {X : Type} [Group X]
    {Δ : Set (Subgroup X)} {T B : Subgroup X} (hT : T ≤ conjSetStab Δ) (hBT : B ≤ T)
    (hB : (B.subgroupOf T).map (conjPermHom hT).rangeRestrict = ⊥) :
    ∀ J ∈ Δ, B ≤ normalizer (J : Set X) := by
  intro J hJ b hb
  have hmem := Subgroup.mem_map_of_mem (conjPermHom hT).rangeRestrict
    (show (⟨b, hBT hb⟩ : T) ∈ B.subgroupOf T from hb)
  rw [hB, Subgroup.mem_bot] at hmem
  have hρ : conjPermHom hT ⟨b, hBT hb⟩ = 1 := congrArg Subtype.val hmem
  exact (conjPermHom_eq_one_iff hT _).mp hρ J hJ

private theorem image_hypotheses {X Y : Type} [Group X] [Finite X] [Group Y]
    {T B : Subgroup X} (P : Sylow 2 X) (hPT : (P : Subgroup X) ≤ T) (hBT : B ≤ T)
    (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X)) (φ : T →* Y) :
    Odd (Nat.card ((B.subgroupOf T).map φ)) ∧
      (¬ 3 ∣ Nat.card ((B.subgroupOf T).map φ)) ∧
      (((B.subgroupOf T).map φ : Subgroup Y) : Set Y) *
          ((((P.subtype hPT : Sylow 2 T) : Subgroup T).map φ : Subgroup Y) : Set Y) =
        ((((P.subtype hPT : Sylow 2 T) : Subgroup T).map φ : Subgroup Y) : Set Y) *
          (((B.subgroupOf T).map φ : Subgroup Y) : Set Y) := by
  have hd : Nat.card ((B.subgroupOf T).map φ) ∣ Nat.card B := by
    have h := Subgroup.card_map_dvd (B.subgroupOf T) φ
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBT).toEquiv] at h
  refine ⟨Odd.of_dvd_nat hBo hd, fun h => hB3 (h.trans hd), ?_⟩
  simpa only [Sylow.coe_subtype] using CFSG.GroupTheory.map_permutes_map φ
    (CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBT hPT hperm)

theorem le_normalizer_of_conjPermHom_quotient_perm {X : Type} [Group X] [Finite X]
    {Δ : Set (Subgroup X)} {T B : Subgroup X} (hT : T ≤ conjSetStab Δ)
    (P : Sylow 2 X) (hPT : (P : Subgroup X) ≤ T) (hBT : B ≤ T)
    (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (α : Type) [Finite α] (N : Subgroup (conjPermHom hT).range) [N.Normal]
    (hN : IsPGroup 2 N) (e : (conjPermHom hT).range ⧸ N ≃* Equiv.Perm α) :
    ∀ J ∈ Δ, B ≤ normalizer (J : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ := (conjPermHom hT).rangeRestrict
  obtain ⟨hodd, hthree, hprod⟩ := image_hypotheses P hPT hBT hBo hB3 hperm φ
  have hbot := eq_bot_of_permutes_sylow_two_of_odd_of_not_three_dvd_of_quotient_perm α N hN e
      ((P.subtype hPT).mapSurjective (conjPermHom hT).rangeRestrict_surjective)
      ((B.subgroupOf T).map φ) hodd hthree hprod
  exact le_normalizer_of_conjPermHom_map_eq_bot hT hBT hbot

theorem le_normalizer_of_conjPermHom_quotient_card_168 {X Q : Type} [Group X] [Finite X]
    [Group Q] [Finite Q] [IsSimpleGroup Q] (hQ : Nat.card Q = 168)
    {Δ : Set (Subgroup X)} {T B : Subgroup X} (hT : T ≤ conjSetStab Δ)
    (P : Sylow 2 X) (hPT : (P : Subgroup X) ≤ T) (hBT : B ≤ T)
    (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (N : Subgroup (conjPermHom hT).range) [N.Normal] (hN : IsPGroup 2 N)
    (e : (conjPermHom hT).range ⧸ N ≃* Q) :
    ∀ J ∈ Δ, B ≤ normalizer (J : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ := (conjPermHom hT).rangeRestrict
  obtain ⟨hodd, hthree, hprod⟩ := image_hypotheses P hPT hBT hBo hB3 hperm φ
  have hbot := eq_bot_of_permutes_sylow_two_of_odd_of_not_three_dvd_of_quotient_card_168 hQ N hN e
      ((P.subtype hPT).mapSurjective (conjPermHom hT).rangeRestrict_surjective)
      ((B.subgroupOf T).map φ) hodd hthree hprod
  exact le_normalizer_of_conjPermHom_map_eq_bot hT hBT hbot

theorem le_normalizer_funSet_of_preserves_of_quotient_perm {X : Type} [Group X] [Finite X]
    {𝔉 : ∀ {Y : Type} [Group Y], Subgroup Y → Subgroup Y → Prop}
    (hconj : ∀ (g : X) {K : Subgroup X},
      𝔉 ⊤ K → 𝔉 ⊤ (K.map (MulAut.conj g).toMonoidHom))
    (P : Sylow 2 X) (B : Subgroup X)
    (hB : ∀ b ∈ B, Set.MapsTo (Subgroup.map (MulAut.conj b).toMonoidHom)
      (FunSet 𝔉 X (P : Subgroup X)) (FunSet 𝔉 X (P : Subgroup X)))
    (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (α : Type) [Finite α]
    (N : Subgroup (conjPermHom (le_refl (conjSetStab (FunSet 𝔉 X (P : Subgroup X))))).range)
    [N.Normal] (hN : IsPGroup 2 N)
    (e : (conjPermHom (le_refl (conjSetStab (FunSet 𝔉 X (P : Subgroup X))))).range ⧸ N ≃*
      Equiv.Perm α) : ∀ J ∈ FunSet 𝔉 X (P : Subgroup X), B ≤ normalizer (J : Set X) :=
  le_normalizer_of_conjPermHom_quotient_perm le_rfl P
    (sylow_le_conjSetStab_funSet hconj P) (le_conjSetStab_of_mapsTo_conj hB)
    hBo hB3 hperm α N hN e

theorem le_normalizer_funSet_of_preserves_of_quotient_card_168 {X Q : Type} [Group X] [Finite X]
    [Group Q] [Finite Q] [IsSimpleGroup Q] (hQ : Nat.card Q = 168)
    {𝔉 : ∀ {Y : Type} [Group Y], Subgroup Y → Subgroup Y → Prop}
    (hconj : ∀ (g : X) {K : Subgroup X},
      𝔉 ⊤ K → 𝔉 ⊤ (K.map (MulAut.conj g).toMonoidHom))
    (P : Sylow 2 X) (B : Subgroup X)
    (hB : ∀ b ∈ B, Set.MapsTo (Subgroup.map (MulAut.conj b).toMonoidHom)
      (FunSet 𝔉 X (P : Subgroup X)) (FunSet 𝔉 X (P : Subgroup X)))
    (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (N : Subgroup (conjPermHom (le_refl (conjSetStab (FunSet 𝔉 X (P : Subgroup X))))).range)
    [N.Normal] (hN : IsPGroup 2 N)
    (e : (conjPermHom (le_refl (conjSetStab (FunSet 𝔉 X (P : Subgroup X))))).range ⧸ N ≃* Q) :
    ∀ J ∈ FunSet 𝔉 X (P : Subgroup X), B ≤ normalizer (J : Set X) :=
  le_normalizer_of_conjPermHom_quotient_card_168 hQ le_rfl P
    (sylow_le_conjSetStab_funSet hconj P) (le_conjSetStab_of_mapsTo_conj hB)
    hBo hB3 hperm N hN e

theorem isPGroup_conjPermHom_range_of_ncard_le_two
    {X : Type} [Group X] [Finite X] (Δ : Set (Subgroup X)) (hΔ : Δ.ncard ≤ 2) :
    IsPGroup 2 (conjPermHom (le_refl (conjSetStab Δ))).range := by
  have hcard : Nat.card Δ ≤ 2 := by simpa only [Nat.card_coe_set_eq] using hΔ
  have hperm : IsPGroup 2 (Equiv.Perm Δ) := by
    refine IsPGroup.of_card (n := Nat.card Δ / 2) ?_
    rw [Nat.card_perm]
    generalize Nat.card Δ = n at hcard ⊢
    interval_cases n <;> rfl
  exact hperm.to_subgroup _

theorem exists_twoKernel_quotient_perm_of_ncard_le_two
    {X : Type} [Group X] [Finite X] (Δ : Set (Subgroup X)) (hΔ : Δ.ncard ≤ 2) :
    let A := (conjPermHom (le_refl (conjSetStab Δ))).range
    ∃ N : Subgroup A, ∃ _hN : N.Normal, IsPGroup 2 N ∧
      Nonempty ((A ⧸ N) ≃* Equiv.Perm (Fin 1)) := by
  dsimp only
  let A := (conjPermHom (le_refl (conjSetStab Δ))).range
  have hA : IsPGroup 2 A := isPGroup_conjPermHom_range_of_ncard_le_two Δ hΔ
  have : Subsingleton (A ⧸ (⊤ : Subgroup A)) := QuotientGroup.subsingleton_quotient_top
  let e : (A ⧸ (⊤ : Subgroup A)) ≃* Equiv.Perm (Fin 1) :=
    MulEquiv.ofBijective (1 : (A ⧸ (⊤ : Subgroup A)) →* Equiv.Perm (Fin 1))
      ⟨fun x y _ => Subsingleton.elim x y, fun σ => ⟨1, Subsingleton.elim _ σ⟩⟩
  exact ⟨⊤, inferInstance, hA.to_subgroup ⊤, ⟨e⟩⟩

section LieTwo


open CFSG.Open CFSG.LocalAnalysis.UniquenessCase

theorem funSet_action_twoKernel_quotient_of_funTwoType
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n p f : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : CFSG.Blueprint.LieModel X t n p f) (htwo : FunTwoType t n) (P : Sylow 2 X) :
    let Δ := FunSet (fundPred (p ^ f)) X (P : Subgroup X)
    let A := (conjPermHom (le_refl (conjSetStab Δ))).range
    ∃ N : Subgroup A, ∃ _hN : N.Normal, IsPGroup 2 N ∧
      Nonempty ((A ⧸ N) ≃* Equiv.Perm (Fin 1)) := by
  apply exists_twoKernel_quotient_perm_of_ncard_le_two
  exact ((kFunCount_holds X t n p f hp hp2 hadm hX P).1 htwo).le.trans (by decide)

end LieTwo

end CFSG.LocalAnalysis.UniquenessCase.UC22.F14

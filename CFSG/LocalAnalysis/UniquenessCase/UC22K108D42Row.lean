module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSylowUnique
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.AutBasic
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutCard
public import CFSG.Quasithin.Vol2.D42SylowGen
public import CFSG.LargeExtraspecial.A2ModOrdCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open Subgroup

section Abstract

variable {Gh : Type} [Group Gh] [Finite Gh]

theorem k108D42_odd_index {S B : Subgroup Gh} (hSn : S.Normal) (hSB : S ⊔ B = ⊤) (hB : Odd (Nat.card B)) :
    Odd S.index := by
  haveI := hSn
  have h : S.index = S.relIndex B := by
    rw [← relIndex_top_right S, ← hSB, relIndex_sup_left B S]
  rw [h]
  exact hB.of_dvd_nat (relIndex_dvd_card S B)

theorem k108D42_le_of_isPGroup_two {S P : Subgroup Gh} (hSn : S.Normal) (hS : Odd S.index)
    (hP : IsPGroup 2 P) : P ≤ S := by
  haveI := hSn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have h1 : S.relIndex P ∣ 2 ^ n := hn ▸ relIndex_dvd_card S P
  have h2 : S.relIndex P ∣ S.index := by
    rw [← relIndex_sup_left P S]
    exact relIndex_dvd_index_of_le le_sup_left
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hodd : Odd (2 ^ i) := hi ▸ hS.of_dvd_nat h2
  have hi0 : i = 0 := by
    by_contra hne
    exact Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 (dvd_pow_self 2 hne))
  rw [hi0, pow_zero] at hi
  exact relIndex_eq_one.1 hi

theorem k108D42_index_le_three {S : Subgroup Gh} (hSn : S.Normal) (hC : centralizer (S : Set Gh) = ⊥)
    (hAut : Nat.card (MulAut ↥S) ≤ 3 * Nat.card ↥S) : S.index ≤ 3 := by
  haveI := hSn
  have h1 := CFSG.EvenSporadicStandard.HSStd.InvCent.Harada.card_le_card_mulAut hC
  have h2 : S.index * Nat.card ↥S ≤ 3 * Nat.card ↥S := by
    rw [S.index_mul_card]
    exact h1.trans hAut
  exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos

theorem k108D42_prime_dvd_card {S : Subgroup Gh} (hS3 : S.index ≤ 3) (h3 : 3 ∣ Nat.card ↥S) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hpG : p ∣ Nat.card Gh) : p ∣ Nat.card ↥S := by
  rw [← S.index_mul_card] at hpG
  rcases hp.dvd_mul.1 hpG with h | h
  · have hpos : 0 < S.index := Nat.pos_of_ne_zero fun h0 => by
      have h4 := S.index_mul_card
      rw [h0, zero_mul] at h4
      exact (Nat.card_pos (α := Gh)).ne h4
    have hp3 : p ≤ 3 := (Nat.le_of_dvd hpos h).trans hS3
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact Nat.not_even_iff_odd.2 hodd even_two
    have : p = 3 := by
      have := hp.two_le
      omega
    exact this ▸ h3
  · exact h

theorem k108D42_le_of_isPGroup {X M P : Subgroup Gh} {p : ℕ} [Fact p.Prime] (hXp : Nat.card X = p)
    (hXM : X ≤ M) (hstar : ∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) (hP : IsPGroup p P)
    (hXP : X ≤ P) : P ≤ M := by
  haveI : IsCyclic ↥X := isCyclic_of_prime_card hXp
  obtain ⟨⟨t, htX⟩, ht⟩ := IsCyclic.exists_generator (α := ↥X)
  have hmem : ∀ x ∈ X, ∃ k : ℤ, t ^ k = x := fun x hx => by
    obtain ⟨k, hk⟩ := ht ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  refine CFSG.SeitzReduction.F4Pilot.le_of_isPGroup_of_unique (hXM htX)
    (fun g hg => hstar g fun x hx => ?_) hP (hXP htX)
  obtain ⟨k, rfl⟩ := hmem x hx
  have e : g⁻¹ * t ^ k * g = (g⁻¹ * t * g) ^ k := by
    simpa only [inv_inv] using (conj_zpow (a := g⁻¹) (b := t) (i := k)).symm
  rw [e]
  exact zpow_mem hg k

theorem k108D42_le_of_sylowGen {S : Subgroup Gh} (hSn : S.Normal) (hC : centralizer (S : Set Gh) = ⊥)
    (hAut : Nat.card (MulAut ↥S) ≤ 3 * Nat.card ↥S) (h3 : 3 ∣ Nat.card ↥S)
    (hgen : ∀ p : ℕ, p.Prime → Odd p → p ∣ Nat.card ↥S →
      ∀ (R : Sylow p ↥S) (Q : Sylow 2 ↥S), (R : Subgroup ↥S) ⊔ Q = ⊤)
    {T B : Subgroup Gh} (hTB : Hyp10 T B) (hSB : S ⊔ B = ⊤) {X M : Subgroup Gh} (hXB : X ≤ B)
    (hXp : (Nat.card X).Prime) (hXo : Odd (Nat.card X)) (hTM : T ≤ M) (hXM : X ≤ M)
    (hstar : ∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) : S ≤ M := by
  haveI := hSn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.card X).Prime := ⟨hXp⟩
  have hTS : T ≤ S :=
    k108D42_le_of_isPGroup_two hSn (k108D42_odd_index hSn hSB hTB.2.2.1) hTB.1.isPGroup
  have hpS : Nat.card X ∣ Nat.card ↥S :=
    k108D42_prime_dvd_card (k108D42_index_le_three hSn hC hAut) h3 hXp hXo (card_subgroup_dvd_card X)
  have hXpg : IsPGroup (Nat.card X) X := IsPGroup.of_card (n := 1) (pow_one _).symm
  obtain ⟨P, hXP⟩ := hXpg.exists_le_sylow
  have hPM : (P : Subgroup Gh) ≤ M := k108D42_le_of_isPGroup rfl hXM hstar P.isPGroup' hXP
  have hnorm : (⊤ : Subgroup Gh) ≤ normalizer (S : Set Gh) := (normalizer_eq_top (H := S)).ge
  have hPS : CFSG.ABGLocalTools.IsSylowOf (Nat.card X) ((P : Subgroup Gh) ⊓ S) S := by
    refine (CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_top, P.isPGroup', ?_⟩).inf_of_le_normalizer le_top hnorm
    rw [relIndex_top_right]
    exact P.not_dvd_index
  have hTS' : CFSG.ABGLocalTools.IsSylowOf 2 T S := by
    have h := hTB.1.inf_of_le_normalizer le_top hnorm
    rwa [inf_eq_left.2 hTS] at h
  obtain ⟨R, hR⟩ := hPS.exists_sylow_eq_subgroupOf
  obtain ⟨Q, hQ⟩ := hTS'.exists_sylow_eq_subgroupOf
  have hle : (R : Subgroup ↥S) ⊔ Q ≤ M.subgroupOf S := by
    rw [hR, hQ]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact mem_subgroupOf.2 (hPM (mem_subgroupOf.1 hy).1)
    · exact mem_subgroupOf.2 (hTM (mem_subgroupOf.1 hy))
  intro s hs
  have hmem : (⟨s, hs⟩ : ↥S) ∈ (R : Subgroup ↥S) ⊔ Q := by
    rw [hgen _ hXp hXo hpS R Q]
    exact mem_top _
  exact mem_subgroupOf.1 (hle hmem)

end Abstract

section Row


theorem k108Row3D4two_holds :
    ∀ (Gh : Type) [Group Gh] [Finite Gh] (S : Subgroup Gh), S.Normal → IsSimpleGroup ↥S →
      (∃ a b : ↥S, a * b ≠ b * a) → centralizer (S : Set Gh) = ⊥ → Is3D4 ↥S 1 →
      ∀ (T B : Subgroup Gh), Hyp10 T B → S ⊔ B = ⊤ →
      ∀ (X M : Subgroup Gh), X ≤ B → (Nat.card X).Prime → Odd (Nat.card X) →
        T ≤ M → X ≤ M → (∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) → S ≤ M := by
  intro Gh _ _ S hSn _ _ hC hS T B hTB hSB X M hXB hXp hXo hTM hXM hstar
  have hL : CFSG.Blueprint.LieModel ↥S .trialityD4 0 2 1 := hS
  have hcard : Nat.card ↥S = 211341312 := CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_trialityD4 hL
  exact k108D42_le_of_sylowGen hSn hC (CFSG.Quasithin.D4Hex.card_mulAut_of_lieModel_d4 ↥S hS).1.le
    (by rw [hcard]; norm_num)
    (fun p hp hodd hpS R Q => CFSG.Quasithin.H13.D42.sylow_sup_sylow_two_eq_top
      (hL.chevalleyExceptionalModel (by decide)) hp hodd hpS R Q)
    hTB hSB hXB hXp hXo hTM hXM hstar

end Row

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10

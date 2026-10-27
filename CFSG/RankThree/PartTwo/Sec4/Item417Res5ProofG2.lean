module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofIn
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open Res417Three Res417Five

namespace Res417Five

@[expose] def K417G2CoverCent : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (X F T : Subgroup H), CFSG.IsQuasisimple X →
    Nat.card (Subgroup.center X) = 3 →
    ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 →
    CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 → F ≤ Subgroup.normalizer (X : Set H) →
    (∀ f ∈ F, ∃ x ∈ X, ∀ y ∈ X, f * y * f⁻¹ = x * y * x⁻¹) →
    F ⊓ Subgroup.centralizer (X : Set H) = ⊥ → T ≤ X → IsPGroup 2 T →
    F ≤ Subgroup.normalizer (T : Set H) → ¬ T ≤ Subgroup.centralizer (F : Set H) →
    ∃ R : Subgroup H, R ≤ X ∧ CFSG.Assembly.IsElemAbelian 3 R ∧ Nat.card R = 27 ∧
      (Subgroup.center X).map X.subtype ≤ R ∧ F ≤ Subgroup.centralizer (R : Set H) ∧
      R ⊓ (F ⊔ Subgroup.centralizer (X : Set H)) ≤ (Subgroup.center X).map X.subtype

end Res417Five

section Certs


theorem item417InG2Rest_of (hK : K417G2CoverCent) : Item417InG2Rest := by
  intro G _ _ L A E c m hconf hZ hM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, T₁, hFA, hF9, hFC, hT₁L, hT₁, hFT₁, hT₁F⟩ :=
    exists_nine_of_isQuad417 hconf.2.2.2.2.1
  have hA := hconf.2.2.2.2.1.1.prop
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := isElemAbelian_of_le hA hFA
  obtain ⟨R, hRL, hRe, hR27, hZR, hFR, hRFC⟩ := hK G L F T₁ hconf.2.2.1.1 hZ hM hFe hF9
    (hFA.trans hconf.2.2.2.2.2.1) (fun f hf => hconf.inner f (hFA hf)) hFC hT₁L hT₁ hFT₁ hT₁F
  have hcC := hconf.mem_centralizer
  have hc3 : orderOf c = 3 := hconf.2.2.2.2.1.2.2.2.1
  have hcA : c ∈ A := hconf.mem_A
  have hZc : (Subgroup.center L).map L.subtype ≤ Subgroup.zpowers c := by
    rintro _ ⟨z, hz, rfl⟩
    have h3 := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨z, hz⟩)
    rw [hZ] at h3
    exact hconf.mem_zpowers_of_mem_center hz (by simpa using congrArg Subtype.val h3)
  have hcZ : c ∈ (Subgroup.center L).map L.subtype := ⟨_, hconf.mem_center, rfl⟩
  have hcF : c ∉ F := fun h => by
    have : c ∈ F ⊓ Subgroup.centralizer (L : Set G) := ⟨h, hcC⟩
    rw [hFC, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hc3
    norm_num at hc3
  set AD := F ⊔ Subgroup.zpowers c with hAD
  have hADA : AD ≤ A := sup_le hFA (Subgroup.zpowers_le.mpr hcA)
  have hADe : CFSG.Assembly.IsElemAbelian 3 AD := isElemAbelian_of_le hA hADA
  have hAD27 : Nat.card AD = 27 := by
    rw [hAD, card_sup_zpowers_eq_three_mul hc3 hcF fun a ha b hb =>
      hcomm a (hFA ha) b ((Subgroup.zpowers_le.mpr hcA) hb), hF9]
  have hcR : c ∈ Subgroup.centralizer (R : Set G) :=
    Subgroup.centralizer_le hRL hcC
  have hADR : AD ≤ Subgroup.centralizer (R : Set G) :=
    sup_le hFR (Subgroup.zpowers_le.mpr hcR)
  set P := R ⊔ AD with hP
  have hPe : CFSG.Assembly.IsElemAbelian 3 P := isElemAbelian_sup_of_le_centralizer hRe hADe hADR
  have hRAD : R ⊓ AD = Subgroup.zpowers c := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hZR hcZ, Subgroup.mem_sup_right
      (Subgroup.mem_zpowers c)⟩)
    refine le_trans ?_ (hRFC.trans hZc)
    exact inf_le_inf_left R (sup_le_sup_left (Subgroup.zpowers_le.mpr hcC) F)
  have hP243 : Nat.card P = 3 ^ 5 := by
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute R AD
      fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hADR hb) a ha
    rw [hRAD, Nat.card_zpowers, hc3, hR27, hAD27] at hcard
    rw [hP]
    omega
  have hcP : c ∈ P := Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  refine false_of_star417 hconf.1 hconf.2.2.2.1 hcC hc3 hPe
    (fun a ha => congrArg Subtype.val (hPe.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcP⟩))
    (le_sup_left.trans le_sup_right) hF9 hFC hT₁L hT₁ hFT₁ hT₁F ?_
  rw [← hP243]
  exact Subgroup.card_le_of_le le_sup_left

end Certs

end CFSG.RankThree.PartTwo.Sec4

module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelE
public import CFSG.LocalAnalysis.StandardType.GGSpJoinMaxElemRank
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSpOrder

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly
open CFSG.StandardType.OrdPNsSp CFSG.StandardType.OrdPNsGen Matrix NoOffOm

variable {G : Type} [Group G] [Finite G]

theorem hdRo7CLCoordAux_card_inf_pow_of_innerDiag
    (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G)
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) p Bs L)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ L, ∀ y ∈ L, b * y * b⁻¹ = x * y * x⁻¹) :
    ∃ r : ℕ, 5 ≤ r ∧ Nat.card ↥(Bs ⊓ L) = p ^ r := by
  have hperf : commutator ↥L = ⊤ := hM.1
  obtain ⟨lab, _, hhas, _, _, _, _, _, hS, _, _⟩ := largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp3, htag, hn, h5⟩ := hS
  have hp : Nat.Prime p := by rw [hp3]; norm_num
  have hp2 : p ≠ 2 := by omega
  have h1n : 1 ≤ lab.n := by omega
  have hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp lab.rank 2 lab.n :=
    hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC htag (by omega) h1n hhas
  obtain ⟨φ, hinj, hrange⟩ :=
    ggSpLiftInput_holds G L lab.rank lab.n (by omega) hperf hmodel
  haveI : CharP (GaloisField 2 lab.n) 2 :=
    charP_two_of_card (GaloisField.card 2 lab.n (by omega))
  have hZL : Subgroup.center ↥L = ⊥ :=
    hdRo7CLCoordAux_center_L_eq_bot_of_innerDiag p Bs L hM
  obtain ⟨hpow, hcomm, hmax, hcardE⟩ :=
    comap_inf_maximal hH.1.2.1 φ hinj hrange hZL hBsN hinner
  set E : Subgroup (StatedSp lab.rank (GaloisField 2 lab.n)) :=
    (Bs ⊓ L).comap φ with hEdef
  have hcardBs : Nat.card ↥(Bs ⊓ L) = Nat.card ↥E := hcardE.symm
  have hA := genMax_map_statedSpGL (n := lab.rank) (K := GaloisField 2 lab.n) hp hp2 hpow hcomm hmax
  have hΓ : ∀ g : GL (Fin (lab.rank + lab.rank)) (GaloisField 2 lab.n),
      (∀ v w, spFormD lab.rank (GaloisField 2 lab.n) (glin g v) (glin g w) =
        spFormD lab.rank (GaloisField 2 lab.n) v w) → g ∈ isoGL (spFormD lab.rank (GaloisField 2 lab.n)) :=
    fun g hg => hg
  have hneE : E ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥E = 1 := by rw [h]; exact Subgroup.card_bot
    have h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ L) :=
      hdRo7CLCoordAux_card_inf_ge p B Bs x L D J y K hH hZL hBsN hinner
    rw [hcardBs, h1] at h3
    have h2 : (8 : ℕ) ≤ p ^ 3 := by simpa using Nat.pow_le_pow_left hp.two_le 3
    omega
  have hne : ∃ c ∈ E.map (statedSpGL lab.rank (GaloisField 2 lab.n)), c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hneE
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    have h1 : statedSpGL lab.rank (GaloisField 2 lab.n) s = 1 := hcon _ ⟨s, hs, rfl⟩
    exact statedSpGL_injective (h1.trans (map_one _).symm)
  have hle := card_le_pow_lcm (K := GaloisField 2 lab.n) (d := lab.rank + lab.rank)
    (spFormD_isAlt) hA
  have hge := pow_lcm_le_card (K := GaloisField 2 lab.n) (d := lab.rank + lab.rank)
    (spFormD_isAlt) hA hΓ hne
  have hKcard : Nat.card (GaloisField 2 lab.n) = 2 := by
    rw [GaloisField.card 2 lab.n (by omega), hn]; norm_num
  have hord : OrdPNS.ordQ (GaloisField 2 lab.n) p = 2 := by
    unfold OrdPNS.ordQ
    rw [hKcard, hp3]
    exact orderOf_eq_prime (p := 2) (by decide) (by decide)
  have hexp : (lab.rank + lab.rank) / Nat.lcm 2 (OrdPNS.ordQ (GaloisField 2 lab.n) p) =
      lab.rank := by
    rw [hord, Nat.lcm_self,
      show lab.rank + lab.rank = 2 * lab.rank by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hcardmap : Nat.card ↥(E.map (statedSpGL lab.rank (GaloisField 2 lab.n))) =
      Nat.card ↥E := Subgroup.card_map_of_injective statedSpGL_injective
  have hEcard : Nat.card ↥E = p ^ lab.rank := by
    apply le_antisymm
    · rw [hcardmap, hexp] at hle
      exact hle
    · rw [hcardmap, hexp] at hge
      exact hge
  exact ⟨lab.rank, h5, by rw [hcardBs, hEcard]⟩

end CFSG.StandardType.HdRo7C

end

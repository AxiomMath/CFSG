module

public import CFSG.RankThree.SubgroupLists.SymplecticFischerPair
public import CFSG.RankThree.SubgroupLists.TransvectionRecognition
public import CFSG.RankThree.SubgroupLists.SymplecticSkewElations
public import CFSG.RankThree.SubgroupLists.SymplecticSqZero
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

@[expose] def MitchellPartThree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ G : Subgroup (GL V₄ (ZMod p)),
    G ≤ StatedSp 2 (ZMod p) → CFSG.IsQuasisimple G → commutant G = ⊥ → IsIrreducibleOn G →
    (∀ z ∈ Subgroup.center G, (z : GL V₄ (ZMod p)) = 1 ∨ (z : GL V₄ (ZMod p)) = -1) →
    (-1 : GL V₄ (ZMod p)) ∈ G → (∀ x ∈ G, IsSqZero x → x = 1) →
    ∀ t : G, IsNCInv (t : GL V₄ (ZMod p)) →
      ∀ g : G, IsThreePair (t : GL V₄ (ZMod p)) ((g * t * g⁻¹ : G) : GL V₄ (ZMod p))

theorem eq_statedSp_of_isNCInv_five (hIII : MitchellPartThree) (hSpC : FischerSpClique)
    (hOC : FischerOrthClique) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p)) (hq : CFSG.IsQuasisimple G)
    (hC : commutant G = ⊥) (hirr : IsIrreducibleOn G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ (ZMod p)) = 1 ∨ (z : GL V₄ (ZMod p)) = -1)
    (hneg : (-1 : GL V₄ (ZMod p)) ∈ G) {t : GL V₄ (ZMod p)} (htG : t ∈ G) (ht : IsNCInv t) :
    G = StatedSp 2 (ZMod p) := by
  classical
  have hp := (Fact.out : p.Prime)
  have : Group.IsPerfect G := hq.1
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this
    omega
  by_cases hT : ∃ a : V₄ → ZMod p, ∃ c : ZMod p, a ≠ 0 ∧ c ≠ 0 ∧ spTrans a c ∈ G
  · obtain ⟨a, c, ha, hc, hTa⟩ := hT
    exact eq_statedSp_of_spTrans_mem hp2 hGS hirr ha hc hTa
  push Not at hT
  exfalso
  by_cases hU0 : ∀ x ∈ G, IsSqZero x → x = 1
  ·
    exact false_of_threeTranspositions hSpC hOC h2 h3 hGS hq hZ hneg (t := ⟨t, htG⟩) ht
      (hIII p hp5 G hGS hq hC hirr hZ hneg hU0 ⟨t, htG⟩ ht)
  ·
    push Not at hU0
    obtain ⟨x, hxG, hx, hx1⟩ := hU0
    have hx2 := finrank_unipAxis_eq_two_of_not_spTrans (hGS hxG) hx hx1
      fun a c ha hc h => hT a c ha hc (h ▸ hxG)
    exact false_of_skew_elation hp5 hGS hC hirr hT hxG hx hx2

end CFSG.RankThree.SubgroupLists

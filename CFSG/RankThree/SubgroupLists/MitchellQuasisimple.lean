module

public import CFSG.RankThree.SubgroupLists.SymplecticGamma
public import CFSG.RankThree.SubgroupLists.SymplecticFischerThree
public import CFSG.RankThree.SubgroupLists.SymplecticQuasisimple
public import Certificates.Certificate110
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1007
public import Certificates.Certificate1008
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1014
public import Certificates.Certificate1015
public import Certificates.Certificate1016
public import Certificates.Certificate1017
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import Certificates.Certificate7023
public import Certificates.Certificate1022
public import Certificates.Certificate7059

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem mitchell_quasisimple_sp4_of (hIII : MitchellPartThree) (hSpC : FischerSpClique)
    (hOC : FischerOrthClique) (hSp : FischerSpCard) (hO : FischerOrthCard)
    (hU : FischerUnitaryCard) (hR : FischerReflectionCard) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p))
    (hq : CFSG.IsQuasisimple G) :
    Nonempty (G ≃* StatedSp 2 (ZMod p)) ∨ Nonempty (G ≃* SL(2, GaloisField p 2)) ∨
      Nonempty (G ≃* SL(2, ZMod p)) ∨ Nonempty (G ≃* SL(2, ZMod 5)) ∨
      Nonempty (G ≃* SL(2, GaloisField 3 2)) ∨
      (p = 7 ∧ Nat.card (Subgroup.center G) = 2 ∧
        Nonempty ((G ⧸ Subgroup.center G) ≃* alternatingGroup (Fin 7))) := by
  classical
  by_cases hcent : ∀ x ∈ G, x * x = 1 → ∀ y ∈ G, x * y = y * x
  · rcases quasisimple_sp4_of_involutions_central hp2 hGS hq hcent with h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  push Not at hcent
  obtain ⟨x, hxG, hx2, y, hyG, hxy⟩ := hcent
  have : Group.IsPerfect G := hq.1
  by_cases hred : ∃ U : Submodule (ZMod p) (V₄ → ZMod p), IsInvariant G U ∧ U ≠ ⊥ ∧ U ≠ ⊤
  · obtain ⟨U, hU', hU0, hUt⟩ := hred
    rcases quasisimple_reducible_sp4 hp2 hGS hq hU' hU0 hUt with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  have hirr : IsIrreducibleOn G := by
    intro W hW
    by_contra h
    push Not at h
    exact hred ⟨W, hW, h.1, h.2⟩
  by_cases hC : commutant G ≠ ⊥
  · rcases perfect_irreducible_not_absolutely hp2 (by simp) hirr hC with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  push Not at hC
  have hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ (ZMod p)) = 1 ∨ (z : GL V₄ (ZMod p)) = -1 := by
    intro z hz
    have hM : ((z : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) ∈ commutant G := by
      rw [mem_commutant]
      intro g hg
      have := congrArg (fun y : G => ((y : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)))
        (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
      simpa using this
    rw [hC, Algebra.mem_bot] at hM
    obtain ⟨c, hc⟩ := hM
    exact eq_one_or_eq_neg_one_of_scalar (hGS z.2)
      (c := c) (by rw [← hc]; simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply])
  by_cases hneg : (-1 : GL V₄ (ZMod p)) ∈ G
  ·
    have hxN : IsNCInv x := by
      refine ⟨hGS hxG, hx2, ?_, ?_⟩
      · rintro rfl
        exact hxy (by rw [one_mul, mul_one])
      · rintro rfl
        exact hxy (by rw [neg_one_mul, mul_neg_one])
    have hp := (Fact.out : p.Prime)
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inl ⟨MulEquiv.subgroupCongr
        (eq_statedSp_three_of_isNCInv hSp hO hU hR hGS hq hirr hZ hneg hxG hxN)⟩
    have hp5 : 5 ≤ p := by
      have h2le := hp.two_le
      rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
      · exact absurd h hp2
      · exact absurd h hp3
      · exact absurd (h ▸ hp) (by decide)
      · exact h
    exact Or.inl ⟨MulEquiv.subgroupCongr
      (eq_statedSp_of_isNCInv_five hIII hSpC hOC hp5 hGS hq hC hirr hZ hneg hxG hxN)⟩
  ·
    exfalso
    have h2 := two_dvd_card_center_of_neg_one_not_mem hp2 hGS hq hneg
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hz1 : (z : G) ≠ 1 := by
      intro h1
      have : z = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hz
      omega
    rcases hZ z z.2 with h | h
    · exact hz1 (Subtype.ext h)
    · exact hneg (h ▸ (z : G).2)

end CFSG.RankThree.SubgroupLists

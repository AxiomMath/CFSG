module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.RankThree.PartTwo.Late.GammaZero

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem Hyp1921.not_mem_of_mem_sectionCentralizer_of (h : Hyp1921 G A M N L)
    (hZ : ∀ x ∈ L, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) →
      x ∈ CFSG.Open.pCoreOf 2 L)
    {c : G} (hc : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L)) (hc1 : c ≠ 1) :
    c ∉ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc' : c ∈ A ∧ ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L := hc
  intro hcL
  have hc2 : c ∈ CFSG.Open.pCoreOf 2 L := hZ c hcL hc'.2
  have hA3 : CFSG.Assembly.IsElemAbelian 3 A := (isE27_of_mem_partTwoE h.mem_partTwoE).1
  have hc3 : c ^ 3 = 1 := hA3.2 c hc'.1
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨c, hc2⟩
  have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hgcd : Nat.gcd 3 (2 ^ k) = 1 := hcop
  have hone : c ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨hc3, hk'⟩
  rw [hgcd, pow_one] at hone
  exact hc1 hone

theorem Hyp1921.isE27_inf_Q_sup_zpowers_of (h : Hyp1921 G A M N L)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) {Q : Subgroup G} (hQ : IsSylowOf 3 Q N)
    (hAQ : A ≤ Q)
    (hQL9 : Nat.card (Q ⊓ L : Subgroup G) = 9)
    (hQLE : CFSG.Open.IsElemAbelian 3 (Q ⊓ L : Subgroup G))
    (hQL2 : (Q ⊓ L : Subgroup G) ⊓ CFSG.Open.pCoreOf 2 L = ⊥)
    {c : G} (hc : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L)) (hcL : c ∉ L) :
    IsE27 ((Q ⊓ L : Subgroup G) ⊔ Subgroup.zpowers c) ∧
      (Q ⊓ L : Subgroup G) ⊔ Subgroup.zpowers c ≤ Q := by
  clear hQ
  have hc' : c ∈ A ∧ ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L := hc
  have hcA : c ∈ A := hc'.1
  have hcQ : c ∈ Q := hAQ hcA
  have hcN : c ∈ N := h.mem_scriptM_N.2 hcA
  have hcNL : c ∈ Subgroup.normalizer (L : Set G) := hNL hcN
  have hA3 : CFSG.Assembly.IsElemAbelian 3 A := (isE27_of_mem_partTwoE h.mem_partTwoE).1
  have hc3 : c ^ 3 = 1 := hA3.2 c hcA
  have hB3 : CFSG.Assembly.IsElemAbelian 3 (Q ⊓ L : Subgroup G) := hQLE
  have hcomm : ∀ e ∈ (Q ⊓ L : Subgroup G), e * c = c * e := by
    intro e he
    have heQ : e ∈ Q := he.1
    have heL : e ∈ L := he.2
    have hconj : c * e * c⁻¹ ∈ Q ⊓ L :=
      ⟨Q.mul_mem (Q.mul_mem hcQ heQ) (Q.inv_mem hcQ),
        (Subgroup.mem_normalizer_iff.mp hcNL e).mp heL⟩
    have hmem : c * e * c⁻¹ * e⁻¹ ∈ (Q ⊓ L : Subgroup G) ⊓ CFSG.Open.pCoreOf 2 L :=
      ⟨(Q ⊓ L).mul_mem hconj ((Q ⊓ L).inv_mem he), hc'.2 e heL⟩
    rw [hQL2, Subgroup.mem_bot] at hmem
    have h1 : c * e * c⁻¹ = e := mul_inv_eq_one.mp hmem
    calc e * c = c * e * c⁻¹ * c := by rw [h1]
      _ = c * e := by group
  have hcB : c ∉ (Q ⊓ L : Subgroup G) := fun hcB => hcL hcB.2
  exact ⟨CFSG.RankThree.PartTwo.Late.isE27_sup_zpowers hB3 hQL9 hcB hc3 hcomm,
    sup_le inf_le_left (Subgroup.zpowers_le.mpr hcQ)⟩

theorem Hyp1921.normalizer_inf_Q_le_of (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q)
    (hQL9 : Nat.card (Q ⊓ L : Subgroup G) = 9)
    (hQLE : CFSG.Open.IsElemAbelian 3 (Q ⊓ L : Subgroup G))
    {c : G} (hE : IsE27 ((Q ⊓ L : Subgroup G) ⊔ Subgroup.zpowers c))
    (hEQ : (Q ⊓ L : Subgroup G) ⊔ Subgroup.zpowers c ≤ Q) :
    Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsE27 A := isE27_of_mem_partTwoE h.mem_partTwoE
  have hPQ : IsPGroup 3 Q := (CFSG.ABGLocalTools.isSylowOf_iff.mp hQ).2.1
  have hQM : Q ≤ M :=
    CFSG.RankThree.PartTwo.Late.le_of_isPGroup_of_le h.hyp191 hA3 h.mem_scriptM hPQ hAQ
  have hEM : (Q ⊓ L : Subgroup G) ⊔ Subgroup.zpowers c ≤ M := hEQ.trans hQM
  have hM' : M ∈ scriptM (gamma 2 ((Q ⊓ L : Subgroup G) ⊔ Subgroup.zpowers c) : Set G) :=
    CFSG.RankThree.PartTwo.Late.mem_scriptM_gamma_of_le h.hyp191 hET hA3 h.mem_scriptM hE hEM
  have hgM : gamma 2 ((Q ⊓ L : Subgroup G) ⊔ Subgroup.zpowers c) ≤ M := fun x hx => hM'.2 hx
  have hB3 : CFSG.Assembly.IsElemAbelian 3 (Q ⊓ L : Subgroup G) := hQLE
  have hB2 : 2 ≤ CFSG.Open.pRank 3 (Q ⊓ L : Subgroup G) :=
    CFSG.RankThree.PartTwo.Late.two_le_pRank_of_elemAbelian hB3 hQL9.ge
  have hBE : (Q ⊓ L : Subgroup G) ≤ (Q ⊓ L : Subgroup G) ⊔ Subgroup.zpowers c := le_sup_left
  exact (normalizer_le_gamma hBE hB2).trans hgM

end CFSG.RankThree.PartTwo.Late

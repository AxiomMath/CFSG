module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionFive
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem card_ne_one_of_ne_bot_restriction_seven
    {G : Type u} [Group G] [Finite G]
    (X : Subgroup G) (hXne : X ≠ ⊥) : Nat.card X ≠ 1 := by
  intro hcard
  exact hXne (Subgroup.eq_bot_of_card_eq X hcard)

/-- The odd subgroup in source restriction (7) has order three once the
order-six intersection from restriction (6) is available.  Restriction (5)
first makes the quotient map injective on `X`; the remaining cardinal
arithmetic is the divisibility argument for a subgroup of a group of order
six.

The theorem is deliberately stated with the index-six premise exposed.  In
the full restriction-(7) endpoint this premise is supplied by the preceding
fiber estimate, while this lemma remains reusable for either representative
of the commuting-involution alternative in restriction (6).
-/
public theorem firstCase_klein_restrictionSeven_X_card_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hindex :
      let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
      let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
      (N.subgroupOf D).index = 6)
    {X : Subgroup G}
    (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) :
    Nat.card X = 3 := by
  classical
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
  let N : Subgroup G := D ⊓ B

  have hBcard : Nat.card {z : G // z ∈ invertedElements B y} = 1 := by
    simpa [B] using firstCase_klein_restrictionFive hmin c hfirst hklein
      y hy hyH

  have hInf : X ⊓ N = ⊥ := by
    have hXBinf : X ⊓ B = ⊥ := by
      apply le_bot_iff.mp
      intro z hz
      have hzX : z ∈ X := hz.1
      have hzB : z ∈ B := hz.2
      have hzI : z ∈ invertedElements B y := by
        exact ⟨hzB, (hXinv z hzX).2⟩
      have hone : (1 : G) ∈ invertedElements B y := ⟨B.one_mem, by simp⟩
      obtain ⟨z0, hz0⟩ := (Nat.card_eq_one_iff_exists.mp hBcard)
      have hzEq : (⟨z, hzI⟩ : {w : G // w ∈ invertedElements B y}) = z0 :=
        hz0 _
      have h1Eq : (⟨1, hone⟩ : {w : G // w ∈ invertedElements B y}) = z0 :=
        hz0 _
      have hz1 : z = 1 := congrArg Subtype.val (hzEq.trans h1Eq.symm)
      simpa [hz1]
    apply le_bot_iff.mp
    intro z hz
    have hNB : N ≤ B := inf_le_right
    have hzbot : z ∈ (⊥ : Subgroup G) := by
      rw [← hXBinf]
      exact ⟨hz.1, hNB hz.2⟩
    exact hzbot

  have hXleD : X ≤ D := by
    intro z hz
    refine ⟨hXle hz, ?_⟩
    change (z : G) ∈ conjugateSubgroup c.Hhat y
    exact Subgroup.mem_map.mpr ⟨(z : G)⁻¹,
      c.Hhat.inv_mem (hXle hz), by
        change y * (z : G)⁻¹ * y⁻¹ = (z : G)
        calc
          y * (z : G)⁻¹ * y⁻¹ =
              (y * (z : G) * y⁻¹)⁻¹ := by group
          _ = ((z : G)⁻¹)⁻¹ := by rw [(hXinv z hz).2]
          _ = (z : G) := by simp⟩

  have hNnormal : (N.subgroupOf D).Normal := by
    have hBnorm : IsNormalIn B c.Hhat := by
      simpa [B] using firstCase_klein_VU_normal_in_Hhat hmin c
    apply (Subgroup.normal_subgroupOf_iff (show N ≤ D from inf_le_left)).2
    intro n d hn hd
    refine ⟨?_, ?_⟩
    · exact D.mul_mem (D.mul_mem hd ((show N ≤ D from inf_le_left) hn))
        (D.inv_mem hd)
    · exact hBnorm.2 d ((show D ≤ c.Hhat from inf_le_left) hd) n
        ((show N ≤ B from inf_le_right) hn)
  let : (N.subgroupOf D).Normal := hNnormal

  let q : D →* (D ⧸ N.subgroupOf D) :=
    QuotientGroup.mk' (N.subgroupOf D)
  let i : X →* D :=
    { toFun := fun x => ⟨(x : G), hXleD x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  let f : X →* (D ⧸ N.subgroupOf D) := q.comp i

  have hinj : Function.Injective f := by
    intro a b hab
    have hq : f a * (f b)⁻¹ = 1 := by rw [hab]; simp
    have hq' : q (i a * (i b)⁻¹) = 1 := by simpa [f] using hq
    have hmemD : i a * (i b)⁻¹ ∈ N.subgroupOf D :=
      (QuotientGroup.eq_one_iff (i a * (i b)⁻¹)).mp hq'
    have hmemG : (a : G) * (b : G)⁻¹ ∈ X ⊓ N := by
      refine ⟨X.mul_mem a.2 (X.inv_mem b.2), ?_⟩
      exact Subgroup.mem_subgroupOf.mp hmemD
    rw [hInf] at hmemG
    apply Subtype.ext
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmemG)

  have hcardrange : Nat.card f.range = Nat.card X := by
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hdiv : Nat.card X ∣ Nat.card (D ⧸ N.subgroupOf D) := by
    have hdiv' : Nat.card f.range ∣ Nat.card (D ⧸ N.subgroupOf D) :=
      f.range.card_subgroup_dvd_card
    rw [hcardrange] at hdiv'
    exact hdiv'
  have hqcard : Nat.card (D ⧸ N.subgroupOf D) = 6 := by
    rw [← Subgroup.index_eq_card]
    simpa [D, N] using hindex
  rw [hqcard] at hdiv
  have hle : Nat.card X ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
  have hcardne1 : Nat.card X ≠ 1 :=
    card_ne_one_of_ne_bot_restriction_seven X hXne
  have hcardne2 : Nat.card X ≠ 2 := by
    intro h
    rw [h] at hXodd
    norm_num at hXodd
  have hcardne6 : Nat.card X ≠ 6 := by
    intro h
    rw [h] at hXodd
    norm_num at hXodd
  interval_cases hcard : Nat.card X <;> simp_all

end CFSG.GorensteinWalter

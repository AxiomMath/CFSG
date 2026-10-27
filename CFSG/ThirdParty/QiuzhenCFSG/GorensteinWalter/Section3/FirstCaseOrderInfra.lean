module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Order bookkeeping for the Klein-four first case

This module proves the order relations that precede the involution count in
Bender's Section 3.  They use only `H = S U`, the Klein-four branch of
Theorem 2.6, and the quotient `Ĥ/(O₂(Ĥ)O₂′(Ĥ)) ≅ D₆`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem card_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type u} [Group G]
    (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G))
    (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.2
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem oddCore_normal
    {G : Type u} [Group G] (H : Subgroup G) : IsNormalIn (oddCoreOf H) H := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact y.2
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹, ?_, by simp⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥H)).conj_mem y hy (⟨h, hh⟩ : ↥H)

private theorem twoCore_normal
    {G : Type u} [Group G] (H : Subgroup G) :
    IsNormalIn (twoCoreOf H) H := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact y.2
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹, ?_, by simp⟩
    exact (pCore_normal (p := 2) (G := ↥H)).conj_mem y hy (⟨h, hh⟩ : ↥H)

private theorem oddCore_card_eq_pPrimeCore
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card (oddCoreOf H) = Nat.card (pPrimeCore 2 H) := by
  simpa [oddCoreOf] using
    (Subgroup.card_map_of_injective (K := pPrimeCore 2 H) H.subtype_injective)

public theorem firstCase_Hhat_card_eq_three_mul_H
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nat.card c.Hhat = 3 * Nat.card c.H := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h26 := theorem_2_6 hmin c
  have hUeq : c.U = oddCoreOf c.Hhat := h26.1
  have hHSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU hmin c
  have hUleH : c.U ≤ c.H := by
    change oddCoreOf c.H ≤ c.H
    exact (oddCore_normal c.H).1
  have hUnormH : IsNormalIn c.U c.H := by
    change IsNormalIn (oddCoreOf c.H) c.H
    exact oddCore_normal c.H
  have hSnormal : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
    (centralizerSetup_S_le_H c).trans (le_normalizer_of_isNormalIn hUnormH)
  have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.H))
    rw [oddCore_card_eq_pPrimeCore]
    simpa using pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hScardPow : Nat.card (c.S : Subgroup G) =
      2 ^ (Nat.card G).factorization 2 := by
    simpa using Sylow.card_eq_multiplicity c.S
  have hSodd : Nat.Coprime (Nat.card (c.S : Subgroup G)) (Nat.card c.U) := by
    rw [hScardPow]
    exact hUodd.pow_left _
  have hSdisj : Disjoint (c.S : Subgroup G) c.U :=
    Subgroup.disjoint_of_coprime_natCard hSodd
  have hHcard : Nat.card c.H = Nat.card (c.S : Subgroup G) * Nat.card c.U := by
    rw [← hHSU]
    calc
      Nat.card ((c.S : Subgroup G) ⊔ c.U : Subgroup G) =
          Nat.card (c.U ⊔ (c.S : Subgroup G) : Subgroup G) := by rw [sup_comm]
      _ = Nat.card c.U * Nat.card (c.S : Subgroup G) :=
        card_sup_eq_mul_of_disjoint_of_le_normalizer c.U (c.S : Subgroup G)
          hSnormal hSdisj.symm
      _ = Nat.card (c.S : Subgroup G) * Nat.card c.U := by ring
  have hS8 : Nat.card (c.S : Subgroup G) = 8 :=
    firstCase_klein_S_card hmin c hfirst hklein
  have hHcard' : Nat.card c.H = 8 * Nat.card c.U := by simpa [hS8] using hHcard
  let V : Subgroup (↥c.Hhat) := pCore 2 c.Hhat
  let O : Subgroup (↥c.Hhat) := pPrimeCore 2 c.Hhat
  let K : Subgroup (↥c.Hhat) := V ⊔ O
  have hVcard : Nat.card V = 4 := by simpa [V] using hklein.card_four
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
  have hVcop : Nat.Coprime (Nat.card V) (Nat.card O) := by
    rw [hVcard]
    exact hOcop.pow_left 2
  have hdisj : Disjoint V O := Subgroup.disjoint_of_coprime_natCard
    (by simpa [Nat.coprime_comm] using hVcop)
  have hOnorm : O ≤ Subgroup.normalizer (V : Set c.Hhat) := by
    have hVnorm : IsNormalIn V (⊤ : Subgroup (↥c.Hhat)) := by
      refine ⟨le_top, ?_⟩
      intro h _hh x hx
      exact (pCore_normal (p := 2) (G := ↥c.Hhat)).conj_mem x hx h
    exact le_top.trans (le_normalizer_of_isNormalIn hVnorm)
  have hKcard : Nat.card K = Nat.card V * Nat.card O := by
    exact card_sup_eq_mul_of_disjoint_of_le_normalizer V O hOnorm hdisj
  have hOcard : Nat.card O = Nat.card c.U := by
    calc
      Nat.card O = Nat.card (oddCoreOf c.Hhat) := by
        simpa [O] using (oddCore_card_eq_pPrimeCore c.Hhat).symm
      _ = Nat.card c.U := by rw [hUeq]
  have hq := firstCase_klein_quotient_d6 hmin c hfirst hklein
  have hQcard : Nat.card (c.Hhat ⧸ (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) = 6 := by
    rcases hq with ⟨e⟩
    calc
      Nat.card (c.Hhat ⧸ (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) =
          Nat.card (DihedralGroup 3) := Nat.card_congr e.toEquiv
      _ = 6 := by rw [DihedralGroup.nat_card]
  have hKindex : K.index = Nat.card (c.Hhat ⧸ (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) := by
    rw [Subgroup.index_eq_card]
  have hmul := K.card_mul_index
  change Nat.card K * K.index = Nat.card (↥c.Hhat) at hmul
  rw [hKcard, hKindex, hQcard, hVcard, hOcard] at hmul
  have hcard : Nat.card c.Hhat = 24 * Nat.card c.U := by omega
  rw [hcard, hHcard']
  ring

/-- The centralizer has order `|S| |U|`. -/
public theorem firstCase_H_card_eq_cardS_mul_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    Nat.card c.H = Nat.card (c.S : Subgroup G) * Nat.card c.U := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU hmin c
  have hUnormH : IsNormalIn c.U c.H := by
    change IsNormalIn (oddCoreOf c.H) c.H
    exact oddCore_normal c.H
  have hSnormal : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
    (centralizerSetup_S_le_H c).trans (le_normalizer_of_isNormalIn hUnormH)
  have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.H))
    rw [oddCore_card_eq_pPrimeCore]
    simpa using pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hScardPow : Nat.card (c.S : Subgroup G) =
      2 ^ (Nat.card G).factorization 2 := by
    simpa using Sylow.card_eq_multiplicity c.S
  have hSodd : Nat.Coprime (Nat.card (c.S : Subgroup G)) (Nat.card c.U) := by
    rw [hScardPow]
    exact hUodd.pow_left _
  have hSdisj : Disjoint (c.S : Subgroup G) c.U :=
    Subgroup.disjoint_of_coprime_natCard hSodd
  rw [← hHSU]
  calc
    Nat.card ((c.S : Subgroup G) ⊔ c.U : Subgroup G) =
        Nat.card (c.U ⊔ (c.S : Subgroup G) : Subgroup G) := by rw [sup_comm]
    _ = Nat.card c.U * Nat.card (c.S : Subgroup G) :=
      card_sup_eq_mul_of_disjoint_of_le_normalizer c.U (c.S : Subgroup G)
        hSnormal hSdisj.symm
    _ = Nat.card (c.S : Subgroup G) * Nat.card c.U := by ring

/-- In the Klein-four branch, `|H| = 8 |U|`. -/
public theorem firstCase_H_card_eq_eight_mul_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nat.card c.H = 8 * Nat.card c.U := by
  rw [firstCase_H_card_eq_cardS_mul_U hmin c,
    firstCase_klein_S_card hmin c hfirst hklein]

/-- The source index relation `[G:H] = 3 [G:Ĥ]`. -/
public theorem firstCase_H_index_eq_three_mul_Hhat_index
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    c.H.index = 3 * c.Hhat.index := by
  have hHhat := firstCase_Hhat_card_eq_three_mul_H hmin c hfirst hklein
  have hG1 := c.H.card_mul_index
  have hG2 := c.Hhat.card_mul_index
  have hpos : 0 < Nat.card c.H := Nat.card_pos
  apply Nat.mul_left_cancel hpos
  calc
    Nat.card c.H * c.H.index = Nat.card G := hG1
    _ = Nat.card c.Hhat * c.Hhat.index := hG2.symm
    _ = (3 * Nat.card c.H) * c.Hhat.index := by rw [hHhat]
    _ = Nat.card c.H * (3 * c.Hhat.index) := by ring

end CFSG.GorensteinWalter

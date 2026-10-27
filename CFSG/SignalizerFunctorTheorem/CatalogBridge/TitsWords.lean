module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public noncomputable section

open CFSG.LieType.Simplicity.TitsBits CFSG.SectionRank.TitsOrder CFSG.LieType.Ree
open CFSG.Blueprint.Chevalley

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def gBits (s : ℕ) : ℕ := evalB (genWord s)

@[expose] def gBitsInv (s : ℕ) : ℕ := evalB (genWord s).reverse

@[expose] def gPair (l : ℤ) : ℕ × ℕ :=
  if 0 < l then (gBits (l.toNat - 1), gBitsInv (l.toNat - 1))
  else (gBitsInv ((-l).toNat - 1), gBits ((-l).toNat - 1))

@[expose] def wordPair : List ℤ → ℕ × ℕ
  | [] => (oneBits, oneBits)
  | l :: w => (mul (gPair l).1 (wordPair w).1, mul (wordPair w).2 (gPair l).2)

@[expose] def GoodLetter (l : ℤ) : Prop := l ≠ 0 ∧ l.natAbs ≤ 4

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

variable (K) in
@[expose] def gEltG
    (l : ℤ) : reeFixed ReeTag.F4 K 0 :=
  if 0 < l then genG K (l.toNat - 1) else (genG K ((-l).toNat - 1))⁻¹

variable (K) in
@[expose] def gWordG
    (w : List ℤ) : reeFixed ReeTag.F4 K 0 :=
  (w.map (gEltG K)).prod

theorem gWordG_nil :
    gWordG K [] = 1 := rfl

theorem gWordG_cons
    (l : ℤ) (w : List ℤ) : gWordG K (l :: w) = gEltG K l * gWordG K w := by
  simp [gWordG]

theorem gWordG_append
    (w w' : List ℤ) : gWordG K (w ++ w') = gWordG K w * gWordG K w' := by
  simp [gWordG]

theorem hasBits_gEltG
    {l : ℤ} (hl : GoodLetter l) :
    HasBits K (↑(gEltG K l) : adjointGroup ReeTag.F4.tag K) (gPair l).1 ∧
    HasBits K (↑(gEltG K l) : adjointGroup ReeTag.F4.tag K)⁻¹ (gPair l).2 := by
  have key : ∀ s : ℕ, s < 4 →
      HasBits K (↑(genG K s) : adjointGroup ReeTag.F4.tag K) (gBits s) ∧
      HasBits K (↑(genG K s) : adjointGroup ReeTag.F4.tag K)⁻¹ (gBitsInv s) := by
    intro s hs
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    rw [genG_eq_evalG, evalG_inv]
    exact ⟨hasBits_evalG _, hasBits_evalG _⟩
  obtain ⟨hl0, hl4⟩ := hl
  by_cases hpos : 0 < l
  · have hs : l.toNat - 1 < 4 := by omega
    obtain ⟨h1, h2⟩ := key _ hs
    simp only [gEltG, gPair, hpos, ↓reduceIte]
    exact ⟨h1, h2⟩
  · have hs : (-l).toNat - 1 < 4 := by omega
    obtain ⟨h1, h2⟩ := key _ hs
    simp only [gEltG, gPair, hpos, ↓reduceIte, Subgroup.coe_inv, inv_inv]
    exact ⟨h2, h1⟩

theorem hasBits_gWordG
    : ∀ (w : List ℤ), (∀ l ∈ w, GoodLetter l) →
      HasBits K (↑(gWordG K w) : adjointGroup ReeTag.F4.tag K) (wordPair w).1 ∧
      HasBits K (↑(gWordG K w) : adjointGroup ReeTag.F4.tag K)⁻¹ (wordPair w).2
  | [], _ => by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    refine ⟨?_, ?_⟩
    · simpa [gWordG, wordPair] using (hasBits_one (K := K))
    · simpa [gWordG, wordPair] using (hasBits_one (K := K))
  | l :: w, h => by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    obtain ⟨h1, h2⟩ := hasBits_gEltG (K := K) (h l (List.mem_cons_self ..))
    obtain ⟨h3, h4⟩ := hasBits_gWordG w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    rw [gWordG_cons]
    refine ⟨?_, ?_⟩
    · simpa [wordPair] using h1.mul h3
    · rw [Subgroup.coe_mul, mul_inv_rev]
      simpa [wordPair] using h4.mul h2

end CFSG.SignalizerFunctorTheorem.CatalogBridge

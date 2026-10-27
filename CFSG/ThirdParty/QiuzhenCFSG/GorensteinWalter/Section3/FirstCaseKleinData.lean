module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCyclicTwoCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Klein-four-branch data for the first-case count

This module pins the source paragraph
`refs/bender-dihedral-sylow.tex` L543--547:

> Thus `V := O₂(Ĥ)` is of type `(2,2)`.  Then `S` has order 8, and some
> Hall subgroup `K ≠ 1` of `F(U)` equals `I_U(s)` for each involution
> `s ∈ Ĥ − V` (whence `[Ĥ,s]` centralizes `F(U)`).

Only the facts that have been proved are packaged as `FirstCaseKleinData`:

1. `V = O₂(Ĥ)` and `V` is a Klein four group;
2. `|S| = 8`;
3. `Ĥ / VU ≅ D₆` (in the repo's `CentralizerStructure` notation this is
   `DihedralGroup 3`, the same quotient used by `theorem_2_6`);

The remaining three source facts are theorem goals, deliberately **not**
fields of this structure:

4. `K` is a Hall subgroup of `F(U)` and `K = I_U(s)` uniformly for every
   involution `s ∈ Ĥ − V`;
5. `K ≠ 1`, the nontriviality following from Theorem 2.6's
   `C_S(U) = O₂(Ĥ)`;
6. `[Ĥ,s]` centralizes `F(U)` for every such involution `s`.

The constructor from `hmin`, `c`, `hfirst`, and
`hklein : IsKleinFour (pCore 2 c.Hhat)` is the next step; it must prove
those three facts rather than receive them as inputs.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- Cardinality of the join of a subgroup and a subgroup normalizing it,
when the two subgroups are disjoint. -/
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

/-- The ambient two-core `O₂(Ĥ)` is a Klein four group whenever the
type-level `pCore 2 Ĥ` is. -/
public theorem firstCase_klein_V_klein
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    IsKleinFour (twoCoreOf c.Hhat) := by
  let e : pCore 2 c.Hhat ≃* twoCoreOf c.Hhat :=
    Subgroup.equivMapOfInjective (pCore 2 c.Hhat) c.Hhat.subtype
      c.Hhat.subtype_injective
  exact {
    card_four := (Nat.card_congr e.toEquiv).symm.trans hklein.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans hklein.exponent_two
  }

/-- In the first case the Klein-four branch has `Ĥ / VU` isomorphic to the
dihedral group of order six (the `DihedralGroup 3` used by
`CentralizerStructure`). -/
public theorem firstCase_klein_quotient_d6
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (_hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nonempty ((c.Hhat ⧸ (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) ≃* DihedralGroup 3) := by
  have h26 := theorem_2_6 hmin c
  rcases h26.2.2 with hcyclic | hklein'
  · exfalso
    exact firstCase_cyclicTwoCore_impossible hmin c hfirst hcyclic.1
  · exact hklein'.2

/-- In the Klein-four branch of the first case, the Sylow `2`-subgroup `S`
has order `8`.  The quotient `Ĥ / VU ≅ D₆` has a single involution outside
`VU`, so the `2`-part of `|Ĥ|` is `|V| · 2 = 8`. -/
public theorem firstCase_klein_S_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nat.card (↥(c.S : Subgroup G)) = 8 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := c.Hhat
  let N : Subgroup H := pCore 2 H
  let O : Subgroup H := pPrimeCore 2 H
  let K : Subgroup H := N ⊔ O
  have : N.Normal := by
    dsimp [N, H]
    infer_instance
  have : O.Normal := by
    dsimp [O, H]
    infer_instance
  have : K.Normal := by
    dsimp [K, N, O, H]
    infer_instance
  have hNcard : Nat.card N = 4 := hklein.card_four
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := H)
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp hOcop
  have hNp : IsPGroup 2 N := by
    simpa [N] using (pCore_isPGroup (G := H) (p := 2))
  have hNdisjO : Disjoint N O := by
    rcases (IsPGroup.iff_card (p := 2) (G := N)).mp hNp with ⟨n, hn⟩
    have hcop : Nat.Coprime (Nat.card N) (Nat.card O) := by
      rw [hn]
      exact hOcop.pow_left n
    exact Subgroup.disjoint_of_coprime_natCard hcop
  have hOleN : O ≤ Subgroup.normalizer (N : Set H) := by
    have : N.Normal := by infer_instance
    simp [Subgroup.normalizer_eq_top]
  have hKcard : Nat.card (↥K) = Nat.card N * Nat.card O := by
    exact card_sup_eq_mul_of_disjoint_of_le_normalizer N O hOleN hNdisjO
  have hq : Nonempty ((H ⧸ K) ≃* DihedralGroup 3) := by
    simpa [H, N, O, K] using firstCase_klein_quotient_d6 hmin c hfirst hklein
  obtain ⟨eq⟩ := hq
  have hQcard : Nat.card (H ⧸ K) = 6 := by
    calc
      Nat.card (H ⧸ K) = Nat.card (DihedralGroup 3) := Nat.card_congr eq.toEquiv
      _ = 2 * 3 := DihedralGroup.nat_card
      _ = 6 := by norm_num
  have hHcard : Nat.card H = 24 * Nat.card O := by
    have hKindex : K.index = Nat.card (H ⧸ K) := by
      rw [Subgroup.index_eq_card]
    have hmul := K.card_mul_index
    change Nat.card (↥K) * K.index = Nat.card H at hmul
    rw [hKcard, hKindex, hQcard, hNcard] at hmul
    calc
      Nat.card H = (4 * Nat.card O) * 6 := hmul.symm
      _ = 24 * Nat.card O := by ring
  have hfact : (Nat.card H).factorization 2 = 3 := by
    rw [hHcard]
    have hOnot : ¬ 2 ∣ Nat.card O := hOodd.not_two_dvd_nat
    have h24 : (24 : ℕ).factorization 2 = 3 := by
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
      rw [Nat.factorization_mul (by norm_num) (by norm_num)]
      rw [Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
    have hOcard_ne : Nat.card O ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul (by norm_num : (24 : ℕ) ≠ 0)
      hOcard_ne]
    simp [h24, Nat.factorization_eq_zero_of_not_dvd hOnot]
  have hSleHhat : (c.S : Subgroup G) ≤ c.Hhat :=
    (centralizerSetup_S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 (↥c.Hhat) := (c.S).subtype hSleHhat
  have hPcard : Nat.card (P : Subgroup (↥c.Hhat)) =
      2 ^ (Nat.card (↥c.Hhat)).factorization 2 := by
    simpa using (Sylow.card_eq_multiplicity (G := (↥c.Hhat)) (p := 2) P)
  have hPcard' : Nat.card (P : Subgroup (↥c.Hhat)) =
      Nat.card (c.S : Subgroup G) := by
    calc
      Nat.card (P : Subgroup (↥c.Hhat)) =
          Nat.card ((c.S : Subgroup G).subgroupOf c.Hhat) := by
            simp [P]
      _ = Nat.card (c.S : Subgroup G) := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hSleHhat).toEquiv
  rw [hPcard, hfact] at hPcard'
  norm_num at hPcard'
  exact hPcard'.symm

/-- The proved part of the Section-3 Klein-four-branch package: `V = O₂(Ĥ)`
is a Klein four group, `S` has order `8`, and `Ĥ/VU` is the dihedral group
of order six.  The uniform inverted Hall subgroup `K`, its nontriviality,
and the commutator centralization are separate theorem goals. -/
public structure FirstCaseKleinData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) where
  V : Subgroup G
  V_eq : V = twoCoreOf c.Hhat
  V_klein : IsKleinFour V
  S_card : Nat.card (↥(c.S : Subgroup G)) = 8
  quotient_d6 : Nonempty
    ((c.Hhat ⧸ (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) ≃* DihedralGroup 3)

end CFSG.GorensteinWalter

module

public import CFSG.RankThree.PartOne.KE.E7ThreeTorus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.RankThree.PartOne.KE.E7FiveData

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne
open scoped Matrix Pointwise MatrixGroups

@[expose] def e7T3Elt (ε : ℤ) : WeylGroup Tag.E7 :=
  if ε = 1 then (coxeterSystem Tag.E7).wordProd e7T3Word
  else (exists_weyl_neg_one.choose) * (coxeterSystem Tag.E7).wordProd e7T3Word

theorem e7T3_weylImage (u : Fin Tag.E7.rank → ℤ) :
    (coxeterSystem Tag.E7).wordProd e7T3Word • u = e7T3W *ᵥ u := by
  have hw : e7T3Word = ([0, 1, 2, 3, 4, 5] : List (Fin Tag.E7.rank)) ++ [0, 1, 2, 3, 4, 5] ++
      [0, 1, 2, 3, 4, 5] ++ [0, 1, 2, 3, 4, 5] := rfl
  rw [wordProd_smul_eq_wordMat_mulVec, hw, wordMat_append, wordMat_append, wordMat_append, e7T3W,
    e7T12W]
  simp only [pow_succ, pow_zero, one_mul]

theorem e7T3Elt_smul {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (u : Fin Tag.E7.rank → ℤ) : e7T3Elt ε • u = (ε • e7T3W) *ᵥ u := by
  rcases hε with rfl | rfl
  · simp [e7T3Elt, e7T3_weylImage]
  · have hne : ¬ ((-1 : ℤ) = 1) := by norm_num
    simp only [e7T3Elt, hne, ↓reduceIte, mul_smul, e7T3_weylImage]
    rw [exists_weyl_neg_one.choose_spec]
    simp only [neg_smul, one_smul]
    exact (Matrix.neg_mulVec u e7T3W).symm

structure E7ThreeFrame (K L : Type) [Field K] [Field L] [Algebra K L] (ℓ f p : ℕ)
    [Fact ℓ.Prime] [CharP L ℓ] (ε : ℤ) : Type where
  n : ModGL .E7 L
  hnm : n ∈ monomialSubgroup .E7 L
  hnW : ∀ u : Fin Tag.E7.rank → ℤ, weylQuotientHom .E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u
  g0 : ModGL .E7 L
  hg0C : g0 ∈ adjointGroup .E7 L
  hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n
  hperf : ∀ P : Subgroup (ModGL .E7 L), Finite P → P ≤ adjointGroup .E7 L →
    (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
      P ≤ (adjEmb .E7 K L).range
  hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
    (fixedCharTuples (ε • e7T3W) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E7 L)
  hconj : ∀ A : Subgroup (adjointGroup .E7 K), IsPGroup p A → ∃ c : adjointGroup .E7 K,
    ∀ x ∈ A, g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))

theorem exists_e7ThreeFrame (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    Nonempty (E7ThreeFrame K L ℓ f p ε) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  set n : ModGL .E7 L := canonicalRep (coxeterSystem .E7) L (e7T3Elt ε) with hn
  have hnm : n ∈ monomialSubgroup .E7 L := canonicalRep_mem_monomialSubgroup L _
  have hnW : weylQuotientHom .E7 L ⟨n, hnm⟩ = e7T3Elt ε :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hnC : n ∈ adjointGroup .E7 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  have hnWv : ∀ u : Fin Tag.E7.rank → ℤ, weylQuotientHom .E7 L ⟨n, hnm⟩ • u =
      (ε • e7T3W) *ᵥ u := fun u => by rw [hnW]; exact e7T3Elt_smul hε u
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (ε • e7T3W) Fr).map (rootDiagUnitHom .E7 L) := e7T3_twistedTorus n hnm hnWv Fr
  set N : ℕ := e7T3Order (Nat.card K) ε with hNdef
  set Z0 : Subgroup (ModGL .E7 L) := (fixedCharTuples (ε • e7T3W) Fr).map (rootDiagUnitHom .E7 L)
    with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n (Units.map (entrywiseHom Fr)) := hT.ge
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact natCard_e7T3Fixed hε hFr hℓq
  have hN : N ≠ 0 := by
    have h1 : ((Nat.card K : ℤ) - ε) ≠ 0 := by
      have hq2' : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq2
      rcases hε with rfl | rfl <;> omega
    have h2 : ((Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) ≠ 0 := by
      have hq2' : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq2
      rcases hε with rfl | rfl <;> nlinarith
    rw [hNdef, e7T3Order]
    exact mul_ne_zero (Int.natAbs_ne_zero.2 h1) (pow_ne_zero 3 (Int.natAbs_ne_zero.2 h2))
  have hord : p ^ (Nat.card (adjointGroup .E7 K)).factorization p = p ^ N.factorization p :=
    e7T3_ordProj K hp hp3 hε hpf
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E7 2
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hf hK L hp hp3 n hnC Z0 hZ0le hN hZ0card hord
  refine ⟨⟨n, hnm, hnWv, g0, hg0C, hg0, hperf, hT, fun A hA => ?_⟩⟩
  obtain ⟨c, hc⟩ := hconj A hA
  exact ⟨c, fun x hx => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc x hx))⟩

end CFSG.RankThree.PartOne.KE

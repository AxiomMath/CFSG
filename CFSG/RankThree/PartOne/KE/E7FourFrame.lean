module

public import CFSG.RankThree.PartOne.KE.E7FourBlock
public import CFSG.RankThree.PartOne.KE.E7FourArith
public import CFSG.RankThree.PartOne.KE.E7FourClasses
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.RankThree.PartOne.KE.A1Weyl

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne
open scoped Matrix Pointwise MatrixGroups

structure E7FourFrame (K L : Type) [Field K] [Field L] [Algebra K L] (ℓ f p : ℕ)
    [Fact ℓ.Prime] [CharP L ℓ] : Type where
  n : ModGL .E7 L
  hnm : n ∈ monomialSubgroup .E7 L
  hnW : weylQuotientHom .E7 L ⟨n, hnm⟩ = (coxeterSystem .E7).wordProd e7F4Word
  g0 : ModGL .E7 L
  hg0C : g0 ∈ adjointGroup .E7 L
  hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n
  hperf : ∀ P : Subgroup (ModGL .E7 L), Finite P → P ≤ adjointGroup .E7 L →
    (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
      P ≤ (adjEmb .E7 K L).range
  hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
    (fixedCharTuples e7F4W (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E7 L)
  hconj : ∀ A : Subgroup (adjointGroup .E7 K), IsPGroup p A → ∃ c : adjointGroup .E7 K,
    ∀ x ∈ A, g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))

theorem exists_e7FourFrame (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    Nonempty (E7FourFrame K L ℓ f p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E7 L →* ModGL .E7 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  set n : ModGL .E7 L := canonicalRep (coxeterSystem .E7) L
    ((coxeterSystem .E7).wordProd e7F4Word) with hn
  have hnm : n ∈ monomialSubgroup .E7 L := canonicalRep_mem_monomialSubgroup L _
  have hnW : weylQuotientHom .E7 L ⟨n, hnm⟩ = (coxeterSystem .E7).wordProd e7F4Word :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hnC : n ∈ adjointGroup .E7 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  have hnWv : ∀ u, weylQuotientHom .E7 L ⟨n, hnm⟩ • u = e7F4W *ᵥ u := fun u => by
    rw [hnW]
    exact e7F4_weylImage u
  have hT : twistedTorusOf n Φ = (fixedCharTuples e7F4W Fr).map (rootDiagUnitHom .E7 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnWv Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set G1 := fixedBlockTuples e7F4W Fr
    (e7F4Bas e7T12VList e7F4B2List '' {i : Fin Tag.E7.rank | (i : ℕ) < 5}) with hG1
  set G2 := fixedBlockTuples e7F4W Fr
    (e7F4Bas e7F4B2List e7T12VList '' {i : Fin Tag.E7.rank | (i : ℕ) < 5}) with hG2
  set N : ℕ := (Nat.card K ^ 2 + 1) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E7 L) := (G1 ⊔ G2).map (rootDiagUnitHom .E7 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e7F4_card_sup Fr hFr hℓ hℓq
  have hN : N ≠ 0 := pow_ne_zero 2 (by positivity)
  have hord : p ^ (Nat.card (adjointGroup .E7 K)).factorization p = p ^ N.factorization p :=
    e7F4_ordProj hp hp3 hpf
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E7 2
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hf hK L hp hp3 n hnC Z0 hZ0le hN hZ0card hord
  refine ⟨⟨n, hnm, hnW, g0, hg0C, hg0, hperf, hT, fun A hA => ?_⟩⟩
  obtain ⟨c, hc⟩ := hconj A hA
  exact ⟨c, fun x hx => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc x hx))⟩

end CFSG.RankThree.PartOne.KE

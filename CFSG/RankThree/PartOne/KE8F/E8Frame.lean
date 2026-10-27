module

public import CFSG.RankThree.PartOne.KE8F.E8Arith
public import CFSG.RankThree.PartOne.KE8F.E8TorCount
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.RankThree.PartOne.KE.A1Weyl

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise MatrixGroups


theorem e8P4_weylImage (u : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem Tag.E8).wordProd e8P4WW • u = e8P4V *ᵥ u := by
  rw [wordProd_smul_eq_wordMat_mulVec, e8P4_wordMat]

structure E8P4Frame0 (K L : Type) [Field K] [Field L] [Algebra K L] (ℓ f : ℕ) [Fact ℓ.Prime]
    [CharP L ℓ] : Type where
  n : ModGL .E8 L
  hnm : n ∈ monomialSubgroup .E8 L
  hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8P4WW
  g0 : ModGL .E8 L
  hg0C : g0 ∈ adjointGroup .E8 L
  hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n
  hperf : ∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
    (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
      P ≤ (adjEmb .E8 K L).range
  hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
    (fixedCharTuples e8P4V (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E8 L)

structure E8P4Frame (K L : Type) [Field K] [Field L] [Algebra K L] (ℓ f p : ℕ) [Fact ℓ.Prime]
    [CharP L ℓ] : Type extends E8P4Frame0 K L ℓ f where
  hconj : ∀ A : Subgroup (adjointGroup .E8 K), IsPGroup p A → ∃ c : adjointGroup .E8 K,
    ∀ x ∈ A, g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))

theorem e8P4_twistedTorus {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] {n : ModGL .E8 L} (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8P4WW) :
    twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples e8P4V (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E8 L) := by
  have hnWv : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = e8P4V *ᵥ u := fun u => by
    rw [hnW]
    exact e8P4_weylImage u
  rw [← twistedFixedTuples_eq_fixedCharTuples hnWv (iterateFrobenius L ℓ f)]
  exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl (iterateFrobenius L ℓ f)

theorem exists_e8P4Frame0 (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L ℓ] : Nonempty (E8P4Frame0 K L ℓ f) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  set n : ModGL .E8 L := canonicalRep (coxeterSystem .E8) L
    ((coxeterSystem .E8).wordProd e8P4WW) with hn
  have hnm : n ∈ monomialSubgroup .E8 L := canonicalRep_mem_monomialSubgroup L _
  have hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8P4WW :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_gen .E8 K hf L n hnC
  refine ⟨⟨n, hnm, hnW, g0, hg0C, hg0, fun P hP hPC hPF hPperf => ?_,
    e8P4_twistedTorus hnm hnW⟩⟩
  have := (finite_fixed_subgroup_rational_perfect (K := K) (L := L) 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr P hPC hPF).2.2 P le_rfl hPperf
  rwa [adjEmb_range]

theorem exists_e8P4Frame (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    Nonempty (E8P4Frame K L ℓ f p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hpq : ¬ p ∣ Nat.card K := fun h => by
    have h1 : p ∣ Nat.card K * Nat.card K := Dvd.dvd.mul_right h _
    have := (Nat.dvd_add_right h1).1 hpf
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  set n : ModGL .E8 L := canonicalRep (coxeterSystem .E8) L
    ((coxeterSystem .E8).wordProd e8P4WW) with hn
  have hnm : n ∈ monomialSubgroup .E8 L := canonicalRep_mem_monomialSubgroup L _
  have hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8P4WW :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n Φ = (fixedCharTuples e8P4V Fr).map (rootDiagUnitHom .E8 L) :=
    e8P4_twistedTorus hnm hnW
  set N : ℕ := (Nat.card K * Nat.card K + 1) ^ 4 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (fixedCharTuples e8P4V Fr).map (rootDiagUnitHom .E8 L)
    with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact card_T0 hFr hℓq
  have hN : N ≠ 0 := pow_ne_zero 4 (by positivity)
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8P4_ordProj hp hp5 hpq hpf
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp (by omega) n hnC Z0 hZ0le hN hZ0card hord
  refine ⟨⟨⟨n, hnm, hnW, g0, hg0C, hg0, hperf, hT⟩, fun A hA => ?_⟩⟩
  obtain ⟨c, hc⟩ := hconj A hA
  exact ⟨c, fun x hx => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc x hx))⟩

end CFSG.RankThree.PartOne.KE8F

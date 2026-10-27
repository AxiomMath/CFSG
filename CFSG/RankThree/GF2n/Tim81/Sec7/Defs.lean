module

public import CFSG.RankThree.GF2n.Tim81.Sec6.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection CFSG.LieType
  CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

@[expose] def m0Of (M V : Subgroup G) : Subgroup G :=
  ⨆ U ∈ sigmaSet M V, U

abbrev cenOf (X : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (X : Set G)

abbrev sigmaAt (A : Subgroup G) : Set (Subgroup G) :=
  sigmaSet (Subgroup.normalizer (A : Set G)) A

@[expose] def gammaAt (A : Subgroup G) : Set (Subgroup G) :=
  {B | ∃ C ∈ sigmaAt A, B ∈ sigmaAt C}

abbrev MBar (M : Subgroup G) : Type :=
  ↥M ⧸ pCore 2 ↥M

abbrev imgQ (M U : Subgroup G) : Subgroup (MBar M) :=
  (U.subgroupOf M).map (QuotientGroup.mk' _)

@[expose] def IsSUImage {K : Type} [Group K] (X : Subgroup K) (Δ : Set (Subgroup K))
    (f m : ℕ) (hf : 1 ≤ f) (hm : 2 ≤ m) : Prop :=
  ∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) →* K,
    Φ.ker ≤ Subgroup.center _ ∧ Φ.range = X ∧
      ∀ U : Subgroup K, U ∈ Δ ↔ ∃ x,
        U = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf) m).rootGroup
          (unitaryLongRoot m hm)) x).map Φ

@[expose] def IsSpImage {K : Type} [Group K] (X : Subgroup K) (Δ : Set (Subgroup K))
    (f m : ℕ) (hm : 1 ≤ m) : Prop :=
  ∃ Φ : ↥(StatedSp m (GaloisField 2 f)) →* K, Function.Injective Φ ∧ Φ.range = X ∧
    ∀ U : Subgroup K, U ∈ Δ ↔ ∃ x,
      U = (conjSub ((Symplectic.rootDatum m (GaloisField 2 f)).rootGroup
        (Pi.single (⟨m - 1, by omega⟩ : Fin m) 1)) x).map Φ

abbrev p0Of (M V X : Subgroup G) : Subgroup G :=
  Pc M V ⊓ cenOf X

@[expose] def r0Of (M V X : Subgroup G) : Subgroup G :=
  ⨆ C ∈ {C : Subgroup G | C ∈ sigmaSet M V ∧ C ≤ cenOf X}, C

@[expose] def y0Of (V X : Subgroup G) : Subgroup G :=
  ⨆ x ∈ cenOf X, conjSubgroup x V

structure L2Datum (M V A B : Subgroup G) (h : G) : Prop where
  memA : A ∈ sigmaSet M V
  memB : B ∈ sigmaSet M V
  l2 : IsL2Gen A B
  mem : h ∈ A ⊔ B
  order : orderOf h = Nat.card V + 1

structure Sec7Hyp (M V : Subgroup G) (n f : ℕ) : Prop extends Sec6Hyp M V where
  four_le : 4 ≤ n
  one_le : 1 ≤ f
  card_V : Nat.card V = 2 ^ f
  card_Pc : Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1)
  m0 : IsSUImage (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f n one_le
    (Nat.le_trans (Nat.le_add_left 2 2) four_le)
  lbar : ∀ g : G, conjSubgroup g V ∈ sigmaSet M V →
    imgQ M (lOf M V g) =
      inSubgroup (pCore 2) (imgQ M (m0Of M V) ⊓
        Subgroup.normalizer (imgQ M (conjSubgroup g V) : Set (MBar M)))

theorem Hyp.sigmaAt_eq (h : Hyp M V) : sigmaAt V = sigmaSet M V := by
  rw [sigmaAt, h.normalizer_eq]

theorem Hyp.mem_sigmaAt_conjSubgroup_iff (h : Hyp M V) (a : G) {U : Subgroup G} :
    U ∈ sigmaAt (conjSubgroup a V) ↔ conjSubgroup a⁻¹ U ∈ sigmaSet M V := by
  rw [sigmaAt, normalizer_conjSubgroup a V, h.normalizer_eq]
  exact mem_sigmaSet_conjSubgroup_iff a

theorem m0Of_conjSubgroup (a : G) :
    m0Of (conjSubgroup a M) (conjSubgroup a V) = conjSubgroup a (m0Of M V) := by
  apply le_antisymm
  · unfold m0Of
    refine iSup₂_le fun U hU => ?_
    have hU' : conjSubgroup a⁻¹ U ∈ sigmaSet M V :=
      (mem_sigmaSet_conjSubgroup_iff a).mp hU
    calc U = conjSubgroup a (conjSubgroup a⁻¹ U) := by
          rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      _ ≤ conjSubgroup a (⨆ C ∈ sigmaSet M V, C) :=
          conjSubgroup_mono (le_iSup₂_of_le (conjSubgroup a⁻¹ U) hU' le_rfl)
  · have hmap : conjSubgroup a (⨆ C ∈ sigmaSet M V, C) =
        ⨆ C ∈ sigmaSet M V, conjSubgroup a C := by
      simp only [conjSubgroup, Subgroup.map_iSup]
    unfold m0Of
    rw [hmap]
    refine iSup₂_le fun C hC => ?_
    have hC' : conjSubgroup a C ∈ sigmaSet (conjSubgroup a M) (conjSubgroup a V) := by
      refine (mem_sigmaSet_conjSubgroup_iff a).mpr ?_
      rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    exact le_iSup₂_of_le (conjSubgroup a C) hC' le_rfl

theorem Sec5Hyp.self_mem_sigmaAt (hS : Sec5Hyp M V) {A : Subgroup G}
    (hA : A ∈ sigmaSet M V) : V ∈ sigmaAt A := by
  obtain ⟨g, rfl, hH⟩ := hA
  rw [sigmaAt, (hS.root g).toHyp.normalizer_eq]
  exact (hS.mem_sigmaSet_iff_self_mem).mp ⟨g, rfl, hH⟩

theorem Sec6Hyp.mem_gammaAt_self (hS : Sec6Hyp M V) : V ∈ gammaAt V := by
  obtain ⟨A, hA⟩ := hS.ne
  refine ⟨A, ?_, hS.sec5.self_mem_sigmaAt hA⟩
  rw [hS.sec5.toRootHyp.toHyp.sigmaAt_eq]
  exact hA

theorem gammaAt_subset_omegaSet (V : Subgroup G) : gammaAt V ⊆ omegaSet V := by
  intro B hB
  rw [gammaAt] at hB
  obtain ⟨C, hC, hB⟩ := hB
  rw [sigmaAt] at hC hB
  obtain ⟨x, rfl, -⟩ := hC
  obtain ⟨y, rfl, -⟩ := hB
  exact ⟨y * x, trivial, conjSubgroup_conjSubgroup y x V⟩

theorem Sec5Hyp.Pc_subgroupOf (hS : Sec5Hyp M V)
    (hne : (sigmaSet M V).Nonempty) : (Pc M V).subgroupOf M = pCore 2 ↥M := by
  obtain ⟨A, hA⟩ := hne
  obtain ⟨g, -, hH⟩ := hA
  have hQ : inSubgroup (pCore 2) M = Pc M V :=
    (Sec45Shape.pCore_eq_and hS.toRootHyp (hS.shape ⟨g, rfl, hH⟩)).1
  rw [← hQ]
  change ((pCore 2 ↥M).map M.subtype).subgroupOf M = pCore 2 ↥M
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

end CFSG.RankThree.GF2n.Tim81

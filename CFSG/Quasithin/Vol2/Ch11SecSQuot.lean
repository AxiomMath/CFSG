module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch11SecA11Comp
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open

variable {G : Type} [Group G]

theorem pCoreOf_two_eq_map (K : Subgroup G) : pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype :=
  CFSG.openPCoreOf_eq_map_pCore 2 K

theorem map_comap_modO2Image {K A : Subgroup G} (hA : A ≤ K) :
    ((modO2Image K A).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map K.subtype =
      A ⊔ pCoreOf 2 K := by
  unfold modO2Image
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hA, ← pCoreOf_two_eq_map]

theorem sup_eq_of_modO2Image_eq {K A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K)
    (h : modO2Image K A = modO2Image K B) : A ⊔ pCoreOf 2 K = B ⊔ pCoreOf 2 K := by
  rw [← map_comap_modO2Image hA, ← map_comap_modO2Image hB, h]

theorem modO2Image_self (K : Subgroup G) : modO2Image K K = ⊤ := by
  unfold modO2Image
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem le_sup_of_modO2Image_eq_top {K A : Subgroup G} (hA : A ≤ K)
    (h : modO2Image K A = ⊤) : K ≤ A ⊔ pCoreOf 2 K := by
  have := sup_eq_of_modO2Image_eq hA le_rfl (h.trans (modO2Image_self K).symm)
  rw [this]
  exact le_sup_left

theorem perfectCore_sup_eq [Finite G] {A Q : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hQ : Group.IsSolvable ↥Q) (hQA : Q ≤ Subgroup.normalizer (A : Set G)) :
    perfectCore (A ⊔ Q) = A := by
  have hAn : (A.subgroupOf (A ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hQA)
  exact le_antisymm (perfectCore_le_of_sup_solvable le_sup_left hAn rfl hQ)
    (le_perfectCore_of_perfect le_sup_left hA)

theorem isSolvable_pCoreOf_two [Finite G] (K : Subgroup G) : Group.IsSolvable ↥(pCoreOf 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).isNilpotent
  infer_instance

theorem modO2Image_perfect {K A : Subgroup G} (hA : A ≤ K) (hp : ⁅A, A⁆ = A) :
    ⁅modO2Image K A, modO2Image K A⁆ = modO2Image K A := by
  have hA' : ⁅A.subgroupOf K, A.subgroupOf K⁆ = A.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA, hp]
  unfold modO2Image
  rw [← Subgroup.map_commutator, hA']

theorem modO2Image_ne_bot [Finite G] {K A : Subgroup G} (hA : A ≤ K) (hp : ⁅A, A⁆ = A)
    (hne : A ≠ ⊥) : modO2Image K A ≠ ⊥ := by
  intro hbot
  have h1 : A ⊔ pCoreOf 2 K = ⊥ ⊔ pCoreOf 2 K := by
    refine sup_eq_of_modO2Image_eq hA bot_le ?_
    rw [hbot]
    unfold modO2Image
    simp
  have hAQ : A ≤ pCoreOf 2 K := by
    rw [← bot_sup_eq (pCoreOf 2 K), ← h1]
    exact le_sup_left
  have : Group.IsSolvable ↥(pCoreOf 2 K) := isSolvable_pCoreOf_two K
  exact hne (SecA.eq_bot_of_perfect_of_le_solvable hAQ hp)

theorem modO2Image_le_normalizer {K A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    modO2Image K B ≤ Subgroup.normalizer (modO2Image K A : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have hle : B.subgroupOf K ≤ Subgroup.normalizer (A.subgroupOf K : Set ↥K) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hb' := (Subgroup.mem_normalizer_iff.mp (hBA hb)) a
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hb'
  exact (Subgroup.map_mono hle).trans (Subgroup.le_normalizer_map _)

theorem modO2Image_subnormal {K J N : Subgroup G} (hJN : IsSubnormal J N) :
    IsSubnormal (modO2Image K J) (modO2Image K N) :=
  A3.subnormal_map _ (A3.subnormal_comap K.subtype hJN)

theorem isSylowTwoOf_modO2Image [Finite G] {K S : Subgroup G}
    (hS : QuasithinUnique.IsSylowTwoOf S K) : QuasithinUnique.IsSylowTwoOf (modO2Image K S) ⊤ :=
  isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS) _
    (QuotientGroup.mk'_surjective _)

end CFSG.Quasithin.Vol2.Ch11.SecS

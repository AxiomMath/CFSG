module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBF4EndNode
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot

namespace TableBF4TwoInputs

section EndNode

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def nodeElt : adjointGroup .F4 K :=
  TableBF4Two.rho K 3 (uSL 1 * vSL 1)

theorem nodeElt_pow_three : nodeElt K ^ 3 = 1 := by
  rw [nodeElt, ← map_pow, TableBF4Two.S0_pow_three CharTwo.two_eq_zero, map_one]

theorem nodeElt_ne_one : nodeElt K ≠ 1 := fun h =>
  TableBF4Two.S0_ne_one (K := K) CharTwo.two_eq_zero
    (TableBF4Two.rho_injective _ (h.trans (map_one _).symm))

theorem orderOf_nodeElt : orderOf (nodeElt K) = 3 :=
  orderOf_eq_prime nodeElt_pow_three nodeElt_ne_one

theorem nodeElt_mem_highestRootRankOne :
    nodeElt K ∈ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) := by
  rw [Subgroup.mem_subgroupOf, highestRootRankOne_eq_rootSL2R, ← range_rootSL2_rootR]
  exact ⟨uSL 1 * vSL 1, by rw [nodeElt, TableBF4Two.coe_rho]; rfl⟩

theorem zpowers_nodeElt_le :
    Subgroup.zpowers (nodeElt K) ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) :=
  Subgroup.zpowers_le.2 nodeElt_mem_highestRootRankOne

theorem card_zpowers_nodeElt (hK : Nat.card K = 2) :
    Nat.card (Subgroup.zpowers (nodeElt K)) = Nat.card K + 1 := by
  rw [Nat.card_zpowers, orderOf_nodeElt, hK]

theorem centralizer_singleton_eq_zpowers (x : adjointGroup .F4 K) :
    Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) =
      Subgroup.centralizer (Subgroup.zpowers x : Set (adjointGroup .F4 K)) := by
  ext c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (hc x rfl) k).eq
  · intro hc h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hc h (Subgroup.mem_zpowers h)

theorem layer_centralizer_nodeElt (hK : Nat.card K = 2) :
    LargeEvenLayer (Subgroup.centralizer ({nodeElt K} : Set (adjointGroup .F4 K))) = C3Levi K ∧
      IsComponentOf (C3Levi K) (Subgroup.centralizer ({nodeElt K} : Set (adjointGroup .F4 K))) := by
  rw [centralizer_singleton_eq_zpowers]
  have hX := centralizer_nonsplit zpowers_nodeElt_le (Subgroup.isCyclic_zpowers _)
    (card_zpowers_nodeElt hK)
  refine TableBSymp.largeEvenLayer_eq_of_commutator_mem ?_ ?_ isQuasisimple_C3Levi
  · rw [hX.1]
    exact le_sup_right
  · intro g hg h hh
    exact commutator_mem_C3Levi_of_mem_centralizer_nonsplit zpowers_nodeElt_le
      (Subgroup.isCyclic_zpowers _) (card_zpowers_nodeElt hK) hg hh

theorem endNodeAt_nodeElt (hK : Nat.card K = 2) {A : Subgroup (adjointGroup .F4 K)}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hx : nodeElt K ∈ A) :
    TableBF4.EndNodeAt A (nodeElt K) := by
  obtain ⟨hL, hcomp⟩ := layer_centralizer_nodeElt (K := K) hK
  have hX := centralizer_nonsplit zpowers_nodeElt_le (Subgroup.isCyclic_zpowers _)
    (card_zpowers_nodeElt hK)
  refine ⟨hx, nodeElt_ne_one, hL ▸ hcomp, fun s hs => ?_⟩
  rw [hL]
  constructor
  · intro hj
    have hsC :
        s ∈ Subgroup.centralizer (Subgroup.zpowers (nodeElt K) : Set (adjointGroup .F4 K)) := by
      rw [← centralizer_singleton_eq_zpowers, Subgroup.mem_centralizer_singleton_iff]
      exact hA s hs _ hx
    obtain ⟨y, hy, d, hd, rfl⟩ := exists_mul_of_mem_centralizer_nonsplit zpowers_nodeElt_le
      (Subgroup.isCyclic_zpowers _) (card_zpowers_nodeElt hK) hsC
    have hyD : ∀ j ∈ C3Levi K, y * j = j * y := fun j hj =>
      (Subgroup.mem_centralizer_iff.1 (hX.2.2 hy) j hj).symm
    have hdc : (⟨d, hd⟩ : C3Levi K) ∈ Subgroup.center (C3Levi K) := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      have h1 := hj j j.2
      have h2 := hyD j j.2
      change (j : adjointGroup .F4 K) * d = d * j
      calc (j : adjointGroup .F4 K) * d = y⁻¹ * (y * j) * d := by group
        _ = y⁻¹ * (j * y) * d := by rw [h2]
        _ = y⁻¹ * (j * (y * d)) := by group
        _ = y⁻¹ * (y * d * j) := by rw [h1]
        _ = d * j := by group
    rw [center_C3Levi_eq_bot, Subgroup.mem_bot] at hdc
    have hd1 : d = 1 := congrArg Subtype.val hdc
    rw [hd1, mul_one]
    exact hy
  · intro hmem j hj
    exact (Subgroup.mem_centralizer_iff.1 (hX.2.2 hmem) j hj).symm

theorem endNodeAt_of_mulEquiv (hK : Nat.card K = 2) (α : adjointGroup .F4 K ≃* adjointGroup .F4 K)
    {A : Subgroup (adjointGroup .F4 K)} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hx : α (nodeElt K) ∈ A) : TableBF4.EndNodeAt A (α (nodeElt K)) := by
  set A' := A.map α.symm.toMonoidHom with hA'
  have hA'c : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA a ha b hb]
  have hx' : nodeElt K ∈ A' := ⟨α (nodeElt K), hx, by simp⟩
  have h := (endNodeAt_nodeElt hK hA'c hx').map α
  have hmap : A'.map α.toMonoidHom = A := by
    rw [hA', Subgroup.map_map]
    convert Subgroup.map_id A
    ext g
    simp
  rwa [hmap] at h

end EndNode

end TableBF4TwoInputs

end CFSG.StandardType

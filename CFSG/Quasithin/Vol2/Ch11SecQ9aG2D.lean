module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2A
public import CFSG.Quasithin.Vol2.Ch11SecQ9aShC
public import CFSG.Timmesfeld.Orders.ExceptionalTorus

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6

theorem C11P9A.normalizer_subgroupOf_eq {G : Type*} [Group G] {U C : Subgroup G} (hUC : U ≤ C) :
    Subgroup.normalizer ((U.subgroupOf C : Subgroup ↥C) : Set ↥C) =
      (Subgroup.normalizer (U : Set G)).subgroupOf C := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    by_cases hg : g ∈ C
    · simpa [Subgroup.mem_subgroupOf] using h ⟨g, hg⟩
    · have h1 : g ∉ U := fun hgU => hg (hUC hgU)
      have h2 : (x : G) * g * (x : G)⁻¹ ∉ U := fun h3 => hg (by
        have e : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * x := by group
        rw [e]
        exact C.mul_mem (C.mul_mem (C.inv_mem x.2) (hUC h3)) x.2)
      exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
  · intro h g
    simpa [Subgroup.mem_subgroupOf] using h (g : G)

section Borel


theorem C11P9A.card_borelGroup {τ : Tag} {K : Type} [Field K] [Finite K] :
    Nat.card ↥(borelGroup τ K) = Nat.card ↥(posUnipotent τ K) * Nat.card ↥(torusGroup τ K) := by
  have : Finite (ModGL τ K) := finite_modGL
  show Nat.card ↥(torusGroup τ K ⊔ posUnipotent τ K) = _
  exact C11P9A.card_sup_eq_mul torusGroup_le_normalizer_posUnipotent
    (by rw [inf_comm]; exact torusGroup_inf_posUnipotent)


theorem C11P9A.normalizer_posUnipotent_inf_eq {τ : Tag} {K : Type} [Field K] :
    Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) ⊓ adjointGroup τ K =
      borelGroup τ K := by
  obtain ⟨-, -, -, -, -, -, -, -, hnormal, -, -, hBC⟩ := triangular_borel_structure.{0, 0} τ K
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp hnormal
  refine le_antisymm ?_ (le_inf hBN (hBC K).1)
  have hUA : posUnipotent τ K ≤
      Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) ⊓ adjointGroup τ K :=
    le_inf Subgroup.le_normalizer posUnipotent_le_adjointGroup
  have hle := (chevalley_positive_root_overgroup_parabolic_containment inf_le_right hUA).1
  have hJ : {k | weylElt τ K k 1 ∈
      Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) ⊓ adjointGroup τ K} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hk
    have hy : yUnit τ K k (-1) ∈ posUnipotent τ K := by
      rw [yUnit_eq_weylElt_mul, neg_neg]
      exact (Subgroup.mem_normalizer_iff.mp hk.1 _).mp (xUnit_mem_posUnipotent k 1)
    have hn : weylElt τ K k 1 ∈ parabolicSubgroup τ K ∅ := by
      rw [parabolicSubgroup_empty, weylElt_one_eq]
      exact hUB (mul_mem (mul_mem (xUnit_mem_posUnipotent k 1) hy) (xUnit_mem_posUnipotent k 1))
    exact weylElt_mem_parabolicSubgroup_iff.mp hn
  rw [hJ, parabolicSubgroup_empty] at hle
  exact hle

theorem factG2FourBorelNorm_holds : FactG2FourBorelNorm := by
  intro K _ _ _ hK
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hNC := C11P9A.normalizer_posUnipotent_inf_eq (τ := Tag.G2) (K := K)
  have hBN : borelGroup Tag.G2 K ≤ Subgroup.normalizer (posUnipotent Tag.G2 K : Set _) :=
    hNC ▸ inf_le_left
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := hNC ▸ inf_le_right
  obtain ⟨hcov, hinj, -⟩ := exceptional_ordinary_minimal_Borel_intersections Tag.G2 K
  have hcov' : ∀ j, borelGroup Tag.G2 K ⋖ parabolicSubgroup Tag.G2 K {g2Index j} := fun j =>
    (hcov _ (parabolicSubgroup_le_adjointGroup _ _ _)).2 ⟨_, rfl⟩
  have hne : parabolicSubgroup Tag.G2 K {g2Index 0} ≠ parabolicSubgroup Tag.G2 K {g2Index 1} :=
    fun h => absurd (g2Index_injective (hinj h)) (by decide)
  rw [C11P9A.normalizer_subgroupOf_eq hUC, inf_eq_of_covBy (hcov' 0) (hcov' 1) hne]
  refine ⟨fun x hx => hBN hx, ?_⟩
  have e : (Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K))).subgroupOf
      (adjointGroup Tag.G2 K) = (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [← hNC]
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv, C11P9A.card_borelGroup,
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2, hK]
  norm_num

end Borel

end CFSG.Quasithin.Vol2.Ch11.SecS

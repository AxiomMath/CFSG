module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLift
public import CFSG.Quasithin.Vol2.GoldschmidtF431Order

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431

universe u

section Sub

variable {G : Type u} [Group G] (K₀ : Subgroup G)

theorem sub_mem_iff_of_map {Y' : Subgroup K₀} {Y : Subgroup G} (e : Y'.map K₀.subtype = Y)
    (x : K₀) : x ∈ Y' ↔ (x : G) ∈ Y := by
  rw [← e]
  exact (Subgroup.mem_map_iff_mem K₀.subtype_injective).symm

theorem sub_map_subgroupOf {X : Subgroup G} (hX : X ≤ K₀) :
    (X.subgroupOf K₀).map K₀.subtype = X :=
  Subgroup.map_subgroupOf_eq_of_le hX

theorem sub_perfectCore_map {N : Subgroup G} (hN : N ≤ K₀) :
    (perfectCore (N.subgroupOf K₀)).map K₀.subtype = perfectCore N := by
  rw [← perfectCore_map_of_injective K₀.subtype K₀.subtype_injective, sub_map_subgroupOf K₀ hN]

theorem sub_centerOf_map {R : Subgroup G} (hR : R ≤ K₀) :
    (centerOf (R.subgroupOf K₀)).map K₀.subtype = centerOf R := by
  rw [← centerOf_map_of_injective K₀.subtype K₀.subtype_injective, sub_map_subgroupOf K₀ hR]

theorem sub_pCoreOf_map {N : Subgroup G} (hN : N ≤ K₀) :
    (pCoreOf 2 (N.subgroupOf K₀)).map K₀.subtype = pCoreOf 2 N := by
  rw [← pCoreOf_map_of_injective K₀.subtype K₀.subtype_injective, sub_map_subgroupOf K₀ hN]

theorem sub_mem_centerOf_perfectCore {N : Subgroup G} (hN : N ≤ K₀) (x : K₀) :
    x ∈ centerOf (perfectCore (N.subgroupOf K₀)) ↔ (x : G) ∈ centerOf (perfectCore N) := by
  refine sub_mem_iff_of_map K₀ ?_ x
  rw [← centerOf_map_of_injective K₀.subtype K₀.subtype_injective, sub_perfectCore_map K₀ hN]

theorem sub_mem_centerOf_pCoreOf {N : Subgroup G} (hN : N ≤ K₀) (x : K₀) :
    x ∈ centerOf (pCoreOf 2 (N.subgroupOf K₀)) ↔ (x : G) ∈ centerOf (pCoreOf 2 N) := by
  refine sub_mem_iff_of_map K₀ ?_ x
  rw [← centerOf_map_of_injective K₀.subtype K₀.subtype_injective, sub_pCoreOf_map K₀ hN]

theorem sub_mem_centralizer {a x : K₀} :
    x ∈ Subgroup.centralizer ({a} : Set K₀) ↔
      (x : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro e
    exact congrArg Subtype.val e
  · intro e
    exact Subtype.ext e

theorem sub_inf_centralizer {A : Subgroup G} (a : K₀) :
    A.subgroupOf K₀ ⊓ Subgroup.centralizer ({a} : Set K₀) =
      (A ⊓ Subgroup.centralizer ({(a : G)} : Set G)).subgroupOf K₀ := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    sub_mem_centralizer]

theorem sub_centralizer_inf {A : Subgroup G} (a : K₀) :
    Subgroup.centralizer ({a} : Set K₀) ⊓ A.subgroupOf K₀ =
      (Subgroup.centralizer ({(a : G)} : Set G) ⊓ A).subgroupOf K₀ := by
  rw [inf_comm, sub_inf_centralizer, inf_comm]

theorem sub_card {X : Subgroup G} (hX : X ≤ K₀) : Nat.card (X.subgroupOf K₀) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem sub_isSylowTwoOf_iff {A B : Subgroup G} (hAB : A ≤ B) (hB : B ≤ K₀) :
    IsSylowTwoOf (A.subgroupOf K₀) (B.subgroupOf K₀) ↔ IsSylowTwoOf A B := by
  have hA : A ≤ K₀ := hAB.trans hB
  have e : ((A.subgroupOf K₀).subgroupOf (B.subgroupOf K₀)).index = (A.subgroupOf B).index :=
    Subgroup.relIndex_subgroupOf hB
  have p : IsPGroup 2 ↥(A.subgroupOf K₀) ↔ IsPGroup 2 ↥A :=
    ⟨fun hp => hp.of_equiv (Subgroup.subgroupOfEquivOfLe hA), fun hp =>
      hp.of_equiv (Subgroup.subgroupOfEquivOfLe hA).symm⟩
  constructor
  · rintro ⟨-, h2, h3⟩
    exact ⟨hAB, p.1 h2, by rwa [e] at h3⟩
  · rintro ⟨-, h2, h3⟩
    exact ⟨fun x hx => hAB hx, p.2 h2, by rwa [e]⟩

end Sub

end CFSG.Quasithin.H13.F431.Un

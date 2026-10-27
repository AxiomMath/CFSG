module

public import CFSG.Quasithin.Background.C116Two.OrbitAbstract
public import CFSG.Quasithin.Background.C116Two.OrbitFamily
public import CFSG.Quasithin.Background.C116Two.OrbitCentralizer
public import CFSG.Quasithin.Background.C116Two.OrbitFixed

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_orbitW {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T) :
    Nat.card ↥(orbitW A L) * Nat.card ↥(blockZ L) ^ ((A ⊓ Subgroup.normalizer (L : Set G)).relIndex A) =
      Nat.card ↥(orbitC A L) * Nat.card ↥(blockU L) ^ ((A ⊓ Subgroup.normalizer (L : Set G)).relIndex A) := by
  classical
  obtain ⟨hcomm, hLU⟩ := orbit_family_hyps h hAT
  haveI : Fintype ↥(orbitBlocks A L) := Fintype.ofFinite _
  have key := card_iSup_mul_prod_eq (fun i : ↥(orbitBlocks A L) => blockU (i : Subgroup G))
    (fun i => blockZ (i : Subgroup G)) (fun i => (i : Subgroup G)) (fun i => inf_le_left) hcomm hLU
    (fun i => rfl)
  rw [← orbitW_eq_iSup, ← orbitC_eq_iSup] at key
  have hZ : ∀ i : ↥(orbitBlocks A L),
      Nat.card ↥(blockZ (i : Subgroup G)) = Nat.card ↥(blockZ L) := by
    rintro ⟨_, a, _, rfl⟩
    exact card_blockZ_conjByElt a L
  have hU : ∀ i : ↥(orbitBlocks A L),
      Nat.card ↥(blockU (i : Subgroup G)) = Nat.card ↥(blockU L) := by
    rintro ⟨_, a, _, rfl⟩
    exact card_blockU_conjByElt a L
  simp only [hZ, hU, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    card_orbitBlocks] at key
  exact key

theorem relIndex_centralizer_orbitW {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T)
    (hAe : IsElemAbelian 2 A) :
    (A ⊓ Subgroup.centralizer (orbitW A L : Set G)).relIndex A =
      (A ⊓ Subgroup.normalizer (L : Set G)).relIndex A *
        ((A ⊓ Subgroup.normalizer (L : Set G)) ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex
          (A ⊓ Subgroup.normalizer (L : Set G)) := by
  rw [centralizer_orbitW_eq (fun x hx y hy => congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))]
  have hle : A ⊓ Subgroup.centralizer (blockU L : Set G) ≤ A ⊓ Subgroup.normalizer (L : Set G) :=
    fun x hx => ⟨hx.1, inf_centralizer_blockU_le_normalizer h hAT hx⟩
  have heq : A ⊓ Subgroup.centralizer (blockU L : Set G) =
      (A ⊓ Subgroup.normalizer (L : Set G)) ⊓ Subgroup.centralizer (blockU L : Set G) :=
    le_antisymm (le_inf hle inf_le_right) (inf_le_inf_right _ inf_le_left)
  rw [heq, mul_comm]
  exact (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left inf_le_left).symm

theorem fixedPts_inf_centralizer_le {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T) :
    (orbitW A L ⊓ Subgroup.centralizer (A : Set G)) ⊓
        (orbitW A L ⊓ Subgroup.centralizer (L : Set G)) ≤ orbitC A L := by
  classical
  obtain ⟨hcomm, hLU⟩ := orbit_family_hyps h hAT
  haveI : Fintype ↥(orbitBlocks A L) := Fintype.ofFinite _
  intro x hx
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxW, hxA⟩ := Subgroup.mem_inf.mp h1
  obtain ⟨_, hxL⟩ := Subgroup.mem_inf.mp h2
  rw [orbitC_eq_iSup]
  rw [orbitW_eq_iSup] at hxW
  refine iSup_inf_iInf_centralizer_le (fun i : ↥(orbitBlocks A L) => blockU (i : Subgroup G))
    (fun i => blockZ (i : Subgroup G)) (fun i => (i : Subgroup G)) hcomm hLU (fun i => rfl)
    (Subgroup.mem_inf.mpr ⟨hxW, ?_⟩)
  rw [Subgroup.mem_iInf]
  rintro ⟨i, a, ha, rfl⟩
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hl : a⁻¹ * y * a ∈ L := mem_conjByElt.mp hy
  have hca : Commute a x := Subgroup.mem_centralizer_iff.mp hxA a ha
  have hcl : Commute (a⁻¹ * y * a) x := Subgroup.mem_centralizer_iff.mp hxL _ hl
  have hy' : y = a * (a⁻¹ * y * a) * a⁻¹ := by group
  have hcy : Commute y x := by
    rw [hy']
    exact (hca.mul_left hcl).mul_left hca.inv_left
  exact hcy

theorem card_fixed_orbitW_le {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T) :
    Nat.card ↥(orbitW A L ⊓ Subgroup.centralizer (A : Set G)) * Nat.card ↥(blockZ L) ≤
      Nat.card ↥(orbitC A L) *
        Nat.card {u : G // u ∈ blockU L ∧ ∀ b ∈ A ⊓ Subgroup.normalizer (L : Set G),
          ⁅u, b⁆ ∈ blockZ L} := by
  have hL : IsShort2 L := h.chi.1.1
  set K : Subgroup G := orbitW A L ⊓ Subgroup.centralizer (L : Set G) with hK
  set Y : Subgroup G := fixModZ hL (A ⊓ Subgroup.normalizer (L : Set G)) with hY
  have h1 := fixedPts_le_fixModZ_sup h hAT
  have h2 := fixedPts_inf_centralizer_le h hAT
  have h3 := fixModZ_inf_eq (A := A) hL
  have hYK : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y := fun y hy k hk =>
    Subgroup.mem_centralizer_iff.mp hk.2 y (blockU_le_left L hy.1)
  have h4 := card_mul_le_of_le_sup hYK h1
  rw [h3] at h4
  have h5 : Nat.card ↥((orbitW A L ⊓ Subgroup.centralizer (A : Set G)) ⊓ K) ≤
      Nat.card ↥(orbitC A L) := Subgroup.card_le_of_le h2
  calc Nat.card ↥(orbitW A L ⊓ Subgroup.centralizer (A : Set G)) * Nat.card ↥(blockZ L)
      ≤ Nat.card ↥((orbitW A L ⊓ Subgroup.centralizer (A : Set G)) ⊓ K) * Nat.card ↥Y := h4
    _ ≤ Nat.card ↥(orbitC A L) * Nat.card ↥Y := Nat.mul_le_mul_right _ h5
    _ = _ := rfl

end CFSG.Quasithin.C116Two

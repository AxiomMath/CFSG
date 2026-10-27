module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAction

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.QuasithinUnique.Setup.Family

variable {M : Type} [Group M] [Finite M] {G L : Subgroup M}

theorem mem_center_of_mem_ker_actionOnCQ (hLG : L ≤ G) (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hcent : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L) (hperf : Group.IsPerfect ↥L)
    (g : ↥G)
    (hg : g ∈ (actionOnCQ hLG ((Subgroup.normal_subgroupOf_iff hLG).2
      fun l g hl hg => hnorm g hg l hl)).ker) :
    ∃ hgL : (g : M) ∈ L, (⟨(g : M), hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
  have hLn : (L.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff hLG).2 fun l g hl hg => hnorm g hg l hl
  have h1 := (actionOnCQ_eq_one_iff hLG hLn hperf g).1 hg
  have hcomm : ∀ l ∈ L, (g : M) * l = l * (g : M) := fun l hl =>
    ((Subgroup.mem_centralizer_iff.1 h1) l hl).symm
  refine ⟨hcent g g.2 hcomm, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro l
  exact Subtype.ext (hcomm l l.2).symm

theorem card_le_center_mul_aut (hLG : L ≤ G)
    (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hcent : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L) (hperf : Group.IsPerfect ↥L) :
    Nat.card ↥G ≤
      Nat.card (Subgroup.center ↥L) * Nat.card (MulAut (↥L ⧸ Subgroup.center ↥L)) := by
  have hLn : (L.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff hLG).2 fun l g hl hg => hnorm g hg l hl
  let α := actionOnCQ hLG hLn
  have hker := mem_center_of_mem_ker_actionOnCQ hLG hnorm hcent hperf
  have h1 : Nat.card α.ker ≤ Nat.card (Subgroup.center ↥L) := by
    refine Nat.card_le_card_of_injective
      (fun g : α.ker => (⟨⟨(g.1 : M), (hker g.1 g.2).1⟩, (hker g.1 g.2).2⟩ :
        ↥(Subgroup.center ↥L))) ?_
    intro a b hab
    have : (a.1 : M) = (b.1 : M) :=
      congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : M)) hab
    exact Subtype.ext (Subtype.ext this)
  have h2 : Nat.card α.range ≤ Nat.card (MulAut (↥L ⧸ Subgroup.center ↥L)) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  calc Nat.card ↥G = Nat.card (↥G ⧸ α.ker) * Nat.card α.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    _ = Nat.card α.range * Nat.card α.ker := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
    _ ≤ Nat.card (MulAut (↥L ⧸ Subgroup.center ↥L)) * Nat.card (Subgroup.center ↥L) :=
        Nat.mul_le_mul h2 h1
    _ = _ := mul_comm _ _

theorem actionOnCQ_injective_of_center_trivial (hLG : L ≤ G)
    (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hcent : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L) (hperf : Group.IsPerfect ↥L)
    (hZ : ∀ z ∈ Subgroup.center ↥L, z = 1) :
    Function.Injective (actionOnCQ hLG ((Subgroup.normal_subgroupOf_iff hLG).2
      fun l g hl hg => hnorm g hg l hl)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨hgL, hgc⟩ := mem_center_of_mem_ker_actionOnCQ hLG hnorm hcent hperf g hg
  have := hZ _ hgc
  exact Subtype.ext (congrArg (fun z : ↥L => (z : M)) this)

end CFSG.Quasithin.RonanG73

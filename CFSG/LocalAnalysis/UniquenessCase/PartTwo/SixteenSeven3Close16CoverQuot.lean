module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem close16_exists_hom_barSub {D : Data G} {V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil ⊥ V) {X : Subgroup G} (hXM : X ≤ D.M) :
    ∃ φ : ↥X →* ↥(barSub ⊥ V hV X), Function.Surjective φ ∧
      φ.ker = (X ⊓ F11.CTilde D.M ⊥ V).subgroupOf X := by
  have hXs : X ≤ stabTil ⊥ V := hXM.trans hM
  let ψ : ↥X →* ↥(stabTil ⊥ V) := Subgroup.inclusion hXs
  let φ : ↥X →* ↥(barSub ⊥ V hV X) :=
    MonoidHom.codRestrict ((actTil ⊥ V hV).comp ψ) (barSub ⊥ V hV X)
      (fun g => (mem_barSub ⊥ V hV X _).2 ⟨ψ g, g.2, rfl⟩)
  refine ⟨φ, ?_, ?_⟩
  · rintro ⟨_, hφ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub ⊥ V hV X _).1 hφ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  · ext g
    have hMn : D.M ≤ normalizer (V : Set G) := hM.trans (stabTil_le_normalizer ⊥ V)
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cTilde_iff hV hMn]
    have hgX : (g : G) ∈ X := g.2
    constructor
    · intro h1
      exact ⟨hgX, hXM hgX, hXs hgX, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1

theorem close16_simple_of_hom {X C : Subgroup G} (hCX : C ≤ X) {S : Type} [Group S]
    [IsSimpleGroup S] (hS : ¬ IsMulCommutative S) (φ : ↥X →* S)
    (hφ : Function.Surjective φ) (hker : φ.ker = C.subgroupOf X) :
    (∀ N : Subgroup G, C ≤ N → N ≤ X → (N.subgroupOf X).Normal → N = C ∨ N = X) ∧
      ¬ ⁅X, X⁆ ≤ C := by
  constructor
  · intro N hCN hNX hN
    haveI hmap : ((N.subgroupOf X).map φ).Normal := Subgroup.Normal.map hN φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf X).map φ) with h | h
    · left
      have h1 : N.subgroupOf X ≤ φ.ker := by
        intro x hx
        have : φ x ∈ (N.subgroupOf X).map φ := Subgroup.mem_map_of_mem φ hx
        rw [h, Subgroup.mem_bot] at this
        exact this
      rw [hker] at h1
      have h2 : N ≤ C := by
        intro x hx
        exact h1 (show (⟨x, hNX hx⟩ : ↥X) ∈ N.subgroupOf X from hx)
      exact le_antisymm h2 hCN
    · right
      have h1 : N.subgroupOf X = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : φ x ∈ (N.subgroupOf X).map φ := by rw [h]; trivial
        obtain ⟨y, hy, hyx⟩ := hx
        have hyx' : y⁻¹ * x ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
        rw [hker] at hyx'
        have hCN' : C.subgroupOf X ≤ N.subgroupOf X := fun z hz => hCN hz
        have := (N.subgroupOf X).mul_mem hy (hCN' hyx')
        simpa using this
      exact le_antisymm hNX (Subgroup.subgroupOf_eq_top.mp h1)
  · intro hcomm
    apply hS
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    have hxy : ⁅(x : G), (y : G)⁆ ∈ C := hcomm (Subgroup.commutator_mem_commutator x.2 y.2)
    have hk : ⁅x, y⁆ ∈ φ.ker := by
      rw [hker]
      exact hxy
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hk
    exact hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

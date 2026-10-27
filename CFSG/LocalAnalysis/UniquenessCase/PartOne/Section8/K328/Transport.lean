module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Leaves

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Open

theorem subgroupOf_centralizer_inf_eq {G : Type} [Group G] (K Z : Subgroup G) (hZK : Z ≤ K) :
    (Subgroup.centralizer (Z : Set G) ⊓ K).subgroupOf K =
      Subgroup.centralizer ((Z.subgroupOf K : Subgroup K) : Set K) := by
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨hc, -⟩ ⟨z, hzK⟩ hz
    exact Subtype.ext (hc z hz)
  · intro hc
    exact ⟨fun z hz => congrArg Subtype.val (hc ⟨z, hZK hz⟩ hz), hx⟩

theorem isSubnormal_of_map_eq {A B : Type} [Group A] [Group B] (e : A ≃* B) {X : Subgroup A}
    {Y : Subgroup B} (hXY : X.map e.toMonoidHom = Y) (h : X.IsSubnormal) : Y.IsSubnormal := by
  rw [← hXY]
  exact Subgroup.IsSubnormal.map (f := e.toMonoidHom) e.surjective h

theorem pos_of_k328_hyps {G : Type} [Group G] [Finite G] {K Z X : Subgroup G}
    (hZ : Nat.card Z = 3) (hZX : Z ≤ X) (hXC : X ≤ Subgroup.centralizer (Z : Set G) ⊓ K)
    (hsub : (X.subgroupOf (Subgroup.centralizer (Z : Set G) ⊓ K)).IsSubnormal)
    (hXq : CFSG.Open.IsQuasisimple ↥X) (hXZ : Nat.card (Subgroup.center ↥X) = 3)
    (hXt : LieModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
      LieModel (↥X ⧸ Subgroup.center ↥X) .PSU 3 2 3) :
    Pos ↥K (Z.subgroupOf K) (X.subgroupOf K) := by
  have hXK : X ≤ K := hXC.trans inf_le_right
  have hZK : Z ≤ K := hZX.trans hXK
  have hCK : Subgroup.centralizer (Z : Set G) ⊓ K ≤ K := inf_le_right
  let eX : ↥X ≃* ↥(X.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hXK).symm
  refine ⟨?_, ?_, ?_, ?_, isQuasisimple_of_mulEquiv' eX hXq, ?_, ?_⟩
  · rw [card_subgroupOf_of_le hZK, hZ]
  · intro z hz
    exact Subgroup.mem_subgroupOf.2 (hZX (Subgroup.mem_subgroupOf.1 hz))
  · rw [← subgroupOf_centralizer_inf_eq K Z hZK]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hXC (Subgroup.mem_subgroupOf.1 hx))
  · rw [← subgroupOf_centralizer_inf_eq K Z hZK]
    refine isSubnormal_of_map_eq (Subgroup.subgroupOfEquivOfLe hCK).symm ?_ hsub
    ext y
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  · rw [← hXZ]
    exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).symm
  · let f := QuotientGroup.congr (Subgroup.center X) (Subgroup.center (X.subgroupOf K)) eX
      (Subgroup.map_center_eq eX)
    rcases hXt with hl | hl
    · exact Or.inl (LieModel.of_mulEquiv f hl)
    · exact Or.inr (LieModel.of_mulEquiv f hl)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

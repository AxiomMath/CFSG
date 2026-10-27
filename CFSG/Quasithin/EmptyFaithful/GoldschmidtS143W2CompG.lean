module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompLay

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

section Comp

variable {G : Type} [Group G] [Finite G] {H L : Subgroup G}

omit [Finite G] in
theorem isQuasisimple_of_isComponentIn (hL : IsComponentIn L H) : CFSG.IsQuasisimple ↥L :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1

omit [Finite G] in
theorem ne_bot_of_isComponentIn (hL : IsComponentIn L H) : L ≠ ⊥ := by
  intro h
  have : Nontrivial ↥L :=
    CFSG.LocalCores.isQuasisimple_nontrivial (isQuasisimple_of_isComponentIn hL)
  rw [h] at this
  exact not_nontrivial _ this

theorem pCoreOf_le_centralizer_of_isComponentIn (hL : IsComponentIn L H) :
    pCoreOf 2 H ≤ Subgroup.centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRs : Group.IsSolvable (CFSG.pCore 2 ↥H) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
    infer_instance
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hRs
    (Subgroup.Normal.isSubnormal (CFSG.pCore_normal (p := 2) (G := ↥H)))).1 _ hL.2
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  intro p hp
  rw [pCoreOf_eq_map_pCore] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
  have hl' : (⟨l, hL.1 hl⟩ : ↥H) ∈ L.subgroupOf H := Subgroup.mem_subgroupOf.mpr hl
  have := Subgroup.mem_centralizer_iff.mp (hcomm hl') p' hp'
  exact (congrArg Subtype.val this).symm

end Comp

section NoComp

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {Z : Subgroup G}

theorem not_component_le (h : Ctx T M g A t d x) (hf : Wp0 T d x) (hZ : Z ≤ Gw d x)
    (hZn : ∀ u ∈ Gw d x, ∀ k ∈ Z, u * k * u⁻¹ ∈ Z) (hz : d * d ∉ Z) (hwZ : wOfX d x ∈ Z)
    {L : Subgroup G} (hL : IsComponentIn L (Gw d x)) : ¬ L ≤ Z := by
  intro hLZ
  have hq := isQuasisimple_of_isComponentIn hL
  obtain ⟨Sy⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  set S : Subgroup G := (Sy : Subgroup ↥L).map L.subtype with hS
  have hS2 : IsPGroup 2 S := Sy.isPGroup'.map L.subtype
  have hSL : S ≤ L := Subgroup.map_subtype_le _
  have hW2 := h.isPGroup_zpowers_w
  have hcommL : ∀ l ∈ L, l * wOfX d x = wOfX d x * l := fun l hl => mem_Gw_iff.mp (hL.1 hl)
  have hSN : S ≤ Subgroup.normalizer (Subgroup.zpowers (wOfX d x) : Set G) := fun s hs =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.zpow_left (show Commute (wOfX d x) s from (hcommL s (hSL hs)).symm) k).eq)
  have hS₂ : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers (wOfX d x)) :=
    hS2.to_sup_of_normal_right' hW2 hSN
  have hS₂Z : S ⊔ Subgroup.zpowers (wOfX d x) ≤ Z :=
    sup_le (hSL.trans hLZ) (Subgroup.zpowers_le.mpr hwZ)
  have hc := card_le_four_of_pGroup h hf hZ hZn hz hS₂Z hS₂
  exact false_of_quasisimple_sylow_le_small hq hcommL h.w_sq h.w_ne Sy hc
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) le_sup_left

end NoComp

end InspW2

end S143

end CFSG.Quasithin

module

public import CFSG.LieType.HighestRoot.CentTrialityThree
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentC

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Def

variable (K : Type) [Field K]

@[expose] def La : Subgroup (C K) :=
  Subgroup.closure (Set.range (xa (K := K)) ∪ Set.range (xna (K := K)))

variable {K}

theorem xa_mem_La (s : K) : xa s ∈ La K := Subgroup.subset_closure (Or.inl ⟨s, rfl⟩)

end Def

section Main

variable {K : Type} [Field K] [CharP K 2]

theorem reflect_a_a : reflect Tag.G2 i0 rA = rNA := List.ofFn_injective (by decide +kernel)

theorem xna_mem_cent_xv (s : K) : xna s ∈ Subgroup.centralizer ({xv 1} : Set (C K)) := by
  have hrA : IsRoot Tag.G2 rA := (isRoot_pos_iff.2 (by simp)).1
  have h : xna s = ⟨weylElt Tag.G2 K i0 1, weylElt_mem_adjointGroup i0 1⟩ * xa s *
      ⟨weylElt Tag.G2 K i0 1, weylElt_mem_adjointGroup i0 1⟩⁻¹ := by
    refine Subtype.ext ?_
    show gX rNA s = weylElt Tag.G2 K i0 1 * gX rA s * (weylElt Tag.G2 K i0 1)⁻¹
    rw [weylElt_conj_gX i0 hrA s, reflect_a_a]
  rw [h]
  exact mul_mem (mul_mem nA_mem_centralizer_xv
    (Subgroup.mem_centralizer_singleton_iff.2 (cc_av s 1).eq)) (inv_mem nA_mem_centralizer_xv)

theorem La_le_cent_xv : La K ≤ Subgroup.centralizer ({xv 1} : Set (C K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (cc_av s 1).eq
  · exact xna_mem_cent_xv s

theorem La_le_Pa : La K ≤ Pa K := La_le_cent_xv.trans ct

theorem La_le_normalizer_V : La K ≤ Subgroup.normalizer (V K : Set (C K)) :=
  La_le_Pa.trans Pa_le_normalizer_V

theorem yUnit_i0 (c : K) : yUnit Tag.G2 K i0 c = gX rNA c := by
  rw [← pinnedX_neg_single]
  congr 1
  funext i
  rcases fin_two_cases i with rfl | rfl
  · decide
  · decide

theorem exists_mulEquiv_La : Nonempty (La K ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨ρ, hρ, -, hrange⟩ := rankOne_data (K := K) i0
  set f : C K →* ModGL Tag.G2 K := (adjointGroup Tag.G2 K).subtype with hf
  have h1 : f '' Set.range (xa (K := K)) = Set.range (xUnit Tag.G2 K i0) := by
    rw [← Set.range_comp]
    congr 1
    funext s
    exact (rootOne_gX_i0 s).symm
  have h2 : f '' Set.range (xna (K := K)) = Set.range (yUnit Tag.G2 K i0) := by
    rw [← Set.range_comp]
    congr 1
    funext s
    exact (yUnit_i0 s).symm
  have hmap : (La K).map f = ρ.range := by
    rw [hrange, La, MonoidHom.map_closure, Set.image_union, h1, h2]
  exact ⟨((Subgroup.equivMapOfInjective (La K) f (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hmap)).trans (MonoidHom.ofInjective hρ).symm⟩

variable [Finite K]

theorem isQuasisimple_La (hK4 : 4 ≤ Nat.card K) : CFSG.IsQuasisimple (La K) := by
  obtain ⟨e⟩ := exists_mulEquiv_La (K := K)
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2
    (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le hK4)

theorem not_isSolvable_La (hK4 : 4 ≤ Nat.card K) : ¬ Group.IsSolvable (La K) := by
  have hperf : Group.IsPerfect (La K) := (isQuasisimple_La hK4).1
  have : Nontrivial (La K) :=
    ⟨⟨⟨xa 1, xa_mem_La 1⟩, 1, fun h => one_ne_zero (xa_eq_one_iff.1 (congrArg Subtype.val h))⟩⟩
  exact Group.IsPerfect.not_isSolvable (La K)

theorem normal_centralizer_subgroupOf {G : Type*} [Group G] {X V : Subgroup G}
    (hVn : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V) :
    ((Subgroup.centralizer (V : Set G)).subgroupOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
  intro v hv
  have hv' : (g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹ ∈ V := hVn _ (X.inv_mem g.2) v hv
  have h := hn _ hv'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc v * ((g : G) * (n : G) * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹) * (n : G)) * (g : G)⁻¹ := by group
    _ = (g : G) * ((n : G) * ((g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹)) * (g : G)⁻¹ := by rw [h]
    _ = (g : G) * (n : G) * (g : G)⁻¹ * v := by group

theorem isSolvable_La_inf_cent_V (hK4 : 4 ≤ Nat.card K) :
    Group.IsSolvable ↥(La K ⊓ Subgroup.centralizer (V K : Set (C K))) := by
  have hq := isQuasisimple_La hK4
  have : ((Subgroup.centralizer (V K : Set (C K))).subgroupOf (La K)).Normal :=
    normal_centralizer_subgroupOf fun x hx v hv =>
      (Subgroup.mem_normalizer_iff.1 (La_le_normalizer_V hx) v).1 hv
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
      ((Subgroup.centralizer (V K : Set (C K))).subgroupOf (La K)) with hc | htop
  · refine Group.isSolvable_of_comm (fun a b => ?_)
    have ha : (⟨a.1, a.2.1⟩ : La K) ∈ (Subgroup.centralizer (V K : Set (C K))).subgroupOf (La K) :=
      a.2.2
    have h := Subgroup.mem_center_iff.1 (hc ha) ⟨b.1, b.2.1⟩
    exact Subtype.ext (congrArg Subtype.val h).symm
  · exfalso
    have h1 : (⟨xa 1, xa_mem_La 1⟩ : La K) ∈
        (Subgroup.centralizer (V K : Set (C K))).subgroupOf (La K) := htop ▸ Subgroup.mem_top _
    have h2 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 h1) (xb 1) (xb_mem_V 1)
    have h3 : ⁅xa (1 : K), xb (1 : K)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h2.symm
    rw [cm_ab, xc_eq_one_iff] at h3
    simp at h3

end Main

end CFSG.Quasithin.H13.F431.G2.Cent

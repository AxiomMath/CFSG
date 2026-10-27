module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L82

section Generic

variable {Γ : Type u} [Group Γ]

theorem smear_eq_inf_centralizer {J E : Subgroup Γ} (hEJ : E ≤ Subgroup.normalizer (J : Set Γ)) :
    smear J E = J ⊓ Subgroup.centralizer (E : Set Γ) := by
  have h : orbitClosure J E = J := le_antisymm
    (orbitClosure_le fun a ha => (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEJ ha)).le)
    (le_orbitClosure J E)
  rw [smear, h]

theorem inSubgroup_generalizedFitting_eq_self {X : Subgroup Γ} (hs : IsSimpleGroup X)
    (hnc : ¬ IsMulCommutative X) : CFSG.inSubgroup CFSG.generalizedFitting X = X := by
  have hnonab : ∃ a b : X, a * b ≠ b * a := by
    simpa only [isMulCommutative_iff, not_forall] using hnc
  have hlayer : CFSG.layer ↥X = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Unit) (S := fun _ => ↥X) (fun _ => hnonab)
      (MulEquiv.funUnique Unit ↥X).symm
  have htop : CFSG.generalizedFitting ↥X = ⊤ := by
    rw [CFSG.generalizedFitting, hlayer, sup_top_eq]
  unfold CFSG.inSubgroup
  rw [htop, Subgroup.map_top, Subgroup.range_subtype]

theorem le_inSubgroup_generalizedFitting_of_mem_lcal {Y J : Subgroup Γ} (hJ : J ∈ lcal Y) :
    J ≤ CFSG.inSubgroup CFSG.generalizedFitting Y := by
  have h1 := CFSG.LocalCores.component_le_layer (T515f.isComponent_of_mem_lcal hJ)
  have h2 : CFSG.layer ↥Y ≤ CFSG.generalizedFitting ↥Y := le_sup_right
  calc J = (J.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le (lcal_le hJ)).symm
    _ ≤ (CFSG.generalizedFitting ↥Y).map Y.subtype := Subgroup.map_mono (h1.trans h2)

theorem inSubgroup_generalizedFitting_eq_kOf [Finite Γ] {X : Subgroup Γ} (h : sol X = ⊥) :
    CFSG.inSubgroup CFSG.generalizedFitting X = kOf X := by
  rw [kOf_eq_map_layer h, ← generalizedFitting_eq_layer_of_solvableRadical_eq_bot
    ((sol_eq_bot_iff X).mp h)]
  rfl

end Generic

section Setting

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem isRegFam_lcal_kOf
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) : IsRegFam A (kOf (thetaOf θ B)) (lcal (thetaOf θ B)) (bN A θ B) := by
  refine ⟨isDirectProduct_lcal_kOf (h.sol_thetaOf hBA hB), h.lcal_thetaOf_nonempty hBA hB, ?_, ?_,
    ?_, ?_⟩
  · intro L hL hbot
    obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hL
    subst hbot
    exact hnc inferInstance
  · intro a ha L hL
    exact map_conj_mem_lcal hL (h.isFunctor.normalizes_thetaOf hBA ha)
  · intro L hL L' hL'
    exact h.exists_conj_eq_of_mem_lcal hBA hB hL hL'
  · intro L hL
    exact (h.bN_eq_inf_normalizer hBA hB hL).symm

end Setting

end L82

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner
import CFSG.RankThree.PartTwo.Sec14.Ronan148VDelta
import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Normal

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

private theorem isTripleCover_congr_aux {X X' S : Type*} [Group X] [Group X'] [Group S]
    (e : X ≃* X') (h : Sec4.IsTripleCover X S) : Sec4.IsTripleCover X' S := by
  obtain ⟨hcard, ⟨φ⟩⟩ := h
  have hc : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ e hc).symm.trans φ⟩⟩
  rw [← hc, Subgroup.card_map_of_injective e.injective, hcard]

private theorem subgroupOf_le_theta {θ' X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (θ' : Set G)) (hθ3 : ¬ 3 ∣ Nat.card θ')
    (hcp : IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    θ'.subgroupOf X ≤ aschbacherSolvableCore 3 ↥X := by
  have hM : (θ'.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hX
  have hMn : ((θ'.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))).Normal :=
    hM.map _ (QuotientGroup.mk'_surjective _)
  have h3 : ¬ 3 ∣ Nat.card ((θ'.subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))) := by
    intro h
    apply hθ3
    refine h.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hbot := Ronan148W.noNormal3_of_isCentralProductA6Covers hcp _ hMn h3
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

private theorem exists_injective_hom_theta_quot {C O X θ' : Subgroup G} (hXC : X ≤ C)
    (hOC : O ≤ C) (hOθ : O ≤ θ') (hθX : inSubgroup (aschbacherSolvableCore 3) X ≤ O)
    (hXnorm : X ≤ Subgroup.normalizer (θ' : Set G)) (hθ3 : ¬ 3 ∣ Nat.card θ')
    (hcp : IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    [(θ'.subgroupOf C).Normal] :
    ∃ ι : (↥X ⧸ aschbacherSolvableCore 3 ↥X) →* ↥C ⧸ θ'.subgroupOf C,
      Function.Injective ι ∧
        ι.range = ((O ⊔ X).subgroupOf C).map (QuotientGroup.mk' (θ'.subgroupOf C)) := by
  have hker : θ'.subgroupOf X = aschbacherSolvableCore 3 ↥X := by
    refine le_antisymm (subgroupOf_le_theta hXnorm hθ3 hcp) ?_
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hOθ (hθX (Subgroup.mem_map_of_mem X.subtype hx))
  let ψ : ↥X →* ↥C ⧸ θ'.subgroupOf C :=
    (QuotientGroup.mk' (θ'.subgroupOf C)).comp (Subgroup.inclusion hXC)
  have hψker : ψ.ker = aschbacherSolvableCore 3 ↥X := by
    rw [← hker]
    ext x
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (θ'.subgroupOf C) (Subgroup.inclusion hXC x) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hψrange : ψ.range = (X.subgroupOf C).map (QuotientGroup.mk' (θ'.subgroupOf C)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hOmap : (O.subgroupOf C).map (QuotientGroup.mk' (θ'.subgroupOf C)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro o ho
    rw [Subgroup.mem_subgroupOf] at ho ⊢
    exact hOθ ho
  refine ⟨QuotientGroup.lift _ ψ hψker.ge, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro w hw
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    have hx : x ∈ ψ.ker := hw
    rw [hψker] at hx
    exact (QuotientGroup.eq_one_iff x).mpr hx
  · rw [Subgroup.subgroupOf_sup hOC hXC, Subgroup.map_sup, hOmap, bot_sup_eq, ← hψrange]
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk x, rfl⟩

theorem centralizer_le_normalizer_of_cp {A : Subgroup G} {e d : G} {X : Subgroup G}
    (hinv : Ronan148Q.Inv143Q A e d X)
    (hcp : IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) ⊔ X : Subgroup G) : Set G) := by
  rcases hinv with h | ⟨-, -, h6, -⟩
  · exact h
  · have h1080 := HJRes2.card_of_isTripleCover_six h6
    have h388800 := Ronan148V.card_of_isCentralProductA6Covers hcp
    have h := h1080.symm.trans h388800
    omega

theorem exists_cp_quot {C O X : Subgroup G} (hXC : X ≤ C) (hOC : O ≤ C)
    (hθX : inSubgroup (aschbacherSolvableCore 3) X ≤ O) (hO3 : ¬ 3 ∣ Nat.card O)
    (hCO : C ≤ Subgroup.normalizer (O : Set G))
    (hcp : IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    [((pPrimeCoreOf 3 (O ⊔ X)).subgroupOf C).Normal] :
    ∃ J₁ J₂ : Subgroup (↥C ⧸ (pPrimeCoreOf 3 (O ⊔ X)).subgroupOf C),
      J₁ ⊔ J₂ = ((O ⊔ X).subgroupOf C).map (QuotientGroup.mk' _) ∧ ⁅J₁, J₂⁆ = ⊥ ∧
      Nat.card ↥(J₁ ⊓ J₂) = 3 ∧ Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)) ∧
      Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6)) := by
  have hOXC : O ⊔ X ≤ C := sup_le hOC hXC
  have hOθ : O ≤ pPrimeCoreOf 3 (O ⊔ X) :=
    le_pPrimeCoreOf le_sup_left (hOXC.trans hCO)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hO3)
  have hθ3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (O ⊔ X)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hXnorm : X ≤ Subgroup.normalizer (pPrimeCoreOf 3 (O ⊔ X) : Set G) :=
    le_sup_right.trans (le_normalizer_pPrimeCoreOf 3 (O ⊔ X))
  obtain ⟨ι, hinj, hrange⟩ := exists_injective_hom_theta_quot hXC hOC hOθ hθX hXnorm hθ3 hcp
  obtain ⟨U, V, -, -, hUV, hUVc, hUVcard, hU, hV⟩ := hcp
  refine ⟨U.map ι, V.map ι, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hUV, ← MonoidHom.range_eq_map, hrange]
  · rw [← Subgroup.map_commutator, hUVc, Subgroup.map_bot]
  · rw [← Subgroup.map_inf_eq _ _ ι hinj, Subgroup.card_map_of_injective hinj]
    exact hUVcard
  · exact isTripleCover_congr_aux (Subgroup.equivMapOfInjective U ι hinj) hU
  · exact isTripleCover_congr_aux (Subgroup.equivMapOfInjective V ι hinj) hV

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO

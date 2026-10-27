module

public import CFSG.Quasithin.H13.NQCatOddLinearThreeInputs
public import CFSG.Quasithin.SteinbergBQCyclicCenterPerfect
public import CFSG.Quasithin.Background.A3ComponentsCore

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup Module CFSG.Quasithin CFSG.Wreathed.OddLinearThreeCentralizerCore
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem le_map_perfectResidual_of_perfect {G : Type*} [Group G] [Finite G] {C Y : Subgroup G}
    (hYC : Y ≤ C) (hY : ⁅Y, Y⁆ = Y) :
    Y ≤ (CFSG.perfectResidual C).map C.subtype := by
  have hYs : Group.IsPerfect (Y.subgroupOf C) := by
    rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le hYC, hY]
  have h := (CFSG.perfect_residual_transport (G := C) (MonoidHom.id C)).2.2 _ hYs
  calc Y = (Y.subgroupOf C).map C.subtype := (map_subgroupOf_eq_of_le hYC).symm
    _ ≤ (CFSG.perfectResidual C).map C.subtype := map_mono h

variable {F : Type*} [Field F] [Finite F]

theorem odd_linear_three_positive_two_core_rank_one_containment
    (hI : OddLinearThreeInvolutionSylowStructure F) (hF : Odd (Nat.card F))
    (hq : 5 ≤ Nat.card F) (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ scalars 3 F)
    (T : Sylow 2 (SL3 F ⧸ D)) {B : Subgroup (SL3 F ⧸ D)}
    (hB : B ∈ cComp (B ⊔ (T : Subgroup (SL3 F ⧸ D))))
    (hO2 : CFSG.pCore 2 ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D))) ≠ ⊥) {t : SL3 F ⧸ D}
    (htT : t ∈ (T : Subgroup (SL3 F ⧸ D))) (htZ : ∀ x ∈ (T : Subgroup (SL3 F ⧸ D)), x * t = t * x)
    (ht2 : orderOf t = 2) :
    B ≤ (CFSG.perfectResidual (centralizer ({t} : Set (SL3 F ⧸ D)))).map
        (centralizer ({t} : Set (SL3 F ⧸ D))).subtype ∧
      ∃ z : SL3 F, orderOf z = 2 ∧ QuotientGroup.mk' D z = t ∧
        (∀ w : SL3 F, orderOf w = 2 → QuotientGroup.mk' D w = t → w = z) ∧
        (CFSG.perfectResidual (centralizer ({t} : Set (SL3 F ⧸ D)))).map
            (centralizer ({t} : Set (SL3 F ⧸ D))).subtype =
          (preservingFixing (minusSpace (matrixAction F z).toLinearMap)
            (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D) ∧
        Set.InjOn (QuotientGroup.mk' D) (preservingFixing
          (minusSpace (matrixAction F z).toLinearMap) (plusSpace (matrixAction F z).toLinearMap)) ∧
        Nonempty (↥((CFSG.perfectResidual (centralizer ({t} : Set (SL3 F ⧸ D)))).map
          (centralizer ({t} : Set (SL3 F ⧸ D))).subtype) ≃*
            Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSyl, hinv⟩ := hI hF hq D hD
  have hTM : (T : Subgroup (SL3 F ⧸ D)) ≤ B ⊔ (T : Subgroup (SL3 F ⧸ D)) := le_sup_right
  let TM : Sylow 2 ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D))) := T.subtype hTM
  have hTMcoe : (TM : Subgroup ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D)))) =
      (T : Subgroup (SL3 F ⧸ D)).subgroupOf (B ⊔ (T : Subgroup (SL3 F ⧸ D))) :=
    T.coe_subtype hTM
  have heT : ↥(TM : Subgroup ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D)))) ≃* ↥(T : Subgroup (SL3 F ⧸ D)) :=
    (MulEquiv.subgroupCongr hTMcoe).trans (subgroupOfEquivOfLe hTM)
  have hZT : IsCyclic (center ↥(TM : Subgroup ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D))))) := by
    have := (hSyl T).1
    exact isCyclic_of_surjective (centerCongr heT).symm.toMonoidHom (MulEquiv.surjective _)
  have hrank : ∀ E : Subgroup ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D))), E ≤ TM →
      IsElementaryAbelian 2 E → Nat.card E ≤ 4 := by
    intro E hE hEl
    have hEm : E.map (B ⊔ (T : Subgroup (SL3 F ⧸ D))).subtype ≤ T := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : x ∈ (T : Subgroup (SL3 F ⧸ D)).subgroupOf (B ⊔ (T : Subgroup (SL3 F ⧸ D))) := by
        rw [← hTMcoe]
        exact hE hx
      exact mem_subgroupOf.mp h1
    have h2 := (hSyl T).2 _ hEm (hEl.map _)
    rwa [card_map_of_injective (subtype_injective _)] at h2
  let z : ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D))) := ⟨t, hTM htT⟩
  have hzT : z ∈ (TM : Subgroup ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D)))) := by
    rw [hTMcoe, mem_subgroupOf]
    exact htT
  have hzZ : z ∈ centralizer ((TM : Subgroup ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D)))) :
      Set ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D)))) := by
    rw [mem_centralizer_iff]
    intro x hx
    rw [SetLike.mem_coe, hTMcoe, mem_subgroupOf] at hx
    exact Subtype.ext (htZ _ hx)
  have hz2 : orderOf z = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ht2
  have : (CFSG.pCore 2 ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D)))).Normal := CFSG.pCore_normal
  have hBperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hB
  have hBMperf : ⁅B.subgroupOf (B ⊔ (T : Subgroup (SL3 F ⧸ D))),
      B.subgroupOf (B ⊔ (T : Subgroup (SL3 F ⧸ D)))⁆ =
        B.subgroupOf (B ⊔ (T : Subgroup (SL3 F ⧸ D))) := by
    apply Subgroup.map_injective (subtype_injective _)
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le le_sup_left, hBperf]
  have hcore := SteinbergBQ.cyclic_sylow_center_rank_two_core_centralizes_perfect_subgroups TM
    (CFSG.pCore 2 ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D)))) CFSG.pCore_isPGroup hO2 hZT hrank hzT hzZ
    hz2 _ hBMperf
  set R := (CFSG.perfectResidual (centralizer ({z} : Set ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D)))))).map
    (centralizer ({z} : Set ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D))))).subtype with hR
  have hRperf : ⁅R, R⁆ = R := by
    have h1 : Group.IsPerfect (CFSG.perfectResidual
        (centralizer ({z} : Set ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D)))))) :=
      (CFSG.perfect_residual_characterization).2.2.1
    rw [Subgroup.isPerfect_iff] at h1
    rw [hR, ← Subgroup.map_commutator, h1]
  have hRmap : ⁅R.map (B ⊔ (T : Subgroup (SL3 F ⧸ D))).subtype,
      R.map (B ⊔ (T : Subgroup (SL3 F ⧸ D))).subtype⁆ =
        R.map (B ⊔ (T : Subgroup (SL3 F ⧸ D))).subtype := by
    rw [← Subgroup.map_commutator, hRperf]
  have hRC : R.map (B ⊔ (T : Subgroup (SL3 F ⧸ D))).subtype ≤
      centralizer ({t} : Set (SL3 F ⧸ D)) := by
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hy := mem_centralizer_singleton_iff.mp y.2
    exact congrArg Subtype.val hy
  have hBR : B ≤ R.map (B ⊔ (T : Subgroup (SL3 F ⧸ D))).subtype := by
    calc B = (B.subgroupOf (B ⊔ (T : Subgroup (SL3 F ⧸ D)))).map
          (B ⊔ (T : Subgroup (SL3 F ⧸ D))).subtype := (map_subgroupOf_eq_of_le le_sup_left).symm
      _ ≤ R.map (B ⊔ (T : Subgroup (SL3 F ⧸ D))).subtype := map_mono hcore.2
  refine ⟨hBR.trans (le_map_perfectResidual_of_perfect hRC hRmap), ?_⟩
  obtain ⟨z', hz', hz't, huniq, -, -, hL, hinj, ⟨e⟩, -, -⟩ := hinv t ht2
  exact ⟨z', hz', hz't, huniq, hL, hinj, ⟨(MulEquiv.subgroupCongr hL).trans e⟩⟩

end CFSG.Quasithin.H13.NQCat

module

public import CFSG.Quasithin.EmptyFaithful.S143WFin
public import CFSG.Quasithin.EmptyFaithful.S143WNo
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace SzPS8

section PBasic

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

@[expose] def cZU (T M : Subgroup G) : Subgroup G :=
  mcOf T ⊓ Subgroup.centralizer (centerOf (uOfL22 T M) : Set G)

omit [Finite G] in
theorem cZU_le : cZU T M ≤ mcOf T := inf_le_left

omit [Finite G] in
theorem cZU_centralizes {p z : G} (hp : p ∈ cZU T M) (hz : z ∈ centerOf (uOfL22 T M)) :
    p * z = z * p :=
  (Subgroup.mem_centralizer_iff.mp hp.2 z hz).symm

theorem cZU_normal (h : Hyp1281Two G T M (yOfL22 T M)) :
    ∀ x ∈ mcOf T, ∀ p ∈ cZU T M, x * p * x⁻¹ ∈ cZU T M := by
  intro x hx p hp
  refine ⟨(mcOf T).mul_mem ((mcOf T).mul_mem hx hp.1) ((mcOf T).inv_mem hx),
    Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hxN : x ∈ Subgroup.normalizer (centerOf (uOfL22 T M) : Set G) :=
    normalizer_le_normalizer_centerOf _ (h.g1_le_normalizer_uOfL22 hx)
  have hz' : x⁻¹ * z * x ∈ centerOf (uOfL22 T M) := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hxN) z).mp hz
    simpa using this
  have hc : p * (x⁻¹ * z * x) = (x⁻¹ * z * x) * p := cZU_centralizes hp hz'
  calc z * (x * p * x⁻¹) = x * ((x⁻¹ * z * x) * p) * x⁻¹ := by group
    _ = x * (p * (x⁻¹ * z * x)) * x⁻¹ := by rw [hc]
    _ = (x * p * x⁻¹) * z := by group

theorem cZU_normal_subgroupOf (h : Hyp1281Two G T M (yOfL22 T M)) :
    ((cZU T M).subgroupOf (mcOf T)).Normal :=
  ⟨fun n hn g => cZU_normal h (g : G) g.2 (n : G) hn⟩

theorem cZU_isSubnormal (h : Hyp1281Two G T M (yOfL22 T M)) :
    IsSubnormal (cZU T M) (mcOf T) :=
  IsSubnormal.step cZU_le (cZU_normal_subgroupOf h) (IsSubnormal.refl _)

theorem cZU_ker_le_T (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    {p : ↥(mcOf T)} (hp : (p : G) ∈ cZU T M) (h1 : S143V.rhoH h D p = 1) : (p : G) ∈ T :=
  S143W.inf_centralizerHat_le_T h cZU_le (cZU_normal h) (fun _ hp _ hz => cZU_centralizes hp hz)
    ⟨hp, (S143V.mem_ker_rhoH h D p).mp h1⟩

theorem centerOf_uOfL22_le_cZU (h : Hyp1281Two G T M (yOfL22 T M)) :
    centerOf (uOfL22 T M) ≤ cZU T M := by
  intro z hz
  have hzT : z ∈ T := h.uOfL22_le_T hz.1
  refine ⟨h.almostSpecialHyp_g1.T_le_H hzT, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  exact hz.2 w hw.1

theorem img_cZU_ne_bot (h : Hyp1281Two G T M (yOfL22 T M))
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) (D : HatModel T M) : D.img (cZU T M) ≠ ⊥ := by
  classical
  obtain ⟨a, haV, haZ⟩ := h.exists_mem_VZ_not_mem
  obtain ⟨g, hg⟩ := h.exists_goodElt_L
  have hyp := h.lemma_12_8_12_three hU hg D haV haZ
  have hΓne : D.img (mcOf T) ≠ ⊥ := by
    intro hbot
    have horb : ∀ w ∈ MulAction.orbit (D.img (mcOf T)) (D.π a), w = D.π a := by
      rintro w ⟨γ, rfl⟩
      have h1 : (γ : D.V ≃ₗ[ZMod 2] D.V) = 1 :=
        (Subgroup.eq_bot_iff_forall _).mp hbot _ γ.2
      show (γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a) = D.π a
      rw [h1]
      rfl
    obtain ⟨hπa, -, -⟩ := h.hat_VZ_cases hU D haV haZ
    obtain ⟨w, hw⟩ : ∃ w, D.B (D.π a) w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hπa (D.B_nondegenerate _ hcon)
    have hwtop : w ∈ Submodule.span (ZMod 2) (MulAction.orbit (D.img (mcOf T)) (D.π a)) := by
      rw [hyp.span_orbit]
      exact Submodule.mem_top
    have hle : Submodule.span (ZMod 2) (MulAction.orbit (D.img (mcOf T)) (D.π a)) ≤
        Submodule.span (ZMod 2) {D.π a} := by
      rw [Submodule.span_le]
      intro x hx
      rw [horb x hx]
      exact Submodule.subset_span rfl
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hle hwtop)
    apply hw
    rw [map_smul, D.B_isAlt, smul_zero]
  by_cases hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T
  · have hPH' : mcOf T ≤ cZU T M := fun x hx =>
      ⟨hx, Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [hZU] at hz
        exact Subgroup.mem_centralizer_iff.mp hx z hz⟩
    rw [le_antisymm cZU_le hPH']
    exact hΓne
  · have hlt : quasithinOmegaOneCenter T < centerOf (uOfL22 T M) :=
      lt_of_le_of_ne h.omegaOneCenter_le_centerOf_uOfL22 (Ne.symm hZU)
    obtain ⟨y, hyX, hyH, hy1⟩ := S143W.exists_y₀ h hU hg D hlt
    have hyP : y ∈ cZU T M := ⟨hyH, Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (S143W.pOf_centralizes h hU hg (le_conjClosure _ _ hyX) hz).symm⟩
    have hyN : y ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 hyH
    intro hbot
    have hmem : S143V.rhoH h D ⟨y, hyH⟩ ∈ D.img (cZU T M) :=
      HatModel.mem_img.mpr ⟨y, hyP, hyN, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hy1 hmem

end PBasic

end SzPS8

end CFSG.Quasithin

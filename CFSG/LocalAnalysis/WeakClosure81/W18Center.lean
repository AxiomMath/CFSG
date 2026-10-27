module

public import CFSG.LocalAnalysis.WeakClosure81.W18Defs
public import CFSG.LocalAnalysis.WeakClosure81.SixEleven
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

abbrev eOmegaZ (H T : Subgroup G) : Subgroup G :=
  CFSG.Quasithin.conjClosure (omegaOneCenterOf T) H

namespace Hyp183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem charTwo (h : Hyp183 D V₀ V H i) : CFSG.QuasithinUnique.CharTwo H := by
  have hF := h.hyp171.1
  have hF' : (CFSG.generalizedFitting ↥H).map H.subtype = pCoreOf 2 H := by
    rw [← hF]
    unfold Fstar
    rw [CFSG.Adapters.genFittingFStar_eq_foundations]
  rintro y ⟨hyH, hyc⟩
  have hc : (⟨y, hyH⟩ : ↥H) ∈
      Subgroup.centralizer (CFSG.generalizedFitting ↥H : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : (w : G) ∈ pCoreOf 2 H := by
      rw [← hF']
      exact Subgroup.mem_map_of_mem _ hw
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hyc) _ hw')
  have := CFSG.centralizer_generalizedFitting_le ↥H hc
  rw [← hF']
  exact ⟨_, this, rfl⟩

theorem pCoreOf_le_self (H : Subgroup G) : pCoreOf 2 H ≤ H := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem isElemAbelian_eOmegaZ (h : Hyp183 D V₀ V H i) : IsElemAbelian 2 (eOmegaZ H D.T) :=
  omegaOneCenter_conjClosure_isElemAbelian h.charTwo h.isSylowIn_T

theorem normalizer_eOmegaZ (H T : Subgroup G) : H ≤ normalizer (eOmegaZ H T : Set G) :=
  le_normalizer_conjClosure _ _

theorem omegaOneCenterOf_le_eOmegaZ (H T : Subgroup G) : omegaOneCenterOf T ≤ eOmegaZ H T :=
  le_conjClosure _ _

theorem eOmegaZ_le_centerOf (h : Hyp183 D V₀ V H i) : eOmegaZ H D.T ≤ centerOf (pCoreOf 2 H) := by
  have hZctr : omegaOneCenterOf D.T ≤ centerOf (pCoreOf 2 H) :=
    omegaOneCenter_le_center_pCoreOf h.charTwo h.isSylowIn_T
  have hcenterNorm : H ≤ Subgroup.normalizer (centerOf (pCoreOf 2 H) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans
      (E3.normalizer_le_normalizer_centerOf (pCoreOf 2 H))
  show CFSG.Quasithin.conjClosure (omegaOneCenterOf D.T) H ≤ _
  rw [CFSG.Quasithin.conjClosure, Subgroup.closure_le]
  rintro x ⟨g, hg, z, hz, rfl⟩
  exact ((Subgroup.mem_normalizer_iff.1 (hcenterNorm hg)) z).1 (hZctr hz)

theorem eOmegaZ_le_pCoreOf (h : Hyp183 D V₀ V H i) : eOmegaZ H D.T ≤ pCoreOf 2 H :=
  (h.eOmegaZ_le_centerOf).trans inf_le_left

theorem pCoreOf_le_centralizer_eOmegaZ (h : Hyp183 D V₀ V H i) :
    pCoreOf 2 H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hec : e ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := (h.eOmegaZ_le_centerOf he).2
  exact (Subgroup.mem_centralizer_iff.mp hec x hx).symm

theorem V_le_T (h : Hyp183 D V₀ V H i) : V ≤ D.T :=
  (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.setting.pair.le_M
    h.setting.pair.le_normalizer (IsElemAbelian.isPGroup h.setting.isElemAbelian)).trans
    (E1.pCoreOf_two_le_of_isSylowIn (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM))

theorem T_ne_bot (h : Hyp183 D V₀ V H i) : D.T ≠ ⊥ := fun hT =>
  h.setting.pair.ne_bot (le_bot_iff.mp (hT ▸ h.V_le_T))

theorem centralizer_eOmegaZ_le_M (h : Hyp183 D V₀ V H i) :
    Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzc, hz2, hz1⟩ :=
    CFSG.QuasithinUnique.Setup.exists_involution_centerOf h.isSylowIn_T.isPGroup h.T_ne_bot
  have hzE : z ∈ eOmegaZ H D.T := omegaOneCenterOf_le_eOmegaZ H D.T (by
    unfold omegaOneCenterOf omegaOneOf
    exact Subgroup.subset_closure ⟨hzc, hz2⟩)
  obtain ⟨hcent, -⟩ := h.setting.central h.ne_bot z hzc.1
    (fun t ht => (Subgroup.mem_centralizer_iff.mp hzc.2 t ht).symm) (orderOf_eq_prime hz2 hz1)
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzE)).trans hcent

theorem inf_centralizer_eOmegaZ_le_kerMV (h : Hyp183 D V₀ V H i) :
    H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ kerMV V H := by
  refine le_kerMV_of_normal inf_le_left (fun g hg n hn => ?_)
    (by rw [h.setting.normalizer_eq]; exact inf_le_right.trans h.centralizer_eOmegaZ_le_M)
  refine ⟨H.mul_mem (H.mul_mem hg hn.1) (H.inv_mem hg), Subgroup.mem_centralizer_iff.2
    fun e he => ?_⟩
  have he' : g⁻¹ * e * g ∈ eOmegaZ H D.T := by
    have := (Subgroup.mem_normalizer_iff.mp (normalizer_eOmegaZ H D.T (H.inv_mem hg)) e).mp he
    simpa using this
  have hcomm := (Subgroup.mem_centralizer_iff.mp hn.2) (g⁻¹ * e * g) he'
  calc e * (g * n * g⁻¹) = g * ((g⁻¹ * e * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * e * g)) * g⁻¹ := by rw [hcomm]
    _ = g * n * g⁻¹ * e := by group

end Hyp183

end CFSG.LocalAnalysis.WeakClosure81

end

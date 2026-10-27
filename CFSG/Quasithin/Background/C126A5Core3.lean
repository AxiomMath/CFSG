module

public import CFSG.Quasithin.Background.C126A5Core2
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Background.C1PackClassG
public import CFSG.Quasithin.Background.E2SolvTwo

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C1Pack

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} (s : Setting H T M V Y hV)

include s

theorem Z_le_Z_R : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (R₁ H T) := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  intro z hz
  have hzb : z ∈ baum T := C1GN.omegaOneCenterOf_le_baum T (Subgroup.subset_closure hz)
  exact Subgroup.subset_closure ⟨⟨s.S_le_R hzb, Subgroup.centralizer_le s.R_le_T hz.1.2⟩, hz.2⟩

theorem hJ_V₁ : ¬ thompsonJ (R₁ H T) ≤
    Subgroup.centralizer (VZ (R₁ H T) (Y ⊔ R₁ H T) : Set G) := by
  intro hJR
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo s.sylow_P₁ s.charTwo_P₁
    (Z := quasithinOmegaOneCenter (R₁ H T)) le_rfl
  have hZV : quasithinOmegaOneCenter T ≤ VZ (R₁ H T) (Y ⊔ R₁ H T) :=
    s.Z_le_Z_R.trans (le_conjClosure _ _)
  by_cases hP : Y ⊔ R₁ H T ≤ Subgroup.centralizer (VZ (R₁ H T) (Y ⊔ R₁ H T) : Set G)
  ·
    have hZc : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
      B2F.omegaOneCenter_le_inf_centralizer T
    have hYZ : Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      fun y hy => Subgroup.centralizer_le (fun z hz => hZV hz) (hP (s.Y_le_P₁ hy))
    have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun t ht =>
      Subgroup.mem_centralizer_iff.2 fun z hz =>
        (Subgroup.mem_centralizer_iff.1 (hZc hz).2 t ht).symm
    have hHZ : H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      s.gen ▸ sup_le hYZ hTZ
    have hVZ : V ≤ quasithinOmegaOneCenter T := by
      rw [s.hVZ]
      refine conjClosure_le fun h hh z hz => ?_
      have := Subgroup.mem_centralizer_iff.1 (hHZ hh) z hz
      rw [← this]; simpa using hz
    refine s.hJ fun j hj => Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    exact ((Subgroup.mem_centralizer_iff.1 (hZc (hVZ hv)).2 j (thompsonJ_le T hj))).symm
  · have htfae := MinParabolic.tfae_thompsonJ s.minParabolic_P₁ hred hP
    have h1 : ⁅VZ (R₁ H T) (Y ⊔ R₁ H T), thompsonJ (R₁ H T)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hJR
    have h3 : baum (R₁ H T) = baum (pCoreOf 2 (Y ⊔ R₁ H T)) := (htfae.out 1 3).1 h1
    apply s.not_Y_le_normalizer_baum
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (pCoreOf 2 (Y ⊔ R₁ H T) : Set G) :=
      le_normalizer_pCoreOf 2 _ (s.Y_le_P₁ hy)
    have := normalizer_le_normalizer_baum _ hyN
    rwa [← h3, s.baum_R] at this

theorem sylow_S : IsSylowTwoOf (baum T) (Y ⊔ baum T) := by
  obtain ⟨-, hel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo s.sylow_P₁ s.charTwo_P₁
    (Z := quasithinOmegaOneCenter (R₁ H T)) le_rfl
  obtain ⟨-, -, h3, -⟩ := E2_3_two_of_isSolvable hel s.minParabolic_P₁ s.isSolvable_P₁
    (pRank_le_two_of_isSQTKTC s.sqtk_P₁) hred s.hJ_V₁
  rwa [s.baum_R, s.twoResidual_P₁] at h3

end Setting

end CFSG.Quasithin.C126.A5

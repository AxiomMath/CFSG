module

public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6

variable {G : Type} [Group G] [Finite G]

theorem exists_minimal_not_le {S Y M : Subgroup G} (hSY : S ≤ Y) (hY : ¬ Y ≤ M) :
    ∃ P : Subgroup G, S ≤ P ∧ P ≤ Y ∧ ¬ P ≤ M ∧
      ∀ P' : Subgroup G, S ≤ P' → P' < P → P' ≤ M := by
  obtain ⟨P, hP⟩ := (Set.toFinite {P : Subgroup G | S ≤ P ∧ P ≤ Y ∧ ¬ P ≤ M}).exists_minimal
    ⟨Y, hSY, le_rfl, hY⟩
  refine ⟨P, hP.prop.1, hP.prop.2.1, hP.prop.2.2, fun P' hSP' hlt => ?_⟩
  by_contra hP'M
  exact absurd (hP.2 ⟨hSP', hlt.le.trans hP.prop.2.1, hP'M⟩ hlt.le) (not_le_of_gt hlt)

omit [Finite G] in
theorem minParabolic_of_minimal {S P M : Subgroup G} (hsyl : IsSylowTwoOf S P) (hSM : S ≤ M)
    (hPM : ¬ P ≤ M) (hmin : ∀ P' : Subgroup G, S ≤ P' → P' < P → P' ≤ M)
    (hnorm : ¬ P ≤ Subgroup.normalizer (S : Set G)) : MinParabolic P S (P ⊓ M) := by
  refine ⟨hsyl, hnorm, ?_⟩
  have hlt : P ⊓ M < P := lt_of_le_of_ne inf_le_left fun h => hPM (h ▸ inf_le_right)
  have hSPM : S ≤ P ⊓ M := le_inf hsyl.1 hSM
  rw [isUniqueMaxOver_iff]
  refine ⟨⟨hlt, fun K hK hKP => ?_⟩, hSPM, fun N hN hSN => ?_⟩
  · by_contra hKP'
    have hKlt : K < P := lt_of_le_of_ne hKP hKP'
    exact absurd (le_inf hKlt.le (hmin K (hSPM.trans hK.le) hKlt)) (not_le_of_gt hK)
  · have hNM : N ≤ M := hmin N hSN hN.1
    have hNle : N ≤ P ⊓ M := le_inf hN.1.le hNM
    by_contra hne
    have hNlt : N < P ⊓ M := lt_of_le_of_ne hNle hne
    exact absurd (hN.2 _ hNlt inf_le_left) (ne_of_lt hlt)

theorem isSolvable_of_perfectCore_le {U T M V : Subgroup G} (h : MinParabolic U T M)
    (hred : IsTwoReducedIn U V) (hUV : ¬ U ≤ Subgroup.centralizer (V : Set G))
    (hperf : perfectCore U ≤ Subgroup.centralizer (V : Set G)) : Group.IsSolvable ↥U := by
  have hJ : perfectCore U ≤ kerIn M U :=
    (le_inf (perfectCore_le U) hperf).trans (h.inf_centralizer_le_kerIn hred hUV)
  have hsyl := h.isSylowTwoOf_pCoreOf_kerIn
  have hQJ : pCoreOf 2 U ≤ kerIn M U := hsyl.1
  have hNn : ((pCoreOf 2 U).subgroupOf (kerIn M U)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQJ).2
      (h.kerIn_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 U))
  have hJsolv : Group.IsSolvable ↥(kerIn M U) := by
    have h2 : IsPGroup 2 ↥((pCoreOf 2 U).subgroupOf (kerIn M U)) :=
      (hsyl.2.1).of_equiv (Subgroup.subgroupOfEquivOfLe hQJ).symm
    have hnil := h2.isNilpotent
    have : Group.IsSolvable ↥((pCoreOf 2 U).subgroupOf (kerIn M U)) := inferInstance
    have hodd : Odd (Nat.card (↥(kerIn M U) ⧸ (pCoreOf 2 U).subgroupOf (kerIn M U))) := by
      rw [Nat.odd_iff]
      have hrel := hsyl.2.2
      rcases Nat.even_or_odd (Nat.card (↥(kerIn M U) ⧸ (pCoreOf 2 U).subgroupOf (kerIn M U)))
        with he | ho
      · exact absurd (even_iff_two_dvd.1 he) hrel
      · exact Nat.odd_iff.1 ho
    have hq : Group.IsSolvable (↥(kerIn M U) ⧸ (pCoreOf 2 U).subgroupOf (kerIn M U)) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact Group.isSolvable_of_ker_le_range ((pCoreOf 2 U).subgroupOf (kerIn M U)).subtype
      (QuotientGroup.mk' ((pCoreOf 2 U).subgroupOf (kerIn M U)))
      (by simp)
  have hle : perfectCore U ≤ perfectCore (kerIn M U) :=
    le_perfectCore_of_perfect hJ (perfectCore_perfect U)
  have h0 : perfectCore (kerIn M U) = ⊥ := (isSolvable_iff_perfectCore_eq_bot _).1 hJsolv
  rw [isSolvable_iff_perfectCore_eq_bot]
  exact le_bot_iff.1 (hle.trans h0.le)

theorem omegaOneCenterOf_le_omegaOneCenterOf_thompsonJ (T : Subgroup G) :
    omegaOneCenterOf T ≤ omegaOneCenterOf (thompsonJ T) := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxT, hxC⟩, hx2⟩
  have hxA : x ∈ A₀ := by
    have hxCA : x ∈ T ⊓ Subgroup.centralizer (A₀ : Set G) :=
      ⟨hxT, Subgroup.centralizer_le hA₀.1 hxC⟩
    have : x ∈ omegaOneOf (T ⊓ Subgroup.centralizer (A₀ : Set G)) :=
      Subgroup.subset_closure ⟨hxCA, hx2⟩
    rwa [← eq_omegaOneOf_centralizer hA₀] at this
  have hxJ : x ∈ thompsonJ T := le_thompsonJ hA₀ hxA
  refine Subgroup.subset_closure ⟨⟨hxJ, ?_⟩, hx2⟩
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  exact Subgroup.mem_centralizer_iff.1 hxC y (thompsonJ_le T hy)

theorem omegaOneCenterOf_baum (T : Subgroup G) :
    omegaOneCenterOf (baum T) = omegaOneCenterOf (thompsonJ T) := by
  have hJS : thompsonJ (baum T) = thompsonJ T :=
    B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum T) inf_le_left
  apply le_antisymm
  · have h1 : omegaOneCenterOf (baum T) ≤
        omegaOneOf (baum T ⊓ Subgroup.centralizer (thompsonJ (baum T) : Set G)) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨⟨hxS, hxC⟩, hx2⟩
      exact Subgroup.subset_closure ⟨⟨hxS, Subgroup.centralizer_le (thompsonJ_le _) hxC⟩, hx2⟩
    rw [(omegaOne_centralizer_thompsonJ (baum T)).1, hJS] at h1
    exact h1
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨⟨hxJ, hxC⟩, hx2⟩
    have hxE : x ∈ omegaOneCenterOf (thompsonJ T) := Subgroup.subset_closure ⟨⟨hxJ, hxC⟩, hx2⟩
    refine Subgroup.subset_closure ⟨⟨(B6.thompsonJ_le_baum T) hxJ, ?_⟩, hx2⟩
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    exact (Subgroup.mem_centralizer_iff.1 hy.2 x hxE).symm

end CFSG.Quasithin.C1Pack

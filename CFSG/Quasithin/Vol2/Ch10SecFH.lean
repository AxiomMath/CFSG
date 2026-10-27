module

public import CFSG.Quasithin.Vol2.Ch10SecB6C23
public import CFSG.Quasithin.Vol2.Ch10SecE21A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem inH_normalizer_baum (hyp : Hyp10 G T L I) :
    InH T (Subgroup.normalizer (baum T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨SecE.le_normalizer_baum T, fun hb => SecE.baum_ne_bot hyp (le_bot_iff.mp ?_)⟩
  rw [← hb]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
    (hyp.fsu.sylow.1.to_le inf_le_left)

theorem exists_isHStar_le {M Y : Subgroup G} (hY : InH T Y) (hYM : ¬ Y ≤ M) :
    ∃ H : Subgroup G, IsHStar T M H ∧ H ≤ Y := by
  classical
  induction hn : Nat.card Y using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
    by_cases hmin : ∀ Y' : Subgroup G, InH T Y' → Y' ≤ Y → ¬ Y' ≤ M → Y' = Y
    · exact ⟨Y, ⟨hY, hYM, hmin⟩, le_rfl⟩
    · push Not at hmin
      obtain ⟨Y', hY', hY'Y, hY'M, hne⟩ := hmin
      have hlt : Nat.card Y' < n := by
        rw [← hn]
        exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hY'Y hne)
      obtain ⟨H, hH, hHY'⟩ := ih _ hlt hY' hY'M rfl
      exact ⟨H, hH, hHY'.trans hY'Y⟩

theorem exists_isHStar_le_normalizer_baum (hyp : Hyp10 G T L I)
    (hNS : ¬ Subgroup.normalizer (baum T : Set G) ≤ fsuM T L) :
    ∃ H : Subgroup G, IsHStar T (fsuM T L) H ∧ H ≤ Subgroup.normalizer (baum T : Set G) :=
  exists_isHStar_le (inH_normalizer_baum hyp) hNS

omit [Finite G] in
theorem omegaOneCenterOf_thompsonJ_le (T : Subgroup G) :
    omegaOneCenterOf (thompsonJ T) ≤ T := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, -⟩
  exact (iSup₂_le fun _ hA => hA.1 : thompsonJ T ≤ T) hx.1

omit [Finite G] in
theorem omegaOneCenter_le_omegaOneCenterOf_baum (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ omegaOneCenterOf (baum T) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨⟨hzT, hzC⟩, hz2⟩
  refine Subgroup.subset_closure ⟨⟨⟨hzT, ?_⟩, ?_⟩, hz2⟩
  · exact Subgroup.centralizer_le (omegaOneCenterOf_thompsonJ_le T) hzC
  · exact Subgroup.centralizer_le (fun x hx => hx.1) hzC

omit [Finite G] in
theorem VZ_le_omegaOneCenterOf_baum {H : Subgroup G}
    (hHS : H ≤ Subgroup.normalizer (baum T : Set G)) :
    VZ T H ≤ omegaOneCenterOf (baum T) := by
  refine conjClosure_le fun h hh z hz => ?_
  have hN := A4.normalizer_le_normalizer_omegaOneCenterOf (baum T) (hHS hh)
  exact (Subgroup.mem_normalizer_iff.mp hN z).mp (omegaOneCenter_le_omegaOneCenterOf_baum T hz)

omit [Finite G] in
theorem omegaOneCenter_le_self (T : Subgroup G) : quasithinOmegaOneCenter T ≤ T := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨⟨hzT, -⟩, -⟩
  exact hzT

omit [Finite G] in
theorem omegaOneCenter_le_centralizer (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨⟨-, hzC⟩, -⟩
  exact hzC

theorem centralizer_omegaOneCenter_inf_le (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I)
    (hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≠ ⊥) :
    Subgroup.centralizer ((quasithinOmegaOneCenter T ⊓
      Subgroup.centralizer (fsuL0 T L : Set G) : Subgroup G) : Set G) ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) with hCdef
  have hCZ' : C ≤ quasithinOmegaOneCenter T := inf_le_left
  have hCT : C ≤ T := hCZ'.trans (omegaOneCenter_le_self T)
  have hTC : T ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hCZ'.trans (omegaOneCenter_le_centralizer T))
  have hL0C : fsuL0 T L ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.le_centralizer_iff.mpr inf_le_right
  have hCC : C ≤ Subgroup.centralizer (C : Set G) := hCT.trans hTC
  refine SecB.le_fsuM_of_L0T h331 hyp (sup_le hL0C hTC) fun hb => hCZ (le_bot_iff.mp ?_)
  rw [← hb]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCC
    (Subgroup.centralizer_le_normalizer _) (hyp.fsu.sylow.1.to_le hCT)

theorem centralizer_VZ_le (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I)
    (hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≠ ⊥)
    (H : Subgroup G) : Subgroup.centralizer (VZ T H : Set G) ≤ fsuM T L :=
  (Subgroup.centralizer_le (inf_le_left.trans (le_conjClosure _ H))).trans
    (centralizer_omegaOneCenter_inf_le h331 hyp hCZ)

end CFSG.Quasithin.Vol2.Ch10.SecF

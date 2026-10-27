module

public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Vol2.Ch10SecD211F
public import CFSG.Quasithin.Vol2.Ch10StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem inH_of_le_of_sylow (hT : quasithinIsSylowTwo T) {Y H : Subgroup G} (hTY : T ≤ Y)
    (hYH : Y ≤ H) (hH : InH T H) : InH T Y := by
  refine ⟨hTY, fun hbot => hH.2 (le_bot_iff.mp ?_)⟩
  rw [← hbot]
  have hS := isSylowTwoOf_of_quasithinIsSylowTwo hT (hTY.trans hYH)
  exact pCoreOf_le_pCoreOf_of_sylow hYH hT.1 hTY hS.2.2

theorem exists_isHStar_le {M Y : Subgroup G} (hY : InH T Y)
    (hYM : ¬ Y ≤ M) : ∃ H : Subgroup G, IsHStar T M H ∧ H ≤ Y := by
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

theorem le_fsuM_of_isSolvable (h10213 : Stmt10_2_13) (h : Hyp10 G T L I) {Y : Subgroup G}
    (hY : InH T Y) (hYs : Group.IsSolvable ↥Y) : Y ≤ fsuM T L := by
  by_contra hYM
  obtain ⟨H, hH, hHY⟩ := exists_isHStar_le hY hYM
  have hHs : Group.IsSolvable ↥H := by
    have := hYs
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHY)
  have h1 := E1.solvable_nParam_le_one hHs
  rw [(h10213 G T L I h).2.2 H hH] at h1
  exact absurd h1 (by norm_num)

omit [Finite G] in
theorem le_centralizer_of_mem_omegaOneCenter {z : G} (hz : z ∈ quasithinOmegaOneCenter T) :
    T ≤ Subgroup.centralizer ({z} : Set G) := by
  have hzC : z ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr (fun x hx => hx.1) hz
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hzC.2) s hs

theorem mem_omegaOneCenter_inf (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) :
    v₁ * v₂ ∈ quasithinOmegaOneCenter T ⊓ fsuVM T L I := by
  have hTz := T_le_centralizer_z h37 h38 h h3 hc hd
  obtain ⟨ht, -, hv1, -, hv2, -⟩ := hd
  have hzV : v₁ * v₂ ∈ fsuVM T L I :=
    (fsuVM T L I).mul_mem (V1_le_V hv1.1) (commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hv2.1)
  refine ⟨Subgroup.subset_closure ⟨⟨SecA.fsuVM_le_T h hzV, ?_⟩, ?_⟩, hzV⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mp (hTz hs)
  · exact (SecA.isElemAbelian_fsuVM h).2 _ hzV

theorem exists_isHStar_le_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1032 : Stmt10_3_2) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) :
    ∃ H : Subgroup G, IsHStar T (fsuM T L) H ∧
      H ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) := by
  have hz := mem_omegaOneCenter_inf h37 h38 h h3 hc hd
  have hzM := h1032 G T L I h _ hz (z_ne_one h37 h38 h hc hd)
  exact exists_isHStar_le
    ⟨T_le_centralizer_z h37 h38 h h3 hc hd, pCoreOf_Gz_ne_bot h37 h38 h hc hd⟩ hzM

end CFSG.Quasithin.Vol2.Ch10.SecD

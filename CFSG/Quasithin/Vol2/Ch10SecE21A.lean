module

public import CFSG.Quasithin.Vol2.Ch10SecECase1b
public import CFSG.Quasithin.Vol2.Ch10SecBSetup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem normalizer_le_fsuM_of_sylow (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    (huniq : ∃ N : Subgroup G, IsUniqueMaxOver (fsuL0 T L ⊔ T) T N) {R : Subgroup G}
    (hR : R ≠ ⊥) (hRT : R ≤ T) (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hsyl : IsSylowTwoOf R (fsuL0 T L ⊔ R)) : Subgroup.normalizer (R : Set G) ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 R := hyp.fsu.sylow.1.to_le hRT
  have hNR : InH T (Subgroup.normalizer (R : Set G)) := by
    refine ⟨hTR, fun hb => hR (le_bot_iff.mp ?_)⟩
    rw [← hb]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hR2
  have hH : InH T (fsuL0 T L ⊔ T) := ⟨le_sup_right, SecA.pCoreOf_L0T_ne_bot hyp⟩
  have hsyl' : IsSylowTwoOf R (oTwoUpper (fsuL0 T L ⊔ T) ⊔ R) := by
    rw [oTwoUpper_fsuL0_sup h37 h38 hyp]
    exact hsyl
  obtain ⟨R₀, hR₀, hR₀R, hnorm⟩ := h311 G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.sylow _ _ R hNR hH huniq hR hRT hsyl' le_rfl
  by_contra hle
  have hbot := pCoreOf_sup_eq_bot_of_isUniqueM (SecB.isUniqueM_L0T h331 hyp) hle
  apply hR₀
  refine le_bot_iff.mp (hbot ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
    (hR2.to_le hR₀R))
  · exact (hR₀R.trans hRT).trans (le_sup_right.trans le_sup_left)
  · rw [sup_comm]
    exact hnorm

omit [Finite G] in
theorem le_normalizer_baum (T : Subgroup G) : T ≤ Subgroup.normalizer (baum T : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)

theorem baum_ne_bot (hyp : Hyp10 G T L I) : baum T ≠ ⊥ := by
  have hT : T ≠ ⊥ := fun h => SecA.fsuVM_ne_bot hyp.fsu (le_bot_iff.mp (h ▸ SecA.fsuVM_le_T hyp))
  have hJ := thompsonJ_ne_bot_of_isPGroup hyp.fsu.sylow.1 hT
  exact fun h => hJ (le_bot_iff.mp (h ▸ B2F.thompsonJ_le_baum T))

theorem normalizer_baum_le_of_thompsonJ (h3210 : Ch10.TmpL6_3_2_10_eight) (hyp : Hyp10 G T L I)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    Subgroup.normalizer (baum T : Set G) ≤ fsuM T L := by
  have hS2 : IsPGroup 2 (baum T) := hyp.fsu.sylow.1.to_le inf_le_left
  have hJS : thompsonJ T ≤ baum T := B2F.thompsonJ_le_baum T
  by_cases hiii : Ch10.Sub326iii T L I
  · exact (h3210 G T L I (fsuVM T L I) hyp.fsu (Or.inl ⟨hiii, rfl⟩) hJ (baum T) hS2 hJS).2
  · exact (h3210 G T L I (fsuV T I) hyp.fsu (Or.inr ⟨hiii, rfl⟩)
      (hJ.trans (Subgroup.centralizer_le (SecA.fsuV_le_fsuVM T L I))) (baum T) hS2 hJS).2

theorem exists_isUniqueMaxOver_L0T
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hshape : Stmt7_0_1_shape) (hyp : Hyp10 G T L I)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I) :
    ∃ N : Subgroup G, IsUniqueMaxOver (fsuL0 T L ⊔ T) T N :=
  ⟨_, (SecA.minParabolic_L0T h37 h38 hyp (SecA.exists_SL_two_of_cases12 hshape hyp h12)).uniqueMax⟩

theorem e23_case1
    (he23 : E2.E23Statement) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) {n : ℕ}
    (h1 : Ch10.Case10_1_1One T L I n)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    IsSylowTwoOf (baum T) (fsuL0 T L ⊔ baum T) ∧
      baum T ≤ Ch10.T0 T L ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ∧
      thompsonJ T ≤ Ch10.T0 T L ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
  obtain ⟨hKJ, I', hcard, hJeq, hcomm, hind, htrans, htype, -, -, h2, -⟩ :=
    SecA.e23Concl_L0T he23 h37 h38 hshape h3228 hyp (Or.inl ⟨n, h1⟩) hJ
  have hL2 := isL2Natural_of_case1 h37 h38 h322 hyp h1 hKJ hcard hJeq hcomm hind htrans htype
  have hJH := autI_thompsonJ_eq_case1 h37 h38 h322 hyp h1 hKJ hcard hJeq hcomm hind htrans htype
  obtain ⟨hbaum, hsyl, hsylS, -⟩ := h2 hL2
  have hJle : autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T) ≤
      autI (SecA.isElemAbelian_fsuVM hyp) (fsuL0 T L) := hJH ▸ hsyl.1
  refine ⟨?_, le_T0_sup_of_autI_le h37 h38 hyp inf_le_left (hbaum ▸ hJle),
    le_T0_sup_of_autI_le h37 h38 hyp (iSup₂_le fun _ hA => hA.1) hJle⟩
  rw [twoResidual_fsuL0_sup h37 h38 hyp] at hsylS
  exact hsylS

theorem normalizer_baum_le_case1
    (he23 : E2.E23Statement) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (hyp : Hyp10 G T L I) {n : ℕ} (h1 : Ch10.Case10_1_1One T L I n)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    Subgroup.normalizer (baum T : Set G) ≤ fsuM T L :=
  normalizer_le_fsuM_of_sylow h311 h331 h37 h38 hyp
    (exists_isUniqueMaxOver_L0T h37 h38 hshape hyp (Or.inl ⟨n, h1⟩)) (baum_ne_bot hyp)
    inf_le_left (le_normalizer_baum T) (e23_case1 he23 h37 h38 h322 hshape h3228 hyp h1 hJ).1

end CFSG.Quasithin.Vol2.Ch10.SecE

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ContextFacts
public import CFSG.LocalAnalysis.WeakClosure81.SixEleven
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u
public import CFSG.Quasithin.Background.E3MParamTI
public import CFSG.RankThree.GroupTheory.SteinbergBYAschCoreConjugacy
public import CFSG.Quasithin.Background.C1PackC129Case

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def CentTVLeO2LT (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    D.T ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)

private theorem uc22s2342_generator_comm (D : Data G) (Ch : Choice2011 G)
    (h41 : S23_41 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hE2 : IsPGroup 2 c.E) {i : ℕ} (hi : i ≤ 1) {A : Subgroup G}
    (hA : A ∈ CFSG.Quasithin.E3.gammaSet c.E i D.T) : ⁅c.V, A⁆ = ⊥ := by
  obtain ⟨hAT, g, hAg, hm⟩ := hA
  let F : Subgroup G := CFSG.Quasithin.conjSubgroup A g⁻¹
  have hFE : F ≤ c.E := by
    have h := CFSG.Quasithin.E3.conjSubgroup_mono_left g⁻¹ hAg
    rwa [CFSG.Quasithin.E3.conjSubgroup_conj_inv] at h
  have hFg : CFSG.Quasithin.conjSubgroup F g = A := by
    unfold F
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
      CFSG.Quasithin.conjSubgroup_one]
  have hE2' : IsPGroup 2 (CFSG.Quasithin.conjSubgroup c.E g) :=
    hE2.map (MulAut.conj g⁻¹).toMonoidHom
  have hrel : F.relIndex c.E = A.relIndex (CFSG.Quasithin.conjSubgroup c.E g) := by
    rw [← CFSG.Quasithin.E3.relIndex_conjSubgroup F c.E g, hFg]
  have hArel : A.relIndex (CFSG.Quasithin.conjSubgroup c.E g) = 2 ^ i := by
    rw [CFSG.Quasithin.E3.relIndex_eq_two_pow hE2' A, hm]
  have hindex : (F.subgroupOf c.E).index ≤ 2 := by
    have h : F.relIndex c.E ≤ 2 := by
      rw [hrel.trans hArel]
      calc 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hi
        _ = 2 := by norm_num
    simpa [Subgroup.relIndex] using h
  have hcomm := h41 h1930 c F hFE hindex g (by rw [hFg]; exact hAT)
  rwa [hFg] at hcomm

private theorem uc22s2342_wClos_comm (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h41 : S23_41 D Ch) (h1930 : H1930 D)
    (c : Ctx23L D Ch) {i : ℕ} (hi : i ≤ 1) :
    ⁅c.V, CFSG.Quasithin.E3.wClos c.E i D.T⁆ = ⊥ := by
  have hE2 : IsPGroup 2 c.E :=
    CFSG.Open.IsElemAbelian.isPGroup (c.isElemAbelian_E h4 h39 h1930)
  have hcent : CFSG.Quasithin.E3.wClos c.E i D.T ≤
      Subgroup.centralizer (c.V : Set G) :=
    CFSG.Quasithin.E3.wClos_le_of_forall fun A hA => by
      have h := uc22s2342_generator_comm D Ch h41 h1930 c hE2 hi hA
      have h' : ⁅A, c.V⁆ = ⊥ := by rwa [Subgroup.commutator_comm] at h
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := A) (H₂ := c.V)).mp h'
  have h' : ⁅CFSG.Quasithin.E3.wClos c.E i D.T, c.V⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hcent
  rwa [Subgroup.commutator_comm] at h'

private theorem uc22s2342_normalizer_wClos0_le (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h41 : S23_41 D Ch)
    (hCTV : CentTVLeO2LT D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    Subgroup.normalizer (CFSG.Quasithin.E3.wClos c.E 0 D.T : Set G) ≤ c.N := by
  set W0 := CFSG.Quasithin.E3.wClos c.E 0 D.T with hW0
  have hW0_le_T : W0 ≤ D.T := CFSG.Quasithin.E3.wClos_le 0 D.T
  have hW0_comm : ⁅c.V, W0⁆ = ⊥ :=
    uc22s2342_wClos_comm D Ch h4 h39 h41 h1930 c (i := 0) (by norm_num)
  have hW0_le_cent : W0 ≤ Subgroup.centralizer (c.V : Set G) := by
    have h' : ⁅W0, c.V⁆ = ⊥ := by rwa [Subgroup.commutator_comm] at hW0_comm
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := W0) (H₂ := c.V)).mp h'
  have hW0_le_S : W0 ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    fun x hx => (hCTV h1930 c) ⟨hW0_le_T hx, hW0_le_cent hx⟩
  have hE_le_T : c.E ≤ D.T := c.E_le_T h39 h1930
  have hE_le_W0 : c.E ≤ W0 := by
    refine CFSG.Quasithin.E3.le_wClos ?_
    refine ⟨hE_le_T, 1, ?_, ?_⟩
    · rw [CFSG.Quasithin.conjSubgroup_one]
    · rw [CFSG.Quasithin.conjSubgroup_one]
      exact CFSG.Quasithin.E3.mQuot_self c.E
  have hW0_ne : W0 ≠ ⊥ := by
    intro h
    exact c.E_ne_bot h4 h1930 (le_bot_iff.mp (h ▸ hE_le_W0))
  have hW0_p : IsPGroup 2 W0 := D.sylowM.isPGroup.to_le hW0_le_T
  have hSylLT : IsSylowIn 2 D.T (c.L ⊔ D.T) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp (D.sylowG.of_le le_sup_right le_top)
  have hS_le_LT : CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤ c.L ⊔ D.T :=
    CFSG.openPCoreOf_le 2 (c.L ⊔ D.T)
  have hS_p : IsPGroup 2 (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (c.L ⊔ D.T)
  have hW0_eq : W0 = CFSG.Quasithin.E3.wClos c.E 0
      (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) :=
    CFSG.Quasithin.E3.e3_15 hSylLT hS_le_LT hS_p hW0_le_S
  have hLT_norm_S : c.L ⊔ D.T ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (c.L ⊔ D.T)
  have hLT_norm_W0 : c.L ⊔ D.T ≤ Subgroup.normalizer (W0 : Set G) := by
    rw [hW0_eq]
    exact hLT_norm_S.trans
      (CFSG.Quasithin.E3.normalizer_le_normalizer_wClos (V := c.E) (i := 0) _)
  have hloc : IsTwoLocal (Subgroup.normalizer (W0 : Set G)) :=
    ⟨W0, hW0_ne, hW0_p, rfl⟩
  obtain ⟨K, hKmax, hKle⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_exists_isMaxTwoLocal hloc
  have hKmem : K ∈ calMOf (c.L ⊔ D.T) := ⟨hKmax, hLT_norm_W0.trans hKle⟩
  rw [c.hN] at hKmem
  have hK : K = c.N := Set.mem_singleton_iff.mp hKmem
  exact hKle.trans (le_of_eq hK)

private theorem uc22s2342_centralizer_cClos1_le (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h41 : S23_41 D Ch) (h1930 : H1930 D)
    (c : Ctx23L D Ch) :
    Subgroup.centralizer (CFSG.Quasithin.E3.cClos c.E 1 D.T : Set G) ≤ c.N := by
  have hW1_comm : ⁅c.V, CFSG.Quasithin.E3.wClos c.E 1 D.T⁆ = ⊥ :=
    uc22s2342_wClos_comm D Ch h4 h39 h41 h1930 c (i := 1) le_rfl
  have hV_le_cent : c.V ≤ Subgroup.centralizer
      (CFSG.Quasithin.E3.wClos c.E 1 D.T : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := c.V) (H₂ := CFSG.Quasithin.E3.wClos c.E 1 D.T)).mp hW1_comm
  have hV_le_C1 : c.V ≤ CFSG.Quasithin.E3.cClos c.E 1 D.T := by
    rw [CFSG.Quasithin.E3.cClos]
    exact le_inf (c.V_le_T h4 h1930) hV_le_cent
  exact (Subgroup.centralizer_le hV_le_C1).trans
    (c.centralizer_V_le_N h4 h1930)

private theorem uc22s2342_pRank_le_mParam (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h41 : S23_41 D Ch) (h1930 : H1930 D)
    (c : Ctx23L D Ch) :
    CFSG.Open.pRank 2 D.Z ≤
      CFSG.Quasithin.E3.mParam
        (CFSG.Quasithin.autI (c.isElemAbelian_E h4 h39 h1930) ⊤) := by
  have hEelem := c.isElemAbelian_E h4 h39 h1930
  have hspanG := c.E_span
  let Y : ↥D.M × ↥c.N → Subgroup G :=
    fun p => CFSG.Quasithin.conjSubgroup D.Z ((p.1 : G) * (p.2 : G))⁻¹
  have hYleE : ∀ p : ↥D.M × ↥c.N, Y p ≤ c.E := by
    intro p
    have hE_decomp : c.E = ⨆ m : ↥D.M, c.V.map (MulAut.conj (m : G)).toMonoidHom := by
      rw [Ctx23L.E]
      exact uc22br4_conjClosure_eq D.M c.V
    have hV_decomp : c.V = ⨆ n : ↥c.N, D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
      rw [Ctx23L.V]
      exact uc22br4_conjClosure_eq c.N D.Z
    have h1 : Y p = CFSG.Quasithin.conjSubgroup
        (CFSG.Quasithin.conjSubgroup D.Z ((p.2 : G)⁻¹)) ((p.1 : G)⁻¹) := by
      dsimp [Y]
      rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [h1]
    have hZn : CFSG.Quasithin.conjSubgroup D.Z ((p.2 : G)⁻¹) ≤ c.V := by
      rw [hV_decomp]
      simpa [CFSG.Quasithin.conjSubgroup] using
        (le_iSup (fun n : ↥c.N => D.Z.map (MulAut.conj (n : G)).toMonoidHom) p.2)
    have hVm : CFSG.Quasithin.conjSubgroup c.V ((p.1 : G)⁻¹) ≤ c.E := by
      rw [hE_decomp]
      simpa [CFSG.Quasithin.conjSubgroup] using
        (le_iSup (fun m : ↥D.M => c.V.map (MulAut.conj (m : G)).toMonoidHom) p.1)
    exact (CFSG.Quasithin.E3.conjSubgroup_mono_left ((p.1 : G)⁻¹) hZn).trans hVm
  have hTI : ∀ (p : ↥D.M × ↥c.N) (g : G),
      Y p ⊓ CFSG.Quasithin.conjSubgroup (Y p) g ≠ ⊥ →
        CFSG.Quasithin.conjSubgroup (Y p) g = Y p := by
    intro p g hne
    exact c.conjSubgroup_TI h4 h1930 ((p.1 : G) * (p.2 : G))⁻¹ g hne
  have hCN : ∀ (p : ↥D.M × ↥c.N) (x : G),
      x ∈ Subgroup.normalizer (Y p : Set G) →
      (∃ k : ℕ, orderOf x = 2 ^ k) → ∀ y ∈ Y p, x * y * x⁻¹ = y := by
    intro p x hxN hx2
    exact c.conjSubgroup_twoElement_centralizes h4 h1930 ((p.1 : G) * (p.2 : G))⁻¹ hxN hx2
  have hk : ∀ p : ↥D.M × ↥c.N,
      CFSG.Open.pRank 2 D.Z ≤ CFSG.Open.pRank 2 (Y p) := by
    intro p
    have hYmap : Y p =
        D.Z.map (MulAut.conj ((p.1 : G) * (p.2 : G))).toMonoidHom := by
      dsimp [Y, CFSG.Quasithin.conjSubgroup]
      rw [inv_inv]
    rw [hYmap]
    exact le_of_eq (CFSG.RankThree.GroupTheory.SteinbergBY.assembly_pRank_map_mulEquiv
      (by norm_num) (MulAut.conj ((p.1 : G) * (p.2 : G))) D.Z).symm
  exact CFSG.Quasithin.E3.le_mParam_of_tiFamily hEelem Y hYleE hspanG hTI hCN
    (CFSG.Open.pRank 2 D.Z) hk

private theorem uc22s2342_one_lt_sParam (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h41 : S23_41 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) (hn : 2 ≤ CFSG.Open.pRank 2 D.Z) :
    1 < CFSG.Quasithin.E3.sParam (c.isElemAbelian_E h4 h39 h1930) := by
  have hEelem := c.isElemAbelian_E h4 h39 h1930
  have hr : (1 : ℕ∞) < CFSG.Quasithin.E3.rParam c.E := by
    have h40c := h40 h1930 c
    have hNG : Subgroup.normalizer (c.E : Set G) = D.M :=
      c.normalizer_E_eq h4 h39 h1930
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.rMV_eq_rParam hNG] at h40c
    have hlt1 : (1 : ℕ∞) < ((CFSG.Open.pRank 2 D.Z : ℕ) : ℕ∞) + 1 := by
      rw [ENat.lt_add_one_iff (ENat.natCast_ne_top _)]
      exact_mod_cast (by omega : 1 ≤ CFSG.Open.pRank 2 D.Z)
    exact hlt1.trans h40c
  have hm : 1 < CFSG.Quasithin.E3.mParam (CFSG.Quasithin.autI hEelem ⊤) :=
    lt_of_lt_of_le (by omega : 1 < CFSG.Open.pRank 2 D.Z)
      (uc22s2342_pRank_le_mParam D Ch h4 h39 h41 h1930 c)
  exact CFSG.Quasithin.E3.lt_sParam_of_lt hEelem (k := 1) hr hm

theorem s23_42_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h41 : S23_41 D Ch) (hCTV : CentTVLeO2LT D Ch)
    (hn : 2 ≤ CFSG.Open.pRank 2 D.Z) : S23_42 D Ch := by
  intro h1930 c
  have hEelem := c.isElemAbelian_E h4 h39 h1930
  have hspos : 1 < CFSG.Quasithin.E3.sParam hEelem :=
    uc22s2342_one_lt_sParam D Ch h4 h39 h40 h41 h1930 c hn
  have hH_solv : Group.IsSolvable ↥(oTwoFOf D.M ⊔ D.T) := by
    rw [show oTwoFOf D.M = CFSG.Quasithin.oTwoFIn D.M from rfl]
    exact CFSG.Quasithin.isSolvable_oTwoFIn_sup D.sylowM.le D.sylowM.isPGroup
  have hInE : CFSG.Quasithin.E1.InE 1 (oTwoFOf D.M ⊔ D.T) :=
    (CFSG.Quasithin.E1.inE_subgroupOf 1 (oTwoFOf D.M ⊔ D.T)).2
      (CFSG.Quasithin.E1.inE_one_top_of_isSolvable
        (Nat.card ↥(oTwoFOf D.M ⊔ D.T)) ↥(oTwoFOf D.M ⊔ D.T) le_rfl hH_solv)
  have hSylH : CFSG.Quasithin.IsSylowIn 2 D.T (oTwoFOf D.M ⊔ D.T) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp (D.sylowG.of_le le_sup_right le_top)
  have hfac := CFSG.LocalAnalysis.WeakClosure81.six_eleven_three (V := c.E) hEelem
    (H := oTwoFOf D.M ⊔ D.T) (S := D.T) hSylH hInE (i := 0) (j := 1) (by simpa using hspos)
  have hfac' : ((oTwoFOf D.M ⊔ D.T) ⊓
        Subgroup.centralizer (CFSG.Quasithin.E3.cClos c.E 1 D.T : Set G)) ⊔
      ((oTwoFOf D.M ⊔ D.T) ⊓
        Subgroup.normalizer (CFSG.Quasithin.E3.wClos c.E 0 D.T : Set G)) =
      oTwoFOf D.M ⊔ D.T := by
    simpa using hfac
  have hsub : oTwoFOf D.M ⊔ D.T ≤ c.N := by
    rw [← hfac']
    refine sup_le ?_ ?_
    · exact (inf_le_right : ((oTwoFOf D.M ⊔ D.T) ⊓
        Subgroup.centralizer (CFSG.Quasithin.E3.cClos c.E 1 D.T : Set G)) ≤ _).trans
        (uc22s2342_centralizer_cClos1_le D Ch h4 h39 h41 h1930 c)
    · exact (inf_le_right : ((oTwoFOf D.M ⊔ D.T) ⊓
        Subgroup.normalizer (CFSG.Quasithin.E3.wClos c.E 0 D.T : Set G)) ≤ _).trans
        (uc22s2342_normalizer_wClos0_le D Ch h4 h39 h41 hCTV h1930 c)
  exact le_sup_left.trans hsub

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

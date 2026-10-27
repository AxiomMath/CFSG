module

public import CFSG.Quasithin.Vol2.Ch11SecHEnd3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec

variable {G : Type} [Group G] [Finite G]

theorem false_of_config (i : Inp32) {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h : G}
    (hyp : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (h31 : Hyp11_3_1 T L I n V₁ H)
    (hnot : ¬ Concl11_3_2 T L I n V₁ H) (hAT : conjSubgroup (fsuV T I) g ≤ T)
    (hAC : ¬ conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (VZ T H : Set G))
    (hH : h ∈ H) (hM : h ∉ Subgroup.normalizer (L : Set G)) : False := by
  obtain ⟨y, d⟩ := Cfg.exists_data ⟨⟨hyp, hV₁, h31, hnot, hAT, hAC⟩, hH, hM⟩ i
  exact d.false i

theorem centralizer_VZ_le_of (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) {T L I : Subgroup G}
    {n : ℕ} {V₁ H : Subgroup G} (hyp : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (h31 : Hyp11_3_1 T L I n V₁ H) (hnot : ¬ Concl11_3_2 T L I n V₁ H) :
    H ⊓ Subgroup.centralizer (VZ T H : Set G) ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := SecA.isSylowTwoOf_of_isHStar hyp h31.hstar
  have hKC := SecC.inf_centralizer_VZ_eq h1135 h1136 hyp hV₁ h31 hnot
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (le_normalizer_inf_centralizer (SecC.le_normalizer_VZ T H)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨e, he⟩ := two_of_sup hyp.fsu.sylow.1 (hsyl.1.trans (le_normalizer_oTwoUpper H)) x
    ((SecC.oTwoUpper_sup_eq hsyl).ge hx.1)
  have hmem : x ^ 2 ^ e ∈ pCoreOf 2 (oTwoUpper H) := by
    rw [← hKC]
    exact ⟨he, Subgroup.pow_mem _ hx.2 _⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (oTwoUpper H) ⟨_, hmem⟩
  refine ⟨e + k, Subtype.ext ?_⟩
  have hk' : (x ^ 2 ^ e) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  simp [pow_add, pow_mul, hk']

theorem exists_A (h1133 : Stmt11_3_3) (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6)
    {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} (hyp : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (h31 : Hyp11_3_1 T L I n V₁ H) (hnot : ¬ Concl11_3_2 T L I n V₁ H) :
    ∃ g : G, conjSubgroup (fsuV T I) g ≤ T ∧
      ¬ conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (VZ T H : Set G) := by
  have hW := h1133 G T L I n V₁ H hyp hV₁ h31 hnot
  have hex : ∃ A ∈ E3.gammaSet (fsuV T I) 0 T, ¬ A ≤ pCoreOf 2 H := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact hW (by unfold E3.wClos; exact iSup₂_le hall)
  obtain ⟨A, ⟨hAT, g, hAg, hm⟩, hAO⟩ := hex
  have hp : IsPGroup 2 (conjSubgroup (fsuV T I) g) := (SecA.isPGroup_fsuV hyp).map _
  have hAeq : A = conjSubgroup (fsuV T I) g := (E3.mQuot_eq_zero_iff hp hAg).mp hm
  subst hAeq
  refine ⟨g, hAT, fun hC => hAO ?_⟩
  have hTH : T ≤ H := (SecA.isSylowTwoOf_of_isHStar hyp h31.hstar).1
  exact (le_inf (hAT.trans hTH) hC).trans (centralizer_VZ_le_of h1135 h1136 hyp hV₁ h31 hnot)

theorem stmt11_3_2_of (h1102 : Stmt11_0_2) (h1133 : Stmt11_3_3) (h1134 : Stmt11_3_4)
    (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) (h1137 : Stmt11_3_7) (hG16 : ASInputs.AS_G_1_6)
    (hI13 : AS_I_1_3_L2) (hG2 : SecA.FactG2DerivedOrder) (hKF1 : FactTransvInSL3)
    (hKF2 : FactAxisGroupSp4) (hKF3 : FactSL2NatBorel) (hKF5 : FactSL2TwoSylow)
    (hKF6 : FactSL2BorelFPF) : Stmt11_3_2 := by
  intro G _ _ T L I n V₁ H hyp hV₁ h31
  by_contra hnot
  obtain ⟨g, hAT, hAC⟩ := exists_A h1133 h1135 h1136 hyp hV₁ h31 hnot
  obtain ⟨h, hH, hM⟩ := Set.not_subset.mp h31.hstar.2.1
  exact false_of_config ⟨h1102, h1134, h1135, h1136, h1137, hG16, hI13, hG2, hKF1, hKF2, hKF3,
    hKF5, hKF6⟩ hyp hV₁ h31 hnot hAT hAC hH hM

end CFSG.Quasithin.Vol2.Ch11.SecH

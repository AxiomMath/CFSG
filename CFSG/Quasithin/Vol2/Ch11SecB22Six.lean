module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11SecB22Two

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

section General

variable {G : Type} [Group G] [Finite G] {V : Subgroup G}

theorem autI_mem_aSet_of_le (hV : IsElemAbelian 2 V) {g : G} {A : Subgroup G}
    (hAg : A ≤ conjSubgroup V g) (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (hAC : ¬ A ≤ Subgroup.centralizer (V : Set G))
    (hj : E3.mQuot (conjSubgroup V g) A < E3.sParam hV) :
    autI hV A ∈ E3.aSet (E3.sParam hV - E3.mQuot (conjSubgroup V g) A) (autI hV ⊤) := by
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
  refine ⟨autI_mono hV le_top, (autI_eq_bot_iff hV hAN).not.2 hAC,
    isElemAbelian2_autI hV hAel hAN, fun B hB hm => ?_⟩
  rw [E3.mQuot_autI_preI hV hAN hB] at hm
  set B' := preI hV A hAN B with hB'def
  have hB'A : B' ≤ A := preI_le hV
  have hB's : E3.mQuot (conjSubgroup V g) B' < E3.sParam hV := by
    rw [E3.mQuot_add hB'A hAg]
    omega
  have h7B := E3.e3_7 hV (le_inf (hB'A.trans hAg) (hB'A.trans hAN)) hB's
  have h7A := E3.e3_7 hV (le_inf hAg hAN) hj
  ext w
  have e1 : w ∈ fixV B ↔ w.val ∈ Subgroup.centralizer (B' : Set G) := by
    conv_lhs => rw [← autI_preI hV hB (hA := hAN)]
    exact mem_fixV_autI hV (hB'A.trans hAN) w
  rw [e1, mem_fixV_autI hV hAN w]
  constructor
  · intro hc
    have h1 : w.val ∈ V ⊓ Subgroup.centralizer (B' : Set G) := ⟨IntMod.val_mem w, hc⟩
    rw [h7B, ← h7A] at h1
    exact h1.2
  · intro hc
    have h1 : w.val ∈ V ⊓ Subgroup.centralizer (A : Set G) := ⟨IntMod.val_mem w, hc⟩
    rw [h7A, ← h7B] at h1
    exact h1.2

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem centralizer_le_sectionCentralizer {V₁ V₃ : Subgroup G} (h13 : V₁ ≤ V₃) :
    Subgroup.centralizer (V₃ : Set G) ≤ sectionCentralizer V₃ V₁ := by
  intro c hc
  refine ⟨Subgroup.centralizer_le_normalizer _ hc,
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le h13 hc), fun v hv => ?_⟩
  rw [← Subgroup.mem_centralizer_iff.mp hc v hv, mul_inv_cancel_right, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem centralizer_cClos_le (hNF : NatFacts) (hFM : FactMParam) (hFH : FactHyperplaneT)
    (hS44 : FactSp4FourExt) (hN : FactNot4213) (hG12 : FactG2Twelve) (h4213 : TmpL6_4_2_13)
    (h311 : Theorem311Stmt) (h63 : ASInputs.AS_E_6_3) (h664 : ASInputs.AS_E_6_6_four)
    (h614 : ASInputs.AS_E_6_14) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1114 : Stmt11_1_4) (hyp : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hG2 : KindG2 L (fsuV T I) n) :
    Subgroup.centralizer (E3.cClos (fsuV T I) 1 (ROf T L V₁) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hn, hLV, hVL, hnat, -, -⟩ := natSetting h1102 hyp
  have hTV := T_le_normalizer_fsuV T I
  have hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
  have hs := sParam_eq hFM hFH hS44 hN h4213 h311 h63 h664 h614 h331 h1102 h1103 hyp
    (Or.inl ⟨hG2, rfl⟩) hV
  obtain ⟨V₁', V₂', V₃, hV₁', -, hV₃, h12, h23, hu1, -, -⟩ := exists_isVi hNF h1102 hyp
  have hV1eq : V₁ = V₁' := hu1 V₁ hV₁
  subst hV1eq
  have hL1T : QuasithinUnique.IsSylowTwoOf T (LOf L V₁ ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
  have hRT : ROf T L V₁ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hL1T
  have hVR : fsuV T I ≤ ROf T L V₁ := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((fsuV_le_T hyp).trans le_sup_right) (sup_le ?_ hTV) (isPGroup_fsuV hyp)
    exact ((perfectCore_le _).trans inf_le_left).trans hLV
  have hW : E3.wClos (fsuV T I) 1 (ROf T L V₁) ≤ Subgroup.centralizer (V₃ : Set G) := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAR, g, hAg, hAj⟩ := hA
    by_cases hAC : A ≤ Subgroup.centralizer (fsuV T I : Set G)
    · exact hAC.trans (Subgroup.centralizer_le (IsVi.le_fsuV hV₃))
    have hAN : A ≤ Subgroup.normalizer (fsuV T I : Set G) := (hAR.trans hRT).trans hTV
    have hmem := autI_mem_aSet_of_le hV hAg hAN hAC (by rw [hAj, hs]; omega)
    rw [hAj, hs] at hmem
    exact hG12 G L (fsuV T I) ⊤ T V₁ V₃ n hV hn hLV hVL hnat hG2 le_top
      (inf_le_right.trans (normalizer_fsuV_le h331 hyp)) hTS hTV hyp.normal
      (IsVi.cV_le hV₁) (h12.trans h23) (IsVi.le_fsuV hV₃) (IsVi.isEndStable hV₁)
      (IsVi.isEndStable hV₃) (by rw [IsVi.relIndex_eq hV₁, mul_one]) (IsVi.relIndex_eq hV₃)
      (IsVi.le_normalizer hV₁) (IsVi.le_normalizer hV₃) A hAR hmem
  have hV3C : V₃ ≤ E3.cClos (fsuV T I) 1 (ROf T L V₁) := by
    refine le_inf ((IsVi.le_fsuV hV₃).trans hVR) fun v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hW hw) v hv).symm
  exact (Subgroup.centralizer_le hV3C).trans ((centralizer_le_sectionCentralizer
    (h12.trans h23)).trans (h1114 G T L I n V₁ V₃ hyp hV₁ hV₃).1)

end CFSG.Quasithin.Vol2.Ch11.SecB

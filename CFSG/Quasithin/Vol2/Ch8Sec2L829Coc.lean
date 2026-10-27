module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829R3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829F3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829Red
public import CFSG.Quasithin.Vol2.Ch8Sec2D2Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L829Coc

variable {G : Type} [Group G] [Finite G]

@[expose] def Stmt8_2_2P7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → H ⊓ fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G)

@[expose] def Cocode829Sweep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → Row711M24Cocode T L I →
          oTwoUpper H ≤ ch82I (fsuV T I) h ⊔ kerIn (H ⊓ fsuM T L) H ∨
            ∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ Subgroup.centralizer (ch82I (fsuV T I) h : Set G) ∧
              Subgroup.normalizer (X : Set G) ≤ fsuM T L

theorem H_eq_ch82I_sup_T_829 (hmod : StmtFSUModule) {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    {H : Subgroup G} {h : G} {k : ℕ} (hH : IsHStar T (fsuM T L) H) (hC : Concl822 T L I H h k) :
    H = ch82I (fsuV T I) h ⊔ T := by
  obtain ⟨hV, -⟩ := hmod G T L I hyp.fsu
  obtain ⟨-, hhI, hIC, -, -, -, hMIeq, hker, -, hcases, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    id hC
  have hnt := nontrivial_star_82 hcases
  have hIN := not_le_normalizer_ch82I_82 hV hhI hker hnt
  exact eq_ch82I_sup_82 hyp.fsu.sylow hH hIC.1 hMIeq hIN

theorem oTwoUpper_le_centralizer_U_829 {T H V : Subgroup G} {h : G} (hT2 : IsPGroup 2 T)
    (hHIT : H = ch82I V h ⊔ T)
    (hIU : ch82I V h ≤ Subgroup.centralizer (ch82U V h : Set G))
    (hTU : T ≤ Subgroup.normalizer (ch82U V h : Set G)) :
    oTwoUpper H ≤ Subgroup.centralizer (ch82U V h : Set G) := by
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxH, hxo⟩
  have hx : x ∈ Subgroup.centralizer (ch82U V h : Set G) ⊔ T := by
    rw [hHIT] at hxH
    exact sup_le_sup_right hIU T hxH
  exact mem_of_mem_sup_of_pow_eq_one (B6.le_normalizer_centralizer hTU) hT2 hx hxo
    (pow_orderOf_eq_one x)

theorem H_le_normalizer_LU_829 {T H V L : Subgroup G} {h : G}
    (hHIT : H = ch82I V h ⊔ T)
    (hIU : ch82I V h ≤ Subgroup.centralizer (ch82U V h : Set G))
    (hTU : T ≤ Subgroup.normalizer (ch82U V h : Set G))
    (hNL : Subgroup.normalizer (ch82U V h : Set G) ≤
      Subgroup.normalizer (ch82LU L (ch82U V h) : Set G)) :
    H ≤ Subgroup.normalizer (ch82LU L (ch82U V h) : Set G) := by
  have hIN : ch82I V h ≤ Subgroup.normalizer (ch82U V h : Set G) :=
    hIU.trans (Subgroup.centralizer_le_normalizer _)
  rw [hHIT]
  exact sup_le (hIN.trans hNL) (hTU.trans hNL)

theorem commutator_oTwoUpper_LU_829 {H U L : Subgroup G}
    (hY : oTwoUpper H ≤ Subgroup.centralizer (U : Set G))
    (h828 : ⁅ch82LU L U, Subgroup.centralizer (U : Set G)⁆ ≤ pCoreOf 2 (ch82LU L U)) :
    ⁅oTwoUpper H, ch82LU L U⁆ ≤ pCoreOf 2 (ch82LU L U) := by
  calc ⁅oTwoUpper H, ch82LU L U⁆ ≤ ⁅Subgroup.centralizer (U : Set G), ch82LU L U⁆ :=
        Subgroup.commutator_mono hY le_rfl
    _ = ⁅ch82LU L U, Subgroup.centralizer (U : Set G)⁆ := Subgroup.commutator_comm _ _
    _ ≤ pCoreOf 2 (ch82LU L U) := h828

theorem pRank_three_le_one_cocode_829 (hLU : HLU82) (hcard : Mathieu.StmtH13Card) (h827 : Step827)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hmod : StmtFSUModule)
    (h711n : Stmt7_1_1_normal) {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    (h821 : Hyp8_2_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I)
    (hcoc : Row711M24Cocode T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hH : IsHStar T (fsuM T L) H) (hh : h ∈ H) (hC : Concl822 T L I H h k)
    (hC5 : Concl825 T L I h k) (hC8 : Concl828 T L I h) :
    H = ch82I (fsuV T I) h ⊔ T ∧ CFSG.Open.pRank 3 H ≤ 1 :=
  pRank_three_le_one_82 hmod hyp hH hC hC5 hC8
    (exists_f_cocode_829 hLU hcard h827 h37 h38 h39 hmod h711n hyp h731 h821 hrow hcoc hH hh hC hC5)

theorem not_le_fsuM_ch82I_829 {M V : Subgroup G} {h : G} (hV : IsElemAbelian 2 V)
    (hhI : h ∈ ch82I V h)
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hnt : Nontrivial (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)))
    (hMI : M ⊓ ch82I V h = ch82I V h ⊓ Subgroup.normalizer (V : Set G)) :
    ¬ ch82I V h ≤ M := by
  intro hIM
  have hIN : ch82I V h ≤ Subgroup.normalizer (V : Set G) := by
    have h1 : ch82I V h ≤ M ⊓ ch82I V h := le_inf hIM le_rfl
    rw [hMI] at h1
    exact h1.trans inf_le_right
  have hVh : B6.conjSub h V = V := B6.conjSub_eq_self (hIN hhI)
  have hIV : ch82I V h = V := by
    unfold ch82I
    rw [hVh, sup_idem]
  have hP : IsPGroup 2 (ch82I V h) := by
    rw [hIV]
    exact B2F.isPGroup_of_isElemAbelian hV
  have hpc : pCoreOf 2 (ch82I V h) = ch82I V h :=
    CFSG.QuasithinUnique.pCoreOf_eq_of_isPGroup hP
  change Nontrivial (↥(ch82I V h) ⧸ (kerIn (M ⊓ ch82I V h) (ch82I V h)).subgroupOf (ch82I V h))
    at hnt
  rw [hker, hpc, Subgroup.subgroupOf_self] at hnt
  exact (not_nontrivial_iff_subsingleton.mpr QuotientGroup.subsingleton_quotient_top) hnt

theorem not_le_of_centralizes_829 {M : Subgroup G} {I : Subgroup G} {X : Subgroup G}
    (hI : ¬ I ≤ M) (hXI : X ≤ Subgroup.centralizer (I : Set G))
    (hNX : Subgroup.normalizer (X : Set G) ≤ M) : False := by
  have hIX : I ≤ Subgroup.centralizer (X : Set G) := Subgroup.le_centralizer_iff.mp hXI
  exact hI ((hIX.trans (Subgroup.centralizer_le_normalizer _)).trans hNX)

theorem step829Cocode_of (hmod : StmtFSUModule) (hP7 : Stmt8_2_2P7) (hsweep : Cocode829Sweep) :
    Step829Cocode := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hcoc
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hT : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  obtain ⟨-, hhI, hIC, -, -, -, hMIeq, hker, -, hcases, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    id hC
  have hnt := nontrivial_star_82 hcases
  rcases hsweep G T L I hyp h731 h821 hc hrow H h k hH hh hC hcoc with hY | ⟨X, -, hXI, hNX⟩
  · exact T_normalizes_pCore_ch82I_829 hT hVT hTV hh hhI
      (hP7 G T L I hyp h731 h821 hc hrow H h k hH hh hC) hY
  · exact (not_le_of_centralizes_829
      (not_le_fsuM_ch82I_829 hV hhI hker hnt hMIeq) hXI hNX).elim

end L829Coc

end CFSG.Quasithin.H13

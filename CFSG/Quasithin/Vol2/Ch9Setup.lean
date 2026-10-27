module

public import CFSG.Quasithin.Vol2.Ch7E61
public import CFSG.Quasithin.Vol2.Ch10Reselect.Hyp702A

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin.E3 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

structure Setup (T L I : Subgroup G) (n : ℕ) : Prop where
  hyp : Hyp7_0_2A G T L I
  comm : IsMulCommutative ↥(fsuV T I)
  row : Row711OmegaPlus T L I n
  hV : IsElemAbelian 2 (fsuV T I)
  hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)
  hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L
  hVM : fsuV T I = fsuVM T L I
  hMN : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G)
  hVLT : fsuV T I ≤ fsuL0 T L ⊔ T
  hRed : IsPrimeReduced 2 ((fsuV T I).subgroupOf (fsuL0 T L ⊔ T))
  hQ : pCoreOf 2 (fsuL0 T L ⊔ T) = T ⊓ Subgroup.centralizer (fsuV T I : Set G)
  hJ : thompsonJ T ≤ Subgroup.centralizer (fsuV T I : Set G)
  uniq : IsUniqueM (L ⊔ T) (fsuM T L)

theorem Setup.of_fsuV_eq_fsuVM (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2A G T L I) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711OmegaPlus T L I n) (hVM : fsuV T I = fsuVM T L I) : Setup T L I n := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hMN : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hVM]
    exact le_normalizer_conjClosure _ _
  obtain ⟨hVLT, hRed, hQ⟩ := h3228 G T L I hyp.fsu
  exact ⟨hyp, inferInstance, hrow, hV, hN, hNM, hVM, hMN, hVLT, hRed, hQ,
    thompsonJ_le_centralizer_fsuVA h37 h38 h39 hyp hV hN,
    lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39 hyp.fsu.sylow
      hyp.fsu.maximal⟩

theorem Setup.of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h326 : Stmt3_2_6LtA) (hyp : Hyp7_0_2A G T L I)
    [IsMulCommutative ↥(fsuV T I)] (hrow : Row711OmegaPlus T L I n) : Setup T L I n := by
  refine Setup.of_fsuV_eq_fsuVM h37 h38 h39 h3228 hyp hrow ?_
  rcases h326 G T L I hyp.fsu hrow.1 with ⟨_, -, hVVM, -⟩ | h3
  · exact hVVM
  · exact (hyp.notThree ⟨hrow.1, h3⟩).elim

theorem Setup.of_hyp702 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h326 : Stmt3_2_6Lt) (hyp : Hyp7_0_2 G T L I)
    [IsMulCommutative ↥(fsuV T I)] (hrow : Row711OmegaPlus T L I n) : Setup T L I n := by
  refine Setup.of_fsuV_eq_fsuVM h37 h38 h39 h3228 hyp.toA hrow ?_
  rcases h326 G T L I hyp.fsu hrow.1 with ⟨_, -, hVVM, -⟩ | h3
  · exact hVVM
  · exact (hyp.notThree ⟨hrow.1, h3⟩).elim

namespace Setup

variable (S : Setup T L I n)
include S

theorem two_le : 2 ≤ n := S.row.2.1

theorem L_lt_L0 : L < fsuL0 T L := S.row.1

theorem L_le_L0 : L ≤ fsuL0 T L := S.L_lt_L0.le

theorem exists_not_mem_normalizer : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
  by_contra h
  push Not at h
  apply S.L_lt_L0.ne'
  refine le_antisymm (conjClosure_le fun t ht l hl => ?_) S.L_le_L0
  exact (Subgroup.mem_normalizer_iff.mp (h t ht) l).mp hl

omit [Finite G] S in
theorem L0_le_fsuM : fsuL0 T L ≤ fsuM T L := Subgroup.le_normalizer

omit [Finite G] S in
theorem T_le_normalizer_L0 : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) :=
  le_normalizer_conjClosure L T

omit [Finite G] S in
theorem T_le_fsuM : T ≤ fsuM T L := T_le_normalizer_L0

theorem L_le_fsuM : L ≤ fsuM T L := S.L_le_L0.trans L0_le_fsuM

omit [Finite G] S in
theorem L0T_le_fsuM : fsuL0 T L ⊔ T ≤ fsuM T L := sup_le L0_le_fsuM T_le_fsuM

theorem L0_sup_T : fsuL0 T L ⊔ T = L ⊔ T :=
  le_antisymm (sup_le (conjClosure_le fun _t ht _l hl =>
      (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hl))
        (Subgroup.mem_sup_right (T.inv_mem ht))) le_sup_right)
    (sup_le_sup_right S.L_le_L0 T)

theorem normalizer_V_eq : Subgroup.normalizer (fsuV T I : Set G) = fsuM T L :=
  le_antisymm S.hNM S.hMN

theorem fsuV_le_T : fsuV T I ≤ T := CFSG.Quasithin.H13.fsuV_le_T S.hyp.fsu S.hV S.hN

theorem fsuV_ne_bot : fsuV T I ≠ ⊥ := CFSG.Quasithin.H13.fsuV_ne_bot S.hyp.fsu

theorem isPGroup_fsuV : IsPGroup 2 (fsuV T I) := isPGroup_of_isElemAbelian_two S.hV

theorem centralizer_le_fsuM : Subgroup.centralizer (fsuV T I : Set G) ≤ fsuM T L :=
  (Subgroup.centralizer_le_normalizer _).trans S.hNM

theorem L0_le_normalizer_V : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  le_sup_left.trans S.hN

theorem T_le_normalizer_V : T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  le_sup_right.trans S.hN

theorem fsuV_le_Q : fsuV T I ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
  le_inf S.fsuV_le_T fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw =>
    congrArg Subtype.val (S.comm.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)

theorem isPGroup_Q : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  rw [← S.hQ]
  exact pCoreOf_isPGroup 2 _

theorem L0T_le_normalizer_Q : fsuL0 T L ⊔ T ≤ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G) := by
  rw [← S.hQ]
  exact le_normalizer_pCoreOf 2 _

theorem normalizer_le_of_le {C : Subgroup G} (hC2 : IsPGroup 2 C) (hC1 : C ≠ ⊥)
    (hLT : L ⊔ T ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ fsuM T L := by
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer (C : Set G))
    ⟨C, hC1, hC2, rfl⟩
  have hEq : M' = fsuM T L := S.uniq.2 M' ⟨hM', hLT.trans hle⟩
  exact hEq ▸ hle

end Setup

end CFSG.Quasithin.H13.Ch9

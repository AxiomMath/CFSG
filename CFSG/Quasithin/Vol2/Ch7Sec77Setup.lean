module

public import CFSG.Quasithin.Background.HSL3S77Bridge
public import CFSG.Quasithin.Vol2.Ch7E61
public import CFSG.Quasithin.Vol2.Ch7Lem761End

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

structure Setup (T L I : Subgroup G) : Prop where
  hyp : Hyp7_0_2 G T L I
  h731 : Hyp7_3_1 T L I
  comm : IsMulCommutative ↥(fsuV T I)
  row : Row711SL3Pair T L I 1
  hV : IsElemAbelian 2 (fsuV T I)
  hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)
  hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L
  hL : L = fsuL0 T L
  hMN : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G)
  hVLT : fsuV T I ≤ fsuL0 T L ⊔ T
  hRed : IsPrimeReduced 2 ((fsuV T I).subgroupOf (fsuL0 T L ⊔ T))
  hQ : pCoreOf 2 (fsuL0 T L ⊔ T) = T ⊓ Subgroup.centralizer (fsuV T I : Set G)
  hJ : thompsonJ T ≤ Subgroup.centralizer (fsuV T I : Set G)
  uniq : IsUniqueM (L ⊔ T) (fsuM T L)

theorem Setup.of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h711n : Stmt7_1_1_normal) (h325 : Stmt3_2_5)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711SL3Pair T L I 1) : Setup T L I := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  obtain ⟨hL, hMN⟩ := fsuM_le_normalizer_of_pair h711n h325 hyp hrow
  obtain ⟨hVLT, hRed, hQ⟩ := h3228 G T L I hyp.fsu
  exact ⟨hyp, h731, inferInstance, hrow, hV, hN, hNM, hL, hMN, hVLT, hRed, hQ,
    thompsonJ_le_centralizer_fsuV h37 h38 h39 hyp hV hN,
    lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39 hyp.fsu.sylow
      hyp.fsu.maximal⟩

namespace Setup

variable (S : Setup T L I)
include S

theorem fsuL0_eq : fsuL0 T L = L := S.hL.symm

theorem fsuM_eq : fsuM T L = Subgroup.normalizer (L : Set G) := by
  change Subgroup.normalizer (fsuL0 T L : Set G) = _
  rw [S.fsuL0_eq]

theorem T_le_fsuM : T ≤ fsuM T L := (le_sup_right : T ≤ L ⊔ T).trans S.uniq.1.2

theorem L_le_fsuM : L ≤ fsuM T L := (le_sup_left : L ≤ L ⊔ T).trans S.uniq.1.2

theorem fsuM_le_normalizer_L : fsuM T L ≤ Subgroup.normalizer (L : Set G) := S.fsuM_eq.le

theorem T_le_normalizer_L : T ≤ Subgroup.normalizer (L : Set G) :=
  S.T_le_fsuM.trans S.fsuM_le_normalizer_L

theorem fsuV_le_T : fsuV T I ≤ T := CFSG.Quasithin.H13.fsuV_le_T S.hyp.fsu S.hV S.hN

theorem fsuV_ne_bot : fsuV T I ≠ ⊥ := CFSG.Quasithin.H13.fsuV_ne_bot S.hyp.fsu

theorem isPGroup_fsuV : IsPGroup 2 (fsuV T I) := isPGroup_of_isElemAbelian_two S.hV

theorem centralizer_le_fsuM :
    Subgroup.centralizer (fsuV T I : Set G) ≤ fsuM T L :=
  (Subgroup.centralizer_le_normalizer _).trans S.hNM

theorem L_le_normalizer_V : L ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  S.L_le_fsuM.trans S.hMN

theorem T_le_normalizer_V : T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  le_sup_right.trans S.hN

theorem exists_twist : ∃ t ∈ T, I ⊔ CFSG.conjugate I t = fsuV T I ∧
    I ⊓ CFSG.conjugate I t = ⊥ ∧ ¬ IsXSectionIso L ⊥ I (CFSG.conjugate I t) := S.row.1

theorem commutator_I : ⁅I, L⁆ = I := by
  have h := S.hyp.fsu.irrPlus.2.2.2.1
  have hL' : conjClosure L T = L := S.hL.symm
  rwa [hL'] at h

theorem L_le_normalizer_I : L ≤ Subgroup.normalizer (I : Set G) := by
  have h := S.hyp.fsu.irrPlus.2.2.1
  have hL' : conjClosure L T = L := S.hL.symm
  rwa [hL'] at h

theorem eq_commutator : fsuV T I = ⁅fsuV T I, L⁆ := by
  obtain ⟨t, htT, hsup, -, -⟩ := S.exists_twist
  refine le_antisymm ?_ ?_
  · rw [← hsup]
    refine sup_le ?_ ?_
    · calc I = ⁅I, L⁆ := S.commutator_I.symm
        _ ≤ ⁅I ⊔ CFSG.conjugate I t, L⁆ := Subgroup.commutator_mono le_sup_left le_rfl
    · have hconj : CFSG.conjugate ⁅I, L⁆ t = ⁅CFSG.conjugate I t, CFSG.conjugate L t⁆ := by
        unfold CFSG.conjugate
        exact Subgroup.map_commutator _ _ _
      have hLt : CFSG.conjugate L t = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 (inv_mem (S.T_le_normalizer_L htT))
      rw [S.commutator_I, hLt] at hconj
      calc CFSG.conjugate I t = ⁅CFSG.conjugate I t, L⁆ := hconj
        _ ≤ ⁅I ⊔ CFSG.conjugate I t, L⁆ := Subgroup.commutator_mono le_sup_right le_rfl
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    have hlv : l * v⁻¹ * l⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (S.L_le_normalizer_V hl) _).mp ((fsuV T I).inv_mem hv)
    have : v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) := by group
    rw [commutatorElement_def, this]
    exact (fsuV T I).mul_mem hv hlv

theorem autI_top_le : autI S.hV ⊤ ≤
    Subgroup.normalizer (autI S.hV (fsuL0 T L) : Set (MulAut (IntMod (fsuV T I) S.hV))) :=
  autI_top_le_normalizer S.hV S.hNM

theorem exists_model : ∃ e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2),
    (autI S.hV (fsuL0 T L)).map (congrHom e) = pairSL (ZMod 2) ∧
      (autI S.hV ⊤).map (congrHom e) ≤ pairNorm (ZMod 2) := by
  obtain ⟨htw, hnat⟩ := S.row
  obtain ⟨t, -, φ, hφN, hinf, hsup, hniso, -⟩ := exists_twist_eq S.hV S.hN S.hNM htw
  have hL3 : BinaryNaturalSL (V := IntMod (fsuV T I) S.hV) (autI S.hV (fsuL0 T L))
      (intSub S.hV I) ⊥ 3 1 := hnat
  obtain ⟨e, he, hNe⟩ := S77.exists_model hL3 hφN hinf hsup hniso
  exact ⟨e, he, (Subgroup.map_mono S.autI_top_le).trans hNe.le⟩

end Setup

end CFSG.Quasithin.H13.Sec77

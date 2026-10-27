module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseAIface
public import CFSG.Quasithin.H13.GoldschmidtM22EndN5g
public import CFSG.Quasithin.H13.GoldschmidtM22EndN5b

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {g : G} {D : Subgroup G}

theorem caseA_m22 (hKu : StmtKuM22) (hIII : M22CaseAThree) (hl : M22LemmasG)
    (h : Hyp6Sec2 G T M L V) (hk : EndN4Concl T L V g D)
    (hA : Subgroup.centralizer (V : Set G) ≤ V) : Nonempty (G ≃* NativeSporadic.M22) := by
  have hZ : Nat.card (quasithinOmegaOneCenter T) = 2 := (hl.h622 G T M L V h).2.1
  obtain ⟨e⟩ := (hl.h622 G T M L V h).1
  obtain ⟨P⟩ := endN2 hl.g64 hl.h621 hl.h622 hl.h626 hl.h629 hl.h6210 hl.h6211 hl.h6212 h
    hk.hZS
  obtain ⟨z, hzZ, hz1, hZz⟩ := exists_gen_Z hZ
  have hCV : Subgroup.centralizer (V : Set G) = V := centralizer_eq_of_le h hA
  have hpc : pCoreOf 2 (Subgroup.normalizer (V : Set G)) = V := hk.pCoreOf_normalizer.trans hCV
  have hT : Nat.card ↥T = 128 := card_T_of_caseA h hA hk.normalizer_eq e
  have hkD := hk.kData
  obtain ⟨φ₃, hφ₃s, hφ₃k⟩ := hkD.exists_hom_S3_Z2 h P hZ hl.h629 hl.h6210 hl.h6212 hT
  obtain ⟨X, hXsyl, hXC⟩ :=
    hkD.exists_sylow_three h P hZ hl.h621 hl.h629 hl.h6210 hl.h6211 hl.h6212 hT
  obtain ⟨φ₅, hφ₅s, hφ₅k⟩ := exists_hom_perm5 hk.normalizer_eq e
  obtain ⟨d, hd1, hd2, hd3, hd4⟩ := hIII G T M L V g D z hl h hk hA hZz
  refine hKu G T (Subgroup.normalizer (V : Set G)) (HH T) D z h.simple h.sylow
    h.toHyp611.T_le_normalizer (T_le_HH T) ?_ ?_ ?_ ?_ ?_ ?_ hkD.D_le_HH hkD.H_le_normalizer_D
    hkD.extra ⟨φ₃, hφ₃s, hφ₃k⟩ ?_ (hkD.center_eq.trans hZz) ⟨X, hXsyl, hXC.trans hZz⟩
    (HH_eq_centralizer_of_gen hZz) ⟨d, hd1, hd2, hd3, hd4⟩
  · rw [hpc]
    exact h.toHyp611.isElemAbelian
  · rw [hpc]
    exact KData.card_V h
  · rw [hpc]
  · rw [hpc, inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _), hCV]
  · exact ⟨φ₅, hφ₅s, by rw [hφ₅k, hk.pCoreOf_normalizer]⟩
  · rw [hk.oTwoUpper_normalizer, hpc]
    exact h.natural
  · intro x hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxCHU : x ∈ CHU T L V := hk.centralizer_inf_HH_le ⟨hxC, hxH⟩
    have hxV : x ∈ V := hA (hk.E_le_centralizer ⟨hxC, hxCHU⟩)
    exact hkD.V0_le_D ⟨hxV, hxCHU⟩

theorem stmt6_2_13_of (hKu : StmtKuM22) (hB1 : M22CaseBOne) (hB2 : M22CaseBTwo)
    (hA3 : M22CaseAThree) (hl : M22LemmasG) : Stmt6_2_13 := by
  intro G _ _ T M L V h hZS
  obtain ⟨g, D, hk⟩ := endN4_concl hl h hZS
  exact caseA_m22 hKu hA3 hl h hk (centralizer_le_of_caseB hB1 hB2 hl h hk)

end CFSG.Quasithin.H13.GM22

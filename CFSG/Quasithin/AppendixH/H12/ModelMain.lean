module

public import CFSG.Quasithin.AppendixH.H12.ModelN
public import CFSG.Quasithin.AppendixH.H12.ModelV2
public import CFSG.Quasithin.AppendixH.H12.ModelT0
public import CFSG.Quasithin.AppendixH.H12.Overgroups
public import CFSG.Quasithin.Background.HM22Recog

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (IsMaximalIn IsExtHatOf ptStab)

abbrev N0 : Subgroup Γ12 := ptStab glHom G0 (ptSub 5)

theorem center_map_G0 :
    (Subgroup.center ↥G0).map G0.subtype = Subgroup.zpowers zU :=
  center_G0 (hZ := (M22Link.isHat_G).2.1)

theorem T0_le_M0 : T0 ≤ M0 := T0_le_ptStab_Wsub

theorem T0_le_N0 : T0 ≤ N0 := by
  intro x hx
  have hxvec : x ∈ vecStab 5 := T0_le_vecStab_five hx
  have hxG : x ∈ G0 := vecStab_le_G0 5 hxvec
  have hfix : gmv x 5 = 5 := ((mem_vecStab_iff (by norm_num) x).mp hxvec).2
  exact (mem_ptStab_iff G0 (ptSub 5) x).mpr
    ⟨hxG, by rw [smulSub_ptSub hxG (by norm_num), hfix]⟩

theorem zpowers_zU_le_M0 : Subgroup.zpowers zU ≤ M0 :=
  Subgroup.zpowers_le.mpr zU_mem_M0

theorem zpowers_zU_le_N0 : Subgroup.zpowers zU ≤ N0 :=
  (isIntDirect_ptStab (c := 5) (by norm_num) (by norm_num)).2.1

theorem M0_N0_maximal :
    IsMaximalIn M0 G0 ∧ IsMaximalIn N0 G0 ∧ M0 ≠ N0 ∧
      ∀ X : Subgroup Γ12, IsMaximalIn X G0 → T0 ≤ X → X = M0 ∨ X = N0 := by
  obtain ⟨M, N, -, -, hTM, hTN, -, -, -, -, hMmax, hNmax, hMN, hall, hMuniq, hNuniq⟩ :=
    overgroups_of_isHat (L := G0) (T := T0) M22Link.isHat_G isSylowIn_T0
  have hZ : (Subgroup.center ↥G0).map G0.subtype = Subgroup.zpowers zU := center_map_G0
  have hM0eq : M0 = M :=
    hMuniq M0 M0_le_G0 T0_le_M0 (by rw [hZ]; exact zpowers_zU_le_M0) card_M0
  have hN0eq : N0 = N :=
    hNuniq N0 inf_le_left T0_le_N0 (by rw [hZ]; exact zpowers_zU_le_N0) card_ptStab_five
  rw [hM0eq, hN0eq]
  exact ⟨hMmax, hNmax, hMN, hall⟩

theorem clause4_G0 :
    Clause4 G0 T0 M0 N0 := by
  obtain ⟨hcard, hcore, hext⟩ := structure_M0
  exact ⟨M0_N0_maximal.1, M0_N0_maximal.2.1, T0_le_M0, T0_le_N0, M0_N0_maximal.2.2.1,
    M0_N0_maximal.2.2.2, ⟨hcore ▸ Q0_isElemAbelian, hcore ▸ hcard, hext⟩,
    clause4_N_part center_map_G0⟩

theorem clause5_G0 :
    Clause5 glHom G0 T0 N0 ι0 f0 (ptSub 5) :=
  ⟨clause5_core.1, clause5_core.2.1, clause5_core.2.2, rfl⟩

theorem clause6_G0 : Clause6 glHom G0 M0 f0 := clause6_M0

theorem clause78_G0 :
    Clause78 glHom G0 M0 ι0 f0 (ptSub 5) (ptSub 1465) :=
  clause78_M0 center_map_G0

theorem model_clauses :
    FormClause glHom G0 ι0 f0 ∧ Clause4 G0 T0 M0 N0 ∧ Clause5 glHom G0 T0 N0 ι0 f0 (ptSub 5) ∧
      Clause6 glHom G0 M0 f0 ∧ Clause78 glHom G0 M0 ι0 f0 (ptSub 5) (ptSub 1465) :=
  ⟨formClause_G0, clause4_G0, clause5_G0, clause6_G0, clause78_G0⟩

end CFSG.Quasithin.AppendixH.H12.Model

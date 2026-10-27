module

public import CFSG.Quasithin.Recognition.St84.AppTreeE5

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ

variable {H : Type} [Group H] [Finite H]

theorem f112_EOdd_inf_ofA_range_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range =
      ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA := by
  haveI hN : (f112saK' L1 L2 S).Normal := f112saK'_normal_of_hyp111R hF hR
  haveI hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal :=
    f112sa_P1'_normal hF
  haveI hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal :=
    f112sa_P2'_normal hF
  refine le_antisymm ?_ ?_
  · rintro u ⟨huE, huA⟩
    obtain ⟨p, hp⟩ := huA
    have hchi : f112saChiR hF hR u = 1 := MonoidHom.mem_ker.mp
      (f112EOdd_le_ker_chi_of_f112Hyp_of_hyp111R hF hR huE)
    have hchi1 : f112saChi1R hF hR p = 1 := by
      rw [← f112saChiR_ofA hF hR p, hp]
      exact hchi
    have hp1 : (p : H) ∈ f112saP1' L1 L2 S :=
      (f112saChi1R_eq_one_iff hF hR p).mp hchi1
    exact Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hp1, hp⟩
  · rintro u ⟨a, ha, rfl⟩
    exact ⟨f112sa_P1'_map_le_EOdd (Subgroup.mem_map_of_mem _ ha), ⟨a, rfl⟩⟩

theorem f112_EOdd_inf_ofB_range_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range =
      ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB := by
  haveI hN : (f112saK' L1 L2 S).Normal := f112saK'_normal_of_hyp111R hF hR
  haveI hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal :=
    f112sa_P1'_normal hF
  haveI hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal :=
    f112sa_P2'_normal hF
  refine le_antisymm ?_ ?_
  · rintro u ⟨huE, huB⟩
    obtain ⟨p, hp⟩ := huB
    have hchi : f112saChiR hF hR u = 1 := MonoidHom.mem_ker.mp
      (f112EOdd_le_ker_chi_of_f112Hyp_of_hyp111R hF hR huE)
    have hchi2 : f112saChi2R hF hR p = 1 := by
      rw [← f112saChiR_ofB hF hR p, hp]
      exact hchi
    have hp1 : (p : H) ∈ f112saP2' L1 L2 S :=
      (f112saChi2R_eq_one_iff hF hR p).mp hchi2
    exact Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hp1, hp⟩
  · rintro u ⟨a, ha, rfl⟩
    exact ⟨f112sa_P2'_map_le_EOdd (Subgroup.mem_map_of_mem _ ha), ⟨a, rfl⟩⟩

theorem f112_EOdd_inf_ofA_range_inf_ofB_range_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ⊓ (f112Gold L1 L2 S).ofB.range =
      ((f112saK L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA := by
  let X := f112Gold L1 L2 S
  have hKP1' : f112saK L1 L2 S ≤ f112saP1' L1 L2 S :=
    sup_le ((show f112saX1 L1 L2 S ≤ oTwoRes L1 from inf_le_left).trans le_sup_left)
      (show f112saX2 L1 L2 S ≤ f112saP1' L1 L2 S from le_sup_right)
  rw [f112_EOdd_inf_ofA_range_of_hyp111R hF hR]
  refine le_antisymm ?_ ?_
  · rintro u ⟨huM, huB⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp huM
    have haP1' : (a : H) ∈ f112saP1' L1 L2 S := Subgroup.mem_subgroupOf.mp ha
    have huBase : X.ofA a ∈ (Monoid.PushoutI.base X.diagram).range := by
      rw [← X.ofA_range_inf_ofB_range]
      exact ⟨⟨a, rfl⟩, huB⟩
    obtain ⟨c, hc⟩ := huBase
    have htoA : X.toA c = a := X.ofA_injective (by rw [X.ofA_toA, hc])
    have haB : (a : H) ∈ bigB L1 L2 S := by
      rw [← htoA]
      exact (f112_inf_eq_bigB_of_hyp111R hR) ▸ c.2
    have haK : (a : H) ∈ f112saK L1 L2 S := by
      have h : (a : H) ∈ f112saP1' L1 L2 S ⊓ bigB L1 L2 S := ⟨haP1', haB⟩
      rwa [f112sa_P1'_inf_bigB hF] at h
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_subgroupOf.mpr haK, rfl⟩
  · refine le_inf ?_ ?_
    · exact Subgroup.map_mono (Subgroup.subgroupOf_mono (f112P1 L1 L2 S) hKP1')
    · rintro u ⟨a, ha, rfl⟩
      have haB : (a : H) ∈ bigB L1 L2 S :=
        f112sa_K_le_bigB L1 L2 S (Subgroup.mem_subgroupOf.mp ha)
      have haP2 : (a : H) ∈ f112P2 L1 L2 S :=
        ((f112_inf_eq_bigB_of_hyp111R hR) ▸ haB).2
      have heq : X.ofA a = X.ofB ⟨(a : H), haP2⟩ :=
        f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨a.2, haP2⟩
      rw [heq]
      exact ⟨⟨(a : H), haP2⟩, rfl⟩

end CFSG.Quasithin.F112R.St84

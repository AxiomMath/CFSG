module

public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylow

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Main


theorem nt_le_of_sylow {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) (hCN : CtNormalizesStatement) (S : Subgroup G)
    (hQS : Q ≤ S) (hSC : S ≤ E1Ct hH.ctx t) (hSD : S ≤ E1Dpre M Q B t)
    (hS2 : QuotSat S Q (fun W _ => IsPGroup 2 W)) (hodd : ¬ 2 ∣ S.relIndex (E1Dpre M Q B t)) :
    Nt M (LB M Q B) t ≤ S := by
  set N : Subgroup G := Nt M (LB M Q B) t with hNdef
  set C : Subgroup G := E1Ct hH.ctx t with hCdef
  set D : Subgroup G := E1Dpre M Q B t with hDdef
  set H : Subgroup G := C ⊓ D with hHdef
  have hHC : H ≤ C := inf_le_left
  have hHD : H ≤ D := inf_le_right
  have hSH : S ≤ H := le_inf hSC hSD
  have hRC : Rt M (LB M Q B) t ≤ C := fun r hr =>
    Subgroup.mem_inf.mpr ⟨hH.ctx.Rt_le_CommQ t hr, hH.ctx.Rt_le_H0 t hr⟩
  have hNC : N ≤ C := (orthE1_Nt_le_Rt M (LB M Q B) t).trans hRC
  have hND : N ≤ D := by
    rw [hDdef]
    unfold E1Dpre
    refine le_iSup₂_of_le (1 : G) (Lgen M (LB M Q B)).one_mem ?_
    intro x hx
    exact mem_conjSubgroup.mpr (by simpa using hx)
  have hNH : N ≤ H := le_inf hNC hND
  have hCmem : ∀ c ∈ C, c ∈ M ∧ ⁅c, t⁆ ∈ Q := fun c hc' =>
    mem_CommQ.mp (Subgroup.mem_inf.mp hc').1
  have hNorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    obtain ⟨hM, hcomm⟩ := hCmem h (hHC hh)
    have heq : conjSubgroup h N = N := (hCN G M Q Z B t hH h hM hcomm).2.1
    have hmem : h * n * h⁻¹ ∈ conjSubgroup h N := by
      rw [mem_conjSubgroup]
      have e : h⁻¹ * (h * n * h⁻¹) * h = n := by group
      rw [e]
      exact hn
    rw [heq] at hmem
    exact hmem
  haveI hNn : (N.subgroupOf H).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hNorm (g : G) g.2 (a : G) ha⟩
  have hNpg : IsPGroup 2 (N.subgroupOf H) :=
    (caseASylow_Nt_isPGroup M (LB M Q B) t).comap_subtype
  have hSpg : IsPGroup 2 S := by
    obtain ⟨hn, hq⟩ := hS2
    haveI := hn
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hq
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp (isPGroup_Q' hH.ctx.hyp)
    refine IsPGroup.of_card (n := a + b) ?_
    rw [← orthE1_card_quot_mul hQS, ha, hb, pow_add]
  have hSpg' : IsPGroup 2 (S.subgroupOf H) := hSpg.comap_subtype
  have hdvd : S.relIndex H ∣ S.relIndex D :=
    ⟨H.relIndex D, (Subgroup.relIndex_mul_relIndex S H D hSH hHD).symm⟩
  have hidx : ¬ 2 ∣ (S.subgroupOf H).index := fun h => hodd (Nat.dvd_trans h hdvd)
  haveI := hNn
  have hle : N.subgroupOf H ≤ (hSpg'.toSylow hidx : Subgroup H) :=
    IsPGroup.le_sylow_of_normal hNpg (hSpg'.toSylow hidx)
  intro x hx
  have hxH : x ∈ H := hNH hx
  have hy : (⟨x, hxH⟩ : H) ∈ N.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
  have hz : (⟨x, hxH⟩ : H) ∈ S.subgroupOf H := hle hy
  exact Subgroup.mem_subgroupOf.mp hz

end Main

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end

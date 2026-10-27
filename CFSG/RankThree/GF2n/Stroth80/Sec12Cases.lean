module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.Q_le_H0 (hc : Ctx M Q Z B) : Q ≤ H0 M Z := fun x hx =>
  ⟨hc.hyp.Q_normal.1 hx, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    hc.hyp.toHyp79.V_central hz hx⟩

theorem Ctx.Q_le_CN (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) : Q ≤ hc.CN t := fun x hx =>
  Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hx, fun v hv => hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩

theorem Rt_le_Lgen (M L : Subgroup G) (t : G) : Rt M L t ≤ Lgen M L := by
  unfold Rt Lgen
  exact iSup₂_mono fun m hm => iSup_le fun _ => le_rfl

theorem Lgen_le_of_normalized {N T : Subgroup G} (hNT : N ≤ T)
    (hT : M ≤ Subgroup.normalizer (T : Set G)) : Lgen M N ≤ T := by
  unfold Lgen
  refine iSup₂_le fun m hm => ?_
  have h1 : conjSubgroup m N ≤ conjSubgroup m T := Subgroup.map_mono hNT
  rwa [conjSubgroup_eq_self_iff.mpr (hT hm)] at h1

theorem quotSat_isProdOf {P₁ P₂ : ∀ (X : Type) [Group X], Prop}
    {A B S : Subgroup G} (hQA : Q ≤ A) (hQB : Q ≤ B) (hAB : A ⊓ B = Q) (hS : A ⊔ B = S)
    (hc : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ Q) (hSn : (Q.subgroupOf S).Normal)
    (hA : QuotSat A Q P₁) (hB : QuotSat B Q P₂) : QuotSat S Q (IsProdOf P₁ P₂) := by
  obtain ⟨hnA, hPA⟩ := hA
  obtain ⟨hnB, hPB⟩ := hB
  haveI := hSn
  haveI := hnA
  haveI := hnB
  obtain ⟨e⟩ := quotProd Q A B S hQA hQB hAB hS hc
  exact ⟨hSn, _, _, _, _, hPA, hPB, ⟨e⟩⟩

end CFSG.RankThree.GF2n.Stroth80

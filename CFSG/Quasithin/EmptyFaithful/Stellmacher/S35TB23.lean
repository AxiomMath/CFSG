module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35TB23A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Mbl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2aP10
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Hom
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.TB23

open S35.II

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem eq_stab_of_edge_groups (hS : Sit H M S) {γ la lb : Geo H M} (hγ : vtype γ = false)
    (hla : la ∈ nbrs γ) (hlb : lb ∈ nbrs γ) (hsb : ¬ S34.SameBlock γ la lb) {U : Subgroup G}
    (hQ : Qv γ ≤ U) (hUs : U ≤ stab γ) (ha : stab γ ⊓ stab la ≤ U)
    (hb : stab γ ⊓ stab lb ≤ U) : U = stab γ := by
  obtain ⟨c⟩ := S35.Ch2.exists_chart2 hS hγ
  have hpt : c.pt la ≠ c.pt lb := fun h => hsb ((c.sameBlock_iff hS hγ hla hlb).mpr h)
  have htop := S35.F2a.sup_eq_top_of_fixPt_ne (c.card_Dl hS hla) (c.card_Dl hS hlb) hpt
  have hle : c.Dl la ⊔ c.Dl lb ≤ c.bar U := sup_le (c.bar_mono ha) (c.bar_mono hb)
  rw [htop, top_le_iff] at hle
  have h := c.preθ_bar hS hγ hUs hQ
  rw [hle] at h
  refine le_antisymm hUs fun x hx => ?_
  rw [← h]
  exact (c.mem_preθ_iff ⟨x, hx⟩).mpr trivial

theorem thmBcase23 (hS : Sit H M S) (hII : CaseII H M) (hTF : ThatFacts H M)
    (hNT : NbarThat H M) : ThmBcase23 H M := by
  intro h6b γ la lb β α' hγ hla hlb hβ hβγ hα' hα'γ hsb hcase r hr hrZ hrC hTb hTa
  have vla : vtype la = true := Std.vtype_nbr_S5 hγ hla
  have vlb : vtype lb = true := Std.vtype_nbr_S5 hγ hlb
  have vβ : vtype β = false := Std.vtype_nbr_S3 vla hβ
  have vα' : vtype α' = false := Std.vtype_nbr_S3 vlb hα'
  have hla' : la ∈ nbrs β := Std.mem_nbrs_symm.mp hβ
  have hlb' : lb ∈ nbrs α' := Std.mem_nbrs_symm.mp hα'
  have hγla : γ ∈ nbrs la := Std.mem_nbrs_symm.mp hla
  have hγlb : γ ∈ nbrs lb := Std.mem_nbrs_symm.mp hlb
  have hdβ : dist β γ = 2 := Std.dist_eq_two_iff.mpr ⟨la, hla, hβ, hβγ⟩
  have hrW : r ∈ Wb γ := Std.Vn_le_Wb hdβ hr.1
  have hVn : stab γ ≤ Subgroup.normalizer (Vn γ : Set G) := Std.Vn_normal γ
  let N : Subgroup G := Nst (stab γ) (Vn γ) hVn r
  have hNs : N ≤ stab γ := Nst_le
  have hZb : Zv α' ≤ Vn γ := (Std.Zv_le_Zv_of_nbr hS vα' hlb').trans (Std.Zv_le_Vn hlb)
  have hZa : Zv β ≤ Vn γ := (Std.Zv_le_Zv_of_nbr hS vβ hla').trans (Std.Zv_le_Vn hla)
  have hPb : Qv lb ⊓ That2 α' lb ≤ N := fun q hq =>
    mem_Nst.mpr ⟨Std.Qv_le_stab hS hγlb hq.1, hZb (hTb q hq)⟩
  have hPa : Qv la ⊓ That2 β la ≤ N := fun q hq =>
    mem_Nst.mpr ⟨Std.Qv_le_stab hS hγla hq.1, hZa (hTa q hq)⟩
  have hQb : Qv α' ⊓ Qv lb ≤ N := fun q hq =>
    hPb ⟨hq.2, ((hTF α' lb vα' hlb').1) hq.1⟩
  have hQa : Qv β ⊓ Qv la ≤ N := fun q hq =>
    hPa ⟨hq.2, ((hTF β la vβ hla').1) hq.1⟩
  have hQγ : Qv γ ≤ stab γ := pCoreOf_le 2 _
  have hQn : stab γ ≤ Subgroup.normalizer (Qv γ : Set G) := le_normalizer_pCoreOf 2 _
  have hsup : N ⊔ Qv γ = stab γ := by
    apply le_antisymm (sup_le hNs hQγ)
    rcases hcase with hF | h1
    · have hDa := hF β la γ vβ hla' hla hβγ.symm
      have hDb := hF α' lb γ vα' hlb' hlb hα'γ.symm
      exact (eq_stab_of_edge_groups hS hγ hla hlb hsb (U := N ⊔ Qv γ) le_sup_right
        (sup_le hNs hQγ) (hDa.trans (sup_le_sup_right hQa _))
        (hDb.trans (sup_le_sup_right hQb _))).ge
    · have h1' : stab γ ≤ That2 γ la ⊔ That2 γ lb := Subgroup.relIndex_eq_one.mp h1
      refine h1'.trans (sup_le ?_ ?_)
      · exact (hNT β la γ vβ hla' hla hβγ.symm).trans (sup_le_sup_right hQa _)
      · exact (hNT α' lb γ vα' hlb' hlb hα'γ.symm).trans (sup_le_sup_right hQb _)
  have hidx : N.relIndex (stab γ) ≤ 4 := by
    have hA : (Qv γ ⊓ Qv lb).relIndex (Qv γ) = 2 := Std.relIndex_Qv hS hγ hlb
    have hAD : Qv γ ⊓ Qv lb ≤ stab α' ⊓ stab lb :=
      le_inf (inf_le_right.trans (Std.Qv_le_stab hS hα')) (inf_le_right.trans (pCoreOf_le 2 _))
    have hT : (That2 α' lb).relIndex (stab α' ⊓ stab lb) = 2 := (hTF α' lb vα' hlb').2.2
    have hPle : (Qv γ ⊓ Qv lb) ⊓ That2 α' lb ≤ N ⊓ Qv γ := fun q hq =>
      ⟨hPb ⟨hq.1.2, hq.2⟩, hq.1.1⟩
    have hQn' : N ≤ Subgroup.normalizer (Qv γ : Set G) := hNs.trans hQn
    have h1 := relIndex_le_of_sup hQn' hsup hPle
    have h2 : ((Qv γ ⊓ Qv lb) ⊓ That2 α' lb).relIndex (Qv γ) ≤ 4 := by
      rw [← Subgroup.relIndex_mul_relIndex _ (Qv γ ⊓ Qv lb) _ inf_le_left inf_le_left, hA,
        Subgroup.inf_relIndex_left]
      have := Subgroup.relIndex_le_of_le_right (H := That2 α' lb) hAD
        (by rw [hT]; norm_num)
      omega
    exact h1.trans h2
  obtain ⟨hq⟩ := quot_stab_five hS.glob.amalg hγ
  have hL : oTwoRes (stab γ) ≤ N := S35.B5.oTwoRes_le_of_relIndex_le_four ⟨hq⟩ hNs hidx
  exact false_of_Lr hS hII h6b hγ hlb hlb' hα'γ hr.2 hrW hrZ
    (fun v hv => by
      have := hrC v hv
      rwa [commutatorElement_def] at this)
    (fun l hl => (hL hl).2)

end S35.TB23

end F53.Stellmacher

end CFSG.Quasithin

module

public import CFSG.Quasithin.EmptyFaithful.SzF53B2Core
public import CFSG.Quasithin.EmptyFaithful.SzF53A1
public import CFSG.Quasithin.EmptyFaithful.SBc13B2Core
public import CFSG.Quasithin.Recognition.F112WLocal2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace SzF53B2

section Amalg

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace B2Setup

theorem card_le_sixteen (h : B2Setup H M S) {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (hEQ : E ≤ pCoreOf 2 H) (hEH : H ≤ Subgroup.normalizer (E : Set G)) :
    Nat.card E ≤ 16 := by
  have hyp := h.amalgamHypV
  have hS3 := h.isNaturalS3
  have hSM : S ≤ M := hyp.sylow₁.1
  have hSH : S ≤ H := hyp.sylow₂.1
  have hQaS : pCoreOf 2 M ≤ S := isSylowTwoOf_pCoreOf_le hyp.sylow₁
  have hQbS : pCoreOf 2 H ≤ S := isSylowTwoOf_pCoreOf_le hyp.sylow₂
  have hMN : M ≤ Subgroup.normalizer (VZ S M : Set G) := hyp.normalizes
  have hZ : H ≤ Subgroup.normalizer
      ((VZ S M ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
    rw [h.inf_centralizer_S]; exact h.zb_normal
  have h102 : ⁅conjClosure (VZ S M) H, pCoreOf 2 H⁆ = quasithinOmegaOneCenter S := by
    rw [F112W.commutator_conjClosure_pCoreOf hyp hS3 h.crit hZ, h.inf_centralizer_S]
  obtain ⟨x, hxM, hxS⟩ : ∃ x ∈ M, x ∉ S := by
    by_contra hcon
    push Not at hcon
    have : S.relIndex M = 1 := Subgroup.relIndex_eq_one.mpr hcon
    have h3 := h.relIndex_facts.2.2
    omega
  set V : Subgroup G := VZ S M with hVdef
  set Zb : Subgroup G := quasithinOmegaOneCenter S with hZbdef
  set Qa : Subgroup G := pCoreOf 2 M with hQadef
  set Qb : Subgroup G := pCoreOf 2 H with hQbdef
  set Vb : Subgroup G := conjClosure V H with hVbdef
  set Ql : Subgroup G := conjSub x Qb with hQldef
  set Vl : Subgroup G := conjSub x Vb with hVldef
  set Y : Subgroup G := E ⊓ Qa ⊓ Ql with hYdef
  have hxV : conjSub x V = V := F7.conjSub_eq_of_mem_normalizer (hMN hxM)
  have hxQa : conjSub x Qa = Qa :=
    F7.conjSub_eq_of_mem_normalizer (hxM |> (le_normalizer_pCoreOf 2 M))
  have hZbV : Zb ≤ V := le_conjClosure _ _
  have hVE : ¬ V ≤ E := by
    intro hVE
    have hVbE : Vb ≤ E := conjClosure_le fun k hk z hz =>
      (Subgroup.mem_normalizer_iff.mp (hEH hk) z).mp (hVE hz)
    obtain ⟨-, -, -, x', -, hx'Vb, -, -, -, hcomm, -, hcard, -⟩ :=
      F112W.critDist_two_structure hyp hS3 h.crit
    have hV'E : conjSub x' V ≤ E := hx'Vb.trans hVbE
    have hbot : ⁅V, conjSub x' V⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono hVE hV'E).trans (F7.commutator_self_eq_bot hE).le)
    rw [hbot] at hcomm
    rw [← hcomm, Subgroup.card_bot] at hcard
    omega
  have hEV : E ⊓ V ≤ Zb := by
    refine h.le_zb_of_normalizes_S inf_le_right ?_ ?_
    · exact le_normalizer_inf (hSH.trans hEH) (hSM.trans hMN)
    · intro heq
      exact hVE fun v hv => (show v ∈ E ⊓ V from heq.symm ▸ hv).1
  have hQaH : Qa ≤ H := hQaS.trans hSH
  have hQaCH : Qa ≤ conjSub x H := by
    rw [← hxQa]
    exact conjSub_mono x hQaH
  have hQaQl : Qa ≤ Subgroup.normalizer (Ql : Set G) := by
    have h2 : Ql = pCoreOf 2 (conjSub x H) := by rw [pCoreOf_conjSub]
    rw [h2]
    exact hQaCH.trans (le_normalizer_pCoreOf 2 _)
  have hYn : Qa ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_inf (le_normalizer_inf (hQaH.trans hEH) Subgroup.le_normalizer) hQaQl
  have hYE : Y ≤ E := inf_le_left.trans inf_le_left
  have hYQa : Y ≤ Qa := inf_le_left.trans inf_le_right
  have hYQb : Y ≤ Qb := hYE.trans hEQ
  have hYQl : Y ≤ Ql := inf_le_right
  have hb : ⁅Vb, Y⁆ ≤ V := by
    refine (Subgroup.commutator_mono le_rfl hYQb).trans ?_
    rw [h102]
    exact hZbV
  have hl : ⁅Vl, Y⁆ ≤ V := by
    have h1 : ⁅Vl, Y⁆ ≤ ⁅Vl, Ql⁆ := Subgroup.commutator_mono le_rfl hYQl
    have h2 : ⁅Vl, Ql⁆ = conjSub x Zb := by
      rw [hVldef, hQldef, conjSub_commutator, h102]
    rw [h2] at h1
    exact h1.trans ((conjSub_mono x hZbV).trans hxV.le)
  have hYab : IsElemAbelian 2 Y := F7.isElemAbelian_mono hE hYE
  have hor := h.le_or_ge_V hxM hxS hYab hYQa hYn hb hl
  have hYV : Y ≤ V := by
    rcases hor with hVY | hYV
    · exact absurd (hVY.trans hYE) hVE
    · exact hYV
  have hYZb : Y ≤ Zb := fun y hy => hEV ⟨hYE hy, hYV hy⟩
  have hYcard : Nat.card Y ≤ 2 := (Subgroup.card_le_of_le hYZb).trans (by rw [h.card_Zb])
  have hES : E ≤ S := hEQ.trans hQbS
  have hr1 : Qa.relIndex E ≤ 2 := by
    have h2 : Qa.relIndex S = 2 := h.relIndex_facts.2.1
    have := Subgroup.relIndex_le_of_le_right (H := Qa) hES (by rw [h2]; norm_num)
    omega
  have hr2 : Ql.relIndex (Qa ⊓ E) ≤ 4 := by
    have hq := SBc13.nonempty_oTwoQuot_equiv_conjSub x h.amalgam.quot_left
    have := relIndex_pCoreOf_le_four_five (X := conjSub x H) (A := Qa ⊓ E) hq
      (inf_le_left.trans hQaCH) (fun a ha => by
        rw [F7.isElemAbelian_pow_eq_one hE ha.2]
        exact Subgroup.one_mem _)
    rw [Subgroup.inf_relIndex_right] at this
    rwa [hQldef, hQbdef, ← pCoreOf_conjSub]
  have hc1 := Subgroup.relIndex_mul_card Qa E
  have hc2 := Subgroup.relIndex_mul_card Ql (Qa ⊓ E)
  have hY' : Ql ⊓ (Qa ⊓ E) = Y := by
    rw [hYdef, inf_comm Qa E, inf_comm]
  rw [hY'] at hc2
  calc Nat.card E = Qa.relIndex E * (Ql.relIndex (Qa ⊓ E) * Nat.card Y) := by
        rw [hc2, hc1]
    _ ≤ 2 * (4 * 2) := Nat.mul_le_mul hr1 (Nat.mul_le_mul hr2 hYcard)

theorem not_F53EData (h : B2Setup H M S) {E : Subgroup G} (hE : F53EData H S E) : False := by
  have hSH : S ≤ H := h.sylow_H.1
  have hEQ : E ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hE.le.trans hSH) hE.normal
      (F7.isPGroup_of_isElemAbelian hE.abelian)
  have h16 := h.card_le_sixteen hE.abelian hEQ hE.normal
  have h256 := F53EData.card_ge h.amalgam.quot_left hSH hE
  omega

end B2Setup

end Amalg

end SzF53B2

end CFSG.Quasithin

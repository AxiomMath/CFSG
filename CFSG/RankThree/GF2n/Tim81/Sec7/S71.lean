module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Main
import CFSG.RankThree.GF2n.Tim81.Sec7.PBar
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Basic
import CFSG.RankThree.GF2n.Tim81.Sec7.S71TIProof
import CFSG.RankThree.GF2n.Tim81.Sec7.S77Basic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

private theorem pbarRep_mk' (hS : Sec6Hyp M V) [Module (ZMod 2) (SecMod hS.pbarHyp)]
    (z : ↥M) :
    hS.pbarRep (QuotientGroup.mk' (pCore 2 ↥M) z) = SecMod.secConj hS.pbarHyp z := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := SecMod.mk_surjective hS.pbarHyp v
  rw [Sec6Hyp.pbarRep_mk hS z x, secConj_mk]

private theorem exists_pbarRep_ne (hS : Sec6Hyp M V) [Module (ZMod 2) (SecMod hS.pbarHyp)] :
    ∃ x ∈ imgQ M (m0Of M V), ∃ w : SecMod hS.pbarHyp, hS.pbarRep x w ≠ w := by
  by_contra h
  push Not at h
  obtain ⟨U, hU⟩ := hS.ne
  have hspan : Submodule.span (ZMod 2)
      {u | ∃ a ∈ imgQ M U, ∃ w : SecMod hS.pbarHyp,
        u = hS.pbarRep a w - w} = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro u ⟨a, ha, w, rfl⟩
    rw [h a (imgQ_mono (le_m0Of_of_mem_sigmaSet hU) ha) w]
    exact sub_self _
  rw [Sec6Hyp.span_pbarRep_imgQ hS hU] at hspan
  have hle : ⁅Pc M V, U⁆ ≤ V := by
    intro w hw
    have hwP : w ∈ Pc M V := hS.sec5.commutator_le_Pc hU hw
    have hmem : SecMod.mk hS.pbarHyp ⟨w, hwP⟩ ∈ subSec hS.pbarHyp ⁅Pc M V, U⁆ :=
      (mk_mem_subSec_iff hS.pbarHyp (hS.sec5.V_le_commutator hU)).2 hw
    rw [hspan, Submodule.mem_bot] at hmem
    exact (SecMod.mk_eq_zero_iff hS.pbarHyp ⟨w, hwP⟩).1 hmem
  have hcard : Nat.card V ^ 3 ≤ Nat.card V := by
    rw [← hS.sec5.card_commutator_Pc hU]
    exact Subgroup.card_le_of_le hle
  have hq : 2 ≤ Nat.card V :=
    le_trans (by norm_num) hS.sec5.toRootHyp.four_le_card
  have h31 : 3 ≤ 1 :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card V)).mp (by simpa using hcard)
  omega

theorem Sec7Hyp.stmt71 (hS : Sec7Hyp M V n f) (hT : UnitaryTIModule) : Sec7.Stmt71 M V := by
  intro N hVN hNP hNm0
  haveI : Module (ZMod 2) (SecMod hS.pbarHyp) := hS.pbarModule
  have hnt : ∃ x ∈ imgQ M (m0Of M V), ∃ w : SecMod hS.pbarHyp, hS.pbarRep x w ≠ w :=
    exists_pbarRep_ne hS.toSec6Hyp
  have hTI : ∀ A ∈ (imgQ M '' sigmaSet M V), ∀ B ∈ (imgQ M '' sigmaSet M V),
      Submodule.span (ZMod 2)
          {u | ∃ a ∈ A, ∃ w : SecMod hS.pbarHyp, u = hS.pbarRep a w - w} =
        Submodule.span (ZMod 2)
          {u | ∃ b ∈ B, ∃ w : SecMod hS.pbarHyp, u = hS.pbarRep b w - w} ∨
      Submodule.span (ZMod 2)
          {u | ∃ a ∈ A, ∃ w : SecMod hS.pbarHyp, u = hS.pbarRep a w - w} ⊓
        Submodule.span (ZMod 2)
          {u | ∃ b ∈ B, ∃ w : SecMod hS.pbarHyp, u = hS.pbarRep b w - w} = ⊥ := by
    rintro A ⟨A', hA', rfl⟩ B ⟨B', hB', rfl⟩
    rw [hS.span_pbarRep_imgQ hA', hS.span_pbarRep_imgQ hB']
    rcases hS.toSec6Hyp.stmt71TI A' hA' B' hB' with hEq | hInf
    · exact Or.inl (congrArg (subSec hS.pbarHyp) hEq)
    · exact Or.inr (by
        rw [← subSec_inf hS.pbarHyp (hS.sec5.V_le_commutator hB'), hInf,
          subSec_eq_bot_of_le hS.pbarHyp le_rfl])
  have hirr := hT (MBar M) (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f n
    hS.one_le hS.four_le hS.two_le hS.m0 (SecMod hS.pbarHyp) hS.pbarRep hnt hTI
  have hinv : ∀ x ∈ imgQ M (m0Of M V),
      (subSec hS.pbarHyp N).map (hS.pbarRep x) ≤ subSec hS.pbarHyp N := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_imgQ_iff.mp hx
    rw [pbarRep_mk']
    exact map_secConj_subSec_le hS.pbarHyp z (hNm0 hz)
  rcases hirr hS.card_pbar (subSec hS.pbarHyp N) hinv with hbot | htop
  · left
    refine (subSec_inj hS.pbarHyp hNP hVN hS.pbarHyp.le le_rfl).1 ?_
    rw [hbot, subSec_eq_bot_of_le hS.pbarHyp le_rfl]
  · right
    refine (subSec_inj hS.pbarHyp hNP hVN le_rfl hS.pbarHyp.le).1 ?_
    rw [htop, subSec_self hS.pbarHyp]

theorem sec71Statement_of_unitaryTIModule (hT : UnitaryTIModule) : Sec71Statement := by
  intro G' _ _ M' V' n' f' hS
  exact Sec7Hyp.stmt71 hS hT

end CFSG.RankThree.GF2n.Tim81

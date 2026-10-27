module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
public import CFSG.Timmesfeld.Transvection.Subgroup
import CFSG.RankThree.GF2n.Tim81.Recog.GR
import CFSG.RankThree.GF2n.Tim81.Sec7.Transport
import CFSG.RankThree.GF2n.Tim81.Sec7.Images
public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

theorem Sec7Hyp.stmt76 (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V) : Sec7.Stmt76 V := by
  intro A hA B hB hne
  have hΓA : gammaAt A = gammaAt V := h75 A hA
  have hBΓ : B ∈ gammaAt A := by
    rw [hΓA]
    exact hB
  obtain ⟨C, hC, hBC⟩ := hBΓ
  have hAω : A ∈ omegaSet V := gammaAt_subset_omegaSet V hA
  have hCω : C ∈ omegaSet V := sigmaAt_subset_omegaSet hAω hC
  have hAC : A ∈ sigmaAt C := hS.sec5.mem_sigmaAt_symm hAω hC
  exact hS.toSec6Hyp.commute_or_isL2Gen_at hCω hAC hBC

theorem Sec6Hyp.mem_sigmaSet_of_mem_gammaAt (hS : Sec6Hyp M V) {B : Subgroup G}
    (hB : B ∈ gammaAt V) (hne : B ≠ V) (hc : ⁅V, B⁆ = ⊥) : B ∈ sigmaSet M V := by
  obtain ⟨C, hC, hBC⟩ := hB
  have hCsig : C ∈ sigmaSet M V := by
    rwa [hS.sec5.toRootHyp.toHyp.sigmaAt_eq] at hC
  have hCω : C ∈ omegaSet V := sigmaSet_subset_omegaSet M V hCsig
  have hV : V ∈ sigmaAt C := hS.sec5.self_mem_sigmaAt hCsig
  have h := hS.mem_sigmaAt_of_commute_at hCω hV hBC hc (Ne.symm hne)
  rwa [hS.sec5.toRootHyp.toHyp.sigmaAt_eq] at h

theorem Hyp.conj_mem_gammaAt (h : Hyp M V) {m : G} (hm : m ∈ M) {B : Subgroup G}
    (hB : B ∈ gammaAt V) : conjSubgroup m B ∈ gammaAt V := by
  have hVω : V ∈ omegaSet V := ⟨1, Subgroup.mem_top 1, (conjSubgroup_one V).symm⟩
  have hVm : conjSubgroup m V = V :=
    mem_normalizer_iff_conjSubgroup_eq.mp (h.le_normalizer hm)
  have hB' : conjSubgroup m⁻¹ (conjSubgroup m B) ∈ gammaAt V := by
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hmem : conjSubgroup m B ∈ gammaAt (conjSubgroup m V) :=
    (Hyp.mem_gammaAt_conj_iff h hVω m).mpr hB'
  rwa [hVm] at hmem

theorem Hyp.exists_conj_gammaAt (h : Hyp M V) (h75 : Sec7.Stmt75 V) {A : Subgroup G}
    (hA : A ∈ gammaAt V) :
    ∃ g : G, A = conjSubgroup g V ∧ ∀ B ∈ gammaAt V, conjSubgroup g B ∈ gammaAt V := by
  obtain ⟨g, -, hAg⟩ := gammaAt_subset_omegaSet V hA
  refine ⟨g, hAg, ?_⟩
  intro B hB
  have hΓ : gammaAt A = gammaAt V := h75 A hA
  have hVω : V ∈ omegaSet V := ⟨1, Subgroup.mem_top 1, (conjSubgroup_one V).symm⟩
  have hB' : conjSubgroup g⁻¹ (conjSubgroup g B) ∈ gammaAt V := by
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hBg : conjSubgroup g B ∈ gammaAt (conjSubgroup g V) :=
    (Hyp.mem_gammaAt_conj_iff h hVω g).mpr hB'
  have hBgA : conjSubgroup g B ∈ gammaAt A := by
    rw [hAg]
    exact hBg
  rwa [hΓ] at hBgA

theorem Sec6Hyp.card_commuting_gammaAt (hS : Sec6Hyp M V) :
    Nat.card {B : Subgroup G // B ∈ gammaAt V ∧ B ≠ V ∧ ⁅V, B⁆ = ⊥} =
      Nat.card V ^ 2 * Nat.card (imgQ M '' sigmaSet M V) := by
  have hiff : ∀ B : Subgroup G,
      (B ∈ gammaAt V ∧ B ≠ V ∧ ⁅V, B⁆ = ⊥) ↔ B ∈ sigmaSet M V := by
    intro B
    constructor
    · rintro ⟨hB, hne, hc⟩
      exact hS.mem_sigmaSet_of_mem_gammaAt hB hne hc
    · intro hB
      refine ⟨hS.sigmaSet_subset_gammaAt hB,
        ne_of_mem_sigmaSet hS.sec5.toRootHyp hB, ?_⟩
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hS.sec5.le_M_of_mem_sigmaSet hB).2
  rw [Nat.card_congr (Equiv.subtypeEquivRight (p := fun B : Subgroup G =>
    B ∈ gammaAt V ∧ B ≠ V ∧ ⁅V, B⁆ = ⊥) (q := fun B : Subgroup G =>
    B ∈ sigmaSet M V) hiff)]
  exact hS.card_sigmaSet

theorem Sec7Hyp.stmt76U (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V) (h76 : Sec7.Stmt76 V)
    (hT : Timmesfeld.Transvection.SubgroupTransvectionStatement) (hPC : UnitaryPerpCount) :
    Sec7.Stmt76U V n f := by
  intro _
  have hR := hS.toSec6Hyp
  obtain ⟨f', hf', hcardV, m, hm, Φ, hker, hrange, hmem⟩ :=
    Sec6Hyp.recog hR hR.stmt60 hT (gammaAt_subset_omegaSet V) hR.mem_gammaAt_self
      hR.sigmaSet_subset_gammaAt h76
      (fun B hB hne hc => hR.mem_sigmaSet_of_mem_gammaAt hB hne hc)
      (fun m hm B hB => hR.sec5.toRootHyp.toHyp.conj_mem_gammaAt hm hB)
      (fun A hA => hR.sec5.toRootHyp.toHyp.exists_conj_gammaAt h75 hA)
  have hff : f' = f :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) (hcardV.symm.trans hS.card_V)
  cases hff
  have hn2 : 2 ≤ n := Nat.le_trans (by norm_num) hS.four_le
  have hSUΓ : IsSUImage (⨆ A ∈ gammaAt V, A) (gammaAt V) f m (by omega) (by omega) :=
    ⟨Φ, hker.le, hrange, hmem⟩
  have hSU0 : IsSUImage (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f n
      (by omega) hn2 :=
    hS.m0
  have hcard : Nat.card {B : Subgroup G // B ∈ gammaAt V ∧ B ≠ V ∧ ⁅V, B⁆ = ⊥} =
      (2 ^ f) ^ 2 * Nat.card (imgQ M '' sigmaSet M V) := by
    rw [hR.card_commuting_gammaAt, ← hS.card_V]
  have hm_eq : m = n + 2 :=
    hPC G (MBar M) (⨆ A ∈ gammaAt V, A) (imgQ M (m0Of M V)) (gammaAt V)
      (imgQ M '' sigmaSet M V) f m n hS.one_le hm hn2 hSUΓ hSU0 V
      hR.mem_gammaAt_self hcard
  cases hm_eq
  exact ⟨Φ, hker, hrange, hmem⟩

end CFSG.RankThree.GF2n.Tim81

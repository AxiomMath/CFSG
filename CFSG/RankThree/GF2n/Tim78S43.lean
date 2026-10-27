module

public import CFSG.RankThree.GF2n.Tim78S4Root
public import CFSG.RankThree.GF2n.Tim78S42
import CFSG.RankThree.GF2n.Tim78Critical

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Certified


theorem mem_M_of_normalizes {E : Subgroup G} (hEB : E ≤ B) (hE : E ≠ ⊥) {c : G}
    (hc : ∀ e ∈ E, c * e * c⁻¹ ∈ E) : c ∈ M := by
  obtain ⟨⟨e, heE⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
  have hmem : c * e * c⁻¹ ∈ B ⊓ conjSubgroup c B := by
    refine Subgroup.mem_inf.mpr ⟨hEB (hc e heE), ?_⟩
    rw [mem_conjSubgroup, show c⁻¹ * (c * e * c⁻¹) * c = e by group]
    exact hEB heE
  have hne : B ⊓ conjSubgroup c B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hmem
    apply he1
    refine Subtype.ext ?_
    show e = 1
    calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
      _ = 1 := by rw [hmem]; group
  exact H.conj_eq_iff.mp (conjSubgroup_eq_of_isTI H.ti hne)

theorem exists_hyperplane_ge {E : Subgroup G} (hEB : E ≤ B) (hne : E ≠ B) :
    ∃ Hh : Subgroup G, E ≤ Hh ∧ Hh ≤ B ∧ Nat.card Hh * 2 = Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp H.isPGroup_B
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp (H.isPGroup_B.to_le hEB)
  have hlt : Nat.card E < Nat.card B :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hEB hne)
  have hjm : j < m := by
    rw [hj, hm] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  obtain ⟨K, hK, hEK, hKB⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := G) Nat.prime_two
    (n := m - 1) (H := E) (L := B) (by rw [hj]; exact pow_dvd_pow 2 (by omega))
    (by rw [hm]; exact pow_dvd_pow 2 (Nat.sub_le m 1)) hEB
  refine ⟨K, hEK, hKB, ?_⟩
  rw [hK, hm, ← pow_succ]
  congr 1
  omega

theorem comm_B_of_commutator_mem {c : G} (h : ∀ y ∈ P, ⁅c, y⁆ ∈ B) :
    ∀ b ∈ B, c * b = b * c := by
  have hB : CFSG.GroupTheory.HuppertProduct.mho P 2 = B :=
    H.mho_eq_B_of_ne H.B_le_P H.P_le_Q H.M_le_normalizer_P H.B_lt_P.ne
  have hle : B ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [← hB]
    refine CFSG.GroupTheory.HuppertProduct.mho_le_of_forall fun y hy => ?_
    have hyQ : y ∈ Q := H.P_le_Q hy
    have hzB : ⁅c, y⁆ ∈ B := h y hy
    set z := ⁅c, y⁆ with hz
    have h1 : c * y * c⁻¹ = z * y := by rw [hz, commutatorElement_def]; group
    have h2 : z * y = y * z := H.center_Q hzB hyQ
    have h3 : z * z = 1 := by rw [← sq]; exact H.sq_eq_one z hzB
    have h4 : c * (y * y) * c⁻¹ = y * y := by
      calc c * (y * y) * c⁻¹ = (c * y * c⁻¹) * (c * y * c⁻¹) := by group
        _ = (z * y) * (z * y) := by rw [h1]
        _ = z * (y * z) * y := by group
        _ = z * (z * y) * y := by rw [← h2]
        _ = (z * z) * (y * y) := by group
        _ = y * y := by rw [h3, one_mul]
    rw [Subgroup.mem_centralizer_singleton_iff, sq]
    calc y * y * c = (c * (y * y) * c⁻¹) * c := by rw [h4]
      _ = c * (y * y) := by group
  intro b hb
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hb)).symm

end Certified

section Root


theorem tim78_4_3 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∀ x ∈ B, ∀ g : G, g * x * g⁻¹ ∈ T → g * x * g⁻¹ ∈ B := by
  intro x hx g hu
  by_contra hub
  set u := g * x * g⁻¹ with hudef
  have huBg : u ∈ conjSubgroup g B := by
    rw [mem_conjSubgroup, show g⁻¹ * u * g = x by rw [hudef]; group]
    exact hx
  have hu1 : u ≠ 1 := fun h => hub (h ▸ B.one_mem)
  have hBg : conjSubgroup g B ≠ B := fun h => hub (h ▸ huBg)
  have huC : ∀ p ∈ P, p * u = u * p := fun p hp =>
    Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P hu) p hp
  have hPMg : P ≤ conjSubgroup g M := fun p hp =>
    H.centralizer_le_conj huBg hu1 (Subgroup.mem_centralizer_singleton_iff.mpr (huC p hp))
  have hBMg : B ≤ conjSubgroup g M := H.B_le_P.trans hPMg
  have hMgQg : ∀ m ∈ conjSubgroup g M, ∀ z ∈ conjSubgroup g Q, m * z * m⁻¹ ∈ conjSubgroup g Q := by
    intro m hm z hz
    have : m ∈ Subgroup.normalizer (conjSubgroup g Q : Set G) := by
      rw [normalizer_conjSubgroup]
      exact Subgroup.map_mono H.M_le_normalizer_Q hm
    exact (Subgroup.mem_normalizer_iff.mp this z).mp hz
  by_cases hα : B ≤ conjSubgroup g Q
  ·
    have h1 : conjSubgroup g⁻¹ B ≤ Q := by
      intro z hz
      rw [mem_conjSubgroup, inv_inv] at hz
      have := hα hz
      rwa [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this
    have h2 : conjSubgroup g B ≤ Q := by
      have := H.conj_inv_le_Q h1
      rwa [inv_inv] at this
    have h4 : u ∈ P ⊓ T := ⟨H.conj_le_P h2 huBg, hu⟩
    rw [H.P_inf_T] at h4
    exact hub h4
  ·
    set Qg := conjSubgroup g Q with hQg
    set E := B ⊓ Qg with hE
    have hEB : E ≤ B := inf_le_left
    have hEne : E ≠ B := fun h => hα (h ▸ inf_le_right)
    obtain ⟨Hh, hEHh, hHhB, hHh2⟩ := H.exists_hyperplane_ge hEB hEne
    have hPQg : ∀ p ∈ P, ∀ z ∈ Qg, p * z * p⁻¹ ∈ Qg := fun p hp z hz => hMgQg p (hPMg hp) z hz
    have hNle : ∀ y ∈ P, y ∈ Qg → y ∈ B := by
      intro y hyP hyQg
      refine H.center_quotient hHhB hHh2 hyP fun p hp => ?_
      have h2 : ⁅y, p⁆ ∈ Qg := by
        have e : ⁅y, p⁆ = y * (p * y⁻¹ * p⁻¹) := by rw [commutatorElement_def]; group
        rw [e]
        exact Qg.mul_mem hyQg (hPQg p hp y⁻¹ (Qg.inv_mem hyQg))
      have h3 : ⁅y, p⁆ ∈ B := H.commutator_mem (H.P_le_Q hyP) (H.P_le_Q hp)
      exact hEHh ⟨h3, h2⟩
    have hNE : ∀ y ∈ P, y ∈ Qg → y ∈ E := fun y hy hyQg => ⟨hNle y hy hyQg, hyQg⟩
    by_cases hE0 : E = ⊥
    ·
      have hPQgbot : ∀ y ∈ P, y ∈ Qg → y = 1 := fun y hy hyQ => by
        have := hNE y hy hyQ
        rw [hE0, Subgroup.mem_bot] at this
        exact this
      have hsq : ∀ p ∈ P, p ^ 2 ∈ Qg := by
        intro p hp
        by_cases hp2 : p ^ 2 = 1
        · rw [hp2]
          exact Qg.one_mem
        have hyB : p ^ 2 ∈ B := H.sq_mem (H.P_le_Q hp)
        have hconjpow : ∀ n : ℕ, (g⁻¹ * p * g) ^ n = g⁻¹ * p ^ n * g := fun n => by
          have := conj_pow (a := g⁻¹) (b := p) (i := n)
          simpa using this
        have hy₀M : g⁻¹ * p * g ∈ M := by
          have := hPMg hp
          rwa [mem_conjSubgroup] at this
        have hy₀2 : ∃ k : ℕ, (g⁻¹ * p * g) ^ 2 ^ k = 1 := by
          obtain ⟨k, hk⟩ := H.isPGroup_P ⟨p, hp⟩
          refine ⟨k, ?_⟩
          have hk' : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
          rw [hconjpow, hk']
          group
        have hC : Q ⊓ Subgroup.centralizer ({g⁻¹ * p * g} : Set G) =
            Q ⊓ Subgroup.centralizer ({(g⁻¹ * p * g) ^ 2} : Set G) := by
          refine le_antisymm (fun c hc => ?_) (fun c hc => ?_)
          · refine ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
            have h0 : Commute c (g⁻¹ * p * g) := Subgroup.mem_centralizer_singleton_iff.mp hc.2
            exact h0.pow_right 2
          · obtain ⟨hcQ, hcC⟩ := hc
            have hcC' := Subgroup.mem_centralizer_singleton_iff.mp hcC
            rw [hconjpow] at hcC'
            have hc0Q : g * c * g⁻¹ ∈ Qg := by
              rw [mem_conjSubgroup, show g⁻¹ * (g * c * g⁻¹) * g = c by group]
              exact hcQ
            have hc0C : g * c * g⁻¹ * p ^ 2 = p ^ 2 * (g * c * g⁻¹) := by
              calc g * c * g⁻¹ * p ^ 2
                  = g * (c * (g⁻¹ * p ^ 2 * g)) * g⁻¹ := by group
                _ = g * ((g⁻¹ * p ^ 2 * g) * c) * g⁻¹ := by rw [hcC']
                _ = p ^ 2 * (g * c * g⁻¹) := by group
            have hc0M : g * c * g⁻¹ ∈ M :=
              (H.normalizer_eq_and_centralizer_le.2 _ hyB hp2)
                (Subgroup.mem_centralizer_singleton_iff.mpr hc0C)
            have hc0P : ∀ p' ∈ P, g * c * g⁻¹ * p' = p' * (g * c * g⁻¹) := by
              intro p' hp'
              have h1 : ⁅g * c * g⁻¹, p'⁆ ∈ P := by
                have e : ⁅g * c * g⁻¹, p'⁆ = (g * c * g⁻¹ * p' * (g * c * g⁻¹)⁻¹) * p'⁻¹ := by
                  rw [commutatorElement_def]
                rw [e]
                exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp
                  (H.M_le_normalizer_P hc0M) p').mp hp') (P.inv_mem hp')
              have h2 : ⁅g * c * g⁻¹, p'⁆ ∈ Qg := by
                have e : ⁅g * c * g⁻¹, p'⁆ = (g * c * g⁻¹) * (p' * (g * c * g⁻¹)⁻¹ * p'⁻¹) := by
                  rw [commutatorElement_def]; group
                rw [e]
                exact Qg.mul_mem hc0Q (hPQg p' hp' _ (Qg.inv_mem hc0Q))
              have h3 := hPQgbot _ h1 h2
              rwa [commutatorElement_eq_one_iff_mul_comm] at h3
            refine ⟨hcQ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
            have := hc0P p hp
            calc c * (g⁻¹ * p * g) = g⁻¹ * ((g * c * g⁻¹) * p) * g := by group
              _ = g⁻¹ * (p * (g * c * g⁻¹)) * g := by rw [this]
              _ = g⁻¹ * p * g * c := by group
        have h23 := tim78_2_3 H.fitting hy₀M hy₀2 (by rw [← H.hQ]; exact hC)
        rw [← H.hQ, hconjpow] at h23
        rw [hQg, mem_conjSubgroup]
        exact h23
      refine absurd ?_ hα
      rw [← H.mho_eq_B_of_ne H.B_le_P H.P_le_Q H.M_le_normalizer_P H.B_lt_P.ne]
      exact CFSG.GroupTheory.HuppertProduct.mho_le_of_forall hsq
    ·
      refine absurd (H.le_conj_Q_of_normalizer_eq hCen hU hBMg hEB inf_le_right hE0 ?_) hα
      intro c hcQg hcN b hb
      have hcM : c ∈ M := H.mem_M_of_normalizes hEB hE0 hcN
      refine H.comm_B_of_commutator_mem (c := c) (fun y hy => ?_) b hb
      have h1 : ⁅c, y⁆ ∈ P := by
        have e : ⁅c, y⁆ = (c * y * c⁻¹) * y⁻¹ := by rw [commutatorElement_def]
        rw [e]
        exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_P hcM) y).mp hy)
          (P.inv_mem hy)
      have h2 : ⁅c, y⁆ ∈ Qg := by
        have e : ⁅c, y⁆ = c * (y * c⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
        rw [e]
        exact Qg.mul_mem hcQg (hPQg y hy c⁻¹ (Qg.inv_mem hcQg))
      exact hNle _ h1 h2

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78

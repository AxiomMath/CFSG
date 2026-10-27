module

public import CFSG.Quasithin.Recognition.Kleidman.F204.Assembly
public import CFSG.Quasithin.Recognition.Kleidman.F204.Entry
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalT2d
public import CFSG.Quasithin.EmptyFaithful.S152ZFDefs

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

@[expose] def CaseIIT1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S D X : Subgroup G), Frame L1 L2 S D X →
    ConfigT1 L1 L2 S → ∀ α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S), IsCritData α β α' →
      Zv α' ≤ Qv α → False

@[expose] def CaseIIT2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S D X : Subgroup G), Frame L1 L2 S D X →
    (∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = true) →
    7 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S) →
    ∀ α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S), IsCritData α β α' → Zv α' ≤ Qv α → False

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem Zv_le_centerOf_of_ZCentral (F : Frame L1 L2 S D X) {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hμ : vtype μ = true) (hZ : ZCentral μ) : Zv μ ≤ centerOf (stab μ) := by
  have hA := Amal.of_frame F
  set N : Subgroup G := stab μ ⊓ Subgroup.centralizer (Zv μ : Set G) with hN
  have hNs : N ≤ stab μ := inf_le_left
  have hNn : ∀ n ∈ N, ∀ g ∈ stab μ, g * n * g⁻¹ ∈ N := by
    intro n hn g hg
    obtain ⟨hns, hnc⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hns)
      (Subgroup.inv_mem _ hg), Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hgz : g⁻¹ * z * g ∈ Zv μ := by
      have := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ (hA.stab_le_normalizer_Zv μ hg)) z).mp hz
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hnc _ hgz
    calc z * (g * n * g⁻¹) = g * ((g⁻¹ * z * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * z * g)) * g⁻¹ := by rw [hc]
      _ = g * n * g⁻¹ * z := by group
  obtain ⟨δ, hδ⟩ := exists_adj μ
  have hδn : δ ∈ nbrs μ := hδ
  obtain ⟨-, hT, -⟩ := sylow_sup_Qv F hμ hδn
  have hTN : Qv μ ⊔ Qv δ ≤ N := fun t ht => by
    refine Subgroup.mem_inf.mpr ⟨hT.1 ht, ?_⟩
    rw [hZ _ hT]
    exact mem_centralizer_omegaOne ht
  have hNQ : ¬ N ≤ Qv μ := by
    intro hle
    have h4 := relIndex_Qv_sup_Qv F hμ hδn
    have hle' : Qv δ ⊔ Qv μ ≤ Qv μ := by
      rw [sup_comm]; exact hTN.trans hle
    rw [Subgroup.relIndex_eq_one.mpr hle'] at h4
    omega
  have hmul := exists_mul_Q_of_normal F hμ hNs hNn hNQ
  intro z hz
  refine Subgroup.mem_inf.mpr ⟨(hA.Zv_le_Qv μ).trans (pCoreOf_le 2 _) hz,
    Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  obtain ⟨n, hn, hq⟩ := hmul g hg
  have h1 : z * n = n * z := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 z hz
  have h2 : (n⁻¹ * g) * z = z * (n⁻¹ * g) :=
    Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ hz).2 _ hq
  calc g * z = n * ((n⁻¹ * g) * z) := by group
    _ = n * (z * (n⁻¹ * g)) := by rw [h2]
    _ = (n * z) * (n⁻¹ * g) := by group
    _ = (z * n) * (n⁻¹ * g) := by rw [h1]
    _ = z * g := by group

theorem caseII_T2_false_of_lt (F : Frame L1 L2 S D X)
    (hT2 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = true)
    (hb7 : bMin (P1 L1 L2 S) (P2 L1 L2 S) < 7) {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α) : False := by
  have hA := Amal.of_frame F
  obtain ⟨-, -, hnα, hodd, -⟩ := hA.caseII (frame_dichotomy F) hc hII
  have hαf : vtype α = false := by
    cases h : vtype α
    · rfl
    · exact absurd ((hT2 α).mpr h) hnα
  have h2b := two_le_bMin F
  obtain ⟨k, hk⟩ := hodd
  exact t2_dist_ne_le_five F (fun μ hμ => Zv_le_centerOf_of_ZCentral F hμ ((hT2 μ).mpr hμ)) hαf
    hc.not_le (by rw [hc.dist_eq, hc.bAt_eq]) (by rw [hc.bAt_eq]; omega)

theorem false_of_frame (h1 : CaseIIT1) (h2 : CaseIIT2) (F : Frame L1 L2 S D X) : False := by
  refine f204_false F (fun hT1 α β α' hc hII => h1 G L1 L2 S D X F hT1 α β α' hc hII)
    (fun hT2 α β α' hc hII => ?_)
  by_cases hb7 : 7 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S)
  · exact h2 G L1 L2 S D X F hT2 hb7 α β α' hc hII
  · exact caseII_T2_false_of_lt F hT2 (by omega) hc hII

theorem input15204F112Untw_of (h1 : CaseIIT1) (h2 : CaseIIT2) : He9.Input15204F112Untw := by
  intro G _ _ L1 L2 S hyp _ _ hL1 hL2 hu
  obtain ⟨D, X, F⟩ := exists_frame_of hyp hL1 hL2 hu
  exact false_of_frame h1 h2 F

end CFSG.Quasithin.Kleidman.F204

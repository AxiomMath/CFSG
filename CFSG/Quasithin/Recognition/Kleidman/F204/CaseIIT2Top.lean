module

public import CFSG.Quasithin.Recognition.Kleidman.F204.AssemblyTop
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT2Seven
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT2Ge3
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalT2c

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem caseII_T2_false_ge3 (F : Frame L1 L2 S D X)
    (hT2 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = true)
    (hb3 : 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S)) {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α) : False := by
  have hA := Amal.of_frame F
  have hZ : ∀ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype μ = true → Zv μ ≤ centerOf (stab μ) :=
    fun μ hμ => Zv_le_centerOf_of_ZCentral F hμ ((hT2 μ).mpr hμ)
  have hZFD : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype δ = false → ZFaithful δ := by
    intro δ hδ
    refine (frame_dichotomy F δ).resolve_left fun hcen => ?_
    have := (hT2 δ).mp hcen
    rw [hδ] at this; exact absurd this (by simp)
  obtain ⟨-, -, hnα, hodd, -⟩ := hA.caseII (frame_dichotomy F) hc hII
  have hαf : vtype α = false := by
    cases h : vtype α
    · rfl
    · exact absurd ((hT2 α).mpr h) hnα
  obtain ⟨c, hcb⟩ := Nat.exists_eq_add_of_le hb3
  have hd : dist α α' = c + 3 := by rw [hc.dist_eq, hcb]; ring
  obtain ⟨p, hp0, hpb, hadj, hpd⟩ := exists_geodesic (c + 3) α α' hd
  have hty := vtype_path p (b := c + 3) (by rw [hp0]; exact hαf) hadj
  have hbA : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), c + 3 ≤ bAt δ := by
    intro δ
    have := bMin_le_bAt (H := P1 L1 L2 S) (M := P2 L1 L2 S) δ
    omega
  have hoddb : (c + 3) % 2 = 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hwt : vtype (p (c + 3)) = true := (hty _ le_rfl).mpr hoddb
  have hγt : vtype (p (c + 2)) = false := by
    cases h : vtype (p (c + 2))
    · rfl
    · have := (hty _ (by omega)).mp h; omega
  have hβt : vtype (p 1) = true := (hty 1 (by omega)).mpr rfl
  have hα0 : vtype (p 0) = false := by rw [hp0]; exact hαf
  have hnb : ∀ k, k < c + 3 → p (k + 1) ∈ nbrs (p k) := fun k hk => hadj k hk
  have hnb' : ∀ k, k < c + 3 → p k ∈ nbrs (p (k + 1)) := fun k hk => (hadj k hk).symm
  have hd1 : ∀ k, k < c + 3 → dist (p k) (p (k + 1)) = 1 := fun k hk =>
    CosetGeom.dist_eq_one_iff_adj.mpr (hadj k hk)
  have hpath := dist_path_le p hadj
  have hN : Vn (p 1) ≤ Qv (p (c + 2)) := by
    refine iSup₂_le fun l hl => Zv_le_Qv_of_dist_lt ?_
    have h1 : dist (p 1) l = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hl
    have h2 := hpath 1 (c + 1) (by omega)
    rw [show 1 + (c + 1) = c + 2 by omega] at h2
    have h3 := CosetGeom.dist_triangle (G₁ := P1 L1 L2 S) (G₂ := P2 L1 L2 S) rfl l (p 1) (p (c + 2))
    rw [CosetGeom.dist_comm l (p 1)] at h3
    have := hbA l
    omega
  have hM : Vn (p (c + 3)) ≤ Qv (p 2) := by
    refine iSup₂_le fun x hx => Zv_le_Qv_of_dist_lt ?_
    have h1 : dist (p (c + 3)) x = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hx
    have h2 := hpath 2 (c + 1) (by omega)
    rw [show 2 + (c + 1) = c + 3 by omega] at h2
    have h3 := CosetGeom.dist_triangle (G₁ := P1 L1 L2 S) (G₂ := P2 L1 L2 S) rfl x (p (c + 3)) (p 2)
    rw [CosetGeom.dist_comm x (p (c + 3)), CosetGeom.dist_comm (p (c + 3)) (p 2)] at h3
    have := hbA x
    omega
  have hnot : ¬ Zv (p 0) ≤ Qv (p (c + 3)) := by
    rw [hp0, hpb]; exact hc.not_le
  exact t2_config_false F hb3 hZ hZFD hα0 hβt hwt hγt (hnb' 0 (by omega)) (hnb 1 (by omega))
    (hnb' (c + 2) (by omega)) hN hM hnot

theorem caseIIT2_holds : CaseIIT2 := by
  intro G _ _ L1 L2 S D X F hT2 hb7 α β α' hc hII
  exact caseII_T2_false_ge3 F hT2 (by omega) hc hII

theorem input15204F112Untw_of_caseIIT1 (h1 : CaseIIT1) : He9.Input15204F112Untw :=
  input15204F112Untw_of h1 caseIIT2_holds

end CFSG.Quasithin.Kleidman.F204

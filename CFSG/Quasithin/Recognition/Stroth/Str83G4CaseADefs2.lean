module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAEquiv

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R

variable {G : Type} [Group G] {L1 L2 S : Subgroup G}

@[expose] noncomputable def caseAS {L1 L2 S : Subgroup G} (v w : f112Gamma L1 L2 S) :
    Subgroup (f112Amalgam L1 L2 S).Ghat :=
  CFSG.Open.pCoreOf 2 (CosetGeom.stab v ⊓ CosetGeom.stab w)

@[expose] noncomputable def caseALhat {L1 L2 S : Subgroup G} (v : f112Gamma L1 L2 S) :
    Subgroup (f112Amalgam L1 L2 S).Ghat :=
  ⨆ (w : f112Gamma L1 L2 S) (_ : w ∈ CosetGeom.nbrs v), caseAS v w

@[expose] noncomputable def caseAN {L1 L2 S : Subgroup G} (v : f112Gamma L1 L2 S) :
    Subgroup (f112Amalgam L1 L2 S).Ghat :=
  ⨆ (w : f112Gamma L1 L2 S) (_ : CosetGeom.dist v w = 2), caseAX w

@[expose] noncomputable def caseAY {L1 L2 S : Subgroup G} (v : f112Gamma L1 L2 S) :
    Subgroup (f112Amalgam L1 L2 S).Ghat :=
  CosetGeom.Qy v ⊓ Subgroup.centralizer (caseAX v : Set (f112Amalgam L1 L2 S).Ghat)

theorem caseAS_comm (v w : f112Gamma L1 L2 S) : caseAS v w = caseAS w v := by
  unfold caseAS
  rw [inf_comm]

theorem caseAS_le_stab_left (v w : f112Gamma L1 L2 S) : caseAS v w ≤ CosetGeom.stab v :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left

theorem caseAS_le_stab_right (v w : f112Gamma L1 L2 S) : caseAS v w ≤ CosetGeom.stab w :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right

theorem caseALhat_le_stab (v : f112Gamma L1 L2 S) : caseALhat v ≤ CosetGeom.stab v :=
  iSup₂_le fun w _ => caseAS_le_stab_left v w

theorem caseA_S_smul (g : f112Acting L1 L2 S) (v w : f112Gamma L1 L2 S) :
    caseAS (g • v) (g • w) = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAS v w) := by
  unfold caseAS
  rw [CosetGeom.stab_smul g v, CosetGeom.stab_smul g w, ← conjSub_inf, pCoreOf_conjSub]

theorem caseA_Lhat_smul (g : f112Acting L1 L2 S) (v : f112Gamma L1 L2 S) :
    caseALhat (g • v) = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseALhat v) := by
  unfold caseALhat
  simp_rw [conjSub_iSup]
  refine le_antisymm (iSup₂_le fun w hw => ?_) (iSup₂_le fun w hw => ?_)
  · have hw' : g⁻¹ • w ∈ CosetGeom.nbrs v := by
      have hwA : (f112Amalgam L1 L2 S).graphHat.Adj (g • v) w := hw
      have h := (CosetGeom.smul_adj g⁻¹).mpr hwA
      simpa [CosetGeom.nbrs, inv_smul_smul] using h
    calc caseAS (g • v) w
        = caseAS (g • v) (g • (g⁻¹ • w)) := by rw [smul_inv_smul]
      _ = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAS v (g⁻¹ • w)) :=
            caseA_S_smul g v (g⁻¹ • w)
      _ ≤ ⨆ (w) (_ : w ∈ CosetGeom.nbrs v),
            conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAS v w) :=
            le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs v) =>
              conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAS v w)) (g⁻¹ • w) hw'
  · have hgw : g • w ∈ CosetGeom.nbrs (g • v) := by
      have hwA : (f112Amalgam L1 L2 S).graphHat.Adj v w := hw
      have h := (CosetGeom.smul_adj g).mpr hwA
      simpa [CosetGeom.nbrs] using h
    calc conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAS v w)
        = caseAS (g • v) (g • w) := (caseA_S_smul g v w).symm
      _ ≤ ⨆ (w) (_ : w ∈ CosetGeom.nbrs (g • v)), caseAS (g • v) w :=
            le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs (g • v)) => caseAS (g • v) w)
              (g • w) hgw

theorem caseA_N_smul (g : f112Acting L1 L2 S) (v : f112Gamma L1 L2 S) :
    caseAN (g • v) = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAN v) := by
  unfold caseAN
  simp_rw [conjSub_iSup]
  refine le_antisymm (iSup₂_le fun w hw => ?_) (iSup₂_le fun w hw => ?_)
  · have hw' : CosetGeom.dist v (g⁻¹ • w) = 2 :=
      (CosetGeom.dist_smul g v (g⁻¹ • w)).symm.trans (by rw [smul_inv_smul]; exact hw)
    calc caseAX w
        = caseAX (g • (g⁻¹ • w)) := by rw [smul_inv_smul]
      _ = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAX (g⁻¹ • w)) :=
            caseA_X_smul g (g⁻¹ • w)
      _ ≤ ⨆ (w) (_ : CosetGeom.dist v w = 2),
            conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAX w) :=
            le_iSup₂ (f := fun w (_ : CosetGeom.dist v w = 2) =>
              conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAX w)) (g⁻¹ • w) hw'
  · have hgw : CosetGeom.dist (g • v) (g • w) = 2 := (CosetGeom.dist_smul g v w).trans hw
    calc conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAX w)
        = caseAX (g • w) := (caseA_X_smul g w).symm
      _ ≤ ⨆ (w) (_ : CosetGeom.dist (g • v) w = 2), caseAX w :=
            le_iSup₂ (f := fun w (_ : CosetGeom.dist (g • v) w = 2) => caseAX w) (g • w) hgw

theorem _root_.CFSG.Quasithin.GPath.IsGeodesic.dist_eq_sub {V : Type*} {Γ : SimpleGraph V}
    {n : ℕ} {p : GPath Γ n} (hΓ : Γ.Connected) (h : p.IsGeodesic) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ n) : Γ.dist (p i) (p j) = j - i := by
  have h0j := h.dist_eq hΓ hj
  have h0i := h.dist_eq hΓ (hij.trans hj)
  have hle := GPath.dist_le_sub hΓ p hij hj
  have htri := hΓ.dist_triangle (u := p 0) (v := p i) (w := p j)
  omega

structure caseACritPath (L1 L2 S : Subgroup G) (b : ℕ)
    (x : GPath (f112Amalgam L1 L2 S).graphHat b) : Prop where
  geodesic : x.IsGeodesic
  type_two : CosetGeom.vtype (x 0) = true
  ball : caseABoundAt L1 L2 S (b - 1)
  not_le : ¬ caseAZ (x 0) ≤ CosetGeom.Qy (x b)

theorem caseACritPath.dist_eq {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ b) :
    CosetGeom.dist (x i) (x j) = j - i :=
  GPath.IsGeodesic.dist_eq_sub (CosetGeom.connected rfl) hx.geodesic hij hj

theorem caseACritPath.vtype_eq_true_iff_even {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) {i : ℕ}
    (hi : i ≤ b) : CosetGeom.vtype (x i) = true ↔ Even i := by
  have hd : CosetGeom.dist (x 0) (x i) = i := hx.dist_eq (Nat.zero_le i) hi
  rw [← hx.type_two, eq_comm]
  exact (CosetGeom.vtype_eq_iff_even_dist rfl (x 0) (x i)).trans (by rw [hd])

theorem caseACritPath.vtype_eq_false_iff_odd {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) {i : ℕ}
    (hi : i ≤ b) : CosetGeom.vtype (x i) = false ↔ Odd i := by
  rw [← Nat.not_even_iff_odd, ← (hx.vtype_eq_true_iff_even hi).not]
  cases CosetGeom.vtype (x i) <;> simp

theorem caseA_critPath_of_pair {b : ℕ} (hb : caseABoundAt L1 L2 S (b - 1))
    {β δ : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true) (hd : CosetGeom.dist β δ = b)
    (hnot : ¬ caseAZ β ≤ CosetGeom.Qy δ) :
    ∃ x : GPath (f112Amalgam L1 L2 S).graphHat b,
      caseACritPath L1 L2 S b x ∧ x 0 = β ∧ x b = δ := by
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  obtain ⟨x, hx0, hxb, -⟩ := GPath.exists_geodesic' hconn β δ hd
  refine ⟨x, ⟨?_, by rw [hx0]; exact hβ, hb, by rw [hx0, hxb]; exact hnot⟩, hx0, hxb⟩
  show (f112Amalgam L1 L2 S).graphHat.dist (x 0) (x b) = b
  rw [hx0, hxb]
  exact hd

end CFSG.Quasithin.Stroth

end

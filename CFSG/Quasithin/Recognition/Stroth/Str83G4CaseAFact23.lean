module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAFact1
import CFSG.Quasithin.Recognition.Stroth.Str83G4CP
import CFSG.Quasithin.Recognition.Stroth.Str83G4S1

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R
open CFSG.Open

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem caseA_coe_f112StabEquiv0_theta (h : f112Acting L1 L2 S)
    (hh : h ∈ MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :
    (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ : G) =
      (((f112Completion L1 L2 S).theta (h : (f112Amalgam L1 L2 S).Ghat) :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) := by
  rw [coe_f112StabEquiv0]
  exact congrArg (fun y : ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) => (y : G))
    (RankTwoAmalgam.Completion.coe_theta0 (f112Completion L1 L2 S)
      (f112Completion_isFaithful L1 L2 S) h)

private theorem caseA_coe_f112StabEquiv1_theta (h : f112Acting L1 L2 S)
    (hh : h ∈ MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) :
    (f112StabEquiv1 L1 L2 S ⟨h, hh⟩ : G) =
      (((f112Completion L1 L2 S).theta (h : (f112Amalgam L1 L2 S).Ghat) :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) := by
  rw [coe_f112StabEquiv1]
  exact congrArg (fun y : ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) => (y : G))
    (RankTwoAmalgam.Completion.coe_theta0 (f112Completion L1 L2 S)
      (f112Completion_isFaithful L1 L2 S) h)

private theorem caseA_theta_mem_Z2_of_mem_Z_γ₁ {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {x : (f112Amalgam L1 L2 S).Ghat}
    (hx : x ∈ caseAZ (f112Gamma1 L1 L2 S)) :
    (((f112Completion L1 L2 S).theta x :
      ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) ∈ Z2 L1 L2 S := by
  have hxstab : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
    caseA_Qy_le_stab _ (caseA_Z_le_Qy _ hx)
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hxstab
  have hZ2 : (f112StabEquiv1 L1 L2 S ⟨k, hk⟩ : G) ∈ Z2 L1 L2 S := by
    apply (caseA_mem_Z_γ₁_iff ⟨k, hk⟩).mp
    change ((f112Amalgam L1 L2 S).Ghat1 ⊔
      (f112Amalgam L1 L2 S).Ghat2).subtype k ∈ caseAZ (f112Gamma1 L1 L2 S)
    rw [hkx]
    exact hx
  have hcoe : (f112StabEquiv1 L1 L2 S ⟨k, hk⟩ : G) =
      (((f112Completion L1 L2 S).theta x : ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) := by
    rw [caseA_coe_f112StabEquiv1_theta k hk]
    exact congrArg (fun z : (f112Amalgam L1 L2 S).Ghat =>
      (((f112Completion L1 L2 S).theta z : ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G)) hkx
  rwa [hcoe] at hZ2

private theorem caseA_Z_γ₁_le_Qy_γ₀
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    caseAZ (f112Gamma1 L1 L2 S) ≤ CosetGeom.Qy (f112Gamma0 L1 L2 S) := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, -⟩ := hfr'
  intro x hxZ
  have hxQ1 : x ∈ CosetGeom.Qy (f112Gamma1 L1 L2 S) := caseA_Z_le_Qy _ hxZ
  have hxK1 : x ∈ CosetGeom.ballStab 1 (f112Gamma1 L1 L2 S) :=
    caseA_Qy_le_ballStab_one hfr _ hxQ1
  have hxstab1 : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := caseA_Qy_le_stab _ hxQ1
  obtain ⟨k1, hk1, hk1x⟩ := Subgroup.mem_map.mp hxstab1
  have hZ2 : (f112StabEquiv1 L1 L2 S ⟨k1, hk1⟩ : G) ∈ Z2 L1 L2 S := by
    apply (caseA_mem_Z_γ₁_iff ⟨k1, hk1⟩).mp
    change ((f112Amalgam L1 L2 S).Ghat1 ⊔
      (f112Amalgam L1 L2 S).Ghat2).subtype k1 ∈ caseAZ (f112Gamma1 L1 L2 S)
    rw [hk1x]
    exact hxZ
  have hQ1₁ : (f112StabEquiv1 L1 L2 S ⟨k1, hk1⟩ : G) ∈ Q1 L1 L2 S :=
    z2_le_q1_of_rq hF hB ha hSz hL2 hZ2
  have hd10 : CosetGeom.dist (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) ≤ 1 :=
    (CosetGeom.dist_eq_one_iff_adj.mpr CosetGeom.adj_γ₀_γ₁.symm).le
  have hxstab0 : x ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) :=
    CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := f112Gamma1 L1 L2 S)
      (δ := f112Gamma0 L1 L2 S) hd10 hxK1
  obtain ⟨k0, hk0, hk0x⟩ := Subgroup.mem_map.mp hxstab0
  have hθ0 : (f112StabEquiv0 L1 L2 S ⟨k0, hk0⟩ : G) =
      (((f112Completion L1 L2 S).theta x :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) := by
    rw [caseA_coe_f112StabEquiv0_theta k0 hk0]
    exact congrArg (fun z : (f112Amalgam L1 L2 S).Ghat =>
      (((f112Completion L1 L2 S).theta z : ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G)) hk0x
  have hθ1 : (f112StabEquiv1 L1 L2 S ⟨k1, hk1⟩ : G) =
      (((f112Completion L1 L2 S).theta x :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) := by
    rw [caseA_coe_f112StabEquiv1_theta k1 hk1]
    exact congrArg (fun z : (f112Amalgam L1 L2 S).Ghat =>
      (((f112Completion L1 L2 S).theta z : ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G)) hk1x
  have hQ1₀ : (f112StabEquiv0 L1 L2 S ⟨k0, hk0⟩ : G) ∈ Q1 L1 L2 S := by
    rw [hθ0, ← hθ1]
    exact hQ1₁
  have hfin := (caseA_mem_Qy_γ₀_iff ⟨k0, hk0⟩).mpr hQ1₀
  rw [← hk0x]
  exact hfin

private theorem caseA_Z_γ₁_le_Qy_smul_γ₁
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (m : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :
    caseAZ (f112Gamma1 L1 L2 S) ≤
      CosetGeom.Qy ((m : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S) := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, -⟩ := hfr'
  have hZ0 : caseAZ (f112Gamma1 L1 L2 S) ≤ CosetGeom.Qy (f112Gamma0 L1 L2 S) :=
    caseA_Z_γ₁_le_Qy_γ₀ hfr
  have hab : IsElemAbelian 2 (str83X L1 L2 S) :=
    str83G4S1_of_z2Comm str83G4Z2Comm_holds G L1 L2 S a hfr
  have hXQ2 : str83X L1 L2 S ≤ Q2 L1 L2 S := str83G4_x_le_q2 hfr hab
  intro x hxZ
  set y : (f112Amalgam L1 L2 S).Ghat :=
    (m : (f112Amalgam L1 L2 S).Ghat)⁻¹ * x * (m : (f112Amalgam L1 L2 S).Ghat) with hy
  have hxQ0 : x ∈ CosetGeom.Qy (f112Gamma0 L1 L2 S) := hZ0 hxZ
  have hxK0 : x ∈ CosetGeom.ballStab 1 (f112Gamma0 L1 L2 S) :=
    caseA_Qy_le_ballStab_one hfr _ hxQ0
  have hadj : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S)
      ((m : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S) := by
    have h : (f112Amalgam L1 L2 S).graphHat.Adj
        ((m : f112Acting L1 L2 S) • f112Gamma0 L1 L2 S)
        ((m : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S) :=
      (CosetGeom.smul_adj (m : f112Acting L1 L2 S)).mpr CosetGeom.adj_γ₀_γ₁
    rwa [MulAction.mem_stabilizer_iff.mp m.2] at h
  have hxFix : x ∈ CosetGeom.stab ((m : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S) :=
    CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := f112Gamma0 L1 L2 S)
      (δ := (m : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S)
      (CosetGeom.dist_eq_one_iff_adj.mpr hadj).le hxK0
  have hystab : y ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := by
    have h := hxFix
    rw [CosetGeom.stab_smul] at h
    have := (CFSG.Quasithin.mem_conjSub
      (g := (m : (f112Amalgam L1 L2 S).Ghat))).mp h
    simpa [hy] using this
  obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hystab
  have hθy : (f112StabEquiv1 L1 L2 S ⟨k, hk⟩ : G) =
      (((f112Completion L1 L2 S).theta y :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) := by
    rw [caseA_coe_f112StabEquiv1_theta k hk]
    exact congrArg (fun z : (f112Amalgam L1 L2 S).Ghat =>
      (((f112Completion L1 L2 S).theta z : ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G)) hky
  have hθm : (f112StabEquiv0 L1 L2 S m : G) =
      (((f112Completion L1 L2 S).theta (m : (f112Amalgam L1 L2 S).Ghat) :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) :=
    caseA_coe_f112StabEquiv0_theta m.1 m.2
  have hθy' : (f112Completion L1 L2 S).theta y =
      ((f112Completion L1 L2 S).theta (m : (f112Amalgam L1 L2 S).Ghat))⁻¹ *
        (f112Completion L1 L2 S).theta x *
        (f112Completion L1 L2 S).theta (m : (f112Amalgam L1 L2 S).Ghat) := by
    rw [hy]
    simp only [map_mul, map_inv]
  have hθxZ : (((f112Completion L1 L2 S).theta x :
      ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) ∈ Z2 L1 L2 S :=
    caseA_theta_mem_Z2_of_mem_Z_γ₁ hfr hxZ
  have hθxX : (((f112Completion L1 L2 S).theta x :
      ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) ∈ str83X L1 L2 S :=
    z2_le_str83X L1 L2 S hθxZ
  have huP1 : (f112StabEquiv0 L1 L2 S m : G) ∈ P1 L1 L2 S :=
    (f112StabEquiv0 L1 L2 S m).2
  have huN : (f112StabEquiv0 L1 L2 S m : G) ∈
      Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    le_normalizer_str83X L1 L2 S huP1
  have hmemX : (f112StabEquiv0 L1 L2 S m : G)⁻¹ *
      (((f112Completion L1 L2 S).theta x :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) *
      (f112StabEquiv0 L1 L2 S m : G) ∈ str83X L1 L2 S :=
    (Subgroup.mem_normalizer_iff''.mp huN
      (((f112Completion L1 L2 S).theta x :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G)).mp hθxX
  have hQ2 : (f112StabEquiv1 L1 L2 S ⟨k, hk⟩ : G) ∈ Q2 L1 L2 S := by
    rw [hθy]
    rw [congrArg (fun z : ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) => (z : G)) hθy']
    change (((f112Completion L1 L2 S).theta (m : (f112Amalgam L1 L2 S).Ghat) :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G)⁻¹ *
      (((f112Completion L1 L2 S).theta x :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) *
      (((f112Completion L1 L2 S).theta (m : (f112Amalgam L1 L2 S).Ghat) :
        ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) : G) ∈ Q2 L1 L2 S
    rw [← hθm]
    exact hXQ2 hmemX
  have hyQ : y ∈ CosetGeom.Qy (f112Gamma1 L1 L2 S) := by
    have htmp := (caseA_mem_Qy_γ₁_iff ⟨k, hk⟩).mpr hQ2
    change ((f112Amalgam L1 L2 S).Ghat1 ⊔
      (f112Amalgam L1 L2 S).Ghat2).subtype k ∈ CosetGeom.Qy (f112Gamma1 L1 L2 S) at htmp
    rw [hky] at htmp
    exact htmp
  rw [caseA_Qy_smul]
  exact (CFSG.Quasithin.mem_conjSub (g := (m : (f112Amalgam L1 L2 S).Ghat))).mpr
    (by simpa [hy] using hyQ)

private theorem caseA_Z_γ₁_le_Qy_of_dist_two
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {δ : f112Gamma L1 L2 S}
    (hd : CosetGeom.dist (f112Gamma1 L1 L2 S) δ = 2) :
    caseAZ (f112Gamma1 L1 L2 S) ≤ CosetGeom.Qy δ := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, -⟩ := hfr'
  obtain ⟨ε, hεδ, hε1⟩ := CosetGeom.exists_adj_dist_eq (hG := rfl) (d := 1)
    (α := f112Gamma1 L1 L2 S) (δ := δ) (by omega)
  have hεn : ε ∈ CosetGeom.nbrs (f112Gamma1 L1 L2 S) :=
    CosetGeom.dist_eq_one_iff_adj.mp hε1
  have hγ₀n : f112Gamma0 L1 L2 S ∈ CosetGeom.nbrs (f112Gamma1 L1 L2 S) :=
    CosetGeom.adj_γ₀_γ₁.symm
  obtain ⟨k, hkstab, hkε⟩ :=
    f112_stabilizer_transitive_on_nbrs hF hεn hγ₀n
  have hkδ_adj : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S) (k • δ) := by
    have h : (f112Amalgam L1 L2 S).graphHat.Adj (k • δ) (k • ε) :=
      (CosetGeom.smul_adj k).mpr hεδ
    rw [hkε] at h
    exact h.symm
  have hγ₁n : f112Gamma1 L1 L2 S ∈ CosetGeom.nbrs (f112Gamma0 L1 L2 S) :=
    CosetGeom.adj_γ₀_γ₁
  have hkδn : k • δ ∈ CosetGeom.nbrs (f112Gamma0 L1 L2 S) := hkδ_adj
  obtain ⟨m, hmstab, hm⟩ := f112_stabilizer_transitive_on_nbrs hF hγ₁n hkδn
  have hδeq : δ = (k⁻¹ * m) • f112Gamma1 L1 L2 S := by
    rw [mul_smul, hm, inv_smul_smul]
  have hkZ : CFSG.Quasithin.conjSub (k : (f112Amalgam L1 L2 S).Ghat)
      (caseAZ (f112Gamma1 L1 L2 S)) = caseAZ (f112Gamma1 L1 L2 S) := by
    rw [← caseA_Z_smul]
    rw [show (k : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S =
        f112Gamma1 L1 L2 S from MulAction.mem_stabilizer_iff.mp hkstab]
  intro x hxZ
  set y : (f112Amalgam L1 L2 S).Ghat :=
    (k : (f112Amalgam L1 L2 S).Ghat) * x * (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ with hy
  have hyZ : y ∈ caseAZ (f112Gamma1 L1 L2 S) := by
    have := CFSG.Quasithin.mul_mem_conjSub (g := (k : (f112Amalgam L1 L2 S).Ghat)) hxZ
    rwa [hkZ] at this
  have hym : y ∈ CosetGeom.Qy ((m : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S) :=
    caseA_Z_γ₁_le_Qy_smul_γ₁ hfr ⟨m, hmstab⟩ hyZ
  have hQδeq : CosetGeom.Qy δ =
      CFSG.Quasithin.conjSub ((k⁻¹ : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat)
        (CosetGeom.Qy ((m : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S)) := by
    rw [hδeq, mul_smul, caseA_Qy_smul]
  rw [hQδeq]
  exact (CFSG.Quasithin.mem_conjSub
    (g := ((k⁻¹ : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat))).mpr
      (by simpa [hy] using hym)

private theorem caseA_Z_le_Qy_of_adj_type2
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {β δ : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true)
    (hadj : (f112Amalgam L1 L2 S).graphHat.Adj β δ) :
    caseAZ β ≤ CosetGeom.Qy δ := by
  obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge hadj
  · exfalso
    rw [← hg.1, CosetGeom.vtype_smul, CosetGeom.vtype_γ₀] at hβ
    exact Bool.false_ne_true hβ
  · rw [← hg.2, ← hg.1, caseA_Z_smul, caseA_Qy_smul]
    exact CFSG.Quasithin.conjSub_mono (g : (f112Amalgam L1 L2 S).Ghat)
      (caseA_Z_γ₁_le_Qy_γ₀ hfr)

theorem caseA_boundAt_two
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) : caseABoundAt L1 L2 S 2 := by
  intro β δ hβ hd
  have hcases : CosetGeom.dist β δ = 0 ∨ CosetGeom.dist β δ = 1 ∨
      CosetGeom.dist β δ = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hβδ : β = δ := (CosetGeom.dist_eq_zero_iff rfl).mp h0
    rw [hβδ]
    exact caseA_Z_le_Qy δ
  · exact caseA_Z_le_Qy_of_adj_type2 hfr hβ (CosetGeom.dist_eq_one_iff_adj.mp h1)
  · obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ hβ
    have hdist' : CosetGeom.dist (f112Gamma1 L1 L2 S)
        ((g⁻¹ : f112Acting L1 L2 S) • δ) = 2 := by
      have h1 : (g⁻¹ : f112Acting L1 L2 S) • β = f112Gamma1 L1 L2 S := by
        rw [hg]; simp
      rw [← h1]
      exact (CosetGeom.dist_smul (g⁻¹ : f112Acting L1 L2 S) β δ).trans h2
    rw [hg, caseA_Z_smul]
    have hδ : δ = g • ((g⁻¹ : f112Acting L1 L2 S) • δ) := by simp
    rw [hδ, caseA_Qy_smul]
    exact CFSG.Quasithin.conjSub_mono (g : (f112Amalgam L1 L2 S).Ghat)
      (caseA_Z_γ₁_le_Qy_of_dist_two hfr hdist')

theorem caseA_exists_not_le {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    ∃ β δ : f112Gamma L1 L2 S, CosetGeom.vtype β = true ∧ ¬ caseAZ β ≤ CosetGeom.Qy δ := by
  by_contra hne
  push Not at hne
  obtain ⟨aZ, haZ⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (caseA_Z_ne_bot hfr (f112Gamma1 L1 L2 S))
  have hxQ0 : (aZ : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.Qy (f112Gamma0 L1 L2 S) :=
    hne (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) rfl aZ.2
  have hxG : (aZ : (f112Amalgam L1 L2 S).Ghat) ∈
      ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2) := by
    have hxs := (caseA_Qy_le_stab (f112Gamma0 L1 L2 S)) hxQ0
    rw [caseA_stab_γ₀ L1 L2 S] at hxs
    exact Subgroup.mem_sup_left hxs
  have hfix : ∀ w : f112Gamma L1 L2 S, (⟨(aZ : (f112Amalgam L1 L2 S).Ghat), hxG⟩ :
      f112Acting L1 L2 S) • w = w := by
    intro w
    have hxQw : (aZ : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.Qy w :=
      hne (f112Gamma1 L1 L2 S) w rfl aZ.2
    exact CosetGeom.smul_eq_of_mem_stab ((caseA_Qy_le_stab w) hxQw)
  have h1 := f112_eq_one_of_forall_smul_eq hfr.1 hfix
  apply haZ
  apply Subtype.ext
  have := congrArg (fun g : f112Acting L1 L2 S => (g : (f112Amalgam L1 L2 S).Ghat)) h1
  simpa using this

theorem caseAB_spec {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    caseABoundAt L1 L2 S (caseAB L1 L2 S - 1) ∧
      ∃ β δ : f112Gamma L1 L2 S, CosetGeom.vtype β = true ∧
        CosetGeom.dist β δ = caseAB L1 L2 S ∧ ¬ caseAZ β ≤ CosetGeom.Qy δ := by
  obtain ⟨β₀, δ₀, hβ₀, hnot₀⟩ := caseA_exists_not_le hfr
  have hne : ({n | ∃ β δ : f112Gamma L1 L2 S, CosetGeom.vtype β = true ∧
      CosetGeom.dist β δ = n ∧ ¬ caseAZ β ≤ CosetGeom.Qy δ} : Set ℕ).Nonempty :=
    ⟨_, β₀, δ₀, hβ₀, rfl, hnot₀⟩
  have hmem : caseAB L1 L2 S ∈ {n | ∃ β δ : f112Gamma L1 L2 S,
      CosetGeom.vtype β = true ∧ CosetGeom.dist β δ = n ∧
        ¬ caseAZ β ≤ CosetGeom.Qy δ} :=
    Nat.sInf_mem hne
  have hmemc := hmem
  obtain ⟨β, δ, hβ, hd, hnot⟩ := hmem
  refine ⟨?_, β, δ, hβ, hd, hnot⟩
  intro β' δ' hβ' hd'
  by_contra hnot'
  have hle : caseAB L1 L2 S ≤ CosetGeom.dist β' δ' := by
    unfold caseAB
    exact Nat.sInf_le ⟨β', δ', hβ', rfl, hnot'⟩
  have hpos : 1 ≤ caseAB L1 L2 S := by
    by_contra hlt
    have hzero : caseAB L1 L2 S = 0 := by omega
    have h0 : (0 : ℕ) ∈ {n | ∃ β δ : f112Gamma L1 L2 S, CosetGeom.vtype β = true ∧
        CosetGeom.dist β δ = n ∧ ¬ caseAZ β ≤ CosetGeom.Qy δ} := hzero ▸ hmemc
    obtain ⟨β'', δ'', hβ'', hd0, hnot''⟩ := h0
    have heq : β'' = δ'' := (CosetGeom.dist_eq_zero_iff rfl).mp hd0
    rw [heq] at hnot''
    exact hnot'' (caseA_Z_le_Qy δ'')
  omega

theorem caseA_boundAt_iff_lt {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {k : ℕ} :
    caseABoundAt L1 L2 S k ↔ k < caseAB L1 L2 S := by
  obtain ⟨-, β, δ, hβ, hd, hnot⟩ := caseAB_spec hfr
  constructor
  · intro hk
    by_contra hle
    exact hnot (hk β δ hβ (hd.le.trans (not_lt.mp hle)))
  · intro hk β' δ' hβ' hd'
    by_contra hnot'
    have hmin : caseAB L1 L2 S ≤ CosetGeom.dist β' δ' :=
      Nat.sInf_le ⟨β', δ', hβ', rfl, hnot'⟩
    omega

end CFSG.Quasithin.Stroth

end

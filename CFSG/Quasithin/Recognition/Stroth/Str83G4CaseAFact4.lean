module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAFact23

public section

open CFSG.Quasithin.F112R

namespace CFSG.Quasithin.Stroth

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem theta0_stabEquiv0_symm (p : G) (hp : p ∈ P1 L1 L2 S) :
    (((f112Completion L1 L2 S).theta0 (f112Completion_isFaithful L1 L2 S)
      ((f112StabEquiv0 L1 L2 S).symm ⟨p, hp⟩ : f112Acting L1 L2 S) :
        ↥((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)) : G) = p := by
  rw [← coe_f112StabEquiv0]
  rw [MulEquiv.apply_symm_apply]

private theorem theta0_stabEquiv1_symm (p : G) (hp : p ∈ P2 L1 L2 S) :
    (((f112Completion L1 L2 S).theta0 (f112Completion_isFaithful L1 L2 S)
      ((f112StabEquiv1 L1 L2 S).symm ⟨p, hp⟩ : f112Acting L1 L2 S) :
        ↥((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)) : G) = p := by
  rw [← coe_f112StabEquiv1]
  rw [MulEquiv.apply_symm_apply]

private noncomputable def theta0ConjAct (a1 : G) (ha1 : a1 ∈ P1 L1 L2 S)
    (a2 : G) (ha2 : a2 ∈ P2 L1 L2 S) (w : G) (hw : w ∈ P2 L1 L2 S) :
    f112Acting L1 L2 S :=
  ((((f112StabEquiv0 L1 L2 S).symm ⟨a1, ha1⟩ : f112Acting L1 L2 S) *
    ((f112StabEquiv1 L1 L2 S).symm ⟨a2, ha2⟩ : f112Acting L1 L2 S))⁻¹ *
   ((f112StabEquiv1 L1 L2 S).symm ⟨w, hw⟩ : f112Acting L1 L2 S) *
   (((f112StabEquiv0 L1 L2 S).symm ⟨a1, ha1⟩ : f112Acting L1 L2 S) *
    ((f112StabEquiv1 L1 L2 S).symm ⟨a2, ha2⟩ : f112Acting L1 L2 S)))

private theorem theta0_conjAct_eq (a1 : G) (ha1 : a1 ∈ P1 L1 L2 S)
    (a2 : G) (ha2 : a2 ∈ P2 L1 L2 S) (w : G) (hw : w ∈ P2 L1 L2 S) :
    (((f112Completion L1 L2 S).theta0 (f112Completion_isFaithful L1 L2 S)
      (theta0ConjAct a1 ha1 a2 ha2 w hw) :
        ↥((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)) : G) =
      a2⁻¹ * (a1⁻¹ * w * a1) * a2 := by
  unfold theta0ConjAct
  simp only [map_mul, map_inv]
  push_cast
  rw [theta0_stabEquiv0_symm (p := a1) ha1,
      theta0_stabEquiv1_symm (p := a2) ha2,
      theta0_stabEquiv1_symm (p := w) hw]
  group

private theorem str83R_le_Q1_of_boundAt_three
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hb : caseABoundAt L1 L2 S 3) : str83R L1 L2 S ≤ Q1 L1 L2 S := by
  refine conjClosure_le ?_
  intro h hh x hx
  have hX : str83X L1 L2 S ≤ conjSub h⁻¹ (Q1 L1 L2 S) := by
    refine conjClosure_le ?_
    intro p hp z hz
    rw [mem_conjSub, inv_inv]
    have hzP2 : z ∈ P2 L1 L2 S :=
      (omegaOneCenterOf_le (Q2 L1 L2 S)).trans
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (P2 L1 L2 S)) hz
    let K1 : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :=
      (f112StabEquiv0 L1 L2 S).symm ⟨p⁻¹, (P1 L1 L2 S).inv_mem hp⟩
    let K2 : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) :=
      (f112StabEquiv1 L1 L2 S).symm ⟨h⁻¹, (P2 L1 L2 S).inv_mem hh⟩
    let Hz : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) :=
      (f112StabEquiv1 L1 L2 S).symm ⟨z, hzP2⟩
    let gA : f112Acting L1 L2 S := (K1 : f112Acting L1 L2 S) * (K2 : f112Acting L1 L2 S)
    have hxAZ : (((Hz : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat)) ∈
        caseAZ (f112Gamma1 L1 L2 S) := by
      refine (caseA_mem_Z_γ₁_iff Hz).mpr ?_
      rw [show f112StabEquiv1 L1 L2 S Hz = ⟨z, hzP2⟩ from MulEquiv.apply_symm_apply _ _]
      exact hz
    have hfix1 : (K1 : f112Acting L1 L2 S) • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S :=
      MulAction.mem_stabilizer_iff.mp K1.2
    have hfix2 : (K2 : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S :=
      MulAction.mem_stabilizer_iff.mp K2.2
    have hdist : CosetGeom.dist (f112Gamma1 L1 L2 S) (gA • f112Gamma0 L1 L2 S) ≤ 3 := by
      have h1 : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma1 L1 L2 S)
          (f112Gamma0 L1 L2 S) :=
        (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
          (G₁ := (f112Amalgam L1 L2 S).Ghat1)
          (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm
      have h2 : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S)
          ((K1 : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S) := by
        have := (CosetGeom.smul_adj (K1 : f112Acting L1 L2 S)).mpr
          (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
            (G₁ := (f112Amalgam L1 L2 S).Ghat1)
            (G₂ := (f112Amalgam L1 L2 S).Ghat2))
        rwa [hfix1] at this
      have h3 : (f112Amalgam L1 L2 S).graphHat.Adj
          ((K1 : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S)
          (gA • f112Gamma0 L1 L2 S) := by
        have hk : gA • f112Gamma0 L1 L2 S =
            (K1 : f112Acting L1 L2 S) • ((K2 : f112Acting L1 L2 S) • f112Gamma0 L1 L2 S) := by
          dsimp only [gA]
          rw [mul_smul]
        rw [hk]
        refine (CosetGeom.smul_adj (K1 : f112Acting L1 L2 S)).mpr ?_
        have := (CosetGeom.smul_adj (K2 : f112Acting L1 L2 S)).mpr
          (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
            (G₁ := (f112Amalgam L1 L2 S).Ghat1)
            (G₂ := (f112Amalgam L1 L2 S).Ghat2))
        rwa [hfix2] at this
      have := SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
        (SimpleGraph.Walk.cons h3 SimpleGraph.Walk.nil)))
      exact this
    have hxQδ : (((Hz : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat)) ∈
        CosetGeom.Qy (gA • f112Gamma0 L1 L2 S) :=
      hb (f112Gamma1 L1 L2 S) (gA • f112Gamma0 L1 L2 S) rfl hdist hxAZ
    have hconj : ((gA : (f112Amalgam L1 L2 S).Ghat))⁻¹ *
        ((Hz : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) *
        (gA : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.Qy (f112Gamma0 L1 L2 S) := by
      have := hxQδ
      rw [caseA_Qy_smul gA (f112Gamma0 L1 L2 S)] at this
      exact mem_conjSub.mp this
    have hstab : ((gA : (f112Amalgam L1 L2 S).Ghat))⁻¹ *
        ((Hz : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) *
        (gA : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) :=
      caseA_Qy_le_stab (f112Gamma0 L1 L2 S) hconj
    obtain ⟨hmem, hfix0⟩ := CosetGeom.mem_stab.mp hstab
    let h0 : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :=
      ⟨⟨(gA : (f112Amalgam L1 L2 S).Ghat)⁻¹ *
          ((Hz : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) *
          (gA : (f112Amalgam L1 L2 S).Ghat), hmem⟩, hfix0⟩
    have hQ1 : (f112StabEquiv0 L1 L2 S h0 : G) ∈ Q1 L1 L2 S :=
      (caseA_mem_Qy_γ₀_iff h0).mp (by simpa [h0] using hconj)
    have hgA : gA = ((f112StabEquiv0 L1 L2 S).symm ⟨p⁻¹, (P1 L1 L2 S).inv_mem hp⟩ :
          f112Acting L1 L2 S) *
        ((f112StabEquiv1 L1 L2 S).symm ⟨h⁻¹, (P2 L1 L2 S).inv_mem hh⟩ :
          f112Acting L1 L2 S) := rfl
    have hHz : (Hz : f112Acting L1 L2 S) =
        ((f112StabEquiv1 L1 L2 S).symm ⟨z, hzP2⟩ : f112Acting L1 L2 S) := rfl
    have heq : (f112StabEquiv0 L1 L2 S h0 : G) = h * (p * z * p⁻¹) * h⁻¹ := by
      rw [coe_f112StabEquiv0]
      change (((f112Completion L1 L2 S).theta0 (f112Completion_isFaithful L1 L2 S)
        ((gA : f112Acting L1 L2 S)⁻¹ * (Hz : f112Acting L1 L2 S) *
          gA : f112Acting L1 L2 S) : ↥((f112Completion L1 L2 S).φ1.range ⊔
              (f112Completion L1 L2 S).φ2.range)) : G) = h * (p * z * p⁻¹) * h⁻¹
      rw [hgA, hHz]
      simp only [map_mul, map_inv]
      push_cast
      rw [theta0_stabEquiv1_symm (p := h⁻¹) ((P2 L1 L2 S).inv_mem hh),
          theta0_stabEquiv0_symm (p := p⁻¹) ((P1 L1 L2 S).inv_mem hp),
          theta0_stabEquiv1_symm (p := z) hzP2]
      group
    rw [heq] at hQ1
    exact hQ1
  simpa only [inv_inv] using mem_conjSub.mp (hX hx)

end CFSG.Quasithin.Stroth

namespace CFSG.Quasithin.Stroth

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem caseA_Z_γ₁_le_Qy_of_edge
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hA : str83R L1 L2 S ≤ Q1 L1 L2 S)
    {ε₂ δ : f112Gamma L1 L2 S}
    (h₁ : ε₂ ∈ CosetGeom.nbrs (f112Gamma0 L1 L2 S))
    (h₂ : δ ∈ CosetGeom.nbrs ε₂) :
    caseAZ (f112Gamma1 L1 L2 S) ≤ CosetGeom.Qy δ := by
  intro x hx
  have hd₂ : CosetGeom.dist (f112Gamma1 L1 L2 S) ε₂ ≤ 2 := by
    have hγ₁γ₀ : CosetGeom.dist (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) = 1 :=
      CosetGeom.dist_eq_one_iff_adj.mpr
        (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
          (G₁ := (f112Amalgam L1 L2 S).Ghat1)
          (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm
    have hγ₀ε₂ : CosetGeom.dist (f112Gamma0 L1 L2 S) ε₂ = 1 :=
      CosetGeom.dist_eq_one_iff_adj.mpr h₁
    calc CosetGeom.dist (f112Gamma1 L1 L2 S) ε₂
        ≤ CosetGeom.dist (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) +
          CosetGeom.dist (f112Gamma0 L1 L2 S) ε₂ :=
          CosetGeom.dist_triangle_of_adj
            (CosetGeom.adj_γ₀_γ₁
              (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
              (G₁ := (f112Amalgam L1 L2 S).Ghat1)
              (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm ε₂
      _ = 2 := by rw [hγ₁γ₀, hγ₀ε₂]
  have hxQε₂ : x ∈ CosetGeom.Qy ε₂ :=
    (caseA_boundAt_two hfr) (f112Gamma1 L1 L2 S) ε₂ rfl hd₂ hx
  have hxstabδ : x ∈ CosetGeom.stab δ :=
    (CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := ε₂) (δ := δ)
      (le_of_eq (CosetGeom.dist_eq_one_iff_adj.mpr h₂)))
      ((caseA_Qy_le_ballStab_one hfr ε₂) hxQε₂)
  obtain ⟨k₁, hk₁stab, hk₁⟩ := f112_stabilizer_transitive_on_nbrs hfr.1
    (v := f112Gamma0 L1 L2 S) (w := f112Gamma1 L1 L2 S) (w' := ε₂)
    (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
      (G₁ := (f112Amalgam L1 L2 S).Ghat1)
      (G₂ := (f112Amalgam L1 L2 S).Ghat2)) h₁
  have hk₁invε₂ : (k₁⁻¹ : f112Acting L1 L2 S) • ε₂ = f112Gamma1 L1 L2 S := by
    rw [← hk₁, inv_smul_smul]
  have hδ' : (k₁⁻¹ : f112Acting L1 L2 S) • δ ∈
      CosetGeom.nbrs (f112Gamma1 L1 L2 S) := by
    have := (CosetGeom.smul_adj (k₁⁻¹ : f112Acting L1 L2 S)).mpr h₂
    rwa [hk₁invε₂] at this
  obtain ⟨k₂, hk₂stab, hk₂⟩ := f112_stabilizer_transitive_on_nbrs hfr.1
    (v := f112Gamma1 L1 L2 S) (w := f112Gamma0 L1 L2 S)
    (w' := (k₁⁻¹ : f112Acting L1 L2 S) • δ)
    (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
      (G₁ := (f112Amalgam L1 L2 S).Ghat1)
      (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm hδ'
  have hxstabγ₁ : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
    caseA_Qy_le_stab (f112Gamma1 L1 L2 S) (caseA_Z_le_Qy (f112Gamma1 L1 L2 S) hx)
  obtain ⟨hmemx, hfixx⟩ := CosetGeom.mem_stab.mp hxstabγ₁
  let xAct : f112Acting L1 L2 S := ⟨x, hmemx⟩
  let Hx : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) := ⟨xAct, hfixx⟩
  let K1 : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) := ⟨k₁, hk₁stab⟩
  let K2 : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) := ⟨k₂, hk₂stab⟩
  let a1 : ↥(P1 L1 L2 S) := f112StabEquiv0 L1 L2 S K1
  let a2 : ↥(P2 L1 L2 S) := f112StabEquiv1 L1 L2 S K2
  let z : ↥(P2 L1 L2 S) := f112StabEquiv1 L1 L2 S Hx
  let kA : f112Acting L1 L2 S := (K1 : f112Acting L1 L2 S) * (K2 : f112Acting L1 L2 S)
  have hzZ : (z : G) ∈ Z2 L1 L2 S :=
    (caseA_mem_Z_γ₁_iff Hx).mp (by simpa [Hx, xAct] using hx)
  have hXmem : (a1 : G)⁻¹ * (z : G) * (a1 : G) ∈ str83X L1 L2 S := by
    simpa only [str83X, inv_inv] using
      mem_conjClosure ((P1 L1 L2 S).inv_mem a1.2) hzZ
  have hRmem : (a2 : G)⁻¹ * ((a1 : G)⁻¹ * (z : G) * (a1 : G)) * (a2 : G) ∈
      str83R L1 L2 S := by
    simpa only [str83R, inv_inv] using
      mem_conjClosure ((P2 L1 L2 S).inv_mem a2.2) hXmem
  have hkA : kA • f112Gamma0 L1 L2 S = δ := by
    dsimp only [kA]
    rw [mul_smul, hk₂, smul_inv_smul]
  have hxActδ : xAct • δ = δ := CosetGeom.smul_eq_of_mem_stab hxstabδ
  have he'stab : ((kA)⁻¹ * xAct * kA : f112Acting L1 L2 S) • f112Gamma0 L1 L2 S =
      f112Gamma0 L1 L2 S := by
    calc ((kA)⁻¹ * xAct * kA : f112Acting L1 L2 S) • f112Gamma0 L1 L2 S
        = (kA)⁻¹ • (xAct • (kA • f112Gamma0 L1 L2 S)) := by rw [mul_smul, mul_smul]
      _ = (kA)⁻¹ • (xAct • δ) := by rw [hkA]
      _ = (kA)⁻¹ • δ := by rw [hxActδ]
      _ = (kA)⁻¹ • (kA • f112Gamma0 L1 L2 S) := by rw [hkA]
      _ = f112Gamma0 L1 L2 S := by rw [inv_smul_smul]
  let h0 : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :=
    ⟨(kA)⁻¹ * xAct * kA, he'stab⟩
  have hkAeq : kA = ((f112StabEquiv0 L1 L2 S).symm a1 : f112Acting L1 L2 S) *
      ((f112StabEquiv1 L1 L2 S).symm a2 : f112Acting L1 L2 S) := by
    have e1 : ((f112StabEquiv0 L1 L2 S).symm a1 : f112Acting L1 L2 S) = k₁ :=
      congrArg Subtype.val (MulEquiv.symm_apply_apply (f112StabEquiv0 L1 L2 S) K1)
    have e2 : ((f112StabEquiv1 L1 L2 S).symm a2 : f112Acting L1 L2 S) = k₂ :=
      congrArg Subtype.val (MulEquiv.symm_apply_apply (f112StabEquiv1 L1 L2 S) K2)
    dsimp only [kA]
    rw [e1, e2]
  have hxeq : xAct = ((f112StabEquiv1 L1 L2 S).symm z : f112Acting L1 L2 S) :=
    (congrArg Subtype.val (MulEquiv.symm_apply_apply (f112StabEquiv1 L1 L2 S) Hx)).symm
  have hQ1 : (f112StabEquiv0 L1 L2 S h0 : G) ∈ Q1 L1 L2 S := by
    have hzP2' : (z : G) ∈ P2 L1 L2 S :=
      (omegaOneCenterOf_le (Q2 L1 L2 S)).trans
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (P2 L1 L2 S)) hzZ
    have hh0 : (h0 : f112Acting L1 L2 S) =
        theta0ConjAct (a1 : G) a1.2 (a2 : G) a2.2 (z : G) hzP2' := by
      dsimp only [h0, theta0ConjAct]
      rw [hkAeq, hxeq]
    have hθ : (f112StabEquiv0 L1 L2 S h0 : G) =
        (a2 : G)⁻¹ * ((a1 : G)⁻¹ * (z : G) * (a1 : G)) * (a2 : G) := by
      rw [coe_f112StabEquiv0, hh0, theta0_conjAct_eq]
    rw [hθ]
    exact hA hRmem
  have he'Q : (((h0 : f112Acting L1 L2 S) :
      (f112Amalgam L1 L2 S).Ghat)) ∈ CosetGeom.Qy (f112Gamma0 L1 L2 S) :=
    (caseA_mem_Qy_γ₀_iff h0).mpr hQ1
  have hQδ : CosetGeom.Qy δ = conjSub (kA : (f112Amalgam L1 L2 S).Ghat)
      (CosetGeom.Qy (f112Gamma0 L1 L2 S)) := by
    rw [← hkA, caseA_Qy_smul kA (f112Gamma0 L1 L2 S)]
  rw [hQδ]
  exact mem_conjSub.mpr he'Q

private theorem caseA_Z_γ₁_le_Qy_of_dist_three
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {δ : f112Gamma L1 L2 S}
    (hδ : CosetGeom.dist (f112Gamma1 L1 L2 S) δ = 3) :
    caseAZ (f112Gamma1 L1 L2 S) ≤ CosetGeom.Qy δ := by
  obtain ⟨ε₂, hε₂δ, hd₂⟩ := CosetGeom.exists_adj_dist_eq
    (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
    (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2) rfl
    (α := f112Gamma1 L1 L2 S) (δ := δ) (d := 2) (by omega)
  obtain ⟨ε₁, hε₁ε₂, hd₁⟩ := CosetGeom.exists_adj_dist_eq
    (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
    (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2) rfl
    (α := f112Gamma1 L1 L2 S) (δ := ε₂) (d := 1) (by omega)
  have hε₁nbrs : ε₁ ∈ CosetGeom.nbrs (f112Gamma1 L1 L2 S) :=
    CosetGeom.dist_eq_one_iff_adj.mp hd₁
  have hγ₀nbrs : f112Gamma0 L1 L2 S ∈ CosetGeom.nbrs (f112Gamma1 L1 L2 S) :=
    (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
      (G₁ := (f112Amalgam L1 L2 S).Ghat1)
      (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm
  obtain ⟨e, hestab, hes⟩ := f112_stabilizer_transitive_on_nbrs hfr.1 hε₁nbrs hγ₀nbrs
  have h₁' : (e • ε₂) ∈ CosetGeom.nbrs (f112Gamma0 L1 L2 S) := by
    have := (CosetGeom.smul_adj e).mpr hε₁ε₂
    rw [hes] at this
    exact this.symm
  have h₂' : (e • δ) ∈ CosetGeom.nbrs (e • ε₂) :=
    (CosetGeom.smul_adj e).mpr hε₂δ.symm
  have hcanon : caseAZ (f112Gamma1 L1 L2 S) ≤ CosetGeom.Qy (e • δ) :=
    caseA_Z_γ₁_le_Qy_of_edge hfr hA h₁' h₂'
  have he_stab : (e : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
    CosetGeom.mem_stab.mpr ⟨e.2, MulAction.mem_stabilizer_iff.mp hestab⟩
  have he_norm : (e : (f112Amalgam L1 L2 S).Ghat) ∈
      Subgroup.normalizer (caseAZ (f112Gamma1 L1 L2 S) : Set (f112Amalgam L1 L2 S).Ghat) :=
    caseA_stab_le_normalizer_Z (f112Gamma1 L1 L2 S) he_stab
  have hZnorm : conjSub (((e⁻¹ : f112Acting L1 L2 S)) :
      (f112Amalgam L1 L2 S).Ghat) (caseAZ (f112Gamma1 L1 L2 S)) =
      caseAZ (f112Gamma1 L1 L2 S) :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer (Subgroup.inv_mem _ he_norm)
  have hQeq : conjSub (((e⁻¹ : f112Acting L1 L2 S)) :
      (f112Amalgam L1 L2 S).Ghat) (CosetGeom.Qy (e • δ)) = CosetGeom.Qy δ := by
    rw [← caseA_Qy_smul (e⁻¹ : f112Acting L1 L2 S) (e • δ)]
    congr 1
    rw [inv_smul_smul]
  have hmono := conjSub_mono (((e⁻¹ : f112Acting L1 L2 S)) :
      (f112Amalgam L1 L2 S).Ghat) hcanon
  rwa [hZnorm, hQeq] at hmono

private theorem caseA_boundAt_three_of_str83R_le_Q1
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) : caseABoundAt L1 L2 S 3 := by
  intro β δ hβ hδ
  by_cases h2 : CosetGeom.dist β δ ≤ 2
  · exact (caseA_boundAt_two hfr) β δ hβ h2
  · have h3 : CosetGeom.dist β δ = 3 := by omega
    obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁
      (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
      (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2) hβ
    have hgdist : CosetGeom.dist (f112Gamma1 L1 L2 S) (g⁻¹ • δ) = 3 := by
      have := CosetGeom.dist_smul
        (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
        (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2)
        g (f112Gamma1 L1 L2 S) (g⁻¹ • δ)
      rw [smul_inv_smul] at this
      rw [← this, h3]
    have hcanon : caseAZ (f112Gamma1 L1 L2 S) ≤ CosetGeom.Qy (g⁻¹ • δ) :=
      caseA_Z_γ₁_le_Qy_of_dist_three hfr hA hgdist
    rw [caseA_Z_smul g (f112Gamma1 L1 L2 S)]
    have hQeq : CosetGeom.Qy δ = conjSub (g : (f112Amalgam L1 L2 S).Ghat)
        (CosetGeom.Qy (g⁻¹ • δ)) := by
      rw [← caseA_Qy_smul g (g⁻¹ • δ)]
      congr 1
      rw [smul_inv_smul]
    rw [hQeq]
    exact conjSub_mono (g : (f112Amalgam L1 L2 S).Ghat) hcanon

theorem caseA_boundAt_three_iff
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    caseABoundAt L1 L2 S 3 ↔ str83R L1 L2 S ≤ Q1 L1 L2 S := by
  exact ⟨fun hb => str83R_le_Q1_of_boundAt_three hfr hb,
    fun hA => caseA_boundAt_three_of_str83R_le_Q1 hfr hA⟩

end CFSG.Quasithin.Stroth

end

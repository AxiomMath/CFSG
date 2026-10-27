module

public import CFSG.RankThree.GF2n.Smith81.S81R213Basic
public import CFSG.RankThree.GF2n.Smith81.S81RKer

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G]

section XData

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] Cube K}
  {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)} {z : G}

theorem neg_eq_self_QE (v : M₀.E) : -v = v := by
  have h2 : (2 : K) • v = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  rw [two_smul] at h2
  exact neg_eq_of_add_eq_zero_left h2

theorem E3LDat.xdata (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) {x : G} (hxc : IsConj z x) (hxM : x ∈ M)
    (hxQ : x ∉ Q) {g : GL (Fin 6) K} (hg : IsTransvec K g) (hx : ActsAs φ x g) :
    ∃ (X : Subgroup G) (_ : Sit M Q Z X x) (Tx : XAct M₀ x), CaseII Q Z x ∧
      (∀ e : M₀.E, e ∈ Cs Tx ↔ ψ e ∈ LinearMap.ker (rho K g - 1)) ∧
      (∀ r : M₀.E, r ∈ Rs Tx ↔ ψ r ∈ LinearMap.range (rho K g - 1)) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  obtain ⟨X, hX, hxX⟩ := exists_isZConjugate_mem Dt.hz hxc
  have hs : Sit M Q Z X x := ⟨H, hX, hxX, ne_one_of_isConj_Z Dt.hz1 hxc, hxM, hxQ⟩
  have h12 := smith_1_12 hs
  obtain ⟨Tx⟩ := exists_xact Dt.hD hxM (hs.x_cent h12)
  have hxL := hx.mem_Lgen
  have hφ := hx.phi hxL
  have hCs : ∀ e : M₀.E, e ∈ Cs Tx ↔ ψ e ∈ LinearMap.ker (rho K g - 1) :=
    fun e => mem_Cs_iff Dt.d hxL Tx hφ
  have hRs : ∀ r : M₀.E, r ∈ Rs Tx ↔ ψ r ∈ LinearMap.range (rho K g - 1) :=
    fun r => mem_Rs_iff Dt.d hxL Tx hφ
  have hP1 : Cs Tx ≤ Submodule.span K {e | e ∈ Cs Tx ∧ RootPt M₀ e} := by
    intro e he
    have h1 : ψ e ∈ Submodule.span K {ξ | ξ ∈ LinearMap.ker (rho K g - 1) ∧ IsPure K ξ} :=
      ker_le_span_pure_of_isTransvec hg ((hCs e).mp he)
    have h2 := Submodule.mem_map_of_mem (f := (ψ.symm : Cube K →ₗ[K] M₀.E)) h1
    rw [Submodule.map_span] at h2
    have h3 : e ∈ Submodule.span K ((ψ.symm : Cube K →ₗ[K] M₀.E) ''
        {ξ | ξ ∈ LinearMap.ker (rho K g - 1) ∧ IsPure K ξ}) := by
      simpa only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h2
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨ξ, ⟨hξC, hξP⟩, rfl⟩
    refine ⟨?_, rootPt_of_pure Dt.d H hξP⟩
    rw [hCs]
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hξC
  exact ⟨X, hs, Tx, caseII_of_nf Dt.hD hs Tx hP1
    (fun w hw hw1 => Dt.nf x hxc hxM hxQ w hw hw1), hCs, hRs⟩

theorem Tx_eq_of_phi {x y : G} {g : GL (Fin 6) K} (Dt : E3LDat M Q Z B K γ M₀ ψ φ z)
    (hx : ActsAs φ x g) (hy : ActsAs φ y g) (Tx : XAct M₀ x) (Ty : XAct M₀ y) (e : M₀.E) :
    Ty.T e = Tx.T e := by
  apply ψ.injective
  rw [psi_T Dt.d hy.mem_Lgen Ty (hy.phi hy.mem_Lgen) e, psi_T Dt.d hx.mem_Lgen Tx
    (hx.phi hx.mem_Lgen) e]

theorem conj_of_phi_eq (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) {x₁ y : G} (hx₁c : IsConj z x₁)
    (hx₁M : x₁ ∈ M) (hx₁Q : x₁ ∉ Q) (hyc : IsConj z y) (hyM : y ∈ M) (hyQ : y ∉ Q)
    {g : GL (Fin 6) K} (hg : IsTransvec K g) (hx₁ : ActsAs φ x₁ g) (hy : ActsAs φ y g) :
    ∃ q ∈ Q, y = q * x₁ * q⁻¹ := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  obtain ⟨X₁, hs₁, T₁, hII₁, -, hRs₁⟩ := Dt.xdata hx₁c hx₁M hx₁Q hg hx₁
  obtain ⟨Y, hsy, Ty, hIIy, -, -⟩ := Dt.xdata hyc hyM hyQ hg hy
  have hx₁L := hx₁.mem_Lgen
  have hyL := hy.mem_Lgen
  have hx₁x₁ : x₁ * x₁ = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hx₁c
  have hyy : y * y = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hyc
  have hx₁inv : x₁⁻¹ = x₁ := inv_eq_of_mul_eq_one_right hx₁x₁
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hc₀Q : x₁⁻¹ * y ∈ Q := by
    have h1 : φ ((⟨x₁, hx₁L⟩ : Lgen M (LB M Q B))⁻¹ * ⟨y, hyL⟩) = 1 := by
      rw [map_mul, map_inv, hx₁.phi hx₁L, hy.phi hyL, inv_mul_cancel]
    exact (Dt.d.ker _).mp h1
  have hc₀def : y = x₁ * (x₁⁻¹ * y) := by rw [mul_inv_cancel_left]
  have hπc₀C : M₀.π (x₁⁻¹ * y) ∈ Cs T₁ := by
    rw [mem_Cs]
    have hconj : x₁ * (x₁⁻¹ * y) * x₁⁻¹ = (x₁⁻¹ * y)⁻¹ := by
      calc x₁ * (x₁⁻¹ * y) * x₁⁻¹ = y * x₁⁻¹ := by group
        _ = (x₁⁻¹ * y)⁻¹ := by rw [mul_inv_rev, inv_inv, hx₁inv, hyinv]
    have h1 := T₁.hπ _ hc₀Q
    rw [hconj, Tim79.QuadModel.pi_inv M₀ hc₀Q, neg_eq_self_QE] at h1
    exact h1.symm
  have hC : ∀ q ∈ Q, M₀.π q ∈ Cs T₁ → ⁅q, x₁⁻¹ * y⁆ = 1 := by
    intro q hq hqC
    have hqx₁ : ⁅q, x₁⁆ = 1 := hII₁ q hq ((comm_mem_Z_iff hs₁ T₁ hq).mpr hqC)
    have hqCy : M₀.π q ∈ Cs Ty := by
      rw [mem_Cs, Tx_eq_of_phi Dt hx₁ hy T₁ Ty]
      exact mem_Cs.mp hqC
    have hqy : ⁅q, y⁆ = 1 := hIIy q hq ((comm_mem_Z_iff hsy Ty hq).mpr hqCy)
    have h1 : Commute q x₁ := commutatorElement_eq_one_iff_mul_comm.mp hqx₁
    have h2 : Commute q y := commutatorElement_eq_one_iff_mul_comm.mp hqy
    exact commutatorElement_eq_one_iff_mul_comm.mpr (h1.inv_right.mul_right h2)
  have hperp : ∀ c ∈ Cs T₁, M₀.B (M₀.π (x₁⁻¹ * y)) c = 0 := by
    intro c hc
    obtain ⟨q, hq, rfl⟩ := M₀.π_surj c
    have := (GM.comm_eq_one_iff Dt.hD hq hc₀Q).mp (hC q hq hc)
    rw [Tim79.QuadModel.B_comm, this, neg_zero]
  have hR : M₀.π (x₁⁻¹ * y) ∈ Rs T₁ := perp_Cs hs₁ T₁ hperp
  obtain ⟨d₀, hd₀Q, z', hz', hc₀eq⟩ := exists_comm_of_mem_Rs hs₁ T₁ hc₀Q hR
  have hq'Q : x₁ * d₀ * x₁⁻¹ ∈ Q := conj_mem_Q H hx₁M hd₀Q
  have hyeq : y = (x₁ * d₀ * x₁⁻¹ * x₁ * (x₁ * d₀ * x₁⁻¹)⁻¹) * z' := by
    calc y = x₁ * (x₁⁻¹ * y) := hc₀def
      _ = x₁ * (⁅d₀, x₁⁆ * z') := by rw [hc₀eq]
      _ = (x₁ * d₀ * x₁⁻¹ * x₁ * (x₁ * d₀ * x₁⁻¹)⁻¹) * z' := by
          simp only [commutatorElement_def]; group
  by_cases hz1 : z' = 1
  · exact ⟨_, hq'Q, by rw [hyeq, hz1, mul_one]⟩
  · exfalso
    have hq'M : x₁ * d₀ * x₁⁻¹ ∈ M := H.Q_normal.1 hq'Q
    have hy₁M : x₁ * d₀ * x₁⁻¹ * x₁ * (x₁ * d₀ * x₁⁻¹)⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem hq'M hx₁M) (M.inv_mem hq'M)
    have hy₁Q : x₁ * d₀ * x₁⁻¹ * x₁ * (x₁ * d₀ * x₁⁻¹)⁻¹ ∉ Q := by
      intro h
      apply hx₁Q
      have h1 : (x₁ * d₀ * x₁⁻¹)⁻¹ * (x₁ * d₀ * x₁⁻¹ * x₁ * (x₁ * d₀ * x₁⁻¹)⁻¹) *
          (x₁ * d₀ * x₁⁻¹) ∈ Q := Q.mul_mem (Q.mul_mem (Q.inv_mem hq'Q) h) hq'Q
      simpa [mul_assoc] using h1
    have hy₁c : IsConj z (x₁ * d₀ * x₁⁻¹ * x₁ * (x₁ * d₀ * x₁⁻¹)⁻¹) :=
      hx₁c.trans (isConj_iff.mpr ⟨x₁ * d₀ * x₁⁻¹, rfl⟩)
    apply Dt.nf _ hy₁c hy₁M hy₁Q z' hz' hz1
    rw [← hyeq]
    exact hy₁c.symm.trans hyc

theorem Cs_sup_Cs_eq_top {x₁ x₂ : G} {X₁ X₂ : Subgroup G} (hs₁ : Sit M Q Z X₁ x₁)
    (hs₂ : Sit M Q Z X₂ x₂) (T₁ : XAct M₀ x₁) (T₂ : XAct M₀ x₂) (h : Rs T₁ ⊓ Rs T₂ = ⊥) :
    Cs T₁ ⊔ Cs T₂ = ⊤ := by
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x' hx' => M₀.nondeg x' hx', fun y' hy' => M₀.nondeg y' (fun f => ?_)⟩
    rw [Tim79.QuadModel.B_comm, hy' f, neg_zero]
  have hrefl : M₀.B.IsRefl := by
    intro x' y' hxy
    rw [Tim79.QuadModel.B_comm, hxy, neg_zero]
  by_contra hne
  have hlt : Module.finrank K ↥(Cs T₁ ⊔ Cs T₂) < Module.finrank K M₀.E :=
    Submodule.finrank_lt hne
  have hfin := LinearMap.BilinForm.finrank_orthogonal hnd (Cs T₁ ⊔ Cs T₂)
  have hne' : M₀.B.orthogonal (Cs T₁ ⊔ Cs T₂) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfin
    omega
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at he
  have hperp : ∀ c ∈ Cs T₁ ⊔ Cs T₂, M₀.B e c = 0 := fun c hc => by
    rw [Tim79.QuadModel.B_comm, he c hc, neg_zero]
  have h1 : e ∈ Rs T₁ := perp_Cs hs₁ T₁ fun c hc => hperp c (Submodule.mem_sup_left hc)
  have h2 : e ∈ Rs T₂ := perp_Cs hs₂ T₂ fun c hc => hperp c (Submodule.mem_sup_right hc)
  have h3 : e ∈ Rs T₁ ⊓ Rs T₂ := ⟨h1, h2⟩
  rw [h] at h3
  exact he0 h3

end XData

end CFSG.RankThree.GF2n.Smith81.E3LRoot

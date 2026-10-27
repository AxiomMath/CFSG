module

public import CFSG.RankThree.GF2n.Smith81.S81YGenDef
public import CFSG.RankThree.GF2n.Smith81.S81R213X
public import CFSG.RankThree.GF2n.Smith81.S81TBridge

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGen

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E3LBridge CFSG.RankThree.GF2n.Smith81.E3LCond
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.MinuscT
open scoped commutatorElement

variable {G : Type} [Group G]

section XData

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {V : Type} [AddCommGroup V]
  [Module K V] {ψ : M₀.E ≃ₗ[K] V} {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)}
  {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V} {U₀ : Subgroup (V ≃ₗ[K] V)}
  {IsRt : (V ≃ₗ[K] V) → Prop} {z : G}

theorem GDat.xdata_gen (Dt : GDat M Q Z B K γ M₀ ψ φ Γ p₀ U₀ IsRt z) {x : G} (hxc : IsConj z x)
    (hxM : x ∈ M) (hxQ : x ∉ Q) {r : V ≃ₗ[K] V} (hr : IsRt r) (hx : Acts φ x r) :
    ∃ (X : Subgroup G) (_ : Sit M Q Z X x) (Tx : XAct M₀ x), CaseII Q Z x ∧
      ∀ e : M₀.E, e ∈ Rs Tx ↔ ψ e ∈ LinearMap.range ((r : V →ₗ[K] V) - 1) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  obtain ⟨X, hX, hxX⟩ := exists_isZConjugate_mem Dt.hz hxc
  have hs : Sit M Q Z X x := ⟨H, hX, hxX, ne_one_of_isConj_Z Dt.hz1 hxc, hxM, hxQ⟩
  have h12 := smith_1_12 hs
  obtain ⟨Tx⟩ := exists_xact Dt.hD hxM (hs.x_cent h12)
  have hxL := hx.mem_Lgen
  have hφ := hx.phi hxL
  have hRs : ∀ e : M₀.E, e ∈ Rs Tx ↔ ψ e ∈ LinearMap.range ((r : V →ₗ[K] V) - 1) := by
    intro e
    rw [MinuscT.mem_Rs_iff_E Dt.d hxL Tx hφ, LinearMap.mem_range]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, by simpa using hw.symm⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, by simpa using hw.symm⟩
  exact ⟨X, hs, Tx, Dt.caseII x hxc hxM hxQ r hx hr, hRs⟩

theorem conj_of_acts_eq_gen (Dt : GDat M Q Z B K γ M₀ ψ φ Γ p₀ U₀ IsRt z) {x₁ y : G}
    (hx₁c : IsConj z x₁) (hx₁M : x₁ ∈ M) (hx₁Q : x₁ ∉ Q) (hyc : IsConj z y) (hyM : y ∈ M)
    (hyQ : y ∉ Q) {r : V ≃ₗ[K] V} (hr : IsRt r) (hx₁ : Acts φ x₁ r) (hy : Acts φ y r) :
    ∃ q ∈ Q, y = q * x₁ * q⁻¹ := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  obtain ⟨X₁, hs₁, T₁, hII₁, -⟩ := Dt.xdata_gen hx₁c hx₁M hx₁Q hr hx₁
  obtain ⟨Y, hsy, Ty, hIIy, -⟩ := Dt.xdata_gen hyc hyM hyQ hr hy
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
  have hTy : ∀ e : M₀.E, Ty.T e = T₁.T e := by
    intro e
    apply ψ.injective
    rw [MinuscT.psi_T_E Dt.d hyL Ty (hy.phi hyL) e,
      MinuscT.psi_T_E Dt.d hx₁L T₁ (hx₁.phi hx₁L) e]
  have hπc₀C : M₀.π (x₁⁻¹ * y) ∈ Cs T₁ := by
    rw [mem_Cs]
    have hconj : x₁ * (x₁⁻¹ * y) * x₁⁻¹ = (x₁⁻¹ * y)⁻¹ := by
      calc x₁ * (x₁⁻¹ * y) * x₁⁻¹ = y * x₁⁻¹ := by group
        _ = (x₁⁻¹ * y)⁻¹ := by rw [mul_inv_rev, inv_inv, hx₁inv, hyinv]
    have h1 := T₁.hπ _ hc₀Q
    rw [hconj, Tim79.QuadModel.pi_inv M₀ hc₀Q,
      CFSG.RankThree.GF2n.Smith81.E3LRoot.neg_eq_self_QE] at h1
    exact h1.symm
  have hC : ∀ q ∈ Q, M₀.π q ∈ Cs T₁ → ⁅q, x₁⁻¹ * y⁆ = 1 := by
    intro q hq hqC
    have hqx₁ : ⁅q, x₁⁆ = 1 := hII₁ q hq ((comm_mem_Z_iff hs₁ T₁ hq).mpr hqC)
    have hqCy : M₀.π q ∈ Cs Ty := by
      rw [mem_Cs, hTy]
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

end XData

end CFSG.RankThree.GF2n.Smith81.RootGen

module

public import CFSG.RankThree.GF2n.Smith81.S81NSet

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LCond

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] {M Q Z X : Subgroup G} {x : G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}


section Lift1
variable [Finite G] [CharP K 2]

private theorem e3l_H0_comm {u : G} (hu0 : u ∈ H0 M Z) {z : G} (hz : z ∈ Z) : z * u = u * z :=
  Subgroup.mem_centralizer_iff.mp hu0.2 z hz

private theorem e3l_H0_fix {u : G} (hu0 : u ∈ H0 M Z) {y : G} (hy : y ∈ Z) :
    u⁻¹ * y * u = y := by
  calc u⁻¹ * y * u = u⁻¹ * (y * u) := by group
    _ = u⁻¹ * (u * y) := by rw [e3l_H0_comm hu0 hy]
    _ = y := by group

private theorem e3l_conj_inv_mem_Q (H : StrothHyp M Q Z) {u : G} (hu0 : u ∈ H0 M Z) {v : G}
    (hv : v ∈ Q) : u⁻¹ * v * u ∈ Q := by
  have h := conj_mem_Q H (M.inv_mem hu0.1) hv
  rwa [inv_inv] at h

theorem pi_conj_mem_Cs (hs : Sit M Q Z X x) (Tx : XAct M₀ x) {u : G} (hu0 : u ∈ H0 M Z)
    (hux : ⁅u, x⁆ ∈ Q) {w : G} (hw : w ∈ Q) (hwC : M₀.π w ∈ Cs Tx) :
    M₀.π (u⁻¹ * w * u) ∈ Cs Tx := by
  have H := hs.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hw' : u⁻¹ * w * u ∈ Q := e3l_conj_inv_mem_Q H hu0 hw
  have hwx : x * w * x⁻¹ ∈ Q := conj_mem_Q H hs.memM hw
  have hπwx : M₀.π (x * w * x⁻¹) = M₀.π w := (Tx.hπ w hw).trans (mem_Cs.mp hwC)
  obtain ⟨z₁, hz₁def⟩ : ∃ z : G, z = w⁻¹ * (x * w * x⁻¹) := ⟨_, rfl⟩
  have hz₁ : z₁ ∈ Z := by
    rw [hz₁def]
    exact (Tim79.QuadModel.pi_eq_iff M₀ hw hwx).mp hπwx.symm
  obtain ⟨z₂, hz₂def⟩ : ∃ z : G, z = ⁅w⁻¹, ⁅u, x⁆⁆ := ⟨_, rfl⟩
  have hz₂ : z₂ ∈ Z := by
    rw [hz₂def]
    exact comm_mem_Z H (Q.inv_mem hw) hux
  have hz₃ : z₂ * z₁ ∈ Z := Z.mul_mem hz₂ hz₁
  have hxw : x * w * x⁻¹ = w * z₁ := by
    rw [hz₁def]
    group
  have hcz : ⁅u, x⁆ * z₁ * ⁅u, x⁆⁻¹ = z₁ := by
    rw [← Z_central H hz₁ hux, mul_inv_cancel_right]
  have hcw : ⁅u, x⁆ * w * ⁅u, x⁆⁻¹ = w * z₂ := by
    rw [hz₂def]
    simp only [commutatorElement_def]
    group
  have hA : ⁅u, x⁆ * (x * w * x⁻¹) * ⁅u, x⁆⁻¹ = w * (z₂ * z₁) := by
    rw [hxw]
    calc ⁅u, x⁆ * (w * z₁) * ⁅u, x⁆⁻¹
        = (⁅u, x⁆ * w * ⁅u, x⁆⁻¹) * (⁅u, x⁆ * z₁ * ⁅u, x⁆⁻¹) := by group
      _ = (w * z₂) * z₁ := by rw [hcw, hcz]
      _ = w * (z₂ * z₁) := by group
  have hconj : x * (u⁻¹ * w * u) * x⁻¹ = (u⁻¹ * w * u) * (z₂ * z₁) := by
    have e : x * (u⁻¹ * w * u) * x⁻¹ = u⁻¹ * (⁅u, x⁆ * (x * w * x⁻¹) * ⁅u, x⁆⁻¹) * u := by
      simp only [commutatorElement_def]
      group
    rw [e, hA]
    calc u⁻¹ * (w * (z₂ * z₁)) * u = (u⁻¹ * w * u) * (u⁻¹ * (z₂ * z₁) * u) := by group
      _ = (u⁻¹ * w * u) * (z₂ * z₁) := by rw [e3l_H0_fix hu0 hz₃]
  have hπconj : M₀.π (x * (u⁻¹ * w * u) * x⁻¹) = M₀.π (u⁻¹ * w * u) := by
    rw [hconj, M₀.π_mul _ hw' _ (hZQ hz₃), (M₀.π_ker _ (hZQ hz₃)).mpr hz₃, add_zero]
  rw [mem_Cs, ← Tx.hπ _ hw']
  exact hπconj

theorem comm_conj_key (hs : Sit M Q Z X x) {u : G} (hu0 : u ∈ H0 M Z) (hux : ⁅u, x⁆ ∈ Q) {v : G}
    (hv : v ∈ Q) (hvx : ⁅v, x⁆ ∈ Z) : ⁅u⁻¹ * v * u, x⁆ = ⁅v, ⁅u, x⁆⁆ * ⁅v, x⁆ := by
  have H := hs.hyp
  obtain ⟨c, hc⟩ : ∃ c : G, c = ⁅u, x⁆ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : G, z = ⁅v, x⁆ := ⟨_, rfl⟩
  have hcQ : c ∈ Q := by
    rw [hc]
    exact hux
  have hzZ : z ∈ Z := by
    rw [hz]
    exact hvx
  rw [← hc, ← hz]
  have hzc : z * c = c * z := Z_central H hzZ hcQ
  have e1 : ⁅u⁻¹ * v * u, x⁆ = u⁻¹ * (v * c * (x * v⁻¹ * x⁻¹) * c⁻¹) * u := by
    rw [hc]
    simp only [commutatorElement_def]
    group
  have e2 : x * v⁻¹ * x⁻¹ = v⁻¹ * z := by
    rw [hz]
    simp only [commutatorElement_def]
    group
  have hcz : c * z * c⁻¹ = z := by
    rw [← hzc, mul_inv_cancel_right]
  have e4 : v * c * (v⁻¹ * z) * c⁻¹ = ⁅v, c⁆ * z := by
    rw [commutatorElement_def]
    calc v * c * (v⁻¹ * z) * c⁻¹ = (v * c * v⁻¹ * c⁻¹) * (c * z * c⁻¹) := by group
      _ = (v * c * v⁻¹ * c⁻¹) * z := by rw [hcz]
  have hy : ⁅v, c⁆ * z ∈ Z := Z.mul_mem (comm_mem_Z H hv hcQ) hzZ
  rw [e1, e2, e4, e3l_H0_fix hu0 hy]

private theorem e3l_B_of_comm_eq (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x)
    {u : G} (hu0 : u ∈ H0 M Z) (hux : ⁅u, x⁆ ∈ Q) {v : G} (hv : v ∈ Q) (hvx : ⁅v, x⁆ ∈ Z)
    (hvw : ⁅v, x⁆ = ⁅u⁻¹ * v * u, x⁆) : M₀.B (M₀.π v) (M₀.π ⁅u, x⁆) = 0 := by
  have hkey := comm_conj_key hs hu0 hux hv hvx
  have h1 : ⁅v, ⁅u, x⁆⁆ * ⁅v, x⁆ = 1 * ⁅v, x⁆ := by
    rw [one_mul, ← hkey]
    exact hvw.symm
  have h2 : ⁅v, ⁅u, x⁆⁆ = 1 := mul_right_cancel h1
  exact (GM.comm_eq_one_iff hD hv hux).mp h2

theorem caseI_piComm_mem_Rs (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x)
    (Tx : XAct M₀ x) (hQf : ∀ r ∈ Rs Tx, M₀.Qf r = 0) {u : G} (hu0 : u ∈ H0 M Z)
    (hux : ⁅u, x⁆ ∈ Q)
    (hUC : ∀ w ∈ Q, M₀.π w ∈ Cs Tx → M₀.π (u * w * u⁻¹) - M₀.π w ∈ Rs Tx) :
    M₀.π ⁅u, x⁆ ∈ Rs Tx := by
  refine perp_Cs hs Tx ?_
  intro k hk
  obtain ⟨v, hv, rfl⟩ := M₀.π_surj k
  have hvx : ⁅v, x⁆ ∈ Z := (comm_mem_Z_iff hs Tx hv).mpr hk
  have hwC : M₀.π (u⁻¹ * v * u) ∈ Cs Tx := pi_conj_mem_Cs hs Tx hu0 hux hv hk
  have hwQ : u⁻¹ * v * u ∈ Q := e3l_conj_inv_mem_Q hs.hyp hu0 hv
  have hwx : ⁅u⁻¹ * v * u, x⁆ ∈ Z := (comm_mem_Z_iff hs Tx hwQ).mpr hwC
  have hUCv : M₀.π v - M₀.π (u⁻¹ * v * u) ∈ Rs Tx := by
    have h := hUC _ hwQ hwC
    rwa [show u * (u⁻¹ * v * u) * u⁻¹ = v by group] at h
  have hyQ : v * (u⁻¹ * v * u)⁻¹ ∈ Q := Q.mul_mem hv (Q.inv_mem hwQ)
  have hπy : M₀.π (v * (u⁻¹ * v * u)⁻¹) = M₀.π v - M₀.π (u⁻¹ * v * u) := by
    rw [M₀.π_mul v hv _ (Q.inv_mem hwQ), Tim79.QuadModel.pi_inv M₀ hwQ, sub_eq_add_neg]
  have hyR : M₀.π (v * (u⁻¹ * v * u)⁻¹) ∈ Rs Tx := by
    rw [hπy]
    exact hUCv
  have hy1 : ⁅v * (u⁻¹ * v * u)⁻¹, x⁆ = 1 := comm_eq_one_of_Qf_zero hD hs Tx hQf hyQ hyR
  have hvw : ⁅v, x⁆ = ⁅u⁻¹ * v * u, x⁆ := by
    have h2 := comm_mul hs hyQ hwx
    rw [hy1, mul_one, show v * (u⁻¹ * v * u)⁻¹ * (u⁻¹ * v * u) = v by group] at h2
    exact h2
  have hB := e3l_B_of_comm_eq hD hs hu0 hux hv hvx hvw
  rw [Tim79.QuadModel.B_comm, hB, neg_zero]

theorem caseII_piComm_mem_Rs (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x)
    (Tx : XAct M₀ x) (hII : CaseII Q Z x) {u : G} (hu0 : u ∈ H0 M Z) (hux : ⁅u, x⁆ ∈ Q) :
    M₀.π ⁅u, x⁆ ∈ Rs Tx := by
  refine perp_Cs hs Tx ?_
  intro k hk
  obtain ⟨v, hv, rfl⟩ := M₀.π_surj k
  have hvx : ⁅v, x⁆ ∈ Z := (comm_mem_Z_iff hs Tx hv).mpr hk
  have hwC : M₀.π (u⁻¹ * v * u) ∈ Cs Tx := pi_conj_mem_Cs hs Tx hu0 hux hv hk
  have hwQ : u⁻¹ * v * u ∈ Q := e3l_conj_inv_mem_Q hs.hyp hu0 hv
  have hwx : ⁅u⁻¹ * v * u, x⁆ ∈ Z := (comm_mem_Z_iff hs Tx hwQ).mpr hwC
  have hvw : ⁅v, x⁆ = ⁅u⁻¹ * v * u, x⁆ := by
    rw [hII v hv hvx, hII _ hwQ hwx]
  have hB := e3l_B_of_comm_eq hD hs hu0 hux hv hvx hvw
  rw [Tim79.QuadModel.B_comm, hB, neg_zero]
end Lift1
end CFSG.RankThree.GF2n.Smith81.E3LCond

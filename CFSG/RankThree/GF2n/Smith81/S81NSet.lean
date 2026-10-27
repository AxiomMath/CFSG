module

public import CFSG.RankThree.GF2n.Smith81.Sec1Main
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LCond

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] {M Q Z X : Subgroup G} {x : G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

@[expose] def Cs (Tx : XAct M₀ x) : Submodule K M₀.E := LinearMap.ker ((Tx.T : M₀.E →ₗ[K] M₀.E) - 1)
@[expose] def Rs (Tx : XAct M₀ x) : Submodule K M₀.E := LinearMap.range ((Tx.T : M₀.E →ₗ[K] M₀.E) - 1)
@[expose] def CaseI (Q Z : Subgroup G) (x : G) : Prop := ∀ z ∈ Z, ∃ q ∈ Q, ⁅q, x⁆ = z
@[expose] def CaseII (Q Z : Subgroup G) (x : G) : Prop := ∀ q ∈ Q, ⁅q, x⁆ ∈ Z → ⁅q, x⁆ = 1
@[expose] def RootPt (M₀ : Tim79.QuadModel Q Z K γ) (e : M₀.E) : Prop :=
  e = 0 ∨ ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧ ∃ a ∈ A, M₀.π a = e

section Basics
variable [Finite G] [CharP K 2]

private theorem neg_eq_self_E (v : M₀.E) : -v = v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hv : v + v = 0 := by rw [← two_smul K v, h2, zero_smul]
  exact neg_eq_of_add_eq_zero_left hv

theorem mem_Cs {Tx : XAct M₀ x} {e : M₀.E} : e ∈ Cs Tx ↔ Tx.T e = e := by
  simp only [Cs, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    LinearEquiv.coe_coe, sub_eq_zero]

theorem mem_Rs {Tx : XAct M₀ x} {r : M₀.E} : r ∈ Rs Tx ↔ ∃ e, Tx.T e - e = r := by
  simp only [Rs, LinearMap.mem_range, LinearMap.sub_apply, Module.End.one_apply,
    LinearEquiv.coe_coe]

theorem T_T (hs : Sit M Q Z X x) (Tx : XAct M₀ x) (e : M₀.E) : Tx.T (Tx.T e) = e :=
  XAct.T_T Tx hs.hyp hs.memM hs.x_sq e

theorem Rs_le_Cs (hs : Sit M Q Z X x) (Tx : XAct M₀ x) : Rs Tx ≤ Cs Tx := by
  intro r hr
  obtain ⟨e, rfl⟩ := mem_Rs.mp hr
  rw [mem_Cs, map_sub, T_T hs Tx e, show e - Tx.T e = -(Tx.T e - e) from (neg_sub _ _).symm,
    neg_eq_self_E]

theorem B_T_right (hs : Sit M Q Z X x) (Tx : XAct M₀ x) (e f : M₀.E) :
    M₀.B e (Tx.T f) = M₀.B (Tx.T e) f := by
  have h := Tx.hB (Tx.T e) f
  rw [T_T hs Tx e] at h
  exact h

private theorem B_Cs_Rs (hs : Sit M Q Z X x) (Tx : XAct M₀ x) {c w : M₀.E} (hc : c ∈ Cs Tx)
    (hw : w ∈ Rs Tx) : M₀.B c w = 0 := by
  obtain ⟨f, rfl⟩ := mem_Rs.mp hw
  have hc' : Tx.T c = c := mem_Cs.mp hc
  simp only [map_sub, LinearMap.sub_apply]
  rw [B_T_right hs Tx c f, hc', sub_self]

theorem B_Rs_Rs (hs : Sit M Q Z X x) (Tx : XAct M₀ x) {r s : M₀.E} (hr : r ∈ Rs Tx)
    (hs' : s ∈ Rs Tx) : M₀.B r s = 0 :=
  B_Cs_Rs hs Tx (Rs_le_Cs hs Tx hr) hs'

theorem Qf_sub (hs : Sit M Q Z X x) (Tx : XAct M₀ x) (e : M₀.E) :
    M₀.Qf (Tx.T e - e) = M₀.B (Tx.T e) e := by
  have hK2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsm : (-1 : K) • e = -e := by simp
  have hneg : M₀.Qf (-e) = M₀.Qf e := by
    rw [← hsm, M₀.Qf_smul]
    ring
  have hB : M₀.B (Tx.T e) (-e) = -M₀.B (Tx.T e) e := by
    rw [map_neg]
  rw [sub_eq_add_neg, M₀.Qf_add, hneg, hB, Tx.hQ e]
  linear_combination (M₀.Qf e - M₀.B (Tx.T e) e) * hK2

theorem perp_Cs (hs : Sit M Q Z X x) (Tx : XAct M₀ x) {e : M₀.E}
    (h : ∀ c ∈ Cs Tx, M₀.B e c = 0) : e ∈ Rs Tx := by
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x' hx' => M₀.nondeg x' hx', fun y' hy' => M₀.nondeg y' (fun f => ?_)⟩
    rw [Tim79.QuadModel.B_comm, hy' f, neg_zero]
  have hrefl : M₀.B.IsRefl := by
    intro x' y' hxy
    rw [Tim79.QuadModel.B_comm, hxy, neg_zero]
  have hEq : M₀.B.orthogonal (Rs Tx) = Cs Tx := by
    ext c
    rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_Cs]
    constructor
    · intro hc
      apply sub_eq_zero.mp
      apply M₀.nondeg
      intro f
      have h3 : M₀.B (Tx.T c - c) f = M₀.B c (Tx.T f - f) := by
        simp only [map_sub, LinearMap.sub_apply]
        rw [B_T_right hs Tx c f]
      rw [h3, Tim79.QuadModel.B_comm, hc (Tx.T f - f) (mem_Rs.mpr ⟨f, rfl⟩), neg_zero]
    · intro hc n hn
      obtain ⟨f, rfl⟩ := mem_Rs.mp hn
      have h1 : M₀.B c (Tx.T f - f) = 0 := by
        simp only [map_sub, LinearMap.sub_apply]
        rw [B_T_right hs Tx c f, hc, sub_self]
      rw [Tim79.QuadModel.B_comm, h1, neg_zero]
  have h2 : M₀.B.orthogonal (Cs Tx) = Rs Tx := by
    rw [← hEq]
    exact LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl (Rs Tx)
  have hmem : e ∈ M₀.B.orthogonal (Cs Tx) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro c hc
    rw [Tim79.QuadModel.B_comm, h c hc, neg_zero]
  rw [← h2]
  exact hmem

theorem comm_mem_Z_iff (hs : Sit M Q Z X x) (Tx : XAct M₀ x) {q : G} (hq : q ∈ Q) :
    ⁅q, x⁆ ∈ Z ↔ M₀.π q ∈ Cs Tx := by
  have hc : ⁅q, x⁆ ∈ Q := comm_mem_Q hs.hyp hs.memM hq
  rw [← M₀.π_ker _ hc, Tx.pi_comm hs.hyp hs.memM hq, mem_Cs, sub_eq_zero]
  exact eq_comm

private theorem comm_mul_Z_right (hs : Sit M Q Z X x) {z : G} (hz : z ∈ Z) (b : G) :
    ⁅b * z, x⁆ = ⁅b, x⁆ := by
  have hxz : x * z = z * x := mul_inv_eq_iff_eq_mul.mp (hs.x_cent (smith_1_12 hs) z hz)
  have hzx : z * x * z⁻¹ = x := by rw [← hxz, mul_inv_cancel_right]
  calc ⁅b * z, x⁆ = b * (z * x * z⁻¹) * b⁻¹ * x⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = b * x * b⁻¹ * x⁻¹ := by rw [hzx]
    _ = ⁅b, x⁆ := by rw [commutatorElement_def]

theorem comm_mul (hs : Sit M Q Z X x) {a b : G} (ha : a ∈ Q) (hb : ⁅b, x⁆ ∈ Z) :
    ⁅a * b, x⁆ = ⁅b, x⁆ * ⁅a, x⁆ := by
  have hc : ⁅b, x⁆ * a = a * ⁅b, x⁆ := Z_central hs.hyp hb ha
  have e : ⁅a * b, x⁆ = (a * ⁅b, x⁆ * a⁻¹) * ⁅a, x⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, ← hc, mul_inv_cancel_right]

theorem comm_eq_of_pi_eq (hs : Sit M Q Z X x) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q)
    (h : M₀.π a = M₀.π b) : ⁅a, x⁆ = ⁅b, x⁆ := by
  have hbaQ : b⁻¹ * a ∈ Q := Q.mul_mem (Q.inv_mem hb) ha
  have hz : b⁻¹ * a ∈ Z := by
    rw [← M₀.π_ker _ hbaQ, M₀.π_mul _ (Q.inv_mem hb) a ha, Tim79.QuadModel.pi_inv M₀ hb, h,
      neg_add_cancel]
  calc ⁅a, x⁆ = ⁅b * (b⁻¹ * a), x⁆ := by rw [mul_inv_cancel_left]
    _ = ⁅b, x⁆ := comm_mul_Z_right hs hz b

private theorem comm_inv_mul_mem_Z (hs : Sit M Q Z X x) {y d : G} (hy : y ∈ Q) (hdQ : d ∈ Q)
    (hπc : M₀.π ⁅d, x⁆ = M₀.π y) : ⁅d, x⁆⁻¹ * y ∈ Z := by
  have hcQ : ⁅d, x⁆ ∈ Q := comm_mem_Q hs.hyp hs.memM hdQ
  have hzQ : ⁅d, x⁆⁻¹ * y ∈ Q := Q.mul_mem (Q.inv_mem hcQ) hy
  rw [← M₀.π_ker _ hzQ, M₀.π_mul _ (Q.inv_mem hcQ) y hy, Tim79.QuadModel.pi_inv M₀ hcQ, hπc,
    neg_add_cancel]

private theorem exists_d_of_mem_Rs (hs : Sit M Q Z X x) (Tx : XAct M₀ x) {y : G}
    (hyR : M₀.π y ∈ Rs Tx) : ∃ d ∈ Q, M₀.π ⁅d, x⁆ = M₀.π y := by
  obtain ⟨e, he⟩ := mem_Rs.mp hyR
  obtain ⟨d, hdQ, hd⟩ := M₀.π_surj e
  refine ⟨d, hdQ, ?_⟩
  rw [Tx.pi_comm hs.hyp hs.memM hdQ, hd, ← he,
    show e - Tx.T e = -(Tx.T e - e) from (neg_sub _ _).symm, neg_eq_self_E (Tx.T e - e)]

private theorem conj_comm_inv (hx : x * x = 1) (d : G) : x * ⁅d, x⁆ * x⁻¹ = ⁅d, x⁆⁻¹ := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hc : ⁅d, x⁆ = d * (x * d * x⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  have hd' : x * (x * d * x⁻¹) * x⁻¹ = d := by
    rw [hxinv]
    calc x * (x * d * x) * x = (x * x) * d * (x * x) := by group
      _ = d := by rw [hx, one_mul, mul_one]
  calc x * ⁅d, x⁆ * x⁻¹ = (x * d * x⁻¹) * (x * (x * d * x⁻¹)⁻¹ * x⁻¹) := by
        rw [hc]
        group
    _ = (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)⁻¹ := by group
    _ = (x * d * x⁻¹) * d⁻¹ := by rw [hd']
    _ = ⁅d, x⁆⁻¹ := by
        rw [hc]
        group

private theorem comm_eq_sq_of_conj_inv {c : G} (hc : x * c * x⁻¹ = c⁻¹) : ⁅c, x⁆ = c ^ 2 := by
  have h1 : x * c⁻¹ * x⁻¹ = c := by
    have e1 : x * c⁻¹ * x⁻¹ = (x * c * x⁻¹)⁻¹ := by group
    rw [e1, hc, inv_inv]
  rw [commutatorElement_def, pow_two]
  calc c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) := by group
    _ = c * c := by rw [h1]

theorem gamma_comm_of_mem_Rs (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x)
    (Tx : XAct M₀ x) {y : G} (hy : y ∈ Q) (hyR : M₀.π y ∈ Rs Tx) :
    ⁅y, x⁆ ∈ Z ∧ γ ⁅y, x⁆ = M₀.Qf (M₀.π y) := by
  obtain ⟨d, hdQ, hπc⟩ := exists_d_of_mem_Rs hs Tx hyR
  have hcQ : ⁅d, x⁆ ∈ Q := comm_mem_Q hs.hyp hs.memM hdQ
  have hyc : ⁅y, x⁆ = ⁅d, x⁆ ^ 2 := by
    calc ⁅y, x⁆ = ⁅⁅d, x⁆ * (⁅d, x⁆⁻¹ * y), x⁆ := by rw [mul_inv_cancel_left]
      _ = ⁅⁅d, x⁆, x⁆ := comm_mul_Z_right hs (comm_inv_mul_mem_Z hs hy hdQ hπc) _
      _ = ⁅d, x⁆ ^ 2 := comm_eq_sq_of_conj_inv (conj_comm_inv hs.x_sq d)
  refine ⟨?_, ?_⟩
  · rw [hyc]
    exact sq_mem_Z hs.hyp hcQ
  · rw [hyc, M₀.sq_eq _ hcQ, hπc]

theorem comm_eq_one_of_Qf_zero (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x)
    (Tx : XAct M₀ x) (hQf : ∀ r ∈ Rs Tx, M₀.Qf r = 0) {y : G} (hy : y ∈ Q)
    (hyR : M₀.π y ∈ Rs Tx) : ⁅y, x⁆ = 1 := by
  obtain ⟨hZ, hγ⟩ := gamma_comm_of_mem_Rs hD hs Tx hy hyR
  rw [hQf _ hyR] at hγ
  exact hD.reg.inj _ hZ hγ

theorem exists_comm_of_mem_Rs (hs : Sit M Q Z X x) (Tx : XAct M₀ x) {y : G} (hy : y ∈ Q)
    (hyR : M₀.π y ∈ Rs Tx) : ∃ d ∈ Q, ∃ z ∈ Z, y = ⁅d, x⁆ * z := by
  obtain ⟨d, hdQ, hπc⟩ := exists_d_of_mem_Rs hs Tx hyR
  exact ⟨d, hdQ, _, comm_inv_mul_mem_Z hs hy hdQ hπc, (mul_inv_cancel_left _ _).symm⟩

theorem D_pi_mem_Cs (hs : Sit M Q Z X x) (Tx : XAct M₀ x) {d : G} (hd : d ∈ Q ⊓ QB X) :
    M₀.π d ∈ Cs Tx := by
  obtain ⟨hdQ, hdB⟩ := Subgroup.mem_inf.mp hd
  have hcomm : ⁅d, x⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hs.QB_comm_X hs.mem hdB).symm
  have h0 : M₀.π d - Tx.T (M₀.π d) = 0 := by
    rw [← Tx.pi_comm hs.hyp hs.memM hdQ, hcomm, Tim79.QuadModel.pi_one]
  rw [mem_Cs]
  exact (sub_eq_zero.mp h0).symm

theorem D_eq_one_of_pi_eq_zero (hs : Sit M Q Z X x) {d : G} (hd : d ∈ Q ⊓ QB X)
    (h : M₀.π d = 0) : d = 1 := by
  obtain ⟨hdQ, hdB⟩ := Subgroup.mem_inf.mp hd
  have hdZ : d ∈ Z := (M₀.π_ker _ hdQ).mp h
  have hmem : d ∈ Z ⊓ QB X := Subgroup.mem_inf.mpr ⟨hdZ, hdB⟩
  rw [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at hmem
  exact hmem

private theorem sq_eq_one_of_mem_Z (hD : GlobalModelData M Q Z γ M₀) {z : G} (hz : z ∈ Z) :
    z ^ 2 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h0 : γ (z * z) = 0 := by
    rw [hD.reg.add z hz z hz, ← two_mul, h2, zero_mul]
  rw [pow_two]
  exact hD.reg.inj _ (Z.mul_mem hz hz) h0

theorem Qf_RootPt (hD : GlobalModelData M Q Z γ M₀) {e : M₀.E} (he : RootPt M₀ e) :
    M₀.Qf e = 0 := by
  rcases he with rfl | ⟨A, ⟨g, rfl⟩, hAQ, -, a, haA, hae⟩
  · exact Tim79.QuadModel.Qf_zero
  · have haQ : a ∈ Q := hAQ haA
    have hz : g⁻¹ * a * g ∈ Z := mem_conjSubgroup.mp haA
    have hsq : a ^ 2 = 1 := by
      have e2 : a * a = g * ((g⁻¹ * a * g) ^ 2) * g⁻¹ := by
        rw [pow_two]
        group
      rw [pow_two, e2, sq_eq_one_of_mem_Z hD hz]
      group
    rw [← hae, ← M₀.sq_eq a haQ, hsq, hD.reg.one]

end Basics

end CFSG.RankThree.GF2n.Smith81.E3LCond

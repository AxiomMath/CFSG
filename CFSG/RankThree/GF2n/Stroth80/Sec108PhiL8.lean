module

public import CFSG.LinearAlgebra.AlternatingCross
public import CFSG.RankThree.GF2n.Stroth80.Sec108PhiAxis
public import CFSG.RankThree.GF2n.Stroth80.Sec108SLComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem Sec108Data.phiMat_eq_zero_of_mem_Q (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {q : G} (hq : q ∈ Q) :
    D.phiMat AM ⟨q, hc.Q_le_H0 hq⟩ = 0 := by
  have h1 : AM.φ ⟨q, hc.Q_le_H0 hq⟩ = 1 := (AM.φ_ker _).mpr hq
  ext i j
  rw [D.phiMat_apply, h1, LinearEquiv.coe_one, id_eq, sub_self, map_zero, Matrix.zero_apply]

private theorem Sec108Data.matV_phiMat_conj_eq_of_comm (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {l n : G} (hl : l ∈ LB M Q B)
    (hn : n ∈ hc.CN t) (hq : ⁅l, n⁆ ∈ Q) :
    D.matV AM ⟨l, hc.LB_le_H0 hl⟩ * D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ *
      (D.matV AM ⟨l, hc.LB_le_H0 hl⟩)ᵀ = D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ := by
  have hmR : l ∈ Rt M (LB M Q B) t :=
    le_Rt (M := M) (LB M Q B) D.good.1.mem_LB hl
  have hLt : ⁅l, t⁆ ∈ Q :=
    Subgroup.commutator_le.mp hc.commutator_LB_le_Q l hl t D.good.1.mem_LB
  have hr : ∀ e, AM.φ ⟨l, hc.LB_le_H0 hl⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨l, hc.LB_le_H0 hl⟩ e) :=
    Sec108Data.phi_comm_of_comm_mem AM (m := ⟨l, hc.LB_le_H0 hl⟩)
      (m' := ⟨t, D.t_mem_H0⟩) hLt
  have hA : ∀ j, AM.φ ⟨l, hc.LB_le_H0 hl⟩ (D.bV AM j) =
      ∑ i, D.matV AM ⟨l, hc.LB_le_H0 hl⟩ i j • (D.bV AM i : AM.M₀.E) :=
    fun j => D.phi_bV_eq_sum AM (m := ⟨l, hc.LB_le_H0 hl⟩)
      (fun e he => D.phi_mem_Vsp AM (m := ⟨l, hc.LB_le_H0 hl⟩) hmR he) j
  have hV : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨n, D.CN_le_H0 hn⟩ e = e :=
    fun e he => D.fix_Vsp_of_mem_CN AM hn he
  have ht : ∀ e, AM.φ ⟨n, D.CN_le_H0 hn⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨n, D.CN_le_H0 hn⟩ e) :=
    fun e => D.comm_t_of_mem_CN AM hn e
  have hconj := D.phiMat_conj AM (m := ⟨n, D.CN_le_H0 hn⟩) (r := ⟨l, hc.LB_le_H0 hl⟩)
    (A := D.matV AM ⟨l, hc.LB_le_H0 hl⟩) hr hA hV ht
  have hconv : D.phiMat AM (⟨l, hc.LB_le_H0 hl⟩ * ⟨n, D.CN_le_H0 hn⟩ *
      (⟨l, hc.LB_le_H0 hl⟩)⁻¹) =
      D.phiMat AM (⟨⁅l, n⁆, hc.Q_le_H0 hq⟩ * ⟨n, D.CN_le_H0 hn⟩) := by
    congr 1
    ext
    show l * n * l⁻¹ = ⁅l, n⁆ * n
    rw [commutatorElement_def]
    group
  have hmul : D.phiMat AM (⟨⁅l, n⁆, hc.Q_le_H0 hq⟩ * ⟨n, D.CN_le_H0 hn⟩) =
      D.phiMat AM ⟨⁅l, n⁆, hc.Q_le_H0 hq⟩ + D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ :=
    D.phiMat_mul AM (m := ⟨⁅l, n⁆, hc.Q_le_H0 hq⟩) (m' := ⟨n, D.CN_le_H0 hn⟩)
      (fun e _ => by rw [(AM.φ_ker _).mpr hq]; rfl)
      (fun e he => D.fix_Vsp_of_mem_CN AM hn he) (D.comm_t_of_mem_CN AM hn)
  rw [hconv, hmul, D.phiMat_eq_zero_of_mem_Q AM (q := ⁅l, n⁆) hq, zero_add] at hconj
  exact hconj.symm

private theorem Sec108Data.smul_dotProduct_axis_eq_zero (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β μ : Fin 3 → AM.K}
    {l n : G} (hl : l ∈ LB M Q B) (hn : n ∈ hc.CN t) (hμ : μ ⬝ᵥ β = 0)
    (hmatV : D.matV AM ⟨l, hc.LB_le_H0 hl⟩ = 1 + Matrix.vecMulVec β μ)
    (hq : ⁅l, n⁆ ∈ Q) :
    (![D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 2 1, D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 0 2,
      D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 1 0] ⬝ᵥ β) • μ = 0 := by
  set a : Fin 3 → AM.K := ![D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 2 1,
    D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 0 2, D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 1 0]
  have htrans : (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩)ᵀ = -(D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) := by
    rw [D.phiMat_transpose AM (m := ⟨n, D.CN_le_H0 hn⟩)
      (fun e he => D.fix_Vsp_of_mem_CN AM hn he) (fun e => D.comm_t_of_mem_CN AM hn e),
      CharTwo.neg_eq]
  have hS : D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ = CFSG.LinearAlgebra.crossMatrix a :=
    CFSG.LinearAlgebra.eq_crossMatrix htrans (fun i => D.phiMat_diag AM hn i)
  have hconj := D.matV_phiMat_conj_eq_of_comm AM hl hn hq
  rw [hmatV, hS, CFSG.LinearAlgebra.one_add_vecMulVec_mul_crossMatrix (β := β) (l := μ)
    (a := a), hμ, zero_smul, add_zero] at hconj
  have hsub : CFSG.LinearAlgebra.crossMatrix (a - (a - (β ⬝ᵥ a) • μ)) =
      CFSG.LinearAlgebra.crossMatrix a - CFSG.LinearAlgebra.crossMatrix (a - (β ⬝ᵥ a) • μ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CFSG.LinearAlgebra.crossMatrix] <;> ring
  have hzero : CFSG.LinearAlgebra.crossMatrix (a - (a - (β ⬝ᵥ a) • μ)) = 0 := by
    rw [hsub, hconj, sub_self]
  have hcancel : a - (a - (β ⬝ᵥ a) • μ) = 0 :=
    (CFSG.LinearAlgebra.crossMatrix_eq_zero_iff _).mp hzero
  have hcμ : (β ⬝ᵥ a) • μ = 0 := by
    have h : a - (a - (β ⬝ᵥ a) • μ) = (β ⬝ᵥ a) • μ := by abel
    rwa [h] at hcancel
  rwa [dotProduct_comm]

private theorem Sec108Data.sq_mem_Q_of_mem_CN (D : Sec108Data hc t Y) {n : G}
    (hn : n ∈ hc.CN t) : n ^ 2 ∈ Q := by
  haveI := hc.normal_Q_in_M
  have hnM : n ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hn).1
  have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨n, hnM⟩ ∈ bar M Q (hc.CN t) :=
    Subgroup.mem_map_of_mem _ hn
  have h2 : (QuotientGroup.mk' (Q.subgroupOf M) ⟨n, hnM⟩) ^ 2 = 1 :=
    D.isElemAbelian_bar_CN.2 _ hmem
  rw [← map_pow] at h2
  have h3 := (QuotientGroup.eq_one_iff _).mp h2
  simpa [Subgroup.mem_subgroupOf] using h3

private theorem Sec108Data.mem_CN_of_matV_eq_one (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {l : G} (hl : l ∈ LB M Q B)
    (hmatV : D.matV AM ⟨l, hc.LB_le_H0 hl⟩ = 1) : l ∈ hc.CN t := by
  have hmR : l ∈ Rt M (LB M Q B) t :=
    le_Rt (M := M) (LB M Q B) D.good.1.mem_LB hl
  have hpres : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨l, hc.LB_le_H0 hl⟩ e ∈ AM.Vsp hc t :=
    fun e he => D.phi_mem_Vsp AM (m := ⟨l, hc.LB_le_H0 hl⟩) hmR he
  have hfix : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨l, hc.LB_le_H0 hl⟩ e = e :=
    (D.matV_eq_one_iff AM (m := ⟨l, hc.LB_le_H0 hl⟩) hpres).mp hmatV
  rw [Ctx.mem_CN]
  exact ⟨hmR, Ctx.comm_Vt_of_fix hc AM (hc.LB_le_H0 hl) hfix⟩

private theorem Sec108Data.exists_mul_of_mem_sup (D : Sec108Data hc t Y) {x : G}
    (hx : x ∈ hc.CN t ⊔ LB M Q B) :
    ∃ l ∈ LB M Q B, ∃ n ∈ hc.CN t, l * n = x := by
  have hnorm : LB M Q B ≤ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
    fun l hl => Subgroup.mem_normalizer_fintype fun n hn =>
      D.conj_mem_CN (le_Rt (M := M) (LB M Q B) D.good.1.mem_LB hl) hn
  have hmem : x ∈ ((LB M Q B ⊔ hc.CN t : Subgroup G) : Set G) := by
    rwa [sup_comm]
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (LB M Q B) (hc.CN t) hnorm] at hmem
  obtain ⟨l, hl, n, hn, hln⟩ := Set.mem_mul.mp hmem
  exact ⟨l, hl, n, hn, hln⟩

private noncomputable def Sec108Data.phiMatLB (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : AddSubgroup (Matrix (Fin 3) (Fin 3) AM.K) :=
  Subgroup.toAddSubgroup' (((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM))

private theorem Sec108Data.mem_phiMatLB (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {A : Matrix (Fin 3) (Fin 3) AM.K} :
    A ∈ D.phiMatLB AM ↔
      Multiplicative.ofAdd A ∈ ((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM) :=
  Subgroup.mem_toAddSubgroup' _ A

private theorem Sec108Data.phiMatLB_isAlt (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ∀ A ∈ D.phiMatLB AM, Aᵀ = -A ∧ ∀ i, A i i = 0 := by
  intro A hA
  rw [D.mem_phiMatLB AM] at hA
  obtain ⟨n, -, hphi⟩ := Subgroup.mem_map.mp hA
  have hAeq : A = D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ := by
    have h := D.phiHom_apply AM n
    rw [hphi, toAdd_ofAdd] at h
    exact h
  subst hAeq
  refine ⟨?_, fun i => D.phiMat_diag AM n.2 i⟩
  rw [D.phiMat_transpose AM (m := ⟨n, D.CN_le_H0 n.2⟩)
    (fun e he => D.fix_Vsp_of_mem_CN AM n.2 he) (fun e => D.comm_t_of_mem_CN AM n.2 e),
    CharTwo.neg_eq]

private theorem Sec108Data.card_phiMatLB (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Nat.card AM.K < Nat.card ↥(D.phiMatLB AM) := by
  have hcardT : Nat.card ↥(((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM)) =
      Nat.card Z ^ 2 := D.card_map_phiHom_LB AM
  have hcardS : Nat.card ↥(D.phiMatLB AM) = Nat.card Z ^ 2 := by
    calc Nat.card ↥(D.phiMatLB AM) =
        Nat.card ↥(((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM)) := Nat.card_congr
          { toFun := fun A => ⟨Multiplicative.ofAdd (A : Matrix (Fin 3) (Fin 3) AM.K),
              (D.mem_phiMatLB AM).mp A.2⟩
            invFun := fun m => ⟨Multiplicative.toAdd
                (m : Multiplicative (Matrix (Fin 3) (Fin 3) AM.K)),
              (D.mem_phiMatLB AM).mpr (by simpa using m.2)⟩
            left_inv := fun A => by ext; simp
            right_inv := fun m => by ext; simp }
      _ = Nat.card Z ^ 2 := hcardT
  rw [hcardS, AM.glob.card]
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  calc Nat.card Z = Nat.card Z * 1 := (mul_one _).symm
    _ < Nat.card Z * Nat.card Z := Nat.mul_lt_mul_of_pos_left hq Nat.card_pos
    _ = Nat.card Z ^ 2 := (pow_two _).symm

private theorem Sec108Data.phiMatLB_mulVec_eq_zero (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {e : AM.M₀.E} {w : Fin 3 → AM.K}
    (he : ∀ n (hn : n ∈ LB M Q B ⊓ hc.CN t), AM.φ ⟨n, hc.LB_le_H0 hn.1⟩ e = e)
    (hw : e - ∑ j, w j • D.nu AM (D.eV AM j) ∈ AM.Vsp hc t) :
    ∀ A ∈ D.phiMatLB AM, A *ᵥ w = 0 := by
  intro A hA
  rw [D.mem_phiMatLB AM] at hA
  obtain ⟨n, hn, hphi⟩ := Subgroup.mem_map.mp hA
  have hnLB : (n : G) ∈ LB M Q B := hn
  have hnCN : (n : G) ∈ hc.CN t := n.2
  have hAeq : A = D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ := by
    have h := D.phiHom_apply AM n
    rw [hphi, toAdd_ofAdd] at h
    exact h
  subst hAeq
  set q : AM.M₀.E := ∑ j, w j • D.nu AM (D.eV AM j)
  have hfixE : AM.φ ⟨n, D.CN_le_H0 n.2⟩ e = e := by
    have h := he (n : G) ⟨hnLB, hnCN⟩
    convert h using 1
  have hfixq : AM.φ ⟨n, D.CN_le_H0 n.2⟩ q = q := by
    have hsplit : (e - q) + q = e := by abel
    have hfixsub : AM.φ ⟨n, D.CN_le_H0 n.2⟩ (e - q) = e - q :=
      D.fix_Vsp_of_mem_CN AM n.2 hw
    have h1 : AM.φ ⟨n, D.CN_le_H0 n.2⟩ (e - q) + AM.φ ⟨n, D.CN_le_H0 n.2⟩ q = e := by
      rw [← map_add, hsplit, hfixE]
    have h2 : (e - q) + AM.φ ⟨n, D.CN_le_H0 n.2⟩ q = e := by
      rw [← hfixsub]
      exact h1
    have h3 : (e - q) + AM.φ ⟨n, D.CN_le_H0 n.2⟩ q = (e - q) + q := by
      rw [h2, hsplit]
    exact add_left_cancel h3
  exact (D.phiMat_mulVec_eq_zero_iff AM (m := ⟨n, D.CN_le_H0 n.2⟩)
    (fun e he => D.fix_Vsp_of_mem_CN AM n.2 he) (fun e => D.comm_t_of_mem_CN AM n.2 e) w).mpr
    hfixq

private theorem Sec108Data.nu_eq_zero_of_fix (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {e : AM.M₀.E}
    (he : ∀ n (hn : n ∈ LB M Q B ⊓ hc.CN t), AM.φ ⟨n, hc.LB_le_H0 hn.1⟩ e = e) :
    D.nu AM e = 0 := by
  obtain ⟨y, hy, hyeq⟩ := D.exists_root_eq_smul AM 1
  have hyCN : y ∈ hc.CN t := by
    rw [D.CN_eq]
    obtain ⟨g, hg⟩ := D.sit.conj
    exact Subgroup.mem_sup_right
      ⟨IsZConjugate.le_QB_self hc.hyp ⟨g, hg⟩ hy, ((smith_1_12 D.sit).1 hy).1⟩
  have hyfix : AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ e = e :=
    he y ⟨D.root_le_LB hy, hyCN⟩
  have h' : (AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) e =
      e + D.nu AM e := by
    have h := LinearMap.congr_fun hyeq e
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, one_smul, LinearMap.id_apply] using h
  have hsum : e = e + D.nu AM e := by
    calc e = AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ e := hyfix.symm
      _ = e + D.nu AM e := h'
  exact add_left_cancel (by rw [add_zero]; exact hsum.symm)

theorem Sec108Data.mem_Vsp_of_fix (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {e : AM.M₀.E} (he : ∀ n (hn : n ∈ LB M Q B ⊓ hc.CN t), AM.φ ⟨n, hc.LB_le_H0 hn.1⟩ e = e) :
    e ∈ AM.Vsp hc t := by
  have heU : e ∈ LinearMap.range (D.nu AM) := by
    rw [D.range_nu_eq_ker AM]
    exact LinearMap.mem_ker.mpr (D.nu_eq_zero_of_fix AM he)
  obtain ⟨w, hw⟩ := D.exists_coord AM heU
  have hw0 : w = 0 :=
    CFSG.LinearAlgebra.eq_zero_of_forall_alternating_mulVec_eq_zero (D.phiMatLB AM)
      (D.phiMatLB_isAlt AM) (D.card_phiMatLB AM) (D.phiMatLB_mulVec_eq_zero AM he hw)
  have hq0 : (∑ j, w j • D.nu AM (D.eV AM j)) = 0 := by simp [hw0]
  rw [hq0] at hw
  simpa using hw

theorem Sec108Data.comm_mem_Q_iff_of_not_mem_LB (D : Sec108Data hc t Y) {n l : G}
    (hn : n ∈ hc.CN t) (hnB : n ∉ LB M Q B) (hl : l ∈ LB M Q B) :
    ⁅l, n⁆ ∈ Q ↔ l ∈ hc.CN t := by
  constructor
  · intro hq
    obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
    obtain ⟨β, hβ, hβB⟩ := D.exists_coord_Bsp AM
    obtain ⟨μ, hμ, hmatV⟩ := D.exists_matV_LB AM hβ hβB hl
    have hsmul := D.smul_dotProduct_axis_eq_zero AM hl hn hμ hmatV hq
    by_cases hμ0 : μ = 0
    · exact D.mem_CN_of_matV_eq_one AM hl
        (by rw [hmatV, hμ0, Matrix.vecMulVec_zero, add_zero])
    · exfalso
      have hc0 : ![D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 2 1, D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 0 2,
          D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 1 0] ⬝ᵥ β = 0 := by
        rcases smul_eq_zero.mp hsmul with h | h
        · exact h
        · exact absurd h hμ0
      exact hnB ((D.mem_LB_iff_dotProduct AM (β := β) hβ hβB hn).mpr hc0)
  · intro hlCN
    exact D.comm_CN_mem hlCN hn

theorem Sec108Data.mem_or_mem_of_sq_mem (D : Sec108Data hc t Y) {x : G}
    (hx : x ∈ hc.CN t ⊔ LB M Q B) (h2 : x ^ 2 ∈ Q) : x ∈ hc.CN t ∨ x ∈ LB M Q B := by
  obtain ⟨l, hl, n, hn, hln⟩ := D.exists_mul_of_mem_sup hx
  have hl2 : l ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB hl
  have hn2 : n ^ 2 ∈ Q := D.sq_mem_Q_of_mem_CN hn
  have hx2 : (l * n) ^ 2 ∈ Q := by rw [hln]; exact h2
  have hcomm : ⁅l, n⁆ ∈ Q := by
    have hconj : l * ⁅n, l⁆ * l⁻¹ ∈ Q := by
      have hAB : (l * n) ^ 2 = (l * ⁅n, l⁆ * l⁻¹) * (l ^ 2 * n ^ 2) := by
        rw [pow_two, commutatorElement_def]
        group
      have hB : l ^ 2 * n ^ 2 ∈ Q := Q.mul_mem hl2 hn2
      have hprod : (l * ⁅n, l⁆ * l⁻¹) * (l ^ 2 * n ^ 2) ∈ Q := by rwa [hAB] at hx2
      have hA := Q.mul_mem hprod (Q.inv_mem hB)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at hA
    have hnorm : l⁻¹ ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ (hc.hyp.Q_normal.2 (hc.LB_le_M hl))
    have h := (Subgroup.mem_normalizer_iff.mp hnorm (l * ⁅n, l⁆ * l⁻¹)).mp hconj
    rw [inv_inv] at h
    have hnl : ⁅n, l⁆ ∈ Q := by
      rwa [show l⁻¹ * (l * ⁅n, l⁆ * l⁻¹) * l = ⁅n, l⁆ by group] at h
    have := Q.inv_mem hnl
    rwa [commutatorElement_inv] at this
  by_cases hnLB : n ∈ LB M Q B
  · exact Or.inr (hln ▸ (LB M Q B).mul_mem hl hnLB)
  · exact Or.inl (hln ▸ (hc.CN t).mul_mem
      ((D.comm_mem_Q_iff_of_not_mem_LB hn hnLB hl).mp hcomm) hn)

end CFSG.RankThree.GF2n.Stroth80

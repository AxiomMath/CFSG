module

public import CFSG.Quasithin.MS93.S5Q2X52Coc
public import CFSG.Quasithin.MS93.S5Q2Par

public noncomputable section

namespace CFSG.Quasithin.MS93.S5Q2.X52

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Perm

variable {F : Type} [Field F] (c : ZMod 2 ≃+* F)

abbrev ee (i : Fin 6) : Fin 6 → ZMod 2 := Pi.single i 1

@[expose] def xi (x : Fin 6 → ZMod 2) : MSP.V4 F := B5FinSp.lfun c (B5FinSp.chi x)

theorem xi_add (x y : Fin 6 → ZMod 2) : xi c (x + y) = xi c x + xi c y := by
  rw [xi, xi, xi, B5FinSp.chi_add, B5FinSp.lfun_add]

theorem xi_perm (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0) :
    xi c (fun i => x (σ⁻¹ i)) = MSP.mat (B5FinSp.theta c σ) *ᵥ xi c x := by
  have h1 := B5FinSp.chi_permute (B5FinSp.omegaEquiv.symm σ) x hx
  rw [← B5FinSp.omegaEquiv_apply, MulEquiv.apply_symm_apply] at h1
  rw [xi, xi, h1]
  exact (B5FinSp.theta_mulVec_lfun c σ (B5FinSp.chi x)).symm

theorem perm_ee (σ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    (fun j => ee i (σ⁻¹ j)) = ee (σ i) := by
  funext j
  by_cases h : j = σ i
  · subst h
    simp [ee]
  · have h' : σ.symm j ≠ i := fun h' => h (by rw [← h']; simp)
    simp [ee, h', h]

theorem sum_ee_add (i j : Fin 6) : ∑ k, (ee i + ee j) k = 0 := by
  revert i j
  decide

theorem xi_ee_add_ne_zero {i j : Fin 6} (hij : i ≠ j) : xi c (ee i + ee j) ≠ 0 := by
  intro h0
  have h1 : B5FinSp.chi (ee i + ee j) = 0 := B5FinSp.lfun_injective c (by
    rw [← xi, h0]
    funext a
    simp [B5FinSp.lfun])
  have key : ∀ i j : Fin 6, i ≠ j → B5FinSp.chi (ee i + ee j) ≠ 0 := by decide
  exact key i j hij h1

@[expose] def psi (σ : Equiv.Perm (Fin 6)) : MSP.V4 F := xi c (ee 0 + ee (σ 0))

theorem psi_mul (σ τ : Equiv.Perm (Fin 6)) :
    psi c (σ * τ) = psi c σ + MSP.mat (B5FinSp.theta c σ) *ᵥ psi c τ := by
  unfold psi
  have hτ := xi_perm c σ (ee 0 + ee (τ 0)) (sum_ee_add 0 (τ 0))
  have e1 : (fun j => (ee 0 + ee (τ 0)) (σ⁻¹ j)) = ee (σ 0) + ee (σ (τ 0)) := by
    funext j
    simp only [Pi.add_apply]
    rw [← congrFun (perm_ee σ 0) j, ← congrFun (perm_ee σ (τ 0)) j]
  rw [e1] at hτ
  rw [← hτ, ← xi_add]
  congr 1
  funext j
  simp only [Pi.add_apply, Equiv.Perm.coe_mul, Function.comp_apply]
  have h2 : ∀ p q r : ZMod 2, p + r = p + q + (q + r) := by decide
  exact h2 _ _ _

@[expose] def psiSp (g : MSP.Sp4 F) : MSP.V4 F := psi c ((B5FinSp.theta c).symm g)

theorem psiSp_mul (g g' : MSP.Sp4 F) :
    psiSp c (g * g') = psiSp c g + MSP.mat g *ᵥ psiSp c g' := by
  unfold psiSp
  rw [map_mul, psi_mul, MulEquiv.apply_symm_apply]

theorem xi_zero : xi c 0 = 0 := by
  have h0 : B5FinSp.chi (0 : Fin 6 → ZMod 2) = 0 := by decide
  rw [xi, h0]
  funext a
  simp [B5FinSp.lfun]

theorem xi_one : xi c (fun _ => 1) = 0 := by
  rw [xi, B5FinSp.chi_const]
  funext a
  simp [B5FinSp.lfun]

theorem psi_not_cob [CharP F 2] (m : MSP.V4 F) :
    ∃ σ, psi c σ ≠ MSP.mat (B5FinSp.theta c σ) *ᵥ m - m := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, rfl⟩ : ∃ y : Fin 6 → ZMod 2, ∑ i, y i = 0 ∧ xi c y = m := by
    obtain ⟨v, rfl⟩ := B5FinSp.lfun_surjective c m
    exact ⟨B5FinSp.phi v, B5FinSp.sum_phi v, by rw [xi, B5FinSp.chi_phi]⟩
  have hsw : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 →
      ((fun k => y (Equiv.swap i j k)) + y = 0 ∨ (fun k => y (Equiv.swap i j k)) + y =
        fun _ => 1) := by
    intro i j hi hj
    have h1 := hcon (Equiv.swap i j)
    have h0 : psi c (Equiv.swap i j) = 0 := by
      rw [psi, Equiv.swap_apply_of_ne_of_ne hi.symm hj.symm]
      have : ee 0 + ee 0 = 0 := by
        funext k
        exact CharTwo.add_self_eq_zero _
      rw [this, xi_zero]
    rw [h0, ← xi_perm c _ y hy, eq_comm, sub_eq_zero] at h1
    have h2 : xi c ((fun k => y ((Equiv.swap i j)⁻¹ k)) + y) = 0 := by
      rw [xi_add, h1]
      exact CharTwo.add_self_eq_zero _
    simp only [Equiv.swap_inv] at h2
    have h3 : B5FinSp.chi ((fun k => y (Equiv.swap i j k)) + y) = 0 :=
      B5FinSp.lfun_injective c (by rw [← xi, h2]; funext a; simp [B5FinSp.lfun])
    have heven : ∑ k, ((fun k => y (Equiv.swap i j k)) + y) k = 0 := by
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hy, add_zero]
      exact (Equiv.sum_comp (Equiv.swap i j) y).trans hy
    exact (B5FinSp.chi_eq_zero_iff _ heven).1 h3
  have key : ∀ y : Fin 6 → ZMod 2, ∑ i, y i = 0 →
      (∀ i j : Fin 6, i ≠ 0 → j ≠ 0 →
        ((fun k => y (Equiv.swap i j k)) + y = 0 ∨ (fun k => y (Equiv.swap i j k)) + y =
          fun _ => 1)) → y = 0 ∨ y = fun _ => 1 := by
    decide
  have hy01 := key y hy hsw
  have hm0 : xi c y = 0 := by
    rcases hy01 with rfl | rfl
    · exact xi_zero c
    · exact xi_one c
  have h01 := hcon (Equiv.swap 0 1)
  rw [hm0, Matrix.mulVec_zero, sub_zero, psi, Equiv.swap_apply_left] at h01
  exact xi_ee_add_ne_zero c (by decide) h01

theorem exists_eq_psiSp [Fintype F] [CharP F 2] (hF : Fintype.card F = 2)
    {φ : MSP.Sp4 F → MSP.V4 F} {B : F} (hB : B ≠ 0) {m₀ : MSP.V4 F}
    (hform : ∀ g, φ g = S5.cform B m₀ g) :
    ∃ m : MSP.V4 F, ∀ g, φ g = psiSp c g + (MSP.mat g *ᵥ m - m) := by
  obtain ⟨B', m', hB'⟩ := S5.exists_eq_sqf (k := 1) (by rw [hF, pow_one]) le_rfl (psiSp_mul c)
  have hB'0 : B' ≠ 0 := by
    intro h0
    obtain ⟨σ, hσ⟩ := psi_not_cob c m'
    apply hσ
    have := hB' (B5FinSp.theta c σ)
    rw [h0, zero_smul, zero_add] at this
    rw [← this]
    simp [psiSp]
  have hBB : B = B' := by
    rcases MSP.eq_zero_or_eq_one_of_ringEquiv c B with h | h
    · exact absurd h hB
    rcases MSP.eq_zero_or_eq_one_of_ringEquiv c B' with h' | h'
    · exact absurd h' hB'0
    rw [h, h']
  refine ⟨m₀ - m', fun g => ?_⟩
  rw [hform, hB' g, S5.cform, hBB, Matrix.mulVec_sub]
  abel

end Perm

section Ker

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commute_of_ker (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hC : Zq M L ≤ Subgroup.centralizer (M : Set G)) {n : G} (hn : n ∈ M)
    (hna : a ⟨n, hn⟩ = 1) {w : G} (hw : w ∈ xFix h) : n * w = w * n := by
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hκ : n ∈ S5.kerG a := (S5.mem_kerG a).2 ⟨hn, hna⟩
  have h0 := S5.uCoord_comm_kerG hd h nv hw.1 hw.2 hκ
  have hcC : ⁅n, w⁆ ∈ S5.cXL M L := mem_cXL_of_uCoord_eq_zero h nv (hw.2 n hn) h0
  set c := ⁅n, w⁆ with hc
  have hcn : ∀ j : ℕ, n ^ j * w * (n ^ j)⁻¹ = c ^ j * w := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcm : n ^ j * c = c * n ^ j :=
        (Subgroup.mem_centralizer_iff.1 (hC hcC) _ (M.pow_mem hn j))
      have e1 : n * w * n⁻¹ = c * w := by
        rw [hc, commutatorElement_def]
        group
      calc n ^ (j + 1) * w * (n ^ (j + 1))⁻¹ = n ^ j * (n * w * n⁻¹) * (n ^ j)⁻¹ := by group
        _ = n ^ j * c * w * (n ^ j)⁻¹ := by rw [e1]; group
        _ = c * (n ^ j * w * (n ^ j)⁻¹) := by rw [hcm]; group
        _ = c ^ (j + 1) * w := by rw [ih, pow_succ', mul_assoc]
  obtain ⟨s, o, ho, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  have h2 : (n ^ o) ^ 2 ^ s = 1 := by
    rw [← pow_mul, mul_comm, ← hN, pow_orderOf_eq_one]
  have hno : n ^ o ∈ pCoreOf 2 M := by
    have hna' : a ⟨n ^ o, M.pow_mem hn o⟩ = 1 := by
      have : (⟨n ^ o, M.pow_mem hn o⟩ : ↥M) = ⟨n, hn⟩ ^ o := rfl
      rw [this, map_pow, hna, one_pow]
    exact S5B.mem_pCoreOf_of_ker h hd hna' ⟨s, h2⟩
  have hcomm : n ^ o * w = w * n ^ o := S5.commute_of_mem_pCoreOf hw.1 hno
  have hco : c ^ o = 1 := by
    have := hcn o
    rw [hcomm, mul_inv_cancel_right] at this
    exact (mul_eq_right.1 this.symm)
  have hc2 : c ^ 2 = 1 := S5Q2.sq_eq_one_of_mem_Xq hcC.1
  have hc1 : c = 1 := by
    obtain ⟨t, rfl⟩ := ho
    rw [pow_succ, pow_mul, hc2, one_pow, one_mul] at hco
    exact hco
  rw [hc, commutatorElement_eq_one_iff_mul_comm] at hc1
  exact hc1

end Ker

section Six

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem exists_six (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) (hne : Xq M ≠ Uq M T L ⊔ Zq M L) (c : ZMod 2 ≃+* F) :
    ∃ d : Fin 6 → G, (∀ i, d i ∈ xFix h) ∧
      (∀ (m : G) (hm : m ∈ M) (i : Fin 6),
        m * d i * m⁻¹ * (d ((B5FinSp.theta c).symm (a ⟨m, hm⟩) i))⁻¹ ∈ Zq M L) ∧
      ∀ i j, i ≠ j → d i * (d j)⁻¹ ∉ Zq M L := by
  have hF : Fintype.card F = 2 := by simpa using hd.card_eq
  have : CharP F 2 := hd.charP
  obtain ⟨nv⟩ := hd.nonempty_natVec
  obtain ⟨x, hx, hxN⟩ := exists_mem_xFix_not_mem h hXL hne
  obtain ⟨B, m₀, hB, hform⟩ := exists_cform_of_mem_xFix hd h nv hx hxN
  obtain ⟨m'', hm''⟩ := exists_eq_psiSp c hF hB hform
  set w : Fin 6 → MSP.V4 F := fun i => xi c (ee 0 + ee i) + m'' with hw
  choose u hu using fun i => nv.surj (Multiplicative.ofAdd (w i))
  have hvu : ∀ i, nv.vec (u i) = w i := fun i => by rw [S5.NatVec.vec, hu i]; rfl
  have hv2 : ∀ v : MSP.V4 F, v + v = 0 := S5.v4_add_self
  refine ⟨fun i => x * u i, fun i => (xFix h).mul_mem hx (uq_le_xFix h (u i).2), ?_, ?_⟩
  · intro m hm i
    set σ := (B5FinSp.theta c).symm (a ⟨m, hm⟩) with hσ
    have haσ : a ⟨m, hm⟩ = B5FinSp.theta c σ := by rw [hσ, MulEquiv.apply_symm_apply]
    have hux := (uq_le_xFix h (u i).2).2 m hm
    have hcx := hx.2 m hm
    have e1 : m * (x * u i) * m⁻¹ * (x * u (σ i))⁻¹ =
        (⁅m, x⁆ * ⁅m, (u i : G)⁆) * ((u i : G) * (u (σ i) : G)⁻¹) := by
      have hc : ⁅m, x * u i⁆ = ⁅m, x⁆ * ⁅m, (u i : G)⁆ :=
        comm_mul_eq hx.1 (uq_sup_cXL_le_xq h hux)
      have hxu : (u (σ i) : G)⁻¹ * x⁻¹ = x⁻¹ * (u (σ i) : G)⁻¹ :=
        S5.commute_of_mem_Xq ((Xq M).inv_mem (h.Uq_le_Xq (u (σ i)).2)) ((Xq M).inv_mem hx.1)
      have hxu' : x * (u i : G) = (u i : G) * x :=
        S5.commute_of_mem_Xq hx.1 (h.Uq_le_Xq (u i).2)
      calc m * (x * u i) * m⁻¹ * (x * u (σ i))⁻¹ = ⁅m, x * u i⁆ * (x * u i) *
            ((u (σ i) : G)⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
        _ = ⁅m, x * u i⁆ * (x * u i) * (x⁻¹ * (u (σ i) : G)⁻¹) := by rw [hxu]
        _ = ⁅m, x * u i⁆ * ((u i : G) * x) * (x⁻¹ * (u (σ i) : G)⁻¹) := by rw [hxu']
        _ = ⁅m, x * u i⁆ * ((u i : G) * (u (σ i) : G)⁻¹) := by group
        _ = _ := by rw [hc]
    rw [e1]
    have hN1 : ⁅m, x⁆ * ⁅m, (u i : G)⁆ ∈ Uq M T L ⊔ S5.cXL M L := mul_mem hcx hux
    have hU2 : (u i : G) * (u (σ i) : G)⁻¹ ∈ Uq M T L := mul_mem (u i).2 (inv_mem (u (σ i)).2)
    refine mem_cXL_of_uCoord_eq_zero h nv (mul_mem hN1 (Subgroup.mem_sup_left hU2)) ?_
    rw [uCoord_mul_of_mem h nv hN1 (Subgroup.mem_sup_left hU2),
      uCoord_mul_of_mem h nv hcx hux, ← S5.cocSp_a hd h nv hx.1 hx.2 hm, hm'',
      uCoord_comm_uq h nv hm (u i)]
    have hU2' : S5.uCoord nv ((u i : G) * (u (σ i) : G)⁻¹) = w i - w (σ i) := by
      have := S5.uCoord_mul nv hU2 (S5.cXL M L).one_mem
      rw [mul_one] at this
      rw [this]
      have e2 : (⟨(u i : G) * (u (σ i) : G)⁻¹, hU2⟩ : ↥(Uq M T L)) = u i * (u (σ i))⁻¹ := rfl
      rw [e2, nv.vec_mul, nv.vec_inv, hvu, hvu, sub_eq_add_neg]
    rw [hU2', hvu, haσ]
    have hpsi : psiSp c (B5FinSp.theta c σ) = xi c (ee 0 + ee (σ 0)) := by
      simp [psiSp, psi]
    have hperm := xi_perm c σ (ee 0 + ee i) (sum_ee_add 0 i)
    have e3 : (fun j => (ee 0 + ee i) (σ⁻¹ j)) = ee (σ 0) + ee (σ i) := by
      funext j
      simp only [Pi.add_apply]
      rw [← congrFun (perm_ee σ 0) j, ← congrFun (perm_ee σ i) j]
    rw [e3] at hperm
    have hX : xi c (ee 0 + ee (σ 0)) + xi c (ee (σ 0) + ee (σ i)) = xi c (ee 0 + ee (σ i)) := by
      rw [← xi_add]
      congr 1
      funext j
      simp only [Pi.add_apply]
      have h3 : ∀ p q r : ZMod 2, p + q + (q + r) = p + r := by decide
      exact h3 _ _ _
    rw [hpsi, hw]
    simp only
    rw [Matrix.mulVec_add, ← hperm]
    linear_combination hX + hv2 (MSP.mat (B5FinSp.theta c σ) *ᵥ m'') - hv2 m''
  · intro i j hij hZ
    have e : x * u i * (x * u j)⁻¹ = (u i : G) * (u j : G)⁻¹ := by
      have hxu : (u j : G)⁻¹ * x⁻¹ = x⁻¹ * (u j : G)⁻¹ :=
        S5.commute_of_mem_Xq ((Xq M).inv_mem (h.Uq_le_Xq (u j).2)) ((Xq M).inv_mem hx.1)
      calc x * u i * (x * u j)⁻¹ = x * u i * ((u j : G)⁻¹ * x⁻¹) := by group
        _ = x * u i * (x⁻¹ * (u j : G)⁻¹) := by rw [hxu]
        _ = x * ((u i : G) * x⁻¹) * (u j : G)⁻¹ := by group
        _ = x * (x⁻¹ * (u i : G)) * (u j : G)⁻¹ := by
          rw [S5.commute_of_mem_Xq (h.Uq_le_Xq (u i).2) ((Xq M).inv_mem hx.1)]
        _ = _ := by group
    rw [e] at hZ
    have hv : nv.vec (u i * (u j)⁻¹) = 0 := (nv.vec_eq_zero_iff _).2 hZ.2
    rw [nv.vec_mul, nv.vec_inv, hvu, hvu, hw] at hv
    simp only at hv
    have h0 : xi c (ee i + ee j) = 0 := by
      have e4 : ee i + ee j = (ee 0 + ee i) + (ee 0 + ee j) := by
        funext k
        simp only [Pi.add_apply]
        have h3 : ∀ p q r : ZMod 2, q + r = p + q + (p + r) := by decide
        exact h3 _ _ _
      rw [e4, xi_add]
      linear_combination hv + hv2 (xi c (ee 0 + ee j))
    exact xi_ee_add_ne_zero c hij h0

variable (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
  (hC : Zq M L ≤ Subgroup.centralizer (M : Set G)) (c : ZMod 2 ≃+* F) {d : Fin 6 → G}
  (hdX : ∀ i, d i ∈ xFix h)
  (hconj : ∀ (m : G) (hm : m ∈ M) (i : Fin 6),
    m * d i * m⁻¹ * (d ((B5FinSp.theta c).symm (a ⟨m, hm⟩) i))⁻¹ ∈ Zq M L)
include h hd hC hdX hconj

theorem commute_of_swap {k₀ : G} (hk₀ : k₀ ∈ M) {a₀ b₀ i₀ : Fin 6} (hab : a₀ ≠ b₀)
    (hia : i₀ ≠ a₀) (hib : i₀ ≠ b₀)
    (hk₀a : (B5FinSp.theta c).symm (a ⟨k₀, hk₀⟩) = Equiv.swap a₀ b₀)
    (hk₀d : k₀ * d i₀ = d i₀ * k₀) {m : G} (hm : m ∈ M) {a' b' i : Fin 6} (hab' : a' ≠ b')
    (hia' : i ≠ a') (hib' : i ≠ b')
    (hma : (B5FinSp.theta c).symm (a ⟨m, hm⟩) = Equiv.swap a' b') : m * d i = d i * m := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair ![a₀, b₀, i₀] ![a', b', i]
    (by
      intro p q hpq
      fin_cases p <;> fin_cases q <;> simp_all [eq_comm])
    (by
      intro p q hpq
      fin_cases p <;> fin_cases q <;> simp_all [eq_comm])
  have hπa : π a₀ = a' := hπ 0
  have hπb : π b₀ = b' := hπ 1
  have hπi : π i₀ = i := hπ 2
  obtain ⟨⟨g, hgM⟩, hg⟩ := hd.2.2.1 (B5FinSp.theta c π)
  have hgi : g⁻¹ ∈ M := M.inv_mem hgM
  set k' := g * k₀ * g⁻¹ with hk'
  have hk'M : k' ∈ M := M.mul_mem (M.mul_mem hgM hk₀) hgi
  have hk'a : a ⟨k', hk'M⟩ = a ⟨m, hm⟩ := by
    have e : (⟨k', hk'M⟩ : ↥M) = ⟨g, hgM⟩ * ⟨k₀, hk₀⟩ * (⟨g, hgM⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hg, ← (B5FinSp.theta c).apply_symm_apply (a ⟨k₀, hk₀⟩),
      hk₀a, ← (B5FinSp.theta c).apply_symm_apply (a ⟨m, hm⟩), hma, ← map_inv, ← map_mul,
      ← map_mul, ← Equiv.swap_apply_apply, hπa, hπb]
  have hz := hconj g⁻¹ hgi i
  have hσg : (B5FinSp.theta c).symm (a ⟨g⁻¹, hgi⟩) = π⁻¹ := by
    have e : (⟨g⁻¹, hgi⟩ : ↥M) = (⟨g, hgM⟩)⁻¹ := rfl
    rw [e, map_inv, hg, ← map_inv, MulEquiv.symm_apply_apply]
  have hπi' : π⁻¹ i = i₀ := by rw [← hπi]; simp
  rw [hσg, hπi'] at hz
  set z := g⁻¹ * d i * g⁻¹⁻¹ * (d i₀)⁻¹ with hzdef
  have hzk : k₀ * z = z * k₀ := Subgroup.mem_centralizer_iff.1 (hC hz) k₀ hk₀
  have hgd : g⁻¹ * d i * g = z * d i₀ := by rw [hzdef]; group
  have hk'd : k' * d i = d i * k' := by
    have e1 : d i = g * (z * d i₀) * g⁻¹ := by rw [← hgd]; group
    rw [hk', e1]
    calc g * k₀ * g⁻¹ * (g * (z * d i₀) * g⁻¹) = g * (k₀ * z * d i₀) * g⁻¹ := by group
      _ = g * (z * (k₀ * d i₀)) * g⁻¹ := by rw [hzk]; group
      _ = g * (z * (d i₀ * k₀)) * g⁻¹ := by rw [hk₀d]
      _ = g * (z * d i₀) * g⁻¹ * (g * k₀ * g⁻¹) := by group
  have hn : k'⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hk'M) hm
  have hna : a ⟨k'⁻¹ * m, hn⟩ = 1 := by
    have e : (⟨k'⁻¹ * m, hn⟩ : ↥M) = (⟨k', hk'M⟩)⁻¹ * ⟨m, hm⟩ := rfl
    rw [e, map_mul, map_inv, hk'a, inv_mul_cancel]
  have hnd := commute_of_ker h hd hC hn hna (hdX i)
  calc m * d i = k' * (k'⁻¹ * m) * d i := by group
    _ = k' * (d i * (k'⁻¹ * m)) := by rw [mul_assoc, hnd]
    _ = d i * k' * (k'⁻¹ * m) := by rw [← mul_assoc, hk'd]
    _ = d i * m := by group

omit hconj in
theorem commute_of_fix
    (hsw : ∀ (m : G) (hm : m ∈ M) (a' b' i : Fin 6), a' ≠ b' → i ≠ a' → i ≠ b' →
      (B5FinSp.theta c).symm (a ⟨m, hm⟩) = Equiv.swap a' b' → m * d i = d i * m)
    {m : G} (hm : m ∈ M) {i : Fin 6} (hmi : (B5FinSp.theta c).symm (a ⟨m, hm⟩) i = i) :
    m * d i = d i * m := by
  set S : Set (Equiv.Perm (Fin 6)) := {τ | τ.IsSwap ∧ τ i = i} with hS
  have hSw : ∀ τ ∈ S, τ.IsSwap := fun τ hτ => hτ.1
  have hmem : (B5FinSp.theta c).symm (a ⟨m, hm⟩) ∈ Subgroup.closure S := by
    rw [mem_closure_isSwap hSw]
    refine ⟨Set.toFinite _, fun y => ?_⟩
    set σ := (B5FinSp.theta c).symm (a ⟨m, hm⟩)
    by_cases hy : σ y = y
    · rw [hy]
      exact MulAction.mem_orbit_self y
    · have hyi : y ≠ i := fun h' => hy (h' ▸ hmi)
      have hσyi : σ y ≠ i := fun h' => hyi (σ.injective (h'.trans hmi.symm))
      refine ⟨⟨Equiv.swap y (σ y), Subgroup.subset_closure ⟨⟨y, σ y, fun h' => hy h'.symm, rfl⟩,
        Equiv.swap_apply_of_ne_of_ne hyi.symm hσyi.symm⟩⟩, ?_⟩
      exact Equiv.swap_apply_left y (σ y)
  suffices key : ∀ τ ∈ Subgroup.closure S, ∀ (m : G) (hm : m ∈ M),
      (B5FinSp.theta c).symm (a ⟨m, hm⟩) = τ → m * d i = d i * m from key _ hmem m hm rfl
  intro τ hτ
  induction hτ using Subgroup.closure_induction with
  | mem τ hτ =>
    intro m hm hmτ
    obtain ⟨⟨a', b', hab', rfl⟩, hτi⟩ := hτ
    have hia' : i ≠ a' := fun h' => by
      rw [h', Equiv.swap_apply_left] at hτi
      exact hab' hτi.symm
    have hib' : i ≠ b' := fun h' => by
      rw [h', Equiv.swap_apply_right] at hτi
      exact hab' hτi
    exact hsw m hm a' b' i hab' hia' hib' hmτ
  | one =>
    intro m hm hm1
    have hna : a ⟨m, hm⟩ = 1 := by
      rw [← (B5FinSp.theta c).apply_symm_apply (a ⟨m, hm⟩), hm1, map_one]
    exact commute_of_ker h hd hC hm hna (hdX i)
  | mul τ₁ τ₂ _ _ ih₁ ih₂ =>
    intro m hm hmτ
    obtain ⟨⟨m₁, hm₁⟩, hm₁a⟩ := hd.2.2.1 (B5FinSp.theta c τ₁)
    have hm₂ : m₁⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hm₁) hm
    have h1 := ih₁ m₁ hm₁ (by rw [hm₁a, MulEquiv.symm_apply_apply])
    have h2 := ih₂ (m₁⁻¹ * m) hm₂ (by
      have e : (⟨m₁⁻¹ * m, hm₂⟩ : ↥M) = (⟨m₁, hm₁⟩)⁻¹ * ⟨m, hm⟩ := rfl
      rw [e, map_mul, map_inv, map_mul, map_inv, hm₁a, MulEquiv.symm_apply_apply, hmτ]
      group)
    calc m * d i = m₁ * ((m₁⁻¹ * m) * d i) := by group
      _ = m₁ * (d i * (m₁⁻¹ * m)) := by rw [h2]
      _ = (m₁ * d i) * (m₁⁻¹ * m) := by group
      _ = d i * m₁ * (m₁⁻¹ * m) := by rw [h1]
      _ = d i * m := by group
  | inv τ _ ih =>
    intro m hm hmτ
    have hmi' : m⁻¹ ∈ M := M.inv_mem hm
    have h1 := ih m⁻¹ hmi' (by
      have e : (⟨m⁻¹, hmi'⟩ : ↥M) = (⟨m, hm⟩)⁻¹ := rfl
      rw [e, map_inv, map_inv, hmτ, inv_inv])
    calc m * d i = m * (d i * m⁻¹) * m := by group
      _ = m * (m⁻¹ * d i) * m := by rw [h1]
      _ = d i * m := by group

end Six

end CFSG.Quasithin.MS93.S5Q2.X52

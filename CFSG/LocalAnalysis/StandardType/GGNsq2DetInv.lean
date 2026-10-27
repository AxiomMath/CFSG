module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGNsq2Det
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux3
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1Aux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

section DetInv

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}

theorem ggNSDetChar_automizer (h : GGNSLocalHyp p B Bs K f n ψ) {δ : ↥Bs →* Kˣ}
    (hδ : ∀ (b : ↥Bs) (g : GL (Fin n) K), GGInducesUnitary (p := 2) (f := f) ψ (b : G) g →
      Matrix.GeneralLinearGroup.det g = δ b)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ψ.range Bs) (b : ↥Bs) : δ (φ b) = δ b := by
  let S : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | ∀ b : ↥Bs, δ (φ b) = δ b}
      mul_mem' := fun {a c} ha hc b => by
        show δ (a (c b)) = δ b
        rw [ha, hc]
      one_mem' := fun b => rfl
      inv_mem' := fun {a} ha b => by
        have h1 := ha (a⁻¹ b)
        have h2 : a (a⁻¹ b) = b := a.apply_symm_apply b
        rw [h2] at h1
        exact h1.symm }
  have hle : ggAutomizer ψ.range Bs ≤ S := by
    refine (Subgroup.closure_le S).mpr ?_
    intro φ hφ
    obtain ⟨g, hg, -, hφg⟩ := hφ
    obtain ⟨s, rfl⟩ := hg
    show ∀ b : ↥Bs, δ (φ b) = δ b
    intro b
    exact ggNSDetChar_conj h hδ b (φ b) s (hφg b)
  exact hle hφ b

end DetInv

theorem exists_fixed_det_ne_one {A C : Type*} [Group A] [Group C] (hcomm : ∀ a b : A, a * b = b * a)
    (r : MulAut A) (hr : ∀ a, r (r a) = a) (δ : A →* C) (hδ : ∀ a, δ (r a) = δ a)
    (hC3 : ∀ c : C, c ^ 3 = 1) {b : A} (hb : δ b ≠ 1) : ∃ h : A, r h = h ∧ δ h ≠ 1 := by
  refine ⟨b * r b, ?_, ?_⟩
  · rw [map_mul, hr]
    exact hcomm _ _
  · rw [map_mul, hδ, ← pow_two]
    intro h2
    apply hb
    have h3 := hC3 (δ b)
    calc δ b = (δ b) ^ 3 * ((δ b) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp

theorem ggNSDet_exists_fixed_pair_ne_one
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {ψ : Su K 2 1 6 →* G}
    (h : GGNSLocalHyp 3 B Bs K 1 6 ψ) (hK : Nat.card K = 4)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    {δ : ↥Bs →* Kˣ}
    (hδ : ∀ (b : ↥Bs) (g : GL (Fin 6) K),
      GGInducesUnitary (p := 2) (f := 1) ψ (b : G) g →
        Matrix.GeneralLinearGroup.det g = δ b)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ 3)
    (hBs : 3 ^ 6 ≤ Nat.card ↥Bs)
    {r s : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer ψ.range Bs) (hr : GGIsReflection 3 r)
    (hsA : s ∈ ggAutomizer ψ.range Bs) (hs : GGIsReflection 3 s) :
    ∃ b : ↥Bs, r b = b ∧ s b = b ∧ δ b ≠ 1 := by
  classical
  obtain ⟨b0, hb0⟩ := ggNSDet_exists_ne_one h hK hd hδ hC hBs
  obtain ⟨ε, hεapply, hεrefl⟩ := ggNSDiag_automizer_perm h hd
  obtain ⟨a, b, hab, hr_eq⟩ := ggMUR1_refl_eq_swap h.prime h.odd h.bstar.2.1 ε hεrefl hrA hr
  obtain ⟨c, d, hcd, hs_eq⟩ := ggMUR1_refl_eq_swap h.prime h.odd h.bstar.2.1 ε hεrefl hsA hs
  obtain ⟨m, hma, hmb, hmc, hmd⟩ :=
    CFSG.RankThree.PartOne.WeylIso.exists_fin_ne (n := 5) (by omega) a b c d
  let d0 : Fin 6 → Kˣ := ggNSPosPA_liftUnits hd b0
  let g0 : GL (Fin 6) K := ggNSPosPA_lift hd b0
  have hg0_diag : g0 = TauCeti.diagGL d0 := by
    dsimp only [g0, d0]
    exact (ggNSPosPA_diagGL_liftUnits hd b0).symm
  have hg0_induces : GGInducesUnitary (p := 2) (f := 1) ψ (b0 : G) g0 := by
    dsimp only [g0]
    exact ggNSPosPA_lift_induces hd b0
  have hdetg0 : Matrix.GeneralLinearGroup.det g0 = δ b0 := by
    dsimp only [g0]
    exact hδ b0 (ggNSPosPA_lift hd b0) (ggNSPosPA_lift_induces hd b0)
  have hcard_units : Nat.card (Kˣ) = 3 := by
    rw [Nat.card_units, hK]
  have hcube : ∀ u : Kˣ, u ^ 3 = 1 := by
    intro u
    have h := pow_card_eq_one' (x := u)
    rwa [hcard_units] at h
  have hδcube : ((δ b0 : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hcube (δ b0), Units.val_one]
  have hd0cube : ∀ i, ((d0 i : Kˣ) : K) ^ 3 = 1 := by
    intro i
    rw [← Units.val_pow_eq_pow_val, hcube (d0 i), Units.val_one]
  let evec : Fin 6 → K := fun i => if i = m then ((δ b0 : Kˣ) : K) else 1
  have hevec : ∀ i, evec i ^ 3 = 1 := by
    intro i
    by_cases hi : i = m
    · simp [evec, hi, hδcube]
    · simp [evec, hi]
  have hprod_e : ∏ i : Fin 6, evec i = ((δ b0 : Kˣ) : K) := by
    simp [evec]
  let dvec : Fin 6 → K := fun i => evec i * ((d0 i : Kˣ) : K)⁻¹
  have hdcube : ∀ i, dvec i ^ 3 = 1 := by
    intro i
    dsimp only [dvec]
    rw [mul_pow, inv_pow, hevec i, hd0cube i]
    simp
  have hprod_d0 : ∏ i : Fin 6, ((d0 i : Kˣ) : K) = ((δ b0 : Kˣ) : K) := by
    have hval : ((Matrix.GeneralLinearGroup.det g0 : Kˣ) : K) =
        ∏ i : Fin 6, ((d0 i : Kˣ) : K) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hg0_diag, TauCeti.diagGL_coe,
        Matrix.det_diagonal]
    rw [← hval, hdetg0]
  have hprod_dvec : ∏ i : Fin 6, dvec i = 1 := by
    dsimp only [dvec]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hprod_e, hprod_d0]
    exact mul_inv_cancel₀ (Units.ne_zero (δ b0))
  have hunit : ∀ i, unitaryInvolution K 2 1 (dvec i) * dvec i = 1 := by
    intro i
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ]
    simpa using hdcube i
  let D : Su K 2 1 6 := ggNSPosPB2_diagSU dvec hprod_dvec hunit
  have hD_mem : ψ D ∈ Bs :=
    ggNSDiag_torus_le h hd D ⟨dvec, ggNSPosPB2_diagSU_coe dvec hprod_dvec hunit, hdcube⟩
  let bcorr : ↥Bs := ⟨ψ D * (b0 : G), Bs.mul_mem hD_mem b0.2⟩
  have hdiag_Dg0 : (((D : GL (Fin 6) K) * g0 : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal evec := by
    dsimp only [D, g0, dvec]
    rw [Units.val_mul, ggNSPosPB2_diagSU_coe, ← ggNSPosPA_diagGL_liftUnits hd b0,
      TauCeti.diagGL_coe, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_assoc, inv_mul_cancel₀ (Units.ne_zero (d0 i)), mul_one]
  have hbcorr_induces : GGInducesUnitary (p := 2) (f := 1) ψ (bcorr : G)
      ((D : GL (Fin 6) K) * g0) := by
    dsimp only [bcorr]
    exact ggNSPosPA7_induces_mul (ggNSPosPA_induces_self D) hg0_induces
  have hdetD : Matrix.GeneralLinearGroup.det (D : GL (Fin 6) K) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, ggNSPosPB2_diagSU_coe,
      Matrix.det_diagonal, hprod_dvec, Units.val_one]
  have hδbcorr : δ bcorr = δ b0 := by
    have hdet := hδ bcorr ((D : GL (Fin 6) K) * g0) hbcorr_induces
    rw [map_mul, hdetD, hdetg0, one_mul] at hdet
    exact hdet.symm
  have hδbcorr_ne : δ bcorr ≠ 1 := by
    rw [hδbcorr]
    exact hb0
  have he_ab : evec a = evec b := by
    simp [evec, Ne.symm hma, Ne.symm hmb]
  have he_cd : evec c = evec d := by
    simp [evec, Ne.symm hmc, Ne.symm hmd]
  have hfixed (u v : Fin 6) (heq : evec u = evec v) :
      ((ε (Equiv.swap u v) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) bcorr = bcorr := by
    let gswap : Su K 2 1 6 := ggPermSU (K := K) (f := 1) (Equiv.swap u v)
    let x : Su K 2 1 6 := ggPermSU (K := K) (f := 1) (Equiv.swap u v)⁻¹
    have hx_eq : x = gswap := by
      dsimp only [x, gswap]
      rw [Equiv.swap_inv]
    have hcomm_gswap : ((D : GL (Fin 6) K) * g0) * (gswap : GL (Fin 6) K) =
        (gswap : GL (Fin 6) K) * ((D : GL (Fin 6) K) * g0) := by
      apply Units.ext
      change ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (g0 : Matrix (Fin 6) (Fin 6) K) *
          ((gswap : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        ((gswap : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          (((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (g0 : Matrix (Fin 6) (Fin 6) K))
      rw [show ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (g0 : Matrix (Fin 6) (Fin 6) K) =
          Matrix.diagonal evec from hdiag_Dg0]
      change Matrix.diagonal evec * (Equiv.swap u v).permMatrix K =
        (Equiv.swap u v).permMatrix K * Matrix.diagonal evec
      exact ggNSPosPB2_diag_comm_perm (f := 1) u v evec heq
    have hx_comm : ((D : GL (Fin 6) K) * g0) * (x : GL (Fin 6) K) =
        (x : GL (Fin 6) K) * ((D : GL (Fin 6) K) * g0) := by
      rw [hx_eq]
      exact hcomm_gswap
    have hb_comm_x : (bcorr : G) * ψ x * (bcorr : G)⁻¹ = ψ x := by
      obtain ⟨y, hy, hby⟩ := hbcorr_induces.2 x
      have hy_eq : y = x := by
        apply Subtype.ext
        rw [hy, hx_comm]
        group
      rw [hy_eq] at hby
      exact hby
    have h_apply : ((((ε (Equiv.swap u v) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) bcorr : ↥Bs) : G) =
        ψ x * (bcorr : G) * (ψ x)⁻¹ := by
      dsimp only [x]
      exact hεapply (Equiv.swap u v) bcorr
    apply Subtype.ext
    rw [h_apply]
    have hb_comm_x' : (bcorr : G) * ψ x = ψ x * (bcorr : G) := by
      calc (bcorr : G) * ψ x = ((bcorr : G) * ψ x * (bcorr : G)⁻¹) * (bcorr : G) := by group
        _ = ψ x * (bcorr : G) := by rw [hb_comm_x]
    rw [← hb_comm_x']
    group
  have hfix_r : r bcorr = bcorr := by
    rw [hr_eq]
    exact hfixed a b he_ab
  have hfix_s : s bcorr = bcorr := by
    rw [hs_eq]
    exact hfixed c d he_cd
  exact ⟨bcorr, hfix_r, hfix_s, hδbcorr_ne⟩

end CFSG.StandardType

end

module

public import CFSG.Quasithin.Background.RonanH44Two
public import CFSG.Quasithin.Background.RonanH44SigL

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3
  CFSG.Quasithin.SteinbergCB Matrix Tri
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem tm_coe_mul (A B : SL(3, K)) :
    ((A * B : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) :=
  Matrix.SpecialLinearGroup.coe_mul A B

private theorem tm_coe_one : ((1 : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 :=
  Matrix.SpecialLinearGroup.coe_one

private theorem tm_transvection_coe (c : K) :
    ((SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c : SL(3, K)) :
        Matrix (Fin 3) (Fin 3) K) = 1 + c • Matrix.single (0 : Fin 3) 2 1 := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.smul_single, smul_eq_mul, mul_one]

private theorem tm_conj_affine {A B E : Matrix (Fin 3) (Fin 3) K} (hAB : A * B = 1) (c : K) :
    A * (1 + c • E) * B = 1 + c • (A * E * B) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, hAB]

private theorem tm_conj_inv_affine {A B E : Matrix (Fin 3) (Fin 3) K} (hBA : B * A = 1) :
    B * (A * E * B) * A = E := by
  rw [show B * (A * E * B) * A = B * A * E * (B * A) by simp only [Matrix.mul_assoc], hBA,
    Matrix.one_mul, Matrix.mul_one]

private theorem tm_sub_one_eq (rh W : SL(3, K))
    (hW : W * rh * W⁻¹ = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) 1) :
    (rh : Matrix (Fin 3) (Fin 3) K) - 1 =
      ((W⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * Matrix.single (0 : Fin 3) 2 1 *
        (W : Matrix (Fin 3) (Fin 3) K) := by
  have hAB :
      ((W⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * (W : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← tm_coe_mul, inv_mul_cancel, tm_coe_one]
  have hrh : rh = W⁻¹ * SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) 1 * W := by
    rw [← hW]
    group
  have hm : (rh : Matrix (Fin 3) (Fin 3) K) = 1 + (1 : K) •
      (((W⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * Matrix.single (0 : Fin 3) 2 1 *
        (W : Matrix (Fin 3) (Fin 3) K)) := by
    rw [hrh, tm_coe_mul, tm_coe_mul, tm_transvection_coe 1,
      tm_conj_affine hAB]
  rw [hm, one_smul, add_sub_cancel_left]

private theorem tm_sub_one_sq (rh : SL(3, K)) (hrr : rh * rh = 1) :
    ((rh : Matrix (Fin 3) (Fin 3) K) - 1) * ((rh : Matrix (Fin 3) (Fin 3) K) - 1) = 0 := by
  have hsq : (rh : Matrix (Fin 3) (Fin 3) K) * (rh : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← tm_coe_mul, hrr, tm_coe_one]
  have h2 : ∀ X : Matrix (Fin 3) (Fin 3) K, X + X = 0 := fun X => by
    rw [← two_smul K X, CharTwo.two_eq_zero, zero_smul]
  have e1 : ((rh : Matrix (Fin 3) (Fin 3) K) - 1) * ((rh : Matrix (Fin 3) (Fin 3) K) - 1) =
      (rh : Matrix (Fin 3) (Fin 3) K) * (rh : Matrix (Fin 3) (Fin 3) K) -
        ((rh : Matrix (Fin 3) (Fin 3) K) + (rh : Matrix (Fin 3) (Fin 3) K)) + 1 := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]
    abel
  rw [e1, hsq, h2 (rh : Matrix (Fin 3) (Fin 3) K), sub_zero]
  exact h2 1

private theorem tm_sub_one_ne_zero {rh : SL(3, K)} (hne : rh ≠ 1) :
    (rh : Matrix (Fin 3) (Fin 3) K) - 1 ≠ 0 := by
  intro h
  apply hne
  apply Subtype.ext
  rw [tm_coe_one]
  exact sub_eq_zero.1 h

private theorem tm_bar_sub_one (rh : SL(3, K))
    (hbar : ∀ i j,
      bar n ((rh : Matrix (Fin 3) (Fin 3) K) i j) = (rh : Matrix (Fin 3) (Fin 3) K) i j)
    (i j : Fin 3) :
    bar n (((rh : Matrix (Fin 3) (Fin 3) K) - 1) i j) =
      ((rh : Matrix (Fin 3) (Fin 3) K) - 1) i j := by
  simp only [Matrix.sub_apply, map_sub, hbar]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem tm_bar_affine (N : Matrix (Fin 3) (Fin 3) K) (hN : ∀ i j, bar n (N i j) = N i j)
    (c : K) (i j : Fin 3) :
    bar n ((1 + c • N) i j) = (1 + bar n c • N) i j := by
  by_cases h : i = j <;> simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, h, hN]

private theorem tm_map_coe (g : SL(3, K)) (N : Matrix (Fin 3) (Fin 3) K)
    (hN : ∀ i j, bar n (N i j) = N i j) (c : K)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = 1 + c • N) :
    ((Matrix.SpecialLinearGroup.map (bar n).toRingHom g : SL(3, K)) :
        Matrix (Fin 3) (Fin 3) K) = 1 + bar n c • N := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingEquiv.coe_toRingHom]
  rw [hg]
  exact tm_bar_affine N hN c i j

private theorem tm_map_self (g : SL(3, K))
    (hg : ∀ i j, bar n ((g : Matrix (Fin 3) (Fin 3) K) i j) = (g : Matrix (Fin 3) (Fin 3) K) i j) :
    Matrix.SpecialLinearGroup.map (bar n).toRingHom g = g := by
  apply Subtype.ext
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingEquiv.coe_toRingHom]
  exact hg i j

private theorem tm_rho_conj_sig (hK : Nat.card K = (2 ^ n) ^ 2) (g : SL(3, K)) :
    sig n K * rho hK g * (sig n K)⁻¹ =
      rho hK (Matrix.SpecialLinearGroup.map (bar n).toRingHom g) := by
  have hu : mapGL (bar n) (SpecialLinearGroup.toGL g) =
      SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (bar n).toRingHom g) :=
    Units.ext rfl
  calc sig n K * rho hK g * (sig n K)⁻¹
      = fldAut (bar n) * rhoT hK (SpecialLinearGroup.toGL g) * (fldAut (bar n))⁻¹ := rfl
    _ = rhoT hK (mapGL (bar n) (SpecialLinearGroup.toGL g)) := fldAut_conj_rhoT hK (bar n) _
    _ = rhoT hK (SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (bar n).toRingHom g)) := by
        rw [hu]
    _ = rho hK (Matrix.SpecialLinearGroup.map (bar n).toRingHom g) := rfl

private theorem tm_bar_eq_of_rho_eq (hK : Nat.card K = (2 ^ n) ^ 2)
    {N : Matrix (Fin 3) (Fin 3) K} (hNN : N * N = 0) (hN0 : N ≠ 0) {c : K} {g gb : SL(3, K)}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = 1 + c • N)
    (hgb : (gb : Matrix (Fin 3) (Fin 3) K) = 1 + bar n c • N)
    (hrho : rho hK gb = rho hK g) : bar n c = c := by
  have h1 : rho hK (gb * g⁻¹) = 1 := by
    rw [map_mul, map_inv, hrho, mul_inv_cancel]
  obtain ⟨d, -, hd⟩ := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars).1
    (mem_scalars_of_rho_eq_one hK h1)
  have h2 : (gb : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) (d : K) * (g : Matrix (Fin 3) (Fin 3) K) := by
    rw [← hd, ← tm_coe_mul, inv_mul_cancel_right]
  have hEq : (1 : Matrix (Fin 3) (Fin 3) K) + bar n c • N =
      Matrix.scalar (Fin 3) (d : K) * (1 + c • N) := by
    rw [← hgb, h2, hg]
  have h3 : N = Matrix.scalar (Fin 3) (d : K) * N := by
    have h' := congrArg (fun M => M * N) hEq
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hNN, smul_zero, add_zero,
      Matrix.mul_assoc] at h'
    exact h'
  obtain ⟨a, b, hab⟩ : ∃ a b, N a b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN0 (Matrix.ext fun a b => by simp [hcon a b])
  have hent : N a b = (d : K) * N a b := by
    have h4 := congrFun (congrFun h3 a) b
    simpa [Matrix.scalar_apply, Matrix.diagonal_mul] using h4
  have hd1 : (d : K) = 1 := by
    have h5 : ((d : K) - 1) * N a b = 0 := by linear_combination -hent
    rcases mul_eq_zero.1 h5 with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 hab
  have hEq2 : (1 : Matrix (Fin 3) (Fin 3) K) + bar n c • N = 1 + c • N := by
    rw [hEq, hd1, map_one, one_mul]
  have hX : bar n c • N = c • N := add_left_cancel hEq2
  have hX' := congrFun (congrFun hX a) b
  simp only [Matrix.smul_apply, smul_eq_mul] at hX'
  exact mul_right_cancel₀ hab hX'

private theorem tm_rho_conj_eq_rTr (hK : Nat.card K = (2 ^ n) ^ 2) {W rh : SL(3, K)}
    (hW : W * rh * W⁻¹ = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) 1) :
    rho hK W * rho hK rh * (rho hK W)⁻¹ = rTr hK := by
  have h1 : rho hK (W * rh * W⁻¹) = rho hK W * rho hK rh * (rho hK W)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [← h1, hW]
  exact rho_transvection hK (by decide : (0 : Fin 3) ≠ 2) 1

private theorem tm_rk_eq (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {W rh : SL(3, K)}
    (hW : W * rh * W⁻¹ = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) 1) :
    rk ↥(fixV (Subgroup.zpowers (rho hK rh))) = 5 * n := by
  have h := card_fixV_zpowers_conj (rho hK W) (rho hK rh)
  rw [tm_rho_conj_eq_rTr hK hW] at h
  have h2 : rk ↥(fixV (Subgroup.zpowers (rTr hK))) = rk ↥(fixV (Subgroup.zpowers (rho hK rh))) := by
    unfold rk
    rw [h]
  rw [← h2]
  exact rk_fixV_rTr hn hK

private theorem tm_img_le_norm (hK : Nat.card K = (2 ^ n) ^ 2) : img hK ≤ norm hK :=
  Subgroup.le_normalizer

private theorem tm_bar_of_mem (x : Fq n K) : bar n (x : K) = (x : K) :=
  frobFixed_apply (σ := barR n K) x

private theorem tm_exists_lift (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {r : MulAut (HMod n K)}
    (hr : r ∈ img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K))))
    (hord : orderOf r = 2) :
    ∃ rh : SL(3, K), rho hK rh = r ∧
      (∀ i j, bar n ((rh : Matrix (Fin 3) (Fin 3) K) i j) = (rh : Matrix (Fin 3) (Fin 3) K) i j) ∧
      rh * rh = 1 ∧ rh ≠ 1 := by
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.1
    ((mem_range_rhoF_iff hn hK r).2 (Subgroup.mem_inf.1 hr))
  have hr2 : r * r = 1 := by
    have h1 := pow_orderOf_eq_one r
    rw [hord, pow_two] at h1
    exact h1
  have hsq : h * h = 1 := by
    apply rhoF_injective hn hK
    rw [map_mul, hh, hr2, map_one]
  refine ⟨Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype h, hh, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact tm_bar_of_mem ((h : Matrix (Fin 3) (Fin 3) (Fq n K)) i j)
  · rw [← map_mul, hsq, map_one]
  · intro h1
    have hr1 : r = 1 := by
      rw [← hh]
      show rho hK _ = 1
      rw [h1, map_one]
    rw [hr1, orderOf_one] at hord
    exact absurd hord (by norm_num)

private theorem tm_centSub_set_eq (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hLM : img hK ≤ M) (hMN : M ≤ norm hK)
    (rh W : SL(3, K))
    (hbar : ∀ i j,
      bar n ((rh : Matrix (Fin 3) (Fin 3) K) i j) = (rh : Matrix (Fin 3) (Fin 3) K) i j)
    (hrr : rh * rh = 1) (hne : rh ≠ 1)
    (hW : W * rh * W⁻¹ = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) 1) :
    ((M ⊓ centSub (fixV (Subgroup.zpowers (rho hK rh))) : Subgroup (MulAut (HMod n K))) :
        Set (MulAut (HMod n K))) =
      {x | (∃ (g : SL(3, K)) (c : K), (g : Matrix (Fin 3) (Fin 3) K) =
          1 + c • ((rh : Matrix (Fin 3) (Fin 3) K) - 1) ∧ rho hK g = x) ∧
        sig n K * x * (sig n K)⁻¹ = x} := by
  have hpsi : rho hK W ∈ norm hK := tm_img_le_norm hK (MonoidHom.mem_range.2 ⟨W, rfl⟩)
  have hconj := tm_rho_conj_eq_rTr hK hW
  have hN := tm_sub_one_eq rh W hW
  have hNN := tm_sub_one_sq rh hrr
  have hN0 := tm_sub_one_ne_zero hne
  have hNbar := tm_bar_sub_one rh hbar
  have hWW :
      (W : Matrix (Fin 3) (Fin 3) K) * ((W⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← tm_coe_mul, mul_inv_cancel, tm_coe_one]
  have hW'W :
      ((W⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * (W : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← tm_coe_mul, inv_mul_cancel, tm_coe_one]
  ext x
  simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_setOf_eq, mem_centSub]
  constructor
  · rintro ⟨hxM, hxC⟩
    have hx' : rho hK W * x * (rho hK W)⁻¹ ∈ norm hK :=
      mul_mem (mul_mem hpsi (hMN hxM)) (inv_mem hpsi)
    have hfix : ∀ v ∈ fixV (Subgroup.zpowers (rTr hK)), (rho hK W * x * (rho hK W)⁻¹) v = v := by
      intro v hv
      rw [mem_fixV_zpowers_iff] at hv
      have hr : rho hK rh = (rho hK W)⁻¹ * rTr hK * rho hK W := by
        rw [← hconj]
        group
      have hu : (rho hK W)⁻¹ v ∈ fixV (Subgroup.zpowers (rho hK rh)) := by
        rw [mem_fixV_zpowers_iff, hr, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self,
          hv]
      rw [MulAut.mul_apply, MulAut.mul_apply, hxC _ hu, MulAut.apply_inv_self]
    obtain ⟨c, hc, hxc⟩ := eq_trGL_of_cent hn hK hx' hfix
    have hgmat : ((W⁻¹ * SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c * W :
        SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 + c • ((rh : Matrix (Fin 3) (Fin 3) K) - 1) := by
      rw [tm_coe_mul, tm_coe_mul, tm_transvection_coe c, hN,
        tm_conj_affine hW'W]
    have hgx : rho hK (W⁻¹ * SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c * W)
        = x := by
      rw [map_mul, map_mul, map_inv, rho_transvection, ← hxc]
      group
    have hex : ∃ g : SL(3, K), (g : Matrix (Fin 3) (Fin 3) K) =
        1 + c • ((rh : Matrix (Fin 3) (Fin 3) K) - 1) ∧ rho hK g = x :=
      ⟨_, hgmat, hgx⟩
    obtain ⟨g, hgmat', hgx'⟩ := hex
    refine ⟨⟨g, c, hgmat', hgx'⟩, ?_⟩
    have hfixg : ∀ i j, bar n ((g : Matrix (Fin 3) (Fin 3) K) i j) =
        (g : Matrix (Fin 3) (Fin 3) K) i j := by
      intro i j
      rw [hgmat', tm_bar_affine _ hNbar c i j, hc]
    rw [← hgx', tm_rho_conj_sig hK g, tm_map_self g hfixg]
  · rintro ⟨⟨g, c, hgc, hgx⟩, hsig⟩
    subst hgx
    have hxM : rho hK g ∈ M := hLM (MonoidHom.mem_range.2 ⟨g, rfl⟩)
    have hrho : rho hK (Matrix.SpecialLinearGroup.map (bar n).toRingHom g) = rho hK g :=
      (tm_rho_conj_sig hK g).symm.trans hsig
    have hbc : bar n c = c :=
      tm_bar_eq_of_rho_eq hK hNN hN0 hgc (tm_map_coe g _ hNbar c hgc) hrho
    refine ⟨hxM, ?_⟩
    intro u hu
    rw [mem_fixV_zpowers_iff] at hu
    have hpu : rTr hK (rho hK W u) = rho hK W u := by
      rw [← hconj, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hu]
    have hT := rhoT_trGL_fixes hK hbc (mem_fixV_zpowers_iff.2 hpu)
    have hgT : W * g * W⁻¹ = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c := by
      apply Subtype.ext
      rw [tm_coe_mul, tm_coe_mul, hgc, tm_transvection_coe c, hN,
        tm_conj_affine hWW, tm_conj_inv_affine hWW]
    have hkey : rho hK W * rho hK g * (rho hK W)⁻¹ =
        rhoT hK (trGL (0 : Fin 3) 2 (by decide) c) := by
      rw [← rho_transvection hK (by decide : (0 : Fin 3) ≠ 2) c, ← hgT, map_mul, map_mul, map_inv]
    have key : rho hK W (rho hK g u) = rho hK W u := by
      calc rho hK W (rho hK g u) = (rho hK W * rho hK g * (rho hK W)⁻¹) (rho hK W u) := by
            rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
        _ = rhoT hK (trGL (0 : Fin 3) 2 (by decide) c) (rho hK W u) := by rw [hkey]
        _ = rho hK W u := hT
    exact (MulEquiv.injective (rho hK W)) key

theorem part2 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hLM : img hK ≤ M) (hMN : M ≤ norm hK) :
    ∀ r ∈ img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K))),
      orderOf r = 2 →
      rk ↥(fixV (Subgroup.zpowers r)) = 5 * n ∧
      ∃ rh : SL(3, K), rho hK rh = r ∧ orderOf rh = 2 ∧
        ((M ⊓ centSub (fixV (Subgroup.zpowers r)) : Subgroup (MulAut (HMod n K))) :
            Set (MulAut (HMod n K))) =
          {x | (∃ (g : SL(3, K)) (c : K), (g : Matrix (Fin 3) (Fin 3) K) =
              1 + c • ((rh : Matrix (Fin 3) (Fin 3) K) - 1) ∧ rho hK g = x) ∧
            sig n K * x * (sig n K)⁻¹ = x} := by
  intro r hr hord
  obtain ⟨rh, hrhoeq, hbar, hrr, hne⟩ := tm_exists_lift hn hK hr hord
  subst hrhoeq
  obtain ⟨W, hW⟩ := exists_conj_eq_transvection hrr hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord' : orderOf rh = 2 := orderOf_eq_prime (by rw [pow_two]; exact hrr) hne
  exact ⟨tm_rk_eq hn hK hW, rh, rfl, hord', tm_centSub_set_eq hn hK hLM hMN rh W hbar hrr hne hW⟩

end CFSG.Quasithin.RonanH44

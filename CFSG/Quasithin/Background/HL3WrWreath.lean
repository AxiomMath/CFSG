module

public import CFSG.Quasithin.EmptyFaithful.S152NWreath
public import CFSG.Quasithin.Background.HL3WrA3

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open Matrix S152N
open scoped Matrix

@[expose] def nzv : Fin 3 → Fin 2 → ZMod 2 := ![![1, 0], ![0, 1], ![1, 1]]

@[expose] def nzIdx (v : Fin 2 → ZMod 2) : Fin 3 :=
  if v = ![1, 0] then 0 else if v = ![0, 1] then 1 else 2

theorem nzv_nzIdx : ∀ v : Fin 2 → ZMod 2, v ≠ 0 → nzv (nzIdx v) = v := by decide

theorem nzv_ne_zero : ∀ i : Fin 3, nzv i ≠ 0 := by decide

@[expose] def permFun (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) (i : Fin 3) : Fin 3 :=
  nzIdx (B *ᵥ nzv i)

theorem mulVec_nzv_ne_zero {B C : Matrix (Fin 2) (Fin 2) (ZMod 2)} (h : C * B = 1) (i : Fin 3) :
    B *ᵥ nzv i ≠ 0 := by
  intro h0
  apply nzv_ne_zero i
  calc nzv i = (C * B) *ᵥ nzv i := by rw [h, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem permFun_mul {B C D : Matrix (Fin 2) (Fin 2) (ZMod 2)} (h : D * C = 1) (i : Fin 3) :
    permFun (B * C) i = permFun B (permFun C i) := by
  unfold permFun
  rw [nzv_nzIdx _ (mulVec_nzv_ne_zero h i), Matrix.mulVec_mulVec]

theorem permFun_one : ∀ i : Fin 3, permFun 1 i = i := by decide

theorem eq_one_of_permFun : ∀ B : Matrix (Fin 2) (Fin 2) (ZMod 2),
    (∀ i, permFun B i = i) → B = 1 := by
  decide

theorem blk_one : blk (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by decide

theorem blk_scenMat : ∀ x y : ZMod 2, blk (scenMat x y) = 1 := by decide

theorem blk_inv_mul (g : ↥P1) :
    blk (mat ((g⁻¹ : ↥P1) : ↥SL32)) * blk (mat (g : ↥SL32)) = 1 := by
  rw [← blk_mat_mul (g⁻¹).2, ← Subgroup.coe_mul, inv_mul_cancel, OneMemClass.coe_one, mat_one,
    blk_one]

theorem blk_mul_inv (g : ↥P1) :
    blk (mat (g : ↥SL32)) * blk (mat ((g⁻¹ : ↥P1) : ↥SL32)) = 1 := by
  rw [← blk_mat_mul g.2, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one, mat_one,
    blk_one]

@[expose] noncomputable def sigP1 : ↥P1 →* Equiv.Perm (Fin 3) where
  toFun g :=
    { toFun := permFun (blk (mat (g : ↥SL32)))
      invFun := permFun (blk (mat ((g⁻¹ : ↥P1) : ↥SL32)))
      left_inv := fun i => by
        rw [← permFun_mul (blk_inv_mul g) i, blk_inv_mul g, permFun_one]
      right_inv := fun i => by
        rw [← permFun_mul (blk_mul_inv g) i, blk_mul_inv g, permFun_one] }
  map_one' := Equiv.ext fun i => by
    change permFun (blk (mat 1)) i = i
    rw [mat_one, blk_one, permFun_one]
  map_mul' g h := Equiv.ext fun i => by
    change permFun (blk (mat ((g : ↥SL32) * (h : ↥SL32)))) i =
      permFun (blk (mat (g : ↥SL32))) (permFun (blk (mat (h : ↥SL32))) i)
    rw [blk_mat_mul g.2, permFun_mul (blk_inv_mul h) i]

theorem sigP1_apply (g : ↥P1) (i : Fin 3) : sigP1 g i = permFun (blk (mat (g : ↥SL32))) i := rfl

theorem sigP1_eq_one_iff (g : ↥P1) : sigP1 g = 1 ↔ (g : ↥SL32) ∈ Scen := by
  constructor
  · intro h
    have hB : blk (mat (g : ↥SL32)) = 1 := eq_one_of_permFun _ fun i => by
      rw [← sigP1_apply, h]
      rfl
    obtain ⟨h10, h20, h00⟩ := (mulVec_e0_iff (mat (g : ↥SL32))).1 g.2
    have e11 : mat (g : ↥SL32) 1 1 = 1 := by simpa using congrFun (congrFun hB 0) 0
    have e12 : mat (g : ↥SL32) 1 2 = 0 := by simpa using congrFun (congrFun hB 0) 1
    have e21 : mat (g : ↥SL32) 2 1 = 0 := by simpa using congrFun (congrFun hB 1) 0
    have e22 : mat (g : ↥SL32) 2 2 = 1 := by simpa using congrFun (congrFun hB 1) 1
    refine ⟨mat (g : ↥SL32) 0 1, mat (g : ↥SL32) 0 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h20, h00, e11, e12, e21, e22]
  · rintro ⟨x, y, hxy⟩
    refine Equiv.ext fun i => ?_
    rw [sigP1_apply, hxy, blk_scenMat, permFun_one]
    rfl

@[expose] noncomputable def cP1 : ↥P1 := ⟨c3, c3_mem_P1⟩

@[expose] def cyc3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem sigP1_cP1 : sigP1 cP1 = cyc3 := Equiv.ext fun i => by
  rw [sigP1_apply]
  change permFun (blk (mat c3)) i = cyc3 i
  rw [blk_mat_c3]
  revert i
  decide

@[expose] noncomputable def u0 : ↥SL32 := slOfMat (uMat 0 0 1) (det_uMat 0 0 1)

theorem u0_mem_U3 : u0 ∈ U3 := uMat_mem_U3 0 0 1

@[expose] noncomputable def uP1 : ↥P1 := ⟨u0, U3_le_P1 u0_mem_U3⟩

theorem sigP1_uP1 : sigP1 uP1 = Equiv.swap 1 2 := Equiv.ext fun i => by
  rw [sigP1_apply]
  change permFun (blk (uMat 0 0 1)) i = Equiv.swap 1 2 i
  revert i
  decide

abbrev tq : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem mz2_cases : ∀ q : Multiplicative (ZMod 2), q = 1 ∨ q = tq := by decide

theorem tq_ne_one : tq ≠ 1 := by decide

theorem tq_mul_tq : tq * tq = 1 := by decide

theorem one_inv_mul_mz2 :
    ∀ q : Multiplicative (ZMod 2), (1 : Multiplicative (ZMod 2))⁻¹ * q = q := by
  decide

theorem tq_inv_mul_tq : tq⁻¹ * tq = 1 := by decide

theorem tq_inv_mul_one : tq⁻¹ * 1 = tq := by decide

@[expose] noncomputable def tauPow : Multiplicative (ZMod 2) →* MulAut WMod where
  toFun q := if q = 1 then 1 else tau
  map_one' := by simp
  map_mul' a b := by
    rcases mz2_cases a with rfl | rfl <;> rcases mz2_cases b with rfl | rfl <;>
      simp [tq_mul_tq, tau_mul_self]

theorem tauPow_tq : tauPow tq = tau := by
  change (if tq = 1 then 1 else tau) = tau
  exact ite_eq_right tq_ne_one

theorem tauPow_mem_norm (q : Multiplicative (ZMod 2)) : tauPow q ∈ norm := by
  rcases mz2_cases q with rfl | rfl
  · rw [map_one]
    exact norm.one_mem
  · rw [tauPow_tq]
    exact tau_mem_norm

theorem tauPow_fix_E00 (q : Multiplicative (ZMod 2)) : tauPow q (eW 0 0) = eW 0 0 := by
  rcases mz2_cases q with rfl | rfl
  · rw [map_one]
    rfl
  · rw [tauPow_tq]
    exact tau_eW_diag 0

@[expose] noncomputable def thetaFun (w : ↥P1 ≀ᵣ Multiplicative (ZMod 2)) : MulAut WMod :=
  rho (((w.left 1 : ↥P1) : ↥SL32), ((w.left tq : ↥P1) : ↥SL32)) * tauPow w.right

theorem thetaFun_mul (a b : ↥P1 ≀ᵣ Multiplicative (ZMod 2)) :
    thetaFun (a * b) = thetaFun a * thetaFun b := by
  unfold thetaFun
  rcases mz2_cases a.right with ha | ha
  · have h1 : (a * b).left 1 = a.left 1 * b.left 1 := by
      change a.left 1 * b.left (a.right⁻¹ * 1) = a.left 1 * b.left 1
      rw [ha, one_inv_mul_mz2]
    have h2 : (a * b).left tq = a.left tq * b.left tq := by
      change a.left tq * b.left (a.right⁻¹ * tq) = a.left tq * b.left tq
      rw [ha, one_inv_mul_mz2]
    have h3 : (a * b).right = b.right := by
      change a.right * b.right = b.right
      rw [ha, one_mul]
    rw [h1, h2, h3, ha, map_one, mul_one, ← mul_assoc, ← map_mul]
    rfl
  · have h1 : (a * b).left 1 = a.left 1 * b.left tq := by
      change a.left 1 * b.left (a.right⁻¹ * 1) = a.left 1 * b.left tq
      rw [ha, tq_inv_mul_one]
    have h2 : (a * b).left tq = a.left tq * b.left 1 := by
      change a.left tq * b.left (a.right⁻¹ * tq) = a.left tq * b.left 1
      rw [ha, tq_inv_mul_tq]
    have h3 : (a * b).right = tq * b.right := by
      change a.right * b.right = tq * b.right
      rw [ha]
    rw [h1, h2, h3, ha, map_mul, tauPow_tq]
    have key : tau * rho (((b.left 1 : ↥P1) : ↥SL32), ((b.left tq : ↥P1) : ↥SL32)) =
        rho (((b.left tq : ↥P1) : ↥SL32), ((b.left 1 : ↥P1) : ↥SL32)) * tau := tau_mul_rho _
    have hm : rho (((a.left 1 * b.left tq : ↥P1) : ↥SL32), ((a.left tq * b.left 1 : ↥P1) : ↥SL32)) =
        rho (((a.left 1 : ↥P1) : ↥SL32), ((a.left tq : ↥P1) : ↥SL32)) *
          rho (((b.left tq : ↥P1) : ↥SL32), ((b.left 1 : ↥P1) : ↥SL32)) := by
      rw [← map_mul]
      rfl
    rw [hm, mul_assoc (rho _) tau, ← mul_assoc tau, key]
    simp only [mul_assoc]

@[expose] noncomputable def thetaW : ↥P1 ≀ᵣ Multiplicative (ZMod 2) →* MulAut WMod where
  toFun := thetaFun
  map_one' := by
    change rho (((1 : ↥P1) : ↥SL32), ((1 : ↥P1) : ↥SL32)) * tauPow 1 = 1
    rw [map_one tauPow, mul_one]
    exact map_one rho
  map_mul' := thetaFun_mul

theorem thetaW_apply (w : ↥P1 ≀ᵣ Multiplicative (ZMod 2)) :
    thetaW w = rho (((w.left 1 : ↥P1) : ↥SL32), ((w.left tq : ↥P1) : ↥SL32)) * tauPow w.right :=
  rfl

theorem thetaW_injective : Function.Injective thetaW := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hr : w.right = 1 := by
    rcases mz2_cases w.right with h | h
    · exact h
    · exfalso
      apply tau_not_mem_img
      rw [thetaW_apply, h, tauPow_tq] at hw
      rw [eq_inv_of_mul_eq_one_right hw]
      exact img.inv_mem (rho_mem_img _)
  rw [thetaW_apply, hr, map_one, mul_one] at hw
  have h2 := rho_injective (hw.trans (map_one rho).symm)
  have e1 : w.left 1 = 1 := Subtype.ext (congrArg Prod.fst h2)
  have e2 : w.left tq = 1 := Subtype.ext (congrArg Prod.snd h2)
  refine RegularWreathProduct.ext (funext fun q => ?_) hr
  rcases mz2_cases q with rfl | rfl
  · exact e1
  · exact e2

@[expose] noncomputable def stabE : Subgroup (MulAut WMod) := thetaW.range

theorem mem_stabE_iff {x : MulAut WMod} : x ∈ stabE ↔ x ∈ norm ∧ x (eW 0 0) = eW 0 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨norm.mul_mem (img_le_norm (rho_mem_img _)) (tauPow_mem_norm _), ?_⟩
    rw [thetaW_apply, MulAut.mul_apply, tauPow_fix_E00]
    exact rho_fix_E00 (w.left 1).2 (w.left tq).2
  · rintro ⟨hx, hxE⟩
    obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.1 hx
    · obtain ⟨h1, h2⟩ := mem_P1_of_rho_E00 (a := g.1) (b := g.2) hxE
      refine ⟨⟨fun q => if q = 1 then ⟨g.1, h1⟩ else ⟨g.2, h2⟩, 1⟩, ?_⟩
      rw [thetaW_apply]
      simp
    · have hxE' : rho g (eW 0 0) = eW 0 0 := by
        rw [MulAut.mul_apply, tau_eW_diag] at hxE
        exact hxE
      obtain ⟨h1, h2⟩ := mem_P1_of_rho_E00 (a := g.1) (b := g.2) hxE'
      refine ⟨⟨fun q => if q = 1 then ⟨g.1, h1⟩ else ⟨g.2, h2⟩, tq⟩, ?_⟩
      rw [thetaW_apply, tauPow_tq]
      simp

theorem stabE_le_norm : stabE ≤ norm := fun _ hx => (mem_stabE_iff.1 hx).1

theorem Shat_le_img : Shat ≤ img := Subgroup.map_le_range rho _

@[expose] noncomputable def thetaEquiv : ↥P1 ≀ᵣ Multiplicative (ZMod 2) ≃* ↥stabE :=
  MonoidHom.ofInjective thetaW_injective

theorem coe_thetaEquiv (w : ↥P1 ≀ᵣ Multiplicative (ZMod 2)) :
    ((thetaEquiv w : ↥stabE) : MulAut WMod) = thetaW w :=
  MonoidHom.ofInjective_apply thetaW_injective

@[expose] noncomputable def sigmaW : ↥P1 ≀ᵣ Multiplicative (ZMod 2) →* W3 where
  toFun w := ⟨fun q => sigP1 (w.left q), w.right⟩
  map_one' := RegularWreathProduct.ext (funext fun _ => map_one sigP1) rfl
  map_mul' _ _ := RegularWreathProduct.ext (funext fun _ => map_mul sigP1 _ _) rfl

@[expose] noncomputable def omegaW : ↥stabE →* W3 :=
  sigmaW.comp thetaEquiv.symm.toMonoidHom

theorem omegaW_thetaEquiv (w : ↥P1 ≀ᵣ Multiplicative (ZMod 2)) :
    omegaW (thetaEquiv w) = sigmaW w := by
  simp [omegaW]

theorem omegaW_eq_one_iff (x : ↥stabE) : omegaW x = 1 ↔ (x : MulAut WMod) ∈ Shat := by
  obtain ⟨w, rfl⟩ := thetaEquiv.surjective x
  rw [omegaW_thetaEquiv, coe_thetaEquiv]
  constructor
  · intro h
    have hr : w.right = 1 := congrArg RegularWreathProduct.right h
    have hl : ∀ q, sigP1 (w.left q) = 1 := fun q =>
      congrFun (congrArg RegularWreathProduct.left h) q
    rw [thetaW_apply, hr, map_one, mul_one]
    exact rho_mem_Shat ((sigP1_eq_one_iff _).1 (hl 1)) ((sigP1_eq_one_iff _).1 (hl tq))
  · intro h
    have hr : w.right = 1 := by
      rcases mz2_cases w.right with hr | hr
      · exact hr
      · exfalso
        apply tau_not_mem_img
        have hS : thetaW w ∈ img := Shat_le_img h
        rw [thetaW_apply, hr, tauPow_tq] at hS
        have := img.mul_mem (img.inv_mem
          (rho_mem_img (((w.left 1 : ↥P1) : ↥SL32), ((w.left tq : ↥P1) : ↥SL32)))) hS
        rwa [inv_mul_cancel_left] at this
    rw [thetaW_apply, hr, map_one, mul_one] at h
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj (rho_injective hab)
    have e1 : ((w.left 1 : ↥P1) : ↥SL32) ∈ Scen := by
      rw [← h1]
      exact ha
    have e2 : ((w.left tq : ↥P1) : ↥SL32) ∈ Scen := by
      rw [← h2]
      exact hb
    refine RegularWreathProduct.ext (funext fun q => ?_) hr
    rcases mz2_cases q with rfl | rfl
    · exact (sigP1_eq_one_iff _).2 e1
    · exact (sigP1_eq_one_iff _).2 e2

theorem mul_self_eq_one_of_mem_Shat {s : MulAut WMod} (hs : s ∈ Shat) : s * s = 1 := by
  obtain ⟨⟨a, b⟩, ⟨⟨x, y, ha⟩, ⟨x', y', hb⟩⟩, rfl⟩ := hs
  have ha2 : a * a = 1 := by
    apply eq_of_mat_eq
    rw [mat_mul, ha, scenMat_mul_self, mat_one]
  have hb2 : b * b = 1 := by
    apply eq_of_mat_eq
    rw [mat_mul, hb, scenMat_mul_self, mat_one]
  change rho (a, b) * rho (a, b) = 1
  rw [← map_mul, Prod.mk_mul_mk, ha2, hb2]
  exact map_one rho

namespace W3Gen

noncomputable local instance instFintypeW3 : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEqW3 : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance instDecN0W3 : DecidablePred (· ∈ W3.N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

@[expose] def wa : W3 := ⟨fun q => if q = 1 then cyc3 else 1, 1⟩

@[expose] def wb : W3 := ⟨fun q => if q = 1 then 1 else cyc3, 1⟩

@[expose] def wu : W3 := ⟨fun q => if q = 1 then Equiv.swap 1 2 else 1, 1⟩

@[expose] def wv : W3 := ⟨fun q => if q = 1 then 1 else Equiv.swap 1 2, 1⟩

theorem base_decomp : ∀ v : W3, v.right = 1 → ∃ i j : Fin 3, ∃ k l : Fin 2,
    v = wa ^ (i : ℕ) * wu ^ (k : ℕ) * wb ^ (j : ℕ) * wv ^ (l : ℕ) := by
  decide +kernel

theorem centralizer_N0_le : ∀ w : W3, (∀ n : W3, n ∈ W3.N0 → w * n = n * w) → w ∈ W3.N0 := by
  decide +kernel

end W3Gen

open W3Gen in
theorem W3.eq_bot_of_normal_isPGroup_two {Q : Subgroup W3} (hQ : Q.Normal) (h2 : IsPGroup 2 Q) :
    Q = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : IsPGroup 3 W3.N0 := IsPGroup.of_card (n := 2) (by rw [W3.card_N0]; norm_num)
  have hdis := IsPGroup.disjoint_of_ne 2 3 (by norm_num) Q W3.N0 h2 h3
  have hbot : ∀ x, x ∈ Q → x ∈ W3.N0 → x = 1 := fun x hx hx' =>
    Subgroup.disjoint_def.mp hdis hx hx'
  rw [eq_bot_iff]
  intro q hq
  have hc : ∀ n : W3, n ∈ W3.N0 → q * n = n * q := by
    intro n hn
    have hQ' : q * n * q⁻¹ * n⁻¹ ∈ Q := by
      have := Q.mul_mem hq (hQ.conj_mem q⁻¹ (Q.inv_mem hq) n)
      simpa [mul_assoc] using this
    have hN' : q * n * q⁻¹ * n⁻¹ ∈ W3.N0 :=
      W3.N0.mul_mem (W3.N0_normal.conj_mem n hn q) (W3.N0.inv_mem hn)
    have h1 := hbot _ hQ' hN'
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  exact Subgroup.mem_bot.mpr (hbot q hq (centralizer_N0_le q hc))

open W3Gen in
theorem omegaW_rho_c3_one (h : rho (c3, 1) ∈ stabE) : omegaW ⟨rho (c3, 1), h⟩ = wa := by
  have e : (⟨rho (c3, 1), h⟩ : ↥stabE) =
      thetaEquiv ⟨fun q => if q = 1 then cP1 else 1, 1⟩ := by
    apply Subtype.ext
    rw [coe_thetaEquiv, thetaW_apply]
    simp [cP1]
  rw [e, omegaW_thetaEquiv]
  refine RegularWreathProduct.ext (funext fun q => ?_) rfl
  rcases mz2_cases q with rfl | rfl
  · exact sigP1_cP1
  · simp [sigmaW, wa]

open W3Gen in
theorem omegaW_rho_one_c3 (h : rho (1, c3) ∈ stabE) : omegaW ⟨rho (1, c3), h⟩ = wb := by
  have e : (⟨rho (1, c3), h⟩ : ↥stabE) =
      thetaEquiv ⟨fun q => if q = 1 then 1 else cP1, 1⟩ := by
    apply Subtype.ext
    rw [coe_thetaEquiv, thetaW_apply]
    simp [cP1]
  rw [e, omegaW_thetaEquiv]
  refine RegularWreathProduct.ext (funext fun q => ?_) rfl
  rcases mz2_cases q with rfl | rfl
  · simp [sigmaW, wb]
  · simpa [sigmaW, wb, tq_ne_one] using sigP1_cP1

open W3Gen in
theorem omegaW_rho_u0_one (h : rho (u0, 1) ∈ stabE) : omegaW ⟨rho (u0, 1), h⟩ = wu := by
  have e : (⟨rho (u0, 1), h⟩ : ↥stabE) =
      thetaEquiv ⟨fun q => if q = 1 then uP1 else 1, 1⟩ := by
    apply Subtype.ext
    rw [coe_thetaEquiv, thetaW_apply]
    simp [uP1]
  rw [e, omegaW_thetaEquiv]
  refine RegularWreathProduct.ext (funext fun q => ?_) rfl
  rcases mz2_cases q with rfl | rfl
  · exact sigP1_uP1
  · simp [sigmaW, wu]

open W3Gen in
theorem omegaW_rho_one_u0 (h : rho (1, u0) ∈ stabE) : omegaW ⟨rho (1, u0), h⟩ = wv := by
  have e : (⟨rho (1, u0), h⟩ : ↥stabE) =
      thetaEquiv ⟨fun q => if q = 1 then 1 else uP1, 1⟩ := by
    apply Subtype.ext
    rw [coe_thetaEquiv, thetaW_apply]
    simp [uP1]
  rw [e, omegaW_thetaEquiv]
  refine RegularWreathProduct.ext (funext fun q => ?_) rfl
  rcases mz2_cases q with rfl | rfl
  · simp [sigmaW, wv]
  · simpa [sigmaW, wv, tq_ne_one] using sigP1_uP1

theorem omegaW_right_of_not_mem_img (x : ↥stabE) (hx : (x : MulAut WMod) ∉ img) :
    (omegaW x).right = tq := by
  obtain ⟨w, rfl⟩ := thetaEquiv.surjective x
  rw [omegaW_thetaEquiv]
  rcases mz2_cases w.right with h | h
  · exfalso
    apply hx
    rw [coe_thetaEquiv, thetaW_apply, h, map_one, mul_one]
    exact rho_mem_img _
  · exact h

open W3Gen in
theorem exists_omegaW_eq {H : Subgroup (MulAut WMod)} (hH : H ≤ stabE)
    (ha : rho (c3, 1) ∈ H) (hb : rho (1, c3) ∈ H) (hu : rho (u0, 1) ∈ H) (hv : rho (1, u0) ∈ H)
    {y : MulAut WMod} (hy : y ∈ H) (hyi : y ∉ img) (w : W3) :
    ∃ x : ↥stabE, (x : MulAut WMod) ∈ H ∧ omegaW x = w := by
  set R : Subgroup W3 := (H.subgroupOf stabE).map omegaW with hR
  have hmem : ∀ x : MulAut WMod, ∀ hx : x ∈ H, omegaW ⟨x, hH hx⟩ ∈ R := fun x hx =>
    ⟨⟨x, hH hx⟩, hx, rfl⟩
  have hwa : wa ∈ R := omegaW_rho_c3_one (hH ha) ▸ hmem _ ha
  have hwb : wb ∈ R := omegaW_rho_one_c3 (hH hb) ▸ hmem _ hb
  have hwu : wu ∈ R := omegaW_rho_u0_one (hH hu) ▸ hmem _ hu
  have hwv : wv ∈ R := omegaW_rho_one_u0 (hH hv) ▸ hmem _ hv
  have hbase : ∀ v : W3, v.right = 1 → v ∈ R := by
    intro v hv1
    obtain ⟨i, j, k, l, rfl⟩ := base_decomp v hv1
    exact R.mul_mem (R.mul_mem (R.mul_mem (R.pow_mem hwa _) (R.pow_mem hwu _))
      (R.pow_mem hwb _)) (R.pow_mem hwv _)
  have hyR := hmem y hy
  have hyr := omegaW_right_of_not_mem_img ⟨y, hH hy⟩ hyi
  have hw : w ∈ R := by
    rcases mz2_cases w.right with h | h
    · exact hbase w h
    · have h1 : (w * (omegaW ⟨y, hH hy⟩)⁻¹).right = 1 := by
        rw [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, h, hyr]
        exact mul_inv_cancel tq
      have h2 := R.mul_mem (hbase _ h1) hyR
      rwa [inv_mul_cancel_right] at h2
  obtain ⟨x, hx, hxw⟩ := hw
  exact ⟨x, hx, hxw⟩

end L3Wr

end H

end CFSG.Quasithin

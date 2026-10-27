module

public import CFSG.Quasithin.Background.SmithB42LnL4Grp
public import CFSG.LieType.Universal.SpecialLinearRoots
public import CFSG.Quasithin.Background.SmithCurtisHecke
public import CFSG.LieType.RootSystem.Form

public section

namespace CFSG.Quasithin.B42Ln

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Universal.SpecialLinear CFSG.Quasithin.SmithCurtis

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

theorem hA3 : TauCeti.IsFiniteType (CartanMatrix.A 3) := isFiniteType_A 3

abbrev W4 : Type := (coxeterMatrix hA3).Group

instance : Finite W4 := finite_group hA3

abbrev cs4 : CoxeterSystem (coxeterMatrix hA3) W4 := (coxeterMatrix hA3).toCoxeterSystem

theorem coxeterMatrix_A3 (i j : Fin 3) : coxeterMatrix hA3 i j =
    if i = j then 1 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 3 else 2 := by
  rw [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [CartanMatrix.A]

theorem sw_liftable : (coxeterMatrix hA3).IsLiftable sw := by
  intro i j
  rw [coxeterMatrix_A3]
  revert i j
  decide

@[expose] noncomputable def piW4 : W4 →* Equiv.Perm (Fin 4) := cs4.lift ⟨sw, sw_liftable⟩

theorem piW4_simple (s : Fin 3) : piW4 (cs4.simple s) = sw s :=
  cs4.lift_apply_simple sw_liftable s

@[expose] noncomputable def nW4 : W4 →* G4 := permHom.comp piW4

theorem nW4_simple (s : Fin 3) : nW4 (cs4.simple s) = n4 s := by
  rw [nW4, MonoidHom.comp_apply, piW4_simple]

theorem toStd_weylAction (w : W4) (v : Fin 3 → ℤ) :
    toStd 3 (weylAction hA3 w v) = toStd 3 v ∘ ⇑(piW4 w)⁻¹ := by
  obtain ⟨ω, rfl⟩ := cs4.wordProd_surjective w
  induction ω generalizing v with
  | nil =>
    funext a
    simp
  | cons k ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, Module.End.mul_apply, weylAction_simple,
      toStd_reflection, ih, map_mul, piW4_simple, _root_.mul_inv_rev]
    funext a
    simp only [Function.comp_apply, Equiv.Perm.coe_mul, sw, Equiv.swap_inv]

@[expose] def rootVec (a b : Fin 4) : Fin 3 → ℤ := fun k =>
  if (a : ℕ) ≤ k ∧ (k : ℕ) < b then 1 else if (b : ℕ) ≤ k ∧ (k : ℕ) < a then -1 else 0

theorem toStd_rootVec : ∀ a b : Fin 4, a ≠ b →
    toStd 3 (rootVec a b) = Pi.single a 1 - Pi.single b 1 := by
  decide

theorem rootVec_nonneg_iff : ∀ a b : Fin 4, a ≠ b → (0 ≤ rootVec a b ↔ a < b) := by
  decide

theorem nonneg_iff_lt {a b : Fin 4} (hab : a ≠ b) {v : Fin 3 → ℤ}
    (hv : toStd 3 v = Pi.single a 1 - Pi.single b 1) : 0 ≤ v ↔ a < b := by
  have : v = rootVec a b := toStd_injective 3 (hv.trans (toStd_rootVec a b hab).symm)
  rw [this]
  exact rootVec_nonneg_iff a b hab

theorem length_simple_mul_iff (w : W4) (s : Fin 3) :
    cs4.length (cs4.simple s * w) = cs4.length w + 1 ↔
      (piW4 w)⁻¹ s.castSucc < (piW4 w)⁻¹ s.succ := by
  rw [← cs4.not_isLeftDescent_iff, ← inv_inv w, cs4.isLeftDescent_inv_iff, inv_inv,
    ← nonneg_iff_not_isRightDescent hA3]
  apply nonneg_iff_lt ((piW4 w)⁻¹.injective.ne (Fin.castSucc_lt_succ (i := s)).ne)
  rw [toStd_weylAction, toStd_single, map_inv, inv_inv]
  funext a
  simp only [Function.comp_apply, Pi.sub_apply, Pi.single_apply, Equiv.Perm.eq_inv_iff_eq]

theorem pm_conj_x4_up : ∀ (π : Equiv.Perm (Fin 4)) (s : Fin 3),
    π⁻¹ s.castSucc < π⁻¹ s.succ → IsUp4 (pm π⁻¹ * xM4 s * pm π) := by
  decide

theorem pm_conj_x4_or_y4 : ∀ (π : Equiv.Perm (Fin 4)) (s : Fin 3),
    IsUp4 (pm π⁻¹ * xM4 s * pm π) ∨ IsUp4 (pm π⁻¹ * yM4 s * pm π) := by
  decide

theorem nW4_conj_x4 {w : W4} {s : Fin 3}
    (h : cs4.length (cs4.simple s * w) = cs4.length w + 1) :
    (nW4 w)⁻¹ * x4 s * nW4 w ∈ U4 := by
  rw [length_simple_mul_iff] at h
  show IsUp4 ((((nW4 w)⁻¹ * x4 s * nW4 w : G4)) : 𝕄₄)
  rw [nW4, MonoidHom.comp_apply, permHom_inv]
  exact pm_conj_x4_up _ _ h

@[expose] def cntF (π : Equiv.Perm (Fin 4)) : ℕ :=
  (Finset.univ.filter fun c : Fin 64 => ∀ i j : Fin 4, j < i → up4 c (π i) (π j) = 0).card

@[expose] def invCnt (π : Equiv.Perm (Fin 4)) : ℕ :=
  (Finset.univ.filter fun p : Fin 4 × Fin 4 => p.1 < p.2 ∧ π⁻¹ p.2 < π⁻¹ p.1).card

set_option maxRecDepth 100000 in
theorem cntF_mul_pow : ∀ π : Equiv.Perm (Fin 4), cntF π * 2 ^ invCnt π = 64 := by
  decide +kernel

theorem invCnt_sw_mul : ∀ (π : Equiv.Perm (Fin 4)) (s : Fin 3), π⁻¹ s.castSucc < π⁻¹ s.succ →
    invCnt (sw s * π) = invCnt π + 1 := by
  decide

theorem invCnt_sw : ∀ s : Fin 3, invCnt (sw s) = 1 := by decide

theorem mem_conj_inf_iff {π : Equiv.Perm (Fin 4)} {g : G4} :
    g ∈ U4.map (MulAut.conj (permHom π)).toMonoidHom ⊓ U4 ↔
      g ∈ U4 ∧ ∀ i j : Fin 4, j < i → (g : 𝕄₄) (π i) (π j) = 0 := by
  rw [Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, permHom_inv]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (isUp4_conj_iff h2).1 h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(isUp4_conj_iff h1).2 h2, h1⟩

theorem card_conj_inf (π : Equiv.Perm (Fin 4)) :
    Nat.card ↥(U4.map (MulAut.conj (permHom π)).toMonoidHom ⊓ U4) = cntF π := by
  let e : ↥(U4.map (MulAut.conj (permHom π)).toMonoidHom ⊓ U4) ≃
      {c : Fin 64 // ∀ i j : Fin 4, j < i → up4 c (π i) (π j) = 0} :=
    { toFun := fun g => ⟨code4 ((g : G4) : 𝕄₄), by
        have h := mem_conj_inf_iff.1 g.2
        rw [up4_code4 h.1]
        exact h.2⟩
      invFun := fun c => ⟨uOf c.1, mem_conj_inf_iff.2 ⟨uOf_mem c.1, c.2⟩⟩
      left_inv := fun g => Subtype.ext (eq_uOf (mem_conj_inf_iff.1 g.2).1).symm
      right_inv := fun c => Subtype.ext (code4_up4 c.1) }
  rw [Nat.card_congr e, card_subtype_eq]
  rfl

theorem heckeDeg_permHom (π : Equiv.Perm (Fin 4)) :
    heckeDeg U4 (permHom π) = 2 ^ invCnt π := by
  have h := Subgroup.relIndex_mul_card (U4.map (MulAut.conj (permHom π)).toMonoidHom) U4
  rw [card_conj_inf, card_U4, ← cntF_mul_pow π, mul_comm (cntF π)] at h
  have hc : 0 < cntF π := by
    rcases Nat.eq_zero_or_pos (cntF π) with h0 | h0
    · have := cntF_mul_pow π
      rw [h0, zero_mul] at this
      exact absurd this (by norm_num)
    · exact h0
  exact Nat.eq_of_mul_eq_mul_right hc h

theorem nW4_apply (w : W4) : nW4 w = permHom (piW4 w) := rfl

theorem heckeDeg_mul4 (w : W4) (s : Fin 3)
    (h : cs4.length (cs4.simple s * w) = cs4.length w + 1) :
    heckeDeg U4 (n4 s) * heckeDeg U4 (nW4 w) = heckeDeg U4 (nW4 (cs4.simple s * w)) := by
  rw [length_simple_mul_iff] at h
  rw [nW4_apply, nW4_apply, map_mul, piW4_simple, heckeDeg_permHom, heckeDeg_permHom,
    heckeDeg_permHom, invCnt_sw, invCnt_sw_mul _ _ h, pow_one, pow_succ, mul_comm]

end CFSG.Quasithin.B42Ln

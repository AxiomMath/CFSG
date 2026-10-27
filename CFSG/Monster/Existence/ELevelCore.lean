module

public import CFSG.Monster.Existence.ELevelDef

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.B.TwoA.Census

theorem add_add_self_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x v : V) :
    x + v + x = v := by
  rw [add_right_comm, ZModModule.add_self, zero_add]

theorem add_add_add_self_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x w k : V) :
    x + w + k + w = x + k := by
  rw [add_right_comm (x + w) k w, add_assoc x w w, ZModModule.add_self, add_zero]

theorem add_add_add_self_eq_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x y : V) :
    x + y + x + y = 0 :=
  (add_assoc (x + y) x y).trans (ZModModule.add_self (x + y))

theorem eq_of_pow_mul_pow_mul {G : Type*} [Group G] {z : G} (hz : z ≠ 1) (e c : ZMod 2) (q : G)
    (h : z ^ e.val * (z ^ c.val * q) = q) : e = c := by
  have h1 : z ^ e.val * z ^ c.val = 1 :=
    mul_right_cancel (b := q) ((mul_assoc _ _ q).trans (h.trans (one_mul q).symm))
  have h2 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h2 e with rfl | rfl <;> rcases h2 c with rfl | rfl
  · rfl
  · rw [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul] at h1
    exact absurd h1 hz
  · rw [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, mul_one] at h1
    exact absurd h1 hz
  · rfl

theorem inv_mul_mul_eq_pow_val {G : Type*} [Group G] {a b z : G} {β : ZMod 2}
    (hβ : a * b = b * a ↔ β = 0) (hc : a⁻¹ * b * a * b⁻¹ = 1 ∨ a⁻¹ * b * a * b⁻¹ = z) :
    a⁻¹ * b * a = z ^ β.val * b := by
  have h2 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h2 β with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, one_mul, mul_assoc, ← hβ.2 rfl, inv_mul_cancel_left]
  · rw [ZMod.val_one, pow_one]
    rcases hc with h | h
    · have e : a⁻¹ * b * a = b := mul_inv_eq_one.1 h
      have hab : a * b = b * a :=
        calc a * b = a * (a⁻¹ * b * a) := by rw [e]
          _ = b * a := by rw [mul_assoc, mul_inv_cancel_left]
      exact absurd (hβ.1 hab) one_ne_zero
    · exact mul_inv_eq_iff_eq_mul.1 h

theorem zQ_ne_one : zQ ≠ 1 := fun h =>
  absurd ((orderOf_zQ.symm.trans (congrArg orderOf h)).trans orderOf_one) (by norm_num)

theorem phi0_coordOf_mul_mul (a b c : Q) :
    phi0 (coordOf (a * b * c)) = phi0 (coordOf a) + phi0 (coordOf b) + phi0 (coordOf c) :=
  (phi0_coordOf_mul (a * b) c).trans (congrArg (· + phi0 (coordOf c)) (phi0_coordOf_mul a b))

theorem phi0_coordOf_conj_mul_inv (a b : Q) : phi0 (coordOf (a⁻¹ * b * a * b⁻¹)) = 0 :=
  ((phi0_coordOf_mul (a⁻¹ * b * a) b⁻¹).trans
    (congrArg₂ (· + ·) (phi0_coordOf_mul_mul a⁻¹ b a) (phi0_coordOf_inv b))).trans
    ((congrArg (fun x => x + phi0 (coordOf b) + phi0 (coordOf a) + phi0 (coordOf b))
      (phi0_coordOf_inv a)).trans (add_add_add_self_eq_zero _ _))

theorem inv_mul_mul_eq_zQ_pow (a b : Q) :
    a⁻¹ * b * a = zQ ^ (bL (phi0 (coordOf a)) (phi0 (coordOf b))).val * b :=
  inv_mul_mul_eq_pow_val (commute_iff_bL a b)
    ((phi0_coordOf_eq_zero_iff _).1 (phi0_coordOf_conj_mul_inv a b))

theorem modTwoEnd_phi0_eq_of_conjQ_eq {p : Pvis} {q q' : Q} (h : conjQ p (q⁻¹ * q' * q) = q') :
    modTwoEnd p.1.2 (phi0 (coordOf q')) = phi0 (coordOf q') :=
  have e : phi0 (coordOf (q⁻¹ * q' * q)) = phi0 (coordOf q') :=
    (phi0_coordOf_mul_mul q⁻¹ q' q).trans
      ((congrArg (fun x => x + phi0 (coordOf q') + phi0 (coordOf q)) (phi0_coordOf_inv q)).trans
        (add_add_self_eq _ _))
  (congrArg (modTwoEnd p.1.2) e).symm.trans
    ((phi0_conjQ p _).symm.trans (congrArg (fun r => phi0 (coordOf r)) h))

theorem bL_phi0_eq_of_conjQ_eq {p : Pvis} {q q' : Q} {c : ZMod 2}
    (h : conjQ p (q⁻¹ * q' * q) = q') (hc : conjQ p q' = zQ ^ c.val * q') :
    bL (phi0 (coordOf q)) (phi0 (coordOf q')) = c :=
  eq_of_pow_mul_pow_mul zQ_ne_one _ _ q'
    (((conjQ_zQ_pow_mul p _ q').trans (congrArg (_ * ·) hc)).symm.trans
      ((congrArg (conjQ p) (inv_mul_mul_eq_zQ_pow q q')).symm.trans h))

theorem phi0_coordOf_mul_conjQ_add (p : Pvis) (q w : Q) :
    phi0 (coordOf (q * w * conjQ p q)) + phi0 (coordOf w) =
      phi0 (coordOf q) + modTwoEnd p.1.2 (phi0 (coordOf q)) :=
  (congrArg (· + phi0 (coordOf w)) ((phi0_coordOf_mul_mul q w (conjQ p q)).trans
    (congrArg (phi0 (coordOf q) + phi0 (coordOf w) + ·) (phi0_conjQ p q)))).trans
    (add_add_add_self_eq _ _ _)

theorem bL_modTwoEnd_right {g : latticeO} (hg : ∀ x : L2, modTwoEnd g (modTwoEnd g x) = x)
    (x u : L2) : bL x (modTwoEnd g u) = bL (modTwoEnd g x) u :=
  (bL_modTwoEnd g x (modTwoEnd g u)).symm.trans (congrArg (bL (modTwoEnd g x)) (hg u))

theorem bL_add_modTwoEnd {g : latticeO} (hg : ∀ x : L2, modTwoEnd g (modTwoEnd g x) = x)
    (y u : L2) : bL y (modTwoEnd g u + u) = bL (y + modTwoEnd g y) u :=
  ((map_add (bL y) (modTwoEnd g u) u).trans
    ((congrArg (· + bL y u) (bL_modTwoEnd_right hg y u)).trans (add_comm _ _))).trans
    (LinearMap.map_add₂ bL y (modTwoEnd g y) u).symm

theorem bL_add_modTwoEnd_eq_zero {g : latticeO} (hg : ∀ x : L2, modTwoEnd g (modTwoEnd g x) = x)
    {f : L2} (hf : modTwoEnd g f = f) (y : L2) : bL f (y + modTwoEnd g y) = 0 :=
  (map_add (bL f) y (modTwoEnd g y)).trans
    ((congrArg (bL f y + ·) ((bL_modTwoEnd_right hg f y).trans
      (congrArg (fun x => bL x y) hf))).trans (ZModModule.add_self _))

theorem cosetPair_snd
    (i : ℕ) : (cosetPair i).1.2 = monoAO i :=
  congrArg Prod.snd (coe_cosetPair i)

theorem modTwoEnd_cosetPair_sq
    {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 6) (x : L2) :
    modTwoEnd (cosetPair i).1.2 (modTwoEnd (cosetPair i).1.2 x) = x := by
  have h1 : 1 ≤ i ∧ i < 7 := by omega
  have h : modTwoEnd (monoAO i * monoAO i) = 1 := by
    rcases (mem_zpowers_negOneO_iff _).1 ((QuotientGroup.eq_one_iff _).1
      (mk_monoAO_sq h1.1 h1.2)) with h | h
    · rw [h, modTwoEnd_one]
    · rw [h]
      exact modTwoEnd_eq_one_of_mat (Or.inr mat_negOneO)
  rw [cosetPair_snd]
  exact (LinearMap.congr_fun (modTwoEnd_mul (monoAO i) (monoAO i)) x).symm.trans
    (LinearMap.congr_fun h x)

theorem noConfig_of_checkSpec
    {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 6) (h : CheckSpec i) :
    NoConfig i := by
  obtain ⟨Fb, cs, hFb, hcs, hmain⟩ := h
  intro q q' hs hq' hsq' hcomm hα
  have hκv := modTwoEnd_phi0_eq_of_conjQ_eq hα
  have h2 := bL_phi0_eq_of_conjQ_eq hα (hcs q' hκv)
  have key : ∀ s : Q, IsShortCoord (coordOf s) → IsShortCoord (coordOf (q' * s)) →
      q' * s = s * q' → phi0 (coordOf s) + phi0 (coordOf (cosetW i)) =
        phi0 (coordOf q) + modTwoEnd (cosetPair i).1.2 (phi0 (coordOf q)) → False := by
    intro s hs hsq' hcomm hSW
    have hSv : phi0 (coordOf s) + phi0 (coordOf q') ∈ shortSet := by
      rw [(add_comm (phi0 (coordOf s)) (phi0 (coordOf q'))).trans (phi0_coordOf_mul q' s).symm]
      exact hsq'
    obtain ⟨u, hu1, hu2⟩ := hmain (phi0 (coordOf s)) (phi0 (coordOf q')) hs hq' hSv hκv
      ((bL_comm _ _).trans ((commute_iff_bL q' s).1 hcomm))
      fun f hf => (congrArg (bL f) hSW).trans
        (bL_add_modTwoEnd_eq_zero (modTwoEnd_cosetPair_sq hi) (hFb f hf) _)
    exact hu2 ((congrArg (fun x => bL x u) hSW).trans
      ((bL_add_modTwoEnd (modTwoEnd_cosetPair_sq hi) (phi0 (coordOf q)) u).symm.trans
        ((congrArg (bL (phi0 (coordOf q))) hu1).trans h2)))
  exact key _ hs hsq' hcomm (phi0_coordOf_mul_conjQ_add (cosetPair i) q (cosetW i))

end CFSG.Monster.Existence

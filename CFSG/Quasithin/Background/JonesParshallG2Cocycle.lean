module

public import CFSG.Quasithin.Background.JonesParshallG2Module
public import CFSG.Quasithin.Background.JonesParshallG2Perfect

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Open

variable {F : Type} [Field F]

@[expose] def bilQ (w w' : Ix3 → F) : F :=
  w (.inl 0) * w' (.inr 0) + w (.inl 1) * w' (.inr 1) + w (.inl 2) * w' (.inr 2) +
    w (.inr 0) * w' (.inl 0) + w (.inr 1) * w' (.inl 1) + w (.inr 2) * w' (.inl 2)

@[expose] def quadQ6 (w : Ix3 → F) : F :=
  w (.inl 0) * w (.inr 0) + w (.inl 1) * w (.inr 1) + w (.inl 2) * w (.inr 2)

theorem bilQ_eq (w w' : Ix3 → F) : bilQ w w' = quadQ6 (w + w') - quadQ6 w - quadQ6 w' := by
  simp only [bilQ, quadQ6, Pi.add_apply]
  ring

theorem norm_zI_add (w : Ix3 → F) (c : F) :
    cayleyNorm (zI w + c • cayleyOne F) = c * c + quadQ6 w := by
  rw [q6_eta w, zI_q6, cayleyOne_eq, zmk_smul, zmk_add, cayleyNorm_zmk]
  simp [quadQ6, q6]

theorem bilQ_add_left (w w' x : Ix3 → F) : bilQ (w + w') x = bilQ w x + bilQ w' x := by
  simp only [bilQ, Pi.add_apply]
  ring

theorem bilQ_smul_left (c : F) (w x : Ix3 → F) : bilQ (c • w) x = c * bilQ w x := by
  simp only [bilQ, Pi.smul_apply, smul_eq_mul]
  ring

theorem eq_of_bilQ {z z' : Ix3 → F} (h : ∀ w, bilQ z w = bilQ z' w) : z = z' := by
  have e : ∀ i : Ix3, z i = z' i := by
    intro i
    rcases i with i | i <;> fin_cases i
    · simpa [bilQ, q6] using h (q6 0 0 0 1 0 0)
    · simpa [bilQ, q6] using h (q6 0 0 0 0 1 0)
    · simpa [bilQ, q6] using h (q6 0 0 0 0 0 1)
    · simpa [bilQ, q6] using h (q6 1 0 0 0 0 0)
    · simpa [bilQ, q6] using h (q6 0 1 0 0 0 0)
    · simpa [bilQ, q6] using h (q6 0 0 1 0 0 0)
  exact funext e

variable [CharP F 2]

theorem bilQ_g2Act (g : ↥(cayleyGroup F)) (w w' : Ix3 → F) :
    bilQ (g2Act g w) (g2Act g w') = bilQ w w' := by
  have hq : ∀ x : Ix3 → F, quadQ6 (g2Act g x) + (cgE g (zI x)).1 * (cgE g (zI x)).1 =
      quadQ6 x := fun x => by
    have h := cg_norm g (zI x)
    rw [g2_zI_eq g x, norm_zI_add] at h
    have h' : cayleyNorm (zI x) = quadQ6 x := by
      rw [q6_eta x, zI_q6, cayleyNorm_zmk]
      simp [quadQ6, q6]
    rw [h'] at h
    linear_combination h
  have hc : (cgE g (zI (w + w'))).1 = (cgE g (zI w)).1 + (cgE g (zI w')).1 := by
    rw [zI_add, map_add, Prod.fst_add]
  have h1 := hq (w + w')
  have h2 := hq w
  have h3 := hq w'
  rw [map_add, hc] at h1
  rw [bilQ_eq, bilQ_eq]
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination h1 - h2 - h3 -
    ((cgE g (zI w)).1 * (cgE g (zI w')).1) * h2F

@[expose] def ellG (g : ↥(cayleyGroup F)) (w : Ix3 → F) : F := (cgE g⁻¹ (zI w)).1

omit [CharP F 2] in
theorem ellG_add (g : ↥(cayleyGroup F)) (w w' : Ix3 → F) :
    ellG g (w + w') = ellG g w + ellG g w' := by
  rw [ellG, ellG, ellG, zI_add, map_add, Prod.fst_add]

omit [CharP F 2] in
theorem ellG_smul (g : ↥(cayleyGroup F)) (c : F) (w : Ix3 → F) :
    ellG g (c • w) = c * ellG g w := by
  have hzI : zI (c • w) = c • zI w := by
    rw [q6_eta w, q6_smul, zI_q6, zI_q6, zmk_smul]
    simp
  rw [ellG, ellG, hzI, map_smul, Prod.smul_fst, smul_eq_mul]

@[expose] def fG (g : ↥(cayleyGroup F)) : Ix3 → F :=
  q6 (ellG g (q6 0 0 0 1 0 0)) (ellG g (q6 0 0 0 0 1 0)) (ellG g (q6 0 0 0 0 0 1))
    (ellG g (q6 1 0 0 0 0 0)) (ellG g (q6 0 1 0 0 0 0)) (ellG g (q6 0 0 1 0 0 0))

omit [CharP F 2] in
theorem bilQ_fG (g : ↥(cayleyGroup F)) (w : Ix3 → F) : bilQ (fG g) w = ellG g w := by
  have hw : w = w (.inl 0) • q6 1 0 0 0 0 0 + w (.inl 1) • q6 0 1 0 0 0 0 +
      w (.inl 2) • q6 0 0 1 0 0 0 + w (.inr 0) • q6 0 0 0 1 0 0 + w (.inr 1) • q6 0 0 0 0 1 0 +
      w (.inr 2) • q6 0 0 0 0 0 1 := by
    conv_lhs => rw [q6_eta w]
    simp only [q6_smul, q6_add, mul_one, mul_zero, add_zero, zero_add]
  conv_rhs => rw [hw]
  simp only [ellG_add, ellG_smul]
  simp only [bilQ, fG, q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons]
  ring

theorem ellG_mul (g h : ↥(cayleyGroup F)) (w : Ix3 → F) :
    ellG (g * h) w = ellG g w + ellG h (g2Act g⁻¹ w) := by
  rw [ellG, _root_.mul_inv_rev, cg_mul_apply, g2_zI_eq g⁻¹ w, LinearEquiv.map_add,
    LinearEquiv.map_smul, cg_one, Prod.fst_add, Prod.smul_fst, cayleyOne_eq, add_comm]
  simp only [zmk, smul_eq_mul, mul_one]
  rfl

theorem fG_mem : fG ∈ Z1A (g2Act (F := F)) := by
  intro g h
  refine eq_of_bilQ fun w => ?_
  rw [bilQ_fG, ellG_mul, bilQ_add_left, bilQ_fG]
  congr 1
  have e : w = g2Act g (g2Act g⁻¹ w) := by
    change w = (g2Act g * g2Act g⁻¹) w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  conv_rhs => rw [e]
  rw [bilQ_g2Act, bilQ_fG]

theorem g2Act_smul (g : ↥(cayleyGroup F)) (c : F) (w : Ix3 → F) :
    g2Act g (c • w) = c • g2Act g w := by
  have hzI : zI (c • w) = c • zI w := by
    rw [q6_eta w, q6_smul, zI_q6, zI_q6, zmk_smul]
    simp
  rw [g2Act_apply, g2Act_apply, hzI, LinearEquiv.map_smul, zP_smul]

theorem smul_fG_mem (c : F) : c • fG ∈ Z1A (g2Act (F := F)) := by
  intro g h
  rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, fG_mem g h, smul_add, g2Act_smul]

omit [CharP F 2] in
theorem fG_g2A (A : SL3 F) : fG (g2A A) = 0 := by
  have h : ∀ w, ellG (g2A A) w = 0 := fun w => by
    rw [ellG, ← map_inv]
    rfl
  simp only [fG, h, q6_zero]

theorem fG_g2X (a : Fin 3 → F) : fG (g2X a) = q6 (a 0) (a 1) (a 2) 0 0 0 := by
  have h : ∀ w, ellG (g2X a) w = a 0 * w (.inr 0) + a 1 * w (.inr 1) + a 2 * w (.inr 2) :=
    fun w => by
      rw [ellG, g2X_inv]
      change (xaFun a (zI w)).1 = _
      rw [q6_eta w, zI_q6, xaFun_zmk]
      simp [zmk, q6]
  simp only [fG, h, q6]
  apply q6_congr <;> simp

theorem fG_g2Y (b : Fin 3 → F) : fG (g2Y b) = q6 0 0 0 (b 0) (b 1) (b 2) := by
  have h : ∀ w, ellG (g2Y b) w = b 0 * w (.inl 0) + b 1 * w (.inl 1) + b 2 * w (.inl 2) :=
    fun w => by
      rw [ellG, g2Y_inv]
      change (ybFun b (zI w)).1 = _
      rw [q6_eta w, zI_q6, ybFun_zmk]
      simp [zmk, q6]
  simp only [fG, h, q6]
  apply q6_congr <;> simp

end CFSG.Quasithin.JonesParshall

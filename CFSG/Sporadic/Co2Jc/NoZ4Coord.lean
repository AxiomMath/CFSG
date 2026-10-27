module

public import CFSG.Sporadic.Co2Jc.Native.NoZ4
public import CFSG.Sporadic.Co2Jc.Model

public noncomputable section
namespace CFSG.Sporadic.Co2Jc.NoZ4
open CFSG.Sporadic.Co2Jc
open CFSG.Sporadic.Co2Smith Subgroup

noncomputable local instance : CommGroup ↥Jc :=
  { (inferInstance : Group ↥Jc) with mul_comm := fun a b => Subtype.ext (Jc_comm a.2 b.2) }

theorem Jc_sq (a : ↥Jc) : a * a = 1 := by
  obtain ⟨m, hm, rfl⟩ := exists_jcA a
  rw [← jcA_xor, Nat.xor_self, jcA_zero]

@[expose] def coordBit (i : Fin 10) (a : ↥Jc) : ZMod 2 :=
  if (coord a).testBit i.val then 1 else 0

theorem coordBit_mul (i : Fin 10) (a b : ↥Jc) :
    coordBit i (a * b) = coordBit i a + coordBit i b := by
  rw [coordBit, coord_mul, Nat.testBit_xor]
  rcases Bool.eq_false_or_eq_true ((coord a).testBit i.val) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true ((coord b).testBit i.val) with hb | hb <;>
    simp only [coordBit, ha, hb, if_true, if_false] <;> decide

theorem coordBit_one (i : Fin 10) : coordBit i 1 = 0 := by
  simp [coordBit, coord_one]

@[expose] def coordBitHom (i : Fin 10) : Additive ↥Jc →+ ZMod 2 where
  toFun a := coordBit i a.toMul
  map_zero' := coordBit_one i
  map_add' a b := by
    simpa using coordBit_mul i a.toMul b.toMul

theorem coordBitHom_apply (i : Fin 10) (a : ↥Jc) :
    coordBitHom i (Additive.ofMul a) = coordBit i a := by
  simp [coordBitHom]

theorem coordBitHom_jcA (i : Fin 10) {m : ℕ} (hm : m < 1024) :
    coordBitHom i (Additive.ofMul (jcA m)) = if m.testBit i.val then 1 else 0 := by
  rw [coordBitHom_apply, coordBit, coord_jcA hm]

theorem coordBitHom_e (i j : Fin 10) :
    coordBitHom i (Additive.ofMul (jcA (2 ^ j.val))) = if i = j then 1 else 0 := by
  rw [coordBitHom_jcA i (by
    have h := Nat.pow_lt_pow_right (by norm_num : 1 < 2) j.isLt
    norm_num at h ⊢
    exact h)]
  rw [Nat.testBit_two_pow]
  by_cases h : i.val = j.val
  · have hij : i = j := Fin.ext h
    simp [h, hij]
  · have hji : ¬ j.val = i.val := fun hji => h hji.symm
    have hij : i ≠ j := fun hh => h (congrArg Fin.val hh)
    simp [hji, hij]

theorem Jc_four_smul (a : Additive ↥Jc) : 4 • a = 0 := by
  show Additive.ofMul (a.toMul ^ 4) = 0
  have h4 : a.toMul ^ 4 = 1 := by
    have h2 : a.toMul * a.toMul = 1 := Jc_sq a.toMul
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two, h2, mul_one]
  rw [h4]
  rfl

local instance : Module (ZMod 4) (Additive ↥Jc) :=
  AddCommGroup.zmodModule Jc_four_smul

@[expose] def eL : (Fin 10 → ZMod 4) →ₗ[ZMod 4] Additive ↥Jc where
  toFun y := ∑ i, y i • (Additive.ofMul (jcA (2 ^ i.val)) : Additive ↥Jc)
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_assoc, RingHom.id_apply]

theorem eL_apply (y : Fin 10 → ZMod 4) :
    eL y = ∑ i, y i • (Additive.ofMul (jcA (2 ^ i.val)) : Additive ↥Jc) := rfl

theorem val_smul_one (n : ZMod 4) : n.val • (1 : ZMod 2) = (n.val : ZMod 2) := by
  rw [nsmul_eq_mul, mul_one]

theorem coordBitHom_eL (i : Fin 10) (y : Fin 10 → ZMod 4) :
    coordBitHom i (eL y) = ((y i).val : ZMod 2) := by
  rw [eL_apply]
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · rw [show (y i • (Additive.ofMul (jcA (2 ^ i.val)) : Additive ↥Jc)) =
        (y i).val • (Additive.ofMul (jcA (2 ^ i.val)) : Additive ↥Jc) from rfl]
    rw [map_nsmul, coordBitHom_e]
    simp [val_smul_one]
  · intro j _ hji
    rw [show (y j • (Additive.ofMul (jcA (2 ^ j.val)) : Additive ↥Jc)) =
        (y j).val • (Additive.ofMul (jcA (2 ^ j.val)) : Additive ↥Jc) from rfl]
    rw [map_nsmul, coordBitHom_e, if_neg (Ne.symm hji), nsmul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem coordBitHom_sep (a : Additive ↥Jc)
    (h : ∀ i : Fin 10, coordBitHom i a = 0) : a = 0 := by
  have hx : a.toMul = jcA (coord a.toMul) := (jcA_coord a.toMul).symm
  have hbits : ∀ i, (coord a.toMul).testBit i = false := by
    intro i
    by_cases hi : i < 10
    · have hz : coordBit ⟨i, hi⟩ a.toMul = 0 := h ⟨i, hi⟩
      rcases Bool.eq_false_or_eq_true ((coord a.toMul).testBit i) with hbit | hbit
      · exfalso
        have hz' : (1 : ZMod 2) = 0 := by simpa [coordBit, hbit] using hz
        exact absurd hz' (by decide)
      · exact hbit
    · apply Nat.testBit_eq_false_of_lt
      have hlt := coord_lt a.toMul
      have h2 : (2 : ℕ) ^ 10 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hi)
      omega
  have hc : coord a.toMul = 0 := Nat.zero_of_testBit_eq_false hbits
  rw [show a = Additive.ofMul (jcA (coord a.toMul)) from congrArg Additive.ofMul hx,
    hc, jcA_zero]
  rfl

theorem eL_eq_zero_iff (y : Fin 10 → ZMod 4) :
    eL y = 0 ↔ ∀ i : Fin 10, (y i).val % 2 = 0 := by
  constructor
  · intro h i
    have hz : ((y i).val : ZMod 2) = 0 := by
      have := congrArg (coordBitHom i) h
      rwa [coordBitHom_eL, map_zero] at this
    rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff] at hz
    exact hz
  · intro h
    apply coordBitHom_sep
    intro i
    rw [coordBitHom_eL, ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
    exact h i

theorem eL_surjective : Function.Surjective eL := by
  intro b
  let m := coord b.toMul
  let y : Fin 10 → ZMod 4 := fun i => if m.testBit i.val then 1 else 0
  refine ⟨y, ?_⟩
  have hb : b = Additive.ofMul (jcA (coord b.toMul)) :=
    congrArg Additive.ofMul (jcA_coord b.toMul).symm
  have hsub : ∀ i : Fin 10, coordBitHom i (eL y - b) = 0 := by
    intro i
    rw [hb, map_sub, coordBitHom_eL, coordBitHom_jcA i (coord_lt b.toMul)]
    by_cases h : (coord b.toMul).testBit i.val
    · simp [y, m, h]
      decide
    · simp [y, m, h]
      decide
  have hzero : eL y - b = 0 := coordBitHom_sep _ hsub
  exact sub_eq_zero.mp hzero

theorem glNJT_two_pow (k : Fin 3) (i : Fin 10) :
    Co2Smith.Native.glNJT k.val (2 ^ i.val) =
      (Co2Smith.Native.glNJTab[k.val]!)[i.val]! := by
  fin_cases k <;> fin_cases i <;> decide

theorem qA_jcA_two_pow (k : Fin 3) (i : Fin 10) :
    (qA k.val) (jcA (2 ^ i.val)) =
      jcA ((Co2Smith.Native.glNJTab[k.val]!)[i.val]!) := by
  rw [qA_jcA k.isLt, glNJT_two_pow]

section VGroup

variable {V : Type} [CommGroup V]

theorem V_four_smul (ι : ↥Jc →* V) (h1 : ∀ v : V, ∃ a, v ^ 2 = ι a)
    (a : Additive V) : 4 • a = 0 := by
  obtain ⟨b, hb⟩ := h1 a.toMul
  show Additive.ofMul (a.toMul ^ 4) = 0
  have h4 : a.toMul ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    rw [show a.toMul * a.toMul = ι b by rw [← pow_two]; exact hb]
    rw [← map_mul, Jc_sq, map_one]
  rw [h4]
  rfl

@[expose, instance_reducible] def VModule (ι : ↥Jc →* V) (h1 : ∀ v : V, ∃ a, v ^ 2 = ι a) :
    Module (ZMod 4) (Additive V) :=
  AddCommGroup.zmodModule (V_four_smul ι h1)

@[expose] def iotaA (ι : ↥Jc →* V) : Additive ↥Jc →+ Additive V where
  toFun a := Additive.ofMul (ι a.toMul)
  map_zero' := by simp
  map_add' a b := by simp [map_mul]

theorem iotaA_injective {ι : ↥Jc →* V} (hι : Function.Injective ι) :
    Function.Injective (iotaA ι) := by
  intro a b h
  have h' : ι a.toMul = ι b.toMul := congrArg Additive.toMul h
  have h'' := hι h'
  rw [show a = Additive.ofMul a.toMul from rfl, show b = Additive.ofMul b.toMul from rfl, h'']

@[expose] def phi (v : Fin 10 → Additive V) [Module (ZMod 4) (Additive V)] :
    (Fin 10 → ZMod 4) →ₗ[ZMod 4] Additive V where
  toFun x := ∑ i, x i • v i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_assoc, RingHom.id_apply]

theorem phi_apply (v : Fin 10 → Additive V) [Module (ZMod 4) (Additive V)]
    (x : Fin 10 → ZMod 4) : phi v x = ∑ i, x i • v i := rfl

theorem phi_two_smul {ι : ↥Jc →* V} {v : Fin 10 → Additive V}
    [Module (ZMod 4) (Additive V)]
    (hv : ∀ i, (2 : ZMod 4) • v i = iotaA ι (Additive.ofMul (jcA (2 ^ i.val))))
    (x : Fin 10 → ZMod 4) : phi v ((2 : ZMod 4) • x) = iotaA ι (eL x) := by
  rw [phi_apply, eL_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm : ((2 : ZMod 4) • x) i • v i = x i • ((2 : ZMod 4) • v i) := by
    rw [Pi.smul_apply]
    module
  rw [hterm, hv i, ZMod.map_smul]

theorem phi_injective {ι : ↥Jc →* V} {v : Fin 10 → Additive V}
    [Module (ZMod 4) (Additive V)] (hι : Function.Injective ι)
    (hv : ∀ i, (2 : ZMod 4) • v i = iotaA ι (Additive.ofMul (jcA (2 ^ i.val)))) :
    Function.Injective (phi v) := by
  intro x y hxy
  have h2 : phi v ((2 : ZMod 4) • x) = phi v ((2 : ZMod 4) • y) := by
    rw [LinearMap.map_smul, LinearMap.map_smul, hxy]
  rw [phi_two_smul (ι := ι) (v := v) hv x, phi_two_smul (ι := ι) (v := v) hv y] at h2
  have h2' : eL x = eL y := iotaA_injective hι h2
  have hxy0 : phi v (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  let z : Fin 10 → ZMod 4 := fun i => if (x - y) i = 0 then 0 else 1
  have hz2 : (2 : ZMod 4) • z = x - y := by
    funext i
    have hcases : (x - y) i = 0 ∨ (x - y) i = 2 := by
      have hi : ((x - y) i).val % 2 = 0 :=
        (eL_eq_zero_iff (x - y)).1 (by rw [map_sub, h2', sub_self]) i
      have hlt : ((x - y) i).val < 4 := ZMod.val_lt _
      have hv0 : ((x - y) i).val = 0 ∨ ((x - y) i).val = 2 := by omega
      rcases hv0 with h0 | h2v
      · left; exact ZMod.val_injective 4 h0
      · right; exact ZMod.val_injective 4 h2v
    rcases hcases with h0 | h2v
    · have h0' : x i - y i = 0 := h0
      have hzi0 : z i = 0 := by
        change (if x i - y i = 0 then 0 else 1) = 0
        rw [if_pos h0']
      rw [Pi.smul_apply, hzi0]
      change (2 : ZMod 4) • 0 = x i - y i
      rw [h0', smul_zero]
    · have h2v' : x i - y i = 2 := h2v
      have hzi1 : z i = 1 := by
        change (if x i - y i = 0 then 0 else 1) = 1
        rw [if_neg (by rw [h2v']; decide)]
      rw [Pi.smul_apply, hzi1]
      change (2 : ZMod 4) • 1 = x i - y i
      rw [h2v']
      norm_num
  have hz_eL : eL z = 0 := by
    apply iotaA_injective hι
    rw [map_zero, ← phi_two_smul (ι := ι) (v := v) hv z, hz2, hxy0]
  have hz0 : z = 0 := by
    funext i
    have hzi : (z i).val % 2 = 0 := (eL_eq_zero_iff z).1 hz_eL i
    have h1 : z i = 0 ∨ z i = 1 := by
      by_cases h : x i - y i = 0
      · left
        change (if x i - y i = 0 then 0 else 1) = 0
        rw [if_pos h]
      · right
        change (if x i - y i = 0 then 0 else 1) = 1
        rw [if_neg h]
    rcases h1 with h0 | h1
    · exact h0
    · exfalso
      have h1v : ((1 : ZMod 4)).val % 2 = 0 := by simpa [h1] using hzi
      exact absurd h1v (by decide)
  have hsub : x - y = 0 := by rw [← hz2, hz0, smul_zero]
  exact sub_eq_zero.mp hsub

theorem phi_surjective {ι : ↥Jc →* V} {v : Fin 10 → Additive V}
    [Module (ZMod 4) (Additive V)] (h1 : ∀ v : V, ∃ a, v ^ 2 = ι a)
    (h2 : ∀ v : V, v ^ 2 = 1 → ∃ a, v = ι a)
    (hv : ∀ i, (2 : ZMod 4) • v i = iotaA ι (Additive.ofMul (jcA (2 ^ i.val)))) :
    Function.Surjective (phi v) := by
  intro a
  obtain ⟨b, hb⟩ := h1 a.toMul
  have hb' : (2 : ℕ) • a = iotaA ι (Additive.ofMul b) := by
    rw [show a = Additive.ofMul a.toMul from rfl]
    exact congrArg Additive.ofMul hb
  obtain ⟨x, hx⟩ := eL_surjective (Additive.ofMul b)
  let w := phi v x
  have hw : (2 : ZMod 4) • w = iotaA ι (Additive.ofMul b) := by
    have hw'' : (2 : ZMod 4) • w = phi v ((2 : ZMod 4) • x) := by
      change (2 : ZMod 4) • phi v x = phi v ((2 : ZMod 4) • x)
      exact (LinearMap.map_smul (phi v) (2 : ZMod 4) x).symm
    rw [hw'', phi_two_smul (ι := ι) (v := v) hv x, hx]
  have hb'' : (2 : ZMod 4) • a = iotaA ι (Additive.ofMul b) := by
    change ((2 : ℕ) : ZMod 4) • a = iotaA ι (Additive.ofMul b)
    rw [Nat.cast_smul_eq_nsmul]
    exact hb'
  have h2a : (2 : ZMod 4) • (a - w) = 0 := by
    rw [smul_sub, hb'', hw, sub_self]
  have h2a_nat : (2 : ℕ) • (a - w) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 4) 2 (a - w)]
    change (2 : ZMod 4) • (a - w) = 0
    exact h2a
  have hsq : (Additive.toMul (a - w)) ^ 2 = 1 := by
    have h := congrArg Additive.toMul h2a_nat
    rw [toMul_nsmul] at h
    simpa using h
  obtain ⟨c, hc⟩ := h2 (Additive.toMul (a - w)) hsq
  have hc' : a - w = iotaA ι (Additive.ofMul c) := by
    rw [show a - w = Additive.ofMul (Additive.toMul (a - w)) from rfl, hc]
    rfl
  obtain ⟨y, hy⟩ := eL_surjective (Additive.ofMul c)
  refine ⟨x + (2 : ZMod 4) • y, ?_⟩
  have h2y : phi v ((2 : ZMod 4) • y) = iotaA ι (eL y) :=
    phi_two_smul (ι := ι) (v := v) hv y
  rw [map_add, h2y, hy, ← hc']
  change w + (a - w) = a
  abel

theorem phi_bijective {ι : ↥Jc →* V} {v : Fin 10 → Additive V}
    [Module (ZMod 4) (Additive V)] (hι : Function.Injective ι)
    (h1 : ∀ v : V, ∃ a, v ^ 2 = ι a)
    (h2 : ∀ v : V, v ^ 2 = 1 → ∃ a, v = ι a)
    (hv : ∀ i, (2 : ZMod 4) • v i = iotaA ι (Additive.ofMul (jcA (2 ^ i.val)))) :
    Function.Bijective (phi v) :=
  ⟨phi_injective hι hv, phi_surjective h1 h2 hv⟩

@[expose] def phiEquiv {ι : ↥Jc →* V} {v : Fin 10 → Additive V}
    [Module (ZMod 4) (Additive V)] (hι : Function.Injective ι)
    (h1 : ∀ v : V, ∃ a, v ^ 2 = ι a)
    (h2 : ∀ v : V, v ^ 2 = 1 → ∃ a, v = ι a)
    (hv : ∀ i, (2 : ZMod 4) • v i = iotaA ι (Additive.ofMul (jcA (2 ^ i.val)))) :
    (Fin 10 → ZMod 4) ≃ₗ[ZMod 4] Additive V :=
  LinearEquiv.ofBijective (phi v) (phi_bijective hι h1 h2 hv)

end VGroup

section Matrices

open Matrix

variable {V : Type} [CommGroup V]
variable (ρ : Qj →* MulAut V) (v : Fin 10 → Additive V)
variable [Module (ZMod 4) (Additive V)]

@[expose] noncomputable def rhoA (g : Qj) : Additive V ≃+ Additive V where
  toFun a := Additive.ofMul (ρ g a.toMul)
  invFun a := Additive.ofMul ((ρ g).symm a.toMul)
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by simp [map_mul]

theorem rhoA_mul (g h : Qj) : rhoA ρ (g * h) = (rhoA ρ h).trans (rhoA ρ g) := by
  ext a
  rw [AddEquiv.trans_apply]
  simp [rhoA, map_mul]

@[expose] noncomputable def mat (Φ : (Fin 10 → ZMod 4) ≃ₗ[ZMod 4] Additive V)
    (g : Qj) : Matrix (Fin 10) (Fin 10) (ZMod 4) :=
  fun j i => Φ.symm (rhoA ρ g (v i)) j

theorem phi_mat_col (Φ : (Fin 10 → ZMod 4) ≃ₗ[ZMod 4] Additive V)
    (hΦ : ∀ x, Φ x = phi v x) (g : Qj) (i : Fin 10) :
    phi v (fun j => mat ρ v Φ g j i) = rhoA ρ g (v i) := by
  have h := Φ.apply_symm_apply (rhoA ρ g (v i))
  rw [hΦ] at h
  exact h

theorem phi_mat (Φ : (Fin 10 → ZMod 4) ≃ₗ[ZMod 4] Additive V)
    (hΦ : ∀ x, Φ x = phi v x) (g : Qj) (x : Fin 10 → ZMod 4) :
    phi v (mat ρ v Φ g *ᵥ x) = rhoA ρ g (phi v x) := by
  have hvec : mat ρ v Φ g *ᵥ x =
      ∑ i, x i • (fun j => mat ρ v Φ g j i) := by
    funext j
    simp only [Matrix.mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hvec, map_sum]
  simp only [map_smul]
  rw [show (∑ i, x i • phi v (fun j => mat ρ v Φ g j i)) =
      ∑ i, x i • rhoA ρ g (v i) from
    Finset.sum_congr rfl fun i _ => by rw [phi_mat_col ρ v Φ hΦ]]
  have hsum : (∑ i, x i • rhoA ρ g (v i)) = rhoA ρ g (∑ i, x i • v i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (ZMod.map_smul (rhoA ρ g) (x i) (v i)).symm
  rw [hsum, phi_apply]

theorem mat_one (Φ : (Fin 10 → ZMod 4) ≃ₗ[ZMod 4] Additive V)
    (hΦ : ∀ x, Φ x = phi v x) : mat ρ v Φ 1 = 1 := by
  ext j i
  rw [mat, Matrix.one_apply]
  have hsingle : Φ (Pi.single i 1) = v i := by
    rw [hΦ, phi_apply]
    simp
  have hrho : rhoA ρ 1 = AddEquiv.refl (Additive V) := by
    ext a
    simp [rhoA]
  rw [hrho]
  simp only [AddEquiv.refl_apply]
  rw [← hsingle, Φ.symm_apply_apply]
  simp [Pi.single_apply, eq_comm]

theorem mat_mul (Φ : (Fin 10 → ZMod 4) ≃ₗ[ZMod 4] Additive V)
    (hΦ : ∀ x, Φ x = phi v x) (g h : Qj) :
    mat ρ v Φ (g * h) = mat ρ v Φ g * mat ρ v Φ h := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  apply Φ.injective
  rw [hΦ, hΦ]
  calc phi v (mat ρ v Φ (g * h) *ᵥ x) = rhoA ρ (g * h) (phi v x) :=
        phi_mat ρ v Φ hΦ (g * h) x
    _ = rhoA ρ g (rhoA ρ h (phi v x)) := by rw [rhoA_mul, AddEquiv.trans_apply]
    _ = rhoA ρ g (phi v (mat ρ v Φ h *ᵥ x)) := by rw [phi_mat ρ v Φ hΦ h x]
    _ = phi v (mat ρ v Φ g *ᵥ (mat ρ v Φ h *ᵥ x)) :=
        (phi_mat ρ v Φ hΦ g (mat ρ v Φ h *ᵥ x)).symm
    _ = phi v ((mat ρ v Φ g * mat ρ v Φ h) *ᵥ x) := by rw [Matrix.mulVec_mulVec]

end Matrices

section Equivariance

variable {V : Type} [CommGroup V]
variable (ρ : Qj →* MulAut V) (ι : ↥Jc →* V)
variable (hρ : ∀ g a, ρ g (ι a) = ι ((g : MulAut ↥Jc) a))

include hρ

theorem rhoA_iotaA (g : Qj) (a : ↥Jc) :
    rhoA ρ g (iotaA ι (Additive.ofMul a)) =
      iotaA ι (Additive.ofMul ((g : MulAut ↥Jc) a)) := by
  change Additive.ofMul (ρ g (ι a)) = Additive.ofMul (ι ((g : MulAut ↥Jc) a))
  rw [hρ]

end Equivariance

@[expose] noncomputable def Ghn (k : Fin 3) : Matrix (Fin 10) (Fin 10) ℕ :=
  fun j i => (CFSG.Sporadic.Co2Jc.Native.NoZ4.G2 k.val j i).val

@[expose] noncomputable def Gh (k : Fin 3) : Matrix (Fin 10) (Fin 10) (ZMod 4) :=
  CFSG.Sporadic.Co2Jc.Native.NoZ4.G4 k.val

theorem Gh_apply (k : Fin 3) (j i : Fin 10) :
    Gh k j i = ((Ghn k j i : ℕ) : ZMod 4) := rfl

theorem Ghn_apply (k : Fin 3) (j i : Fin 10) :
    Ghn k j i = (CFSG.Sporadic.Co2Jc.Native.NoZ4.G2 k.val j i).val := rfl

section Generators

variable {V : Type} [CommGroup V]
variable (ρ : Qj →* MulAut V) (ι : ↥Jc →* V)
variable (hι : Function.Injective ι)
variable (hρ : ∀ g a, ρ g (ι a) = ι ((g : MulAut ↥Jc) a))
variable (h1 : ∀ v : V, ∃ a, v ^ 2 = ι a)
variable (h2 : ∀ v : V, v ^ 2 = 1 → ∃ a, v = ι a)
variable [Module (ZMod 4) (Additive V)]
variable (v : Fin 10 → Additive V)
variable (hv : ∀ i, (2 : ZMod 4) • v i = iotaA ι (Additive.ofMul (jcA (2 ^ i.val))))

include hι hρ h1 h2 hv

theorem mat_qAj_parity (Φ : (Fin 10 → ZMod 4) ≃ₗ[ZMod 4] Additive V)
    (hΦ : ∀ x, Φ x = phi v x) (htab : ∀ k : Fin 3, ∀ i : Fin 10,
      (Co2Smith.Native.glNJTab[k.val]!)[i.val]! < 1024)
    (k : Fin 3) (j i : Fin 10) :
    ((mat ρ v Φ ⟨qA k.val, qA_mem k.isLt⟩) j i).val % 2 = Ghn k j i := by
  let g : Qj := ⟨qA k.val, qA_mem k.isLt⟩
  let col : Fin 10 → ZMod 4 := fun j => mat ρ v Φ g j i
  let m : ℕ := (Co2Smith.Native.glNJTab[k.val]!)[i.val]!
  have hm : m < 1024 := htab k i
  have hcol : Φ col = rhoA ρ g (v i) := by
    rw [hΦ]
    exact phi_mat_col ρ v Φ hΦ g i
  have h2a : (2 : ZMod 4) • Φ col = (2 : ZMod 4) • rhoA ρ g (v i) := by rw [hcol]
  have h2b : (2 : ZMod 4) • rhoA ρ g (v i) = iotaA ι (Additive.ofMul (jcA m)) := by
    rw [← ZMod.map_smul (rhoA ρ g) (2 : ZMod 4) (v i)]
    rw [hv i, rhoA_iotaA (ρ := ρ) (ι := ι) (hρ := hρ)]
    congr 2
    exact qA_jcA_two_pow k i
  have h2eq : (2 : ZMod 4) • Φ col = iotaA ι (Additive.ofMul (jcA m)) :=
    h2a.trans h2b
  have h2eq' : iotaA ι (eL col) = iotaA ι (Additive.ofMul (jcA m)) := by
    rw [← phi_two_smul (ι := ι) (v := v) hv col, ← hΦ,
      LinearEquiv.map_smul Φ (2 : ZMod 4) col, h2eq]
  have heL : eL col = Additive.ofMul (jcA m) := iotaA_injective hι h2eq'
  have hbit := congrArg (coordBitHom j) heL
  rw [coordBitHom_eL, coordBitHom_jcA j hm] at hbit
  have hval : (col j).val % 2 = (if m.testBit j.val then 1 else 0) := by
    have := congrArg ZMod.val hbit
    rw [ZMod.val_natCast] at this
    by_cases h : m.testBit j.val <;> simpa [h, ZMod.val_one, ZMod.val_zero] using this
  rw [hval]
  have hG2 : CFSG.Sporadic.Co2Jc.Native.NoZ4.G2 k.val j i =
      (if m.testBit j.val then 1 else 0 : ZMod 2) := by
    simp [CFSG.Sporadic.Co2Jc.Native.NoZ4.G2, m]
  rw [Ghn_apply, hG2]
  by_cases h : m.testBit j.val <;> simp [h, ZMod.val_one, ZMod.val_zero]

end Generators

section Decomp

variable {V : Type} [CommGroup V]
variable (ρ : Qj →* MulAut V) (v : Fin 10 → Additive V)
variable [Module (ZMod 4) (Additive V)]
variable (Φ : (Fin 10 → ZMod 4) ≃ₗ[ZMod 4] Additive V)

@[expose] noncomputable def qAj (k : Fin 3) : Qj := ⟨qA k.val, qA_mem k.isLt⟩

@[expose] noncomputable def X (k : Fin 3) : Matrix (Fin 10) (Fin 10) (ZMod 4) :=
  fun j i => if mat ρ v Φ (qAj k) j i = Gh k j i then 0 else 1

lemma zmod4_eq_or_eq_add_two {a b : ZMod 4} (hb : b = 0 ∨ b = 1)
    (h : a.val % 2 = b.val % 2) : a = b ∨ a = b + 2 := by
  rcases hb with rfl | rfl
  · change a.val % 2 = 0 at h
    have hlt : a.val < 4 := ZMod.val_lt a
    have hv : a.val = 0 ∨ a.val = 2 := by omega
    rcases hv with h0 | h2
    · left; exact ZMod.val_injective 4 h0
    · right; simpa using ZMod.val_injective 4 h2
  · change a.val % 2 = 1 at h
    have hlt : a.val < 4 := ZMod.val_lt a
    have hv : a.val = 1 ∨ a.val = 3 := by omega
    rcases hv with h1 | h3
    · left; exact ZMod.val_injective 4 h1
    · right; simpa using ZMod.val_injective 4 h3

lemma zmod4_eq_add_two_mul_X {a b : ZMod 4} (hb : b = 0 ∨ b = 1) (h : a = b ∨ a = b + 2) :
    a = b + 2 * (if a = b then 0 else 1) := by
  rcases hb with rfl | rfl <;> rcases h with h | h <;> subst h <;>
    simp [show (2 : ZMod 4) ≠ 0 by decide]

theorem mat_qAj_decomp {ι : ↥Jc →* V} (hι : Function.Injective ι)
    (hρ : ∀ g a, ρ g (ι a) = ι ((g : MulAut ↥Jc) a))
    (h1 : ∀ v : V, ∃ a, v ^ 2 = ι a)
    (h2 : ∀ v : V, v ^ 2 = 1 → ∃ a, v = ι a)
    (hv : ∀ i, (2 : ZMod 4) • v i = iotaA ι (Additive.ofMul (jcA (2 ^ i.val))))
    (hΦ : ∀ x, Φ x = phi v x)
    (htab : ∀ k : Fin 3, ∀ i : Fin 10,
      (Co2Smith.Native.glNJTab[k.val]!)[i.val]! < 1024)
    (k : Fin 3) :
    mat ρ v Φ (qAj k) = Gh k + (2 : ZMod 4) • X ρ v Φ k := by
  ext j i
  have hb : Gh k j i = 0 ∨ Gh k j i = 1 := by
    rw [Gh_apply]
    have := Ghn_apply k j i
    rcases Nat.eq_zero_or_pos (Ghn k j i) with h0 | hp
    · left; rw [h0]; rfl
    · right
      have hle : Ghn k j i ≤ 1 := by
        rw [Ghn_apply]
        have := ZMod.val_lt (CFSG.Sporadic.Co2Jc.Native.NoZ4.G2 k.val j i)
        omega
      rw [show Ghn k j i = 1 by omega]; rfl
  have hpar : (mat ρ v Φ (qAj k) j i).val % 2 = (Gh k j i).val % 2 := by
    change (mat ρ v Φ ⟨qA k.val, qA_mem k.isLt⟩ j i).val % 2 = (Gh k j i).val % 2
    rw [mat_qAj_parity (ρ := ρ) (ι := ι) (hι := hι) (hρ := hρ) (h1 := h1) (h2 := h2)
      (v := v) (hv := hv) (Φ := Φ) (hΦ := hΦ) (htab := htab) k j i, Gh_apply]
    rcases Nat.eq_zero_or_pos (Ghn k j i) with h0 | hp
    · rw [h0]; rfl
    · have hle : Ghn k j i ≤ 1 := by
        rw [Ghn_apply]
        have := ZMod.val_lt (CFSG.Sporadic.Co2Jc.Native.NoZ4.G2 k.val j i)
        omega
      rw [show Ghn k j i = 1 by omega]; rfl
  have h := zmod4_eq_or_eq_add_two hb hpar
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact zmod4_eq_add_two_mul_X hb h

end Decomp

end CFSG.Sporadic.Co2Jc.NoZ4

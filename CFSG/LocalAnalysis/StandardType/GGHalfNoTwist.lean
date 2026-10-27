module

public import CFSG.LocalAnalysis.StandardType.GGHalfShear
public import CFSG.LocalAnalysis.StandardType.GGHalfNoTwistMatrix

public section

namespace CFSG.StandardType.GGHalf

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

private lemma pow_eq_pow_mod_three {M : Type*} [Monoid M] {g : M} (hg : g ^ 3 = 1) (m : ℕ) :
    g ^ m = g ^ (m % 3) := by
  conv_lhs => rw [← Nat.mod_add_div m 3]
  rw [pow_add, pow_mul, hg, one_pow, mul_one]

private lemma zpow_eq_pow_val {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) (i : ℤ) :
    g ^ i = g ^ ((i : ZMod 3).val) := by
  rw [← zpow_natCast (a := g) (n := (i : ZMod 3).val), zpow_eq_zpow_emod' (x := g) i hg,
    ZMod.val_intCast]

private lemma pow_val_add {M : Type*} [Monoid M] {g : M} (hg : g ^ 3 = 1) (p q : ZMod 3) :
    g ^ (p + q).val = g ^ p.val * g ^ q.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod_three hg, pow_add]

private lemma pow_val_mul {M : Type*} [Monoid M] {g : M} (hg : g ^ 3 = 1) (p q : ZMod 3) :
    g ^ (p * q).val = (g ^ q.val) ^ p.val := by
  rw [mul_comm p q, ZMod.val_mul, ← pow_mul, ← pow_eq_pow_mod_three hg]

private lemma inv_pow_val {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) (k : ZMod 3) :
    (g⁻¹) ^ k.val = g ^ (-k).val := by
  have hkey : ∀ k : ZMod 3, (-(k.val : ℤ)) % 3 = ((((-k).val : ℕ) : ℤ)) % 3 := by decide
  calc (g⁻¹) ^ k.val
      = (g ^ k.val)⁻¹ := inv_pow g k.val
    _ = g ^ (-(k.val : ℤ)) := by rw [← zpow_natCast, ← zpow_neg]
    _ = g ^ ((-(k.val : ℤ)) % 3) := zpow_eq_zpow_emod' (x := g) _ hg
    _ = g ^ ((((-k).val : ℕ) : ℤ) % 3) := by rw [hkey k]
    _ = g ^ ((-k).val) := by
        rw [← zpow_natCast (a := g) (n := (-k).val)]
        exact (zpow_eq_zpow_emod' (x := g) (((-k).val : ℕ) : ℤ) hg).symm

private def iotaM {M : Type*} [Monoid M] (X Y U : M) (c : Fin 3 → ZMod 3) : M :=
  X ^ (c 0).val * Y ^ (c 1).val * U ^ (c 2).val

private lemma iotaM_add {M : Type*} [CommMonoid M] {X Y U : M}
    (hX : X ^ 3 = 1) (hY : Y ^ 3 = 1) (hU : U ^ 3 = 1) (a b : Fin 3 → ZMod 3) :
    iotaM X Y U (a + b) = iotaM X Y U a * iotaM X Y U b := by
  simp only [iotaM, Pi.add_apply]
  rw [pow_val_add hX, pow_val_add hY, pow_val_add hU]
  ac_rfl

private lemma iotaM_smul {M : Type*} [CommMonoid M] {X Y U : M}
    (hX : X ^ 3 = 1) (hY : Y ^ 3 = 1) (hU : U ^ 3 = 1) (a : ZMod 3) (c : Fin 3 → ZMod 3) :
    iotaM X Y U (a • c) = (iotaM X Y U c) ^ a.val := by
  simp only [iotaM, Pi.smul_apply, smul_eq_mul]
  rw [pow_val_mul hX, pow_val_mul hY, pow_val_mul hU]
  rw [mul_pow, mul_pow]

private def Acts {Bs : Subgroup G} (XB YB UB : ↥Bs) (n : G) (N : Mat3) : Prop :=
  ∀ c : Fin 3 → ZMod 3,
    n * ((iotaM (M := ↥Bs) XB YB UB c) : G) * n⁻¹
      = ((iotaM (M := ↥Bs) XB YB UB (N.mulVec c)) : G)

private lemma ntN1_mulVec (c : Fin 3 → ZMod 3) :
    ntN₁.mulVec c = ![c 0, -c 1, c 2] := by
  funext k
  fin_cases k <;> simp [ntN₁, Matrix.mulVec, Fin.sum_univ_three] <;> rfl

private lemma ntN2_mulVec (c : Fin 3 → ZMod 3) :
    ntN₂.mulVec c = ![c 0, c 2, c 1] := by
  funext k
  fin_cases k <;> simp [ntN₂, Matrix.mulVec, Fin.sum_univ_three] <;> rfl

private lemma ntP_mulVec (i j a b : ZMod 3) (c : Fin 3 → ZMod 3) :
    (ntP i j a b).mulVec c = ![i * c 0 + a * c 1, j * c 0 + b * c 1, c 2] := by
  funext k
  fin_cases k <;>
    simp [ntP, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]

private lemma iotaM_single_zero {Bs : Subgroup G} {XB YB UB : ↥Bs} :
    iotaM XB YB UB (Pi.single 0 1) = XB := by
  simp [iotaM, Pi.single, ZMod.val_one]

private lemma iotaM_single_one {Bs : Subgroup G} {XB YB UB : ↥Bs} :
    iotaM XB YB UB (Pi.single 1 1) = YB := by
  simp [iotaM, Pi.single, ZMod.val_one]

private lemma iotaM_single_two {Bs : Subgroup G} {XB YB UB : ↥Bs} :
    iotaM XB YB UB (Pi.single 2 1) = UB := by
  simp [iotaM, Pi.single, ZMod.val_one]

private lemma acts_diag {Bs : Subgroup G} {XB YB UB : ↥Bs} {n : G}
    (hX : n * (XB : G) * n⁻¹ = (XB : G)) (hY : n * (YB : G) * n⁻¹ = (YB : G)⁻¹)
    (hU : n * (UB : G) * n⁻¹ = (UB : G)) (hY3 : (YB : G) ^ 3 = 1) :
    Acts XB YB UB n ntN₁ := by
  intro c
  rw [ntN1_mulVec]
  simp only [Acts, iotaM, Subgroup.coe_mul, Subgroup.coe_pow]
  rw [show n * ((XB : G) ^ (c 0).val * (YB : G) ^ (c 1).val * (UB : G) ^ (c 2).val) * n⁻¹
      = (n * (XB : G) ^ (c 0).val * n⁻¹) * (n * (YB : G) ^ (c 1).val * n⁻¹)
        * (n * (UB : G) ^ (c 2).val * n⁻¹) by group]
  rw [← conj_pow, ← conj_pow, ← conj_pow, hX, hY, hU, inv_pow_val hY3 (c 1)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

private lemma acts_swap {Bs : Subgroup G} {XB YB UB : ↥Bs} {n : G}
    (hX : n * (XB : G) * n⁻¹ = (XB : G)) (hY : n * (YB : G) * n⁻¹ = (UB : G))
    (hU : n * (UB : G) * n⁻¹ = (YB : G))
    (hYU : (YB : G) * (UB : G) = (UB : G) * (YB : G)) :
    Acts XB YB UB n ntN₂ := by
  intro c
  rw [ntN2_mulVec]
  simp only [Acts, iotaM, Subgroup.coe_mul, Subgroup.coe_pow]
  rw [show n * ((XB : G) ^ (c 0).val * (YB : G) ^ (c 1).val * (UB : G) ^ (c 2).val) * n⁻¹
      = (n * (XB : G) ^ (c 0).val * n⁻¹) * (n * (YB : G) ^ (c 1).val * n⁻¹)
        * (n * (UB : G) ^ (c 2).val * n⁻¹) by group]
  rw [← conj_pow, ← conj_pow, ← conj_pow, hX, hY, hU]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  rw [mul_assoc]
  rw [show (UB : G) ^ (c 1).val * (YB : G) ^ (c 2).val
      = (YB : G) ^ (c 2).val * (UB : G) ^ (c 1).val by
    exact ((show Commute (YB : G) (UB : G) from hYU).symm.pow_pow (c 1).val (c 2).val).eq]
  rw [mul_assoc]

private lemma iotaM_mulVec {Bs : Subgroup G} (hcomm : ∀ a b : ↥Bs, a * b = b * a)
    {XB YB UB Y0 W0 U0 : ↥Bs}
    (hX3 : XB ^ 3 = 1) (hY3 : YB ^ 3 = 1) (hU3 : UB ^ 3 = 1)
    (A : Mat3) (c : Fin 3 → ZMod 3)
    (h0 : Y0 = iotaM XB YB UB (A.mulVec (Pi.single 0 1)))
    (h1 : W0 = iotaM XB YB UB (A.mulVec (Pi.single 1 1)))
    (h2 : U0 = iotaM XB YB UB (A.mulVec (Pi.single 2 1))) :
    iotaM XB YB UB (A.mulVec c) = iotaM Y0 W0 U0 c := by
  letI : CommGroup ↥Bs := { (inferInstance : Group ↥Bs) with mul_comm := hcomm }
  have hdecomp : A.mulVec c = c 0 • A.mulVec (Pi.single 0 1) + c 1 • A.mulVec (Pi.single 1 1)
      + c 2 • A.mulVec (Pi.single 2 1) := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    funext i
    fin_cases i <;>
      simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Fin.sum_univ_three, Pi.smul_apply,
        Pi.add_apply, smul_eq_mul] <;>
      ring
  rw [hdecomp]
  rw [iotaM_add hX3 hY3 hU3, iotaM_add hX3 hY3 hU3]
  rw [iotaM_smul hX3 hY3 hU3, iotaM_smul hX3 hY3 hU3, iotaM_smul hX3 hY3 hU3]
  rw [h0, h1, h2]
  rfl

private lemma acts_one {Bs : Subgroup G} {XB YB UB : ↥Bs} : Acts XB YB UB 1 1 := by
  intro c
  simp [Acts, iotaM, Matrix.one_mulVec]

private lemma acts_mul {Bs : Subgroup G} {XB YB UB : ↥Bs} {n n' : G} {M M' : Mat3}
    (h : Acts XB YB UB n M) (h' : Acts XB YB UB n' M') :
    Acts XB YB UB (n * n') (M * M') := by
  intro c
  have h2 := h' c
  have h1 := h (M'.mulVec c)
  calc n * n' * ((iotaM (M := ↥Bs) XB YB UB c) : G) * (n * n')⁻¹
      = n * (n' * ((iotaM (M := ↥Bs) XB YB UB c) : G) * n'⁻¹) * n⁻¹ := by group
    _ = n * ((iotaM (M := ↥Bs) XB YB UB (M'.mulVec c)) : G) * n⁻¹ := by rw [h2]
    _ = ((iotaM (M := ↥Bs) XB YB UB (M.mulVec (M'.mulVec c))) : G) := h1
    _ = ((iotaM (M := ↥Bs) XB YB UB ((M * M').mulVec c)) : G) := by
        rw [← Matrix.mulVec_mulVec]

private lemma acts_conj {Bs : Subgroup G} (hcomm : ∀ a b : ↥Bs, a * b = b * a)
    {XB YB UB Y0 W0 U0 : ↥Bs} {n : G}
    (hX3 : XB ^ 3 = 1) (hY3 : YB ^ 3 = 1) (hU3 : UB ^ 3 = 1)
    {P Pinv : Mat3} {M : Mat3}
    (h0 : Y0 = iotaM XB YB UB (P.mulVec (Pi.single 0 1)))
    (h1 : W0 = iotaM XB YB UB (P.mulVec (Pi.single 1 1)))
    (h2 : U0 = iotaM XB YB UB (P.mulVec (Pi.single 2 1)))
    (hAct : Acts Y0 W0 U0 n M) (hPP : P * Pinv = 1) :
    Acts XB YB UB n (P * M * Pinv) := by
  intro c
  have hmv1 : P.mulVec (Pinv.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  have hd := iotaM_mulVec hcomm hX3 hY3 hU3 P (Pinv.mulVec c) h0 h1 h2
  rw [hmv1] at hd
  have hd2 := iotaM_mulVec hcomm hX3 hY3 hU3 P (M.mulVec (Pinv.mulVec c)) h0 h1 h2
  have hActc := hAct (Pinv.mulVec c)
  rw [← hd2] at hActc
  rw [← hd] at hActc
  rw [hActc]
  congr 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private lemma vecMulVec_mulVec (A F c : Fin 3 → ZMod 3) :
    (Matrix.vecMulVec A F).mulVec c = (F ⬝ᵥ c) • A := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply,
    Fin.sum_univ_three, smul_eq_mul]
  ring

private lemma shear_mulVec_fixed (A F : Fin 3 → ZMod 3) (hFA : F ⬝ᵥ A = 0) :
    (1 + Matrix.vecMulVec A F).mulVec A = A := by
  rw [Matrix.add_mulVec, vecMulVec_mulVec, hFA, zero_smul, Matrix.one_mulVec, add_zero]

private lemma shear_mulVec_single (A F : Fin 3 → ZMod 3) (k : Fin 3) :
    (1 + Matrix.vecMulVec A F).mulVec (Pi.single k 1) = Pi.single k 1 + (F k) • A := by
  rw [Matrix.add_mulVec, vecMulVec_mulVec, Matrix.one_mulVec, dotProduct_single, mul_one]

private lemma acts_char {Bs : Subgroup G} (hcomm : ∀ a b : ↥Bs, a * b = b * a)
    {XB YB UB : ↥Bs} {n : G} {A F : Fin 3 → ZMod 3}
    (hX3 : XB ^ 3 = 1) (hY3 : YB ^ 3 = 1) (hU3 : UB ^ 3 = 1)
    (hAct : Acts XB YB UB n (1 + Matrix.vecMulVec A F)) (k : Fin 3) :
    n * ((iotaM (M := ↥Bs) XB YB UB (Pi.single k 1)) : G) * n⁻¹
      = ((iotaM (M := ↥Bs) XB YB UB (Pi.single k 1)) : G)
        * ((iotaM (M := ↥Bs) XB YB UB A) : G) ^ (F k).val := by
  letI : CommGroup ↥Bs := { (inferInstance : Group ↥Bs) with mul_comm := hcomm }
  have h := hAct (Pi.single k 1)
  rw [shear_mulVec_single A F k] at h
  rw [show iotaM (M := ↥Bs) XB YB UB (Pi.single k 1 + (F k) • A)
        = iotaM (M := ↥Bs) XB YB UB (Pi.single k 1)
          * (iotaM (M := ↥Bs) XB YB UB A) ^ (F k).val by
      rw [iotaM_add hX3 hY3 hU3, iotaM_smul hX3 hY3 hU3]] at h
  exact h

private lemma gen_mem_zpowers {Bs : Subgroup G} (hcomm : ∀ a b : ↥Bs, a * b = b * a)
    {e a0 n : G} (he : e ∈ Bs) (ha : a0 ∈ Bs) {m : ℕ}
    (h : n * e * n⁻¹ = e * a0 ^ m) :
    n * e * n⁻¹ * e⁻¹ ∈ Subgroup.zpowers a0 := by
  rw [h]
  have hcommG : e * a0 = a0 * e := by
    have hh := hcomm ⟨e, he⟩ ⟨a0, ha⟩
    simpa [Subgroup.coe_mul] using congrArg (fun t : ↥Bs => (t : G)) hh
  rw [show e * a0 ^ m = a0 ^ m * e from
      (Commute.pow_right (show Commute e a0 from hcommG) m).eq,
    mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.npow_mem_zpowers a0 m

private lemma iotaM_eq_one {Bs : Subgroup G} {XB YB UB : ↥Bs}
    (hind : ∀ p q r : ℤ, (XB : G) ^ p * (YB : G) ^ q * (UB : G) ^ r = 1 →
      (3 : ℤ) ∣ p ∧ (3 : ℤ) ∣ q ∧ (3 : ℤ) ∣ r)
    {c : Fin 3 → ZMod 3} (hc : iotaM XB YB UB c = 1) : c = 0 := by
  have hc' : (XB : G) ^ (c 0).val * (YB : G) ^ (c 1).val * (UB : G) ^ (c 2).val = 1 := by
    have h := congrArg (fun b : ↥Bs => (b : G)) hc
    simpa [iotaM, Subgroup.coe_mul, Subgroup.coe_pow] using h
  have hc'' : (XB : G) ^ ((c 0).val : ℤ) * (YB : G) ^ ((c 1).val : ℤ)
      * (UB : G) ^ ((c 2).val : ℤ) = 1 := by
    simpa only [zpow_natCast] using hc'
  obtain ⟨h0, h1, h2⟩ := hind _ _ _ hc''
  have h0' : (c 0).val = 0 := by
    obtain ⟨k, hk⟩ := h0
    have := ZMod.val_lt (c 0)
    omega
  have h1' : (c 1).val = 0 := by
    obtain ⟨k, hk⟩ := h1
    have := ZMod.val_lt (c 1)
    omega
  have h2' : (c 2).val = 0 := by
    obtain ⟨k, hk⟩ := h2
    have := ZMod.val_lt (c 2)
    omega
  funext k
  fin_cases k
  · exact (ZMod.val_eq_zero (c 0)).mp h0'
  · exact (ZMod.val_eq_zero (c 1)).mp h1'
  · exact (ZMod.val_eq_zero (c 2)).mp h2'

theorem no_twist_core {Bs : Subgroup G}
    (hcomm : ∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b) (hexp : ∀ b ∈ Bs, b ^ 3 = 1)
    (hNoTr : GGNoTransvection 3 Bs)
    {x v u : G} (hx : x ∈ Bs) (hv : v ∈ Bs) (hu : u ∈ Bs)
    (hind : ∀ p q r : ℤ, x ^ p * v ^ q * u ^ r = 1 → (3 : ℤ) ∣ p ∧ (3 : ℤ) ∣ q ∧ (3 : ℤ) ∣ r)
    {Z : Set G} (hZ : Z ⊆ Bs) (hgen : Bs ≤ Subgroup.closure ({x, v, u} ∪ Z))
    {s₀ g sk h : G}
    (hs₀ : s₀ ∈ Subgroup.normalizer (Bs : Set G)) (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hsk : sk ∈ Subgroup.normalizer (Bs : Set G)) (hh : h ∈ Subgroup.normalizer (Bs : Set G))
    (hZfix : ∀ z ∈ Z, s₀ * z * s₀⁻¹ = z ∧ g * z * g⁻¹ = z ∧ sk * z * sk⁻¹ = z ∧
      h * z * h⁻¹ = z)
    {i j a b : ℤ}
    (R1x : s₀ * x * s₀⁻¹ = x) (R1u : s₀ * u * s₀⁻¹ = u) (R1v : s₀ * v * s₀⁻¹ = v⁻¹)
    (R2x : g * x * g⁻¹ = x) (R2v : g * v * g⁻¹ = u) (R2u : g * u * g⁻¹ = v)
    (R3y : sk * (x ^ i * v ^ j) * sk⁻¹ = x ^ i * v ^ j) (R3u : sk * u * sk⁻¹ = u)
    (R3w : sk * (x ^ a * v ^ b) * sk⁻¹ = (x ^ a * v ^ b)⁻¹)
    (R4y : h * (x ^ i * v ^ j) * h⁻¹ = x ^ i * v ^ j) (R4u : h * u * h⁻¹ = x ^ a * v ^ b)
    (R4w : h * (x ^ a * v ^ b) * h⁻¹ = u)
    (hj : ¬ (3 : ℤ) ∣ j) (hD : ¬ (3 : ℤ) ∣ i * b - j * a) :
    (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ b := by

  by_contra hnt
  have hjZ : (j : ZMod 3) ≠ 0 := fun h => hj ((ZMod.intCast_zmod_eq_zero_iff_dvd j 3).mp h)
  have hntZ : (i : ZMod 3) ≠ 0 ∨ (b : ZMod 3) ≠ 0 := by
    by_contra h
    push Not at h
    exact hnt ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd i 3).mp h.1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp h.2⟩
  have hDZ : (i : ZMod 3) * b - (j : ZMod 3) * a ≠ 0 := by
    intro h
    apply hD
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (i * b - j * a) 3).mp ?_
    push_cast
    exact h
  obtain ⟨W, hW, A, F, hA, hF, hFA, hWeq⟩ :=
    exists_shear (i : ZMod 3) (j : ZMod 3) (a : ZMod 3) (b : ZMod 3) hjZ hDZ hntZ
  letI : CommGroup ↥Bs :=
    { (inferInstance : Group ↥Bs) with mul_comm := fun p q => Subtype.ext (hcomm p p.2 q q.2) }
  have hcommB : ∀ p q : ↥Bs, p * q = q * p := fun p q => Subtype.ext (hcomm p p.2 q q.2)
  have hx3 : (x : G) ^ 3 = 1 := hexp x hx
  have hv3 : (v : G) ^ 3 = 1 := hexp v hv
  have hu3 : (u : G) ^ 3 = 1 := hexp u hu
  let xB : ↥Bs := ⟨x, hx⟩
  let vB : ↥Bs := ⟨v, hv⟩
  let uB : ↥Bs := ⟨u, hu⟩
  have hxB3 : xB ^ 3 = 1 := by
    apply Subtype.ext
    simpa [xB, Subgroup.coe_pow] using hx3
  have hvB3 : vB ^ 3 = 1 := by
    apply Subtype.ext
    simpa [vB, Subgroup.coe_pow] using hv3
  have huB3 : uB ^ 3 = 1 := by
    apply Subtype.ext
    simpa [uB, Subgroup.coe_pow] using hu3
  let P : Mat3 := ntP (i : ZMod 3) (j : ZMod 3) (a : ZMod 3) (b : ZMod 3)
  let Pinv : Mat3 := ntPinv (i : ZMod 3) (j : ZMod 3) (a : ZMod 3) (b : ZMod 3)
  have hPP : P * Pinv = 1 := by
    show ntP (i : ZMod 3) (j : ZMod 3) (a : ZMod 3) (b : ZMod 3)
        * ntPinv (i : ZMod 3) (j : ZMod 3) (a : ZMod 3) (b : ZMod 3) = 1
    exact ntP_mul_ntPinv (i : ZMod 3) (j : ZMod 3) (a : ZMod 3) (b : ZMod 3) hDZ
  let yB : ↥Bs := iotaM (M := ↥Bs) xB vB uB (P.mulVec (Pi.single 0 1))
  let wB : ↥Bs := iotaM (M := ↥Bs) xB vB uB (P.mulVec (Pi.single 1 1))
  let U0B : ↥Bs := iotaM (M := ↥Bs) xB vB uB (P.mulVec (Pi.single 2 1))
  have hPe0 : P.mulVec (Pi.single 0 1) = ![(i : ZMod 3), (j : ZMod 3), 0] := by
    show (ntP (i : ZMod 3) (j : ZMod 3) (a : ZMod 3) (b : ZMod 3)).mulVec (Pi.single 0 1)
      = ![(i : ZMod 3), (j : ZMod 3), 0]
    rw [ntP_mulVec]
    simp [Pi.single]
  have hPe1 : P.mulVec (Pi.single 1 1) = ![(a : ZMod 3), (b : ZMod 3), 0] := by
    show (ntP (i : ZMod 3) (j : ZMod 3) (a : ZMod 3) (b : ZMod 3)).mulVec (Pi.single 1 1)
      = ![(a : ZMod 3), (b : ZMod 3), 0]
    rw [ntP_mulVec]
    simp [Pi.single]
  have hPe2 : P.mulVec (Pi.single 2 1) = ![(0 : ZMod 3), 0, 1] := by
    show (ntP (i : ZMod 3) (j : ZMod 3) (a : ZMod 3) (b : ZMod 3)).mulVec (Pi.single 2 1)
      = ![(0 : ZMod 3), 0, 1]
    rw [ntP_mulVec]
    simp [Pi.single]
  have hyG : (yB : G) = x ^ i * v ^ j := by
    simp only [yB, hPe0, iotaM, Subgroup.coe_mul, Subgroup.coe_pow, xB, vB, uB,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, ZMod.val_zero, pow_zero, mul_one]
    rw [← zpow_eq_pow_val hx3 i, ← zpow_eq_pow_val hv3 j]
  have hwG : (wB : G) = x ^ a * v ^ b := by
    simp only [wB, hPe1, iotaM, Subgroup.coe_mul, Subgroup.coe_pow, xB, vB, uB,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, ZMod.val_zero, pow_zero, mul_one]
    rw [← zpow_eq_pow_val hx3 a, ← zpow_eq_pow_val hv3 b]
  have hU0G : (U0B : G) = u := by
    simp only [U0B, hPe2, iotaM, Subgroup.coe_mul, Subgroup.coe_pow, xB, vB, uB,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul, mul_one]
  have hwB3 : (wB : G) ^ 3 = 1 := hexp (wB : G) wB.2
  have hActs_s0 : Acts xB vB uB s₀ ntN₁ := acts_diag R1x R1v R1u hv3
  have hActs_g : Acts xB vB uB g ntN₂ :=
    acts_swap R2x R2v R2u (hcomm v hv u hu)
  have hActs_sk : Acts xB vB uB sk (P * ntN₁ * Pinv) :=
    acts_conj hcommB hxB3 hvB3 huB3 rfl rfl rfl
      (acts_diag (by rw [hyG]; exact R3y) (by rw [hwG]; exact R3w)
        (by rw [hU0G]; exact R3u) hwB3) hPP
  have hActs_h : Acts xB vB uB h (P * ntN₂ * Pinv) :=
    acts_conj hcommB hxB3 hvB3 huB3 rfl rfl rfl
      (acts_swap (by rw [hyG]; exact R4y) (by rw [hwG, hU0G]; exact R4w)
        (by rw [hU0G, hwG]; exact R4u)
        (by
          have hh := congrArg (fun t : ↥Bs => (t : G)) (hcommB wB U0B)
          simpa [wB, U0B, Subgroup.coe_mul] using hh)) hPP
  have hlift : ∀ W' ∈ Submonoid.closure
        ({ntN₁, ntN₂, P * ntN₁ * Pinv, P * ntN₂ * Pinv} : Set Mat3),
      ∃ n : G, n ∈ Subgroup.normalizer (Bs : Set G) ∧ Acts xB vB uB n W' ∧
        ∀ z ∈ Z, n * z * n⁻¹ = z := by
    intro W' hW'
    induction hW' using Submonoid.closure_induction with
    | mem W'' hW'' =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW''
      rcases hW'' with rfl | rfl | rfl | rfl
      · exact ⟨s₀, hs₀, hActs_s0, fun z hz => (hZfix z hz).1⟩
      · exact ⟨g, hg, hActs_g, fun z hz => (hZfix z hz).2.1⟩
      · exact ⟨sk, hsk, hActs_sk, fun z hz => (hZfix z hz).2.2.1⟩
      · exact ⟨h, hh, hActs_h, fun z hz => (hZfix z hz).2.2.2⟩
    | one => exact ⟨1, Subgroup.one_mem _, acts_one, fun z hz => by simp⟩
    | mul W1 W2 _ _ ih1 ih2 =>
      obtain ⟨n1, hn1, ha1, hz1⟩ := ih1
      obtain ⟨n2, hn2, ha2, hz2⟩ := ih2
      refine ⟨n1 * n2, Subgroup.mul_mem _ hn1 hn2, acts_mul ha1 ha2, fun z hz => ?_⟩
      rw [show (n1 * n2) * z * (n1 * n2)⁻¹ = n1 * (n2 * z * n2⁻¹) * n1⁻¹ by group,
        hz2 z hz, hz1 z hz]
  obtain ⟨n, hn, hActs, hnZ⟩ := hlift W hW
  have hActs' : Acts xB vB uB n (1 + Matrix.vecMulVec A F) := by
    rw [← hWeq]
    exact hActs
  let a₀ : ↥Bs := iotaM (M := ↥Bs) xB vB uB A
  have ha₀ : (a₀ : G) ∈ Bs := a₀.2
  have ha₁ : (a₀ : G) ≠ 1 := by
    intro h
    have h1 : a₀ = 1 := Subtype.ext h
    exact hA (iotaM_eq_one hind h1)
  have hWA : W.mulVec A = A := by
    rw [hWeq, shear_mulVec_fixed A F hFA]
  have hna : n * (a₀ : G) * n⁻¹ = (a₀ : G) := by
    have h := hActs A
    rw [hWA] at h
    simpa [a₀] using h
  have hnB : ∀ b ∈ Bs, n * b * n⁻¹ ∈ Bs :=
    fun b hb => (Subgroup.mem_normalizer_iff.mp hn b).mp hb
  let φ : ↥Bs →* ↥Bs :=
    { toFun := fun b => ⟨n * (b : G) * n⁻¹, hnB (b : G) b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun b c => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let ψ : ↥Bs →* ↥Bs := φ * invMonoidHom
  have hpsi : ∀ b : ↥Bs, (ψ b : G) = n * (b : G) * n⁻¹ * (b : G)⁻¹ := by
    intro b
    rw [show ψ b = φ b * invMonoidHom b from rfl, Subgroup.coe_mul, invMonoidHom_apply,
      Subgroup.coe_inv]
    rfl
  have hker : Subgroup.closure ({x, v, u} ∪ Z) ≤ Bs := by
    apply (Subgroup.closure_le Bs).mpr
    intro y hy
    simp only [Set.mem_union] at hy
    rcases hy with hy | hy
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h | h | h
      · rw [h]; exact hx
      · rw [h]; exact hv
      · rw [h]; exact hu
    · exact hZ hy
  have himg : ∀ b ∈ Bs, n * b * n⁻¹ * b⁻¹ ∈ Subgroup.zpowers (a₀ : G) := by
    intro b hb
    have hb' : b ∈ Subgroup.closure ({x, v, u} ∪ Z) := hgen hb
    have hmain : ∀ y (hy : y ∈ Subgroup.closure ({x, v, u} ∪ Z)),
        ((ψ ⟨y, hker hy⟩ : ↥Bs) : G) ∈ Subgroup.zpowers (a₀ : G) := by
      intro y hy
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
      · intro y hy
        have hy' := hy
        simp only [Set.mem_union] at hy'
        rcases hy' with hyA | hyZ
        · have hyA' := hyA
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyA'
          rcases hyA' with h | h | h
          · have hchar : n * (x : G) * n⁻¹ = (x : G) * (a₀ : G) ^ (F 0).val := by
              have hh := acts_char hcommB hxB3 hvB3 huB3 hActs' (0 : Fin 3)
              simpa [iotaM_single_zero, xB] using hh
            rw [show (⟨y, hker (Subgroup.subset_closure hy)⟩ : ↥Bs) = xB
                  from Subtype.ext h, hpsi]
            exact gen_mem_zpowers hcommB xB.2 ha₀ hchar
          · have hchar : n * (v : G) * n⁻¹ = (v : G) * (a₀ : G) ^ (F 1).val := by
              have hh := acts_char hcommB hxB3 hvB3 huB3 hActs' (1 : Fin 3)
              simpa [iotaM_single_one, vB] using hh
            rw [show (⟨y, hker (Subgroup.subset_closure hy)⟩ : ↥Bs) = vB
                  from Subtype.ext h, hpsi]
            exact gen_mem_zpowers hcommB vB.2 ha₀ hchar
          · have hchar : n * (u : G) * n⁻¹ = (u : G) * (a₀ : G) ^ (F 2).val := by
              have hh := acts_char hcommB hxB3 hvB3 huB3 hActs' (2 : Fin 3)
              simpa [iotaM_single_two, uB] using hh
            rw [show (⟨y, hker (Subgroup.subset_closure hy)⟩ : ↥Bs) = uB
                  from Subtype.ext h, hpsi]
            exact gen_mem_zpowers hcommB uB.2 ha₀ hchar
        · rw [show (⟨y, hker (Subgroup.subset_closure hy)⟩ : ↥Bs) = ⟨y, hZ hyZ⟩
              from Subtype.ext rfl, hpsi, hnZ y hyZ, mul_inv_cancel]
          exact Subgroup.one_mem _
      · rw [show (⟨1, hker (Subgroup.one_mem _)⟩ : ↥Bs) = 1 from Subtype.ext rfl, hpsi]
        simp
      · intro c d hc hd ihc ihd
        have hprod : ((ψ (⟨c, hker hc⟩ * ⟨d, hker hd⟩) : ↥Bs) : G)
            = ((ψ ⟨c, hker hc⟩ : ↥Bs) : G) * ((ψ ⟨d, hker hd⟩ : ↥Bs) : G) := by
          rw [map_mul]
          rfl
        rw [show (⟨c * d, hker (Subgroup.mul_mem _ hc hd)⟩ : ↥Bs)
              = ⟨c, hker hc⟩ * ⟨d, hker hd⟩ from Subtype.ext rfl, hprod]
        exact Subgroup.mul_mem _ ihc ihd
      · intro c hc ihc
        have hprod : ((ψ (⟨c, hker hc⟩⁻¹) : ↥Bs) : G)
            = ((ψ ⟨c, hker hc⟩ : ↥Bs) : G)⁻¹ := by
          rw [map_inv]
          rfl
        rw [show (⟨c⁻¹, hker (Subgroup.inv_mem _ hc)⟩ : ↥Bs) = ⟨c, hker hc⟩⁻¹
              from Subtype.ext rfl, hprod]
        exact Subgroup.inv_mem _ ihc
    have hfinal := hmain b hb'
    rwa [hpsi] at hfinal
  have hmove : ∃ b ∈ Bs, n * b * n⁻¹ ≠ b := by
    obtain ⟨k, hk⟩ : ∃ k : Fin 3, F k ≠ 0 := by
      by_contra h
      push Not at h
      exact hF (funext h)
    refine ⟨((iotaM (M := ↥Bs) xB vB uB (Pi.single k 1) : ↥Bs) : G),
      (iotaM (M := ↥Bs) xB vB uB (Pi.single k 1)).2, ?_⟩
    set e : ↥Bs := iotaM (M := ↥Bs) xB vB uB (Pi.single k 1) with he
    intro hfix
    have hchar := acts_char hcommB hxB3 hvB3 huB3 hActs' k
    have hchar' : n * (e : G) * n⁻¹ = (e : G) * (a₀ : G) ^ (F k).val := by
      simpa [he] using hchar
    have hone : (a₀ : G) ^ (F k).val = 1 := by
      have hbm : (e : G) = (e : G) * (a₀ : G) ^ (F k).val := by
        calc (e : G) = n * (e : G) * n⁻¹ := hfix.symm
          _ = (e : G) * (a₀ : G) ^ (F k).val := hchar'
      have h := congrArg (fun t => (e : G)⁻¹ * t) hbm
      simpa [mul_assoc] using h.symm
    have hdvd : orderOf (a₀ : G) ∣ (F k).val := orderOf_dvd_of_pow_eq_one hone
    have h3dvd : orderOf (a₀ : G) ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp (a₀ : G) a₀.2)
    have hne1 : orderOf (a₀ : G) ≠ 1 := fun h => ha₁ (orderOf_eq_one_iff.mp h)
    have hord : orderOf (a₀ : G) = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3dvd with h | h
      · exact absurd h hne1
      · exact h
    have hk0 : (F k).val = 0 := by
      rw [hord] at hdvd
      obtain ⟨t, ht⟩ := hdvd
      have := ZMod.val_lt (F k)
      omega
    exact hk ((ZMod.val_eq_zero (F k)).mp hk0)
  exact (not_noTransvection_of_shear hcomm hexp hn ha₀ ha₁ hna himg hmove) hNoTr

end CFSG.StandardType.GGHalf

end

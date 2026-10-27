module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11Q
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11O

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {U : Subgroup G} [IsMulCommutative ↥U]
  {b : Fin 4 → ↥U} {hb : ∀ i, b i ^ 2 = 1}

theorem IsMatCh611.inv {g : G} {A B : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : IsMatCh611 b hb g A)
    (hAB : A * B = 1) : IsMatCh611 b hb g⁻¹ B := by
  unfold IsMatCh611 at h ⊢
  intro c
  have h1 := h (B.mulVec c)
  rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec] at h1
  rw [← h1]
  group

variable [Finite G] {T M L V : Subgroup G} {d u₁ z : G}

namespace Data611

variable (D : Data611 G T M L V d u₁ z)
include D

theorem d_inv : d⁻¹ = d * d := by
  have h3 := D.d3
  rw [pow_succ, pow_two] at h3
  exact inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact h3)

theorem dU_fix {u : G} (hu : u ∈ uCh611 T L V) (hdu : d * u * d⁻¹ = u) : u = 1 := by
  have h1 : d * u * d⁻¹ * u⁻¹ ∈ ch6ZS T L V := by
    rw [hdu, mul_inv_cancel]
    exact (ch6ZS T L V).one_mem
  exact D.dV u (ZS_le_V (D.dUZ u hu h1)) hdu

theorem orbit_prod {X : Subgroup G} (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hdX : d ∈ Subgroup.normalizer (X : Set G)) (hfix : ∀ x ∈ X, d * x * d⁻¹ = x → x = 1)
    {x : G} (hx : x ∈ X) : x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹) = 1 := by
  have h1 : d * x * d⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hdX x).mp hx
  have h2 : d * (d * x * d⁻¹) * d⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hdX _).mp h1
  apply hfix _ (X.mul_mem (X.mul_mem hx h1) h2)
  have h3 : d * (d * (d * x * d⁻¹) * d⁻¹) * d⁻¹ = x := by
    have hd : d * d * d = 1 := by
      have := D.d3
      rwa [pow_succ, pow_two] at this
    have e : d * (d * (d * x * d⁻¹) * d⁻¹) * d⁻¹ = (d * d * d) * x * (d * d * d)⁻¹ := by group
    rw [e, hd, one_mul, inv_one, mul_one]
  calc d * (x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹)) * d⁻¹
      = (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹) * (d * (d * (d * x * d⁻¹) * d⁻¹) * d⁻¹) := by
        group
    _ = (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹) * x := by rw [h3]
    _ = x * (d * x * d⁻¹) * (d * (d * x * d⁻¹) * d⁻¹) := by
        rw [hXc _ (X.mul_mem h1 h2) x hx, ← mul_assoc]

theorem d_z' : d * (d * z * d⁻¹) * d⁻¹ = z * (d * z * d⁻¹) := by
  have hV := D.hyp.toHyp611.isElemAbelian
  have hzV : z ∈ V := ZS_le_V D.zS
  have h := D.orbit_prod (X := V) (fun a ha b hb => B2F.isElemAbelian_comm hV ha hb)
    (D.hyp.data.le_normalizer D.dL) (fun x hx hdx => D.dV x hx hdx) hzV
  have hz'V : d * z * d⁻¹ ∈ V := ZS_le_V D.z'_mem
  have hinv : (z * (d * z * d⁻¹))⁻¹ = z * (d * z * d⁻¹) :=
    inv_eq_of_mul_eq_one_right (by
      rw [← pow_two]; exact hV.2 _ (V.mul_mem hzV hz'V))
  rw [← hinv]
  exact eq_inv_of_mul_eq_one_right h

theorem d_u₂ : d * (d * u₁ * d⁻¹) * d⁻¹ = u₁ * (d * u₁ * d⁻¹) := by
  have h := D.orbit_prod (X := uCh611 T L V) D.comm D.dU (fun x hx hdx => D.dU_fix hx hdx) D.u₁U
  have hu₂ : d * u₁ * d⁻¹ ∈ uCh611 T L V := D.conj_d_mem D.u₁U
  have hinv : (u₁ * (d * u₁ * d⁻¹))⁻¹ = u₁ * (d * u₁ * d⁻¹) :=
    D.inv_eq ((uCh611 T L V).mul_mem D.u₁U hu₂)
  rw [← hinv]
  exact eq_inv_of_mul_eq_one_right h

theorem ind : ∀ c, D.kv c = 1 → c = 0 := by
  intro c hc
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rw [D.kv_eq] at hc
  obtain ⟨hz'1, hz'z⟩ := D.z'_ne
  have hz'Z := D.z'_mem
  set z' := d * z * d⁻¹ with hz'
  set u₂ := d * u₁ * d⁻¹ with hu₂
  have hzU := D.zU
  have hz'U : z' ∈ uCh611 T L V := ZS_le_U hz'Z
  have hu₂U : u₂ ∈ uCh611 T L V := D.conj_d_mem D.u₁U
  set x := z ^ (c 0).val * z' ^ (c 1).val with hx
  have hxZS : x ∈ ch6ZS T L V := (D.mem_ZS_iff).mpr ⟨c 0, c 1, rfl⟩
  have hxU : x ∈ uCh611 T L V := ZS_le_U hxZS
  have h3 : c 3 = 0 := by
    rcases hz (c 3) with h3 | h3
    · exact h3
    exfalso
    rw [h3, zv1, pow_one] at hc
    rcases hz (c 2) with h2 | h2
    · rw [h2, zv0, pow_zero, mul_one] at hc
      have : u₂ = x⁻¹ := eq_inv_of_mul_eq_one_right hc
      rw [D.inv_eq hxU] at this
      apply D.u₁Z
      have h1 : u₂ ∈ ch6ZS T L V := this ▸ hxZS
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ D.dZS) _).mp h1
      simpa [hu₂, mul_assoc] using this
    · rw [h2, zv1, pow_one] at hc
      have h1 : u₂ = (x * u₁)⁻¹ := eq_inv_of_mul_eq_one_right hc
      rw [D.inv_eq ((uCh611 T L V).mul_mem hxU D.u₁U)] at h1
      apply D.u₁Z
      apply D.dUZ u₁ D.u₁U
      have e : d * u₁ * d⁻¹ * u₁⁻¹ = x := by
        rw [← hu₂, h1, mul_inv_cancel_right]
      rw [e]
      exact hxZS
  rw [h3, zv0, pow_zero, mul_one] at hc
  have h2 : c 2 = 0 := by
    rcases hz (c 2) with h2 | h2
    · exact h2
    exfalso
    rw [h2, zv1, pow_one] at hc
    apply D.u₁Z
    have : u₁ = x⁻¹ := eq_inv_of_mul_eq_one_right hc
    rw [this]
    exact (ch6ZS T L V).inv_mem hxZS
  rw [h2, zv0, pow_zero, mul_one] at hc
  have h1 : c 1 = 0 := by
    rcases hz (c 1) with h1 | h1
    · exact h1
    exfalso
    rw [hx, h1, zv1, pow_one] at hc
    rcases hz (c 0) with h0 | h0
    · rw [h0, zv0, pow_zero, one_mul] at hc
      exact hz'1 hc
    · rw [h0, zv1, pow_one] at hc
      apply hz'z
      have : z' = z⁻¹ := eq_inv_of_mul_eq_one_right hc
      rw [this, D.inv_eq hzU]
  have h0 : c 0 = 0 := by
    rcases hz (c 0) with h0 | h0
    · exact h0
    exfalso
    rw [hx, h1, h0, zv1, zv0, pow_one, pow_zero, mul_one] at hc
    exact D.z1 hc
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem kv_injective : Function.Injective D.kv := by
  have := D.isMulCommutative
  exact kvCh611_injective D.ind

theorem kv_surj : ∀ u ∈ uCh611 T L V, ∃ c, D.kv c = u := by
  have := D.isMulCommutative
  exact kvCh611_surj D.ind D.card

theorem kv_single (j : Fin 4) : D.kv (Pi.single j 1) = D.basis j := by
  have := D.isMulCommutative
  exact kvCh611_single _ _ j

abbrev IsMat (g : G) (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  @IsMatCh611 G _ (uCh611 T L V) D.isMulCommutative D.basis D.basis_sq g A

theorem isMat_iff {g : G} {A : Matrix (Fin 4) (Fin 4) (ZMod 2)} :
    D.IsMat g A ↔ ∀ c, g * D.kv c * g⁻¹ = D.kv (A.mulVec c) := Iff.rfl

theorem exists_isMat {g : G} (hg : g ∈ Subgroup.normalizer (uCh611 T L V : Set G)) :
    ∃ A, D.IsMat g A := by
  have := D.isMulCommutative
  exact exists_isMatCh611 D.ind D.card hg

theorem isMat_unique {g : G} {A A' : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : D.IsMat g A)
    (h' : D.IsMat g A') : A = A' := by
  have := D.isMulCommutative
  exact IsMatCh611.unique D.ind h h'

theorem isMat_mul {g g' : G} {A A' : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : D.IsMat g A)
    (h' : D.IsMat g' A') : D.IsMat (g * g') (A * A') := by
  have := D.isMulCommutative
  exact IsMatCh611.mul h h'

theorem isMat_one : D.IsMat 1 1 := by
  have := D.isMulCommutative
  exact isMatCh611_one

theorem isMat_inv {g : G} {A B : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : D.IsMat g A)
    (hAB : A * B = 1) : D.IsMat g⁻¹ B := by
  have := D.isMulCommutative
  exact IsMatCh611.inv h hAB

theorem mem_centralizer_iff_isMat {g : G} {A : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : D.IsMat g A) : g ∈ Subgroup.centralizer (uCh611 T L V : Set G) ↔ A = 1 := by
  have := D.isMulCommutative
  exact IsMatCh611.mem_centralizer_iff D.ind D.card h

theorem kv_col {g : G} {A : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : D.IsMat g A) (j : Fin 4) :
    D.kv (A.col j) = g * D.basis j * g⁻¹ := by
  rw [← Matrix.mulVec_single_one, ← (D.isMat_iff).mp h, D.kv_single]

theorem kv_vec (a b c e : ZMod 2) :
    D.kv ![a, b, c, e] = z ^ a.val * (d * z * d⁻¹) ^ b.val * u₁ ^ c.val * (d * u₁ * d⁻¹) ^ e.val :=
  D.kv_eq _

theorem isMat_d : D.IsMat d matDCh611 := by
  have := D.isMulCommutative
  refine isMatCh611_of_cols D.dU fun j => ?_
  have hc : ∀ j : Fin 4, matDCh611.col j = ![matDCh611 0 j, matDCh611 1 j, matDCh611 2 j,
      matDCh611 3 j] := fun j => by ext i; fin_cases i <;> rfl
  change d * (D.basis j : G) * d⁻¹ = D.kv (matDCh611.col j)
  rw [hc, D.kv_vec]
  fin_cases j
  · show d * z * d⁻¹ = z ^ (0 : ZMod 2).val * (d * z * d⁻¹) ^ (1 : ZMod 2).val *
      u₁ ^ (0 : ZMod 2).val * (d * u₁ * d⁻¹) ^ (0 : ZMod 2).val
    simp [zv1]
  · show d * (d * z * d⁻¹) * d⁻¹ = z ^ (1 : ZMod 2).val * (d * z * d⁻¹) ^ (1 : ZMod 2).val *
      u₁ ^ (0 : ZMod 2).val * (d * u₁ * d⁻¹) ^ (0 : ZMod 2).val
    simp only [zv0, zv1, pow_zero, pow_one, mul_one]
    exact D.d_z'
  · show d * u₁ * d⁻¹ = z ^ (0 : ZMod 2).val * (d * z * d⁻¹) ^ (0 : ZMod 2).val *
      u₁ ^ (0 : ZMod 2).val * (d * u₁ * d⁻¹) ^ (1 : ZMod 2).val
    simp [zv1]
  · show d * (d * u₁ * d⁻¹) * d⁻¹ = z ^ (0 : ZMod 2).val * (d * z * d⁻¹) ^ (0 : ZMod 2).val *
      u₁ ^ (1 : ZMod 2).val * (d * u₁ * d⁻¹) ^ (1 : ZMod 2).val
    simp only [zv0, zv1, pow_zero, pow_one, one_mul]
    exact D.d_u₂

end Data611

end CFSG.Quasithin.H13

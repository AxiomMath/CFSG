module

public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Matrix
open scoped Matrix MatrixGroups Pointwise commutatorElement

theorem le_map_perfectResidual {G : Type*} [Group G] {P Y : Subgroup G}
    (hP : Group.IsPerfect P) (hPY : P ≤ Y) : P ≤ (CFSG.perfectResidual Y).map Y.subtype := by
  have hint : Group.IsPerfect (P.subgroupOf Y) := by
    apply Subgroup.isPerfect_iff.mpr
    have hmap := Subgroup.map_commutator (P.subgroupOf Y) (P.subgroupOf Y) Y.subtype
    rw [Subgroup.map_subgroupOf_eq_of_le hPY, Subgroup.isPerfect_iff.mp hP] at hmap
    apply Subgroup.map_injective Y.subtype_injective
    exact hmap.trans (Subgroup.map_subgroupOf_eq_of_le hPY).symm
  have hle : P.subgroupOf Y ≤ CFSG.perfectResidual Y := by
    apply le_iInf
    intro m
    induction m with
    | zero => exact le_top
    | succ m ih =>
      rw [derivedSeries_succ, ← Subgroup.isPerfect_iff.mp hint]
      exact Subgroup.commutator_mono ih ih
  have h2 := Subgroup.map_mono (f := Y.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hPY] at h2

theorem map_perfectResidual_le {G : Type*} [Group G] (Y : Subgroup G) :
    (CFSG.perfectResidual Y).map Y.subtype ≤ ⁅⁅Y, Y⁆, ⁅Y, Y⁆⁆ := by
  have h2 : (derivedSeries Y 2).map Y.subtype = ⁅⁅Y, Y⁆, ⁅Y, Y⁆⁆ := by
    rw [derivedSeries_succ, derivedSeries_succ, derivedSeries_zero, Subgroup.map_commutator,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h2]
  exact Subgroup.map_mono (iInf_le _ 2)

variable {Ω : Type} [Field Ω]

theorem conj_inv_eq_of_smul {n : ℕ} (hn : 1 ≤ n) (M : GL (Fin n) Ω) (x : SL(n, Ω)) {e : Ω}
    (hx : (M : Matrix (Fin n) (Fin n) Ω) * x * (↑M⁻¹ : Matrix (Fin n) (Fin n) Ω) =
      e • (x : Matrix (Fin n) (Fin n) Ω)) :
    e ≠ 0 ∧ (M : Matrix (Fin n) (Fin n) Ω) * ((x⁻¹ : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) *
      (↑M⁻¹ : Matrix (Fin n) (Fin n) Ω) =
        e⁻¹ • ((x⁻¹ : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  set m := (M : Matrix (Fin n) (Fin n) Ω) with hm
  set m' := (↑M⁻¹ : Matrix (Fin n) (Fin n) Ω) with hm'
  have hmm : m' * m = 1 := M.inv_mul
  have hmm' : m * m' = 1 := M.mul_inv
  set x₀ := (x : Matrix (Fin n) (Fin n) Ω) with hx₀
  set y := ((x⁻¹ : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) with hy
  have hxy : x₀ * y = 1 := by
    rw [hx₀, hy, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hyx : y * x₀ = 1 := by
    rw [hx₀, hy, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have he : e ≠ 0 := by
    intro he
    rw [he, zero_smul] at hx
    have h1 : x₀ = 0 := by
      calc x₀ = m' * (m * x₀ * m') * m := by
            simp only [Matrix.mul_assoc, hmm, Matrix.mul_one]
            rw [← Matrix.mul_assoc, hmm, Matrix.one_mul]
        _ = 0 := by rw [hx, Matrix.mul_zero, Matrix.zero_mul]
    have h2 : x₀.det = 1 := x.2
    rw [h1, Matrix.det_zero] at h2
    exact zero_ne_one h2
  refine ⟨he, ?_⟩
  have hprod : (e • x₀) * (m * y * m') = 1 := by
    rw [← hx]
    calc m * x₀ * m' * (m * y * m') = m * (x₀ * (m' * m) * y) * m' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hmm, Matrix.mul_one, hxy, Matrix.mul_one, hmm']
  calc m * y * m' = (e⁻¹ • y) * ((e • x₀) * (m * y * m')) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [← Matrix.mul_assoc, hyx, Matrix.one_mul, mul_inv_cancel₀ he, one_smul]
    _ = e⁻¹ • y := by rw [hprod, Matrix.mul_one]

theorem conj_commutator_eq_of_smul {n : ℕ} (hn : 1 ≤ n) (M : GL (Fin n) Ω) (a b : SL(n, Ω))
    {c d : Ω}
    (ha : (M : Matrix (Fin n) (Fin n) Ω) * a * (↑M⁻¹ : Matrix (Fin n) (Fin n) Ω) =
      c • (a : Matrix (Fin n) (Fin n) Ω))
    (hb : (M : Matrix (Fin n) (Fin n) Ω) * b * (↑M⁻¹ : Matrix (Fin n) (Fin n) Ω) =
      d • (b : Matrix (Fin n) (Fin n) Ω)) :
    (M : Matrix (Fin n) (Fin n) Ω) * ((⁅a, b⁆ : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) *
        (↑M⁻¹ : Matrix (Fin n) (Fin n) Ω) =
      ((⁅a, b⁆ : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) := by
  obtain ⟨hc, ha'⟩ := conj_inv_eq_of_smul hn M a ha
  obtain ⟨hd, hb'⟩ := conj_inv_eq_of_smul hn M b hb
  rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  set m := (M : Matrix (Fin n) (Fin n) Ω)
  set m' := (↑M⁻¹ : Matrix (Fin n) (Fin n) Ω)
  set a₀ := (a : Matrix (Fin n) (Fin n) Ω)
  set b₀ := (b : Matrix (Fin n) (Fin n) Ω)
  set a₁ := ((a⁻¹ : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω)
  set b₁ := ((b⁻¹ : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω)
  have hmm : m' * m = 1 := M.inv_mul
  have key : m * (a₀ * b₀ * a₁ * b₁) * m' =
      (m * a₀ * m') * (m * b₀ * m') * (m * a₁ * m') * (m * b₁ * m') := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc m' m, hmm, Matrix.one_mul, ← Matrix.mul_assoc m' m, hmm,
      Matrix.one_mul, ← Matrix.mul_assoc m' m, hmm, Matrix.one_mul]
  rw [key, ha, hb, ha', hb']
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show d⁻¹ * (c⁻¹ * (d * c)) = 1 by field_simp, one_smul]

theorem exists_eq_scalar_of_discrepancy (M : GL (Fin 3) Ω) (g : SL(3, Ω)) (S : Set SL(3, Ω))
    (hS : ∀ X ∈ S, ∃ c : Ω, (M : Matrix (Fin 3) (Fin 3) Ω) * X *
      (↑M⁻¹ : Matrix (Fin 3) (Fin 3) Ω) = c • (X : Matrix (Fin 3) (Fin 3) Ω))
    (hT : ∀ (i j : Fin 3) (hij : i ≠ j),
      g * Matrix.SpecialLinearGroup.transvection hij 1 * g⁻¹ ∈ S) :
    ∃ c : Ω, (M : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c := by
  refine exists_eq_scalar_of_commute_conj M (Matrix.SpecialLinearGroup.toGL g) fun i j hij => ?_
  obtain ⟨k, hki, hkj⟩ := exists_ne_and_ne (le_refl 3) i j
  have hik : i ≠ k := Ne.symm hki
  have hkj' : k ≠ j := hkj
  have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hik hkj' hij
    (1 : Ω) 1
  rw [one_mul] at hcomm
  set a := g * Matrix.SpecialLinearGroup.transvection hik 1 * g⁻¹
  set b := g * Matrix.SpecialLinearGroup.transvection hkj' 1 * g⁻¹
  have hab : ⁅a, b⁆ = g * Matrix.SpecialLinearGroup.transvection hij 1 * g⁻¹ := by
    have h := map_commutatorElement (MulAut.conj g) (Matrix.SpecialLinearGroup.transvection hik 1)
      (Matrix.SpecialLinearGroup.transvection hkj' 1)
    simp only [MulAut.conj_apply] at h
    rw [← h, hcomm]
  obtain ⟨c, hc⟩ := hS a (hT i k hik)
  obtain ⟨d, hd⟩ := hS b (hT k j hkj')
  have h1 := conj_commutator_eq_of_smul (by norm_num) M a b hc hd
  rw [hab] at h1
  rw [← map_inv, ← map_mul, ← map_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  calc (M : Matrix (Fin 3) (Fin 3) Ω) *
        ((g * Matrix.SpecialLinearGroup.transvection hij 1 * g⁻¹ : SL(3, Ω)) :
          Matrix (Fin 3) (Fin 3) Ω) =
      ((M : Matrix (Fin 3) (Fin 3) Ω) *
        ((g * Matrix.SpecialLinearGroup.transvection hij 1 * g⁻¹ : SL(3, Ω)) :
          Matrix (Fin 3) (Fin 3) Ω) * (↑M⁻¹ : Matrix (Fin 3) (Fin 3) Ω)) *
        (M : Matrix (Fin 3) (Fin 3) Ω) := by
        rw [Matrix.mul_assoc _ (↑M⁻¹ : Matrix (Fin 3) (Fin 3) Ω), M.inv_mul, Matrix.mul_one]
    _ = _ := by rw [h1]

theorem mem_torusGroup_of_diagonal_mul_eq_scalar₂ {z : ModGL Tag.E6 Ω}
    (hz : z ∈ subsystemGroup Tag.E6 Ω support56) (s t : Ωˣ) {c : Ω}
    (h : diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] * a2Mat₂ z = scalar (Fin 3) c) :
    z ∈ torusGroup Tag.E6 Ω := by
  have hinv : diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω), ((t⁻¹ : Ωˣ) : Ω), 1] *
      diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> first | (simp; done) | (simp; field_simp)
  have hz' : a2Mat₂ z = diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω) * c, ((t⁻¹ : Ωˣ) : Ω) * c, c] := by
    calc a2Mat₂ z = diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω), ((t⁻¹ : Ωˣ) : Ω), 1] *
        (diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] * a2Mat₂ z) := by
          rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = _ := by
          rw [h, Matrix.scalar_apply, diagonal_mul_diagonal]
          congr 1
          funext k
          fin_cases k <;> simp
  have hdet := det_a2Mat₂ hz
  rw [hz', det_diagonal, Fin.prod_univ_three] at hdet
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hdet
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hdet
  set u₀ : Ωˣ := (s * t)⁻¹ * Units.mk0 c hc
  set u₁ : Ωˣ := t⁻¹ * Units.mk0 c hc
  have hu : ((u₀ * u₁)⁻¹ : Ωˣ) = Units.mk0 c hc := by
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    simp only [u₀, u₁, Units.val_mul, Units.val_mk0, Units.val_one]
    linear_combination hdet
  have hmat : a2Mat₂ (e6TorusPair (e6Index 4) (e6Index 5) u₀ (u₀ * u₁)) = a2Mat₂ z := by
    rw [a2Mat₂_torus, hz', hu, inv_mul_cancel_left]
    simp only [u₀, u₁, Units.val_mul, Units.val_mk0]
  have hmem : e6TorusPair (e6Index 4) (e6Index 5) u₀ (u₀ * u₁) ∈
      subsystemGroup Tag.E6 Ω support56 := e6TorusPair_mem_subsystemGroup _ _ u₀ (u₀ * u₁)
  have heq : (⟨_, hmem⟩ : subsystemGroup Tag.E6 Ω support56) = ⟨z, hz⟩ :=
    a2Rep₂_injective (Subtype.ext (by rw [coe_a2Rep₂, coe_a2Rep₂]; exact hmat))
  have hz2 : e6TorusPair (e6Index 4) (e6Index 5) u₀ (u₀ * u₁) = z := congrArg Subtype.val heq
  rw [← hz2]
  exact e6TorusPair_mem_torusGroup _ _ _ _

theorem a2Mat₁_conj_formula {h z g : ModGL Tag.E6 Ω} (hh : h ∈ torusGroup Tag.E6 Ω) {s t : Ωˣ}
    (hs : ∀ c : Ω, h * xUnit Tag.E6 Ω (e6Index 0) c * h⁻¹ = xUnit Tag.E6 Ω (e6Index 0) (s * c))
    (ht : ∀ c : Ω, h * xUnit Tag.E6 Ω (e6Index 2) c * h⁻¹ = xUnit Tag.E6 Ω (e6Index 2) (t * c))
    (hz : z ∈ subsystemGroup Tag.E6 Ω support13) (hg : g ∈ subsystemGroup Tag.E6 Ω support13) :
    h * (z * g * z⁻¹) * h⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 ∧
      a2Mat₁ (h * (z * g * z⁻¹) * h⁻¹) =
        (diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] * a2Mat₁ z) * a2Mat₁ g *
          (a2Mat₁ z⁻¹ * diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω), ((t⁻¹ : Ωˣ) : Ω), 1]) := by
  have hzg : z * g * z⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 :=
    mul_mem (mul_mem hz hg) (inv_mem hz)
  obtain ⟨h1, h2⟩ := a2Mat₁_conj_torus hh hs ht hzg
  refine ⟨h1, ?_⟩
  rw [h2, a2Mat₁_mul (mul_mem hz hg) (inv_mem hz), a2Mat₁_mul hz hg]
  simp only [Matrix.mul_assoc]

theorem a2Mat₂_conj_formula {h z g : ModGL Tag.E6 Ω} (hh : h ∈ torusGroup Tag.E6 Ω) {s t : Ωˣ}
    (hs : ∀ c : Ω, h * xUnit Tag.E6 Ω (e6Index 4) c * h⁻¹ = xUnit Tag.E6 Ω (e6Index 4) (s * c))
    (ht : ∀ c : Ω, h * xUnit Tag.E6 Ω (e6Index 5) c * h⁻¹ = xUnit Tag.E6 Ω (e6Index 5) (t * c))
    (hz : z ∈ subsystemGroup Tag.E6 Ω support56) (hg : g ∈ subsystemGroup Tag.E6 Ω support56) :
    h * (z * g * z⁻¹) * h⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 ∧
      a2Mat₂ (h * (z * g * z⁻¹) * h⁻¹) =
        (diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] * a2Mat₂ z) * a2Mat₂ g *
          (a2Mat₂ z⁻¹ * diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω), ((t⁻¹ : Ωˣ) : Ω), 1]) := by
  have hzg : z * g * z⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 :=
    mul_mem (mul_mem hz hg) (inv_mem hz)
  obtain ⟨h1, h2⟩ := a2Mat₂_conj_torus hh hs ht hzg
  refine ⟨h1, ?_⟩
  rw [h2, a2Mat₂_mul (mul_mem hz hg) (inv_mem hz), a2Mat₂_mul hz hg]
  simp only [Matrix.mul_assoc]

theorem diagonal_inv_pair (s t : Ωˣ) :
    diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] *
        diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω), ((t⁻¹ : Ωˣ) : Ω), 1] = 1 ∧
      diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω), ((t⁻¹ : Ωˣ) : Ω), 1] *
        diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] = 1 := by
  constructor <;>
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> first | (simp; done) | (simp; field_simp)

theorem mem_torusGroup_of_centralizes_twoA2 {h z₁ z₂ : ModGL Tag.E6 Ω}
    (hh : h ∈ torusGroup Tag.E6 Ω) (hz₁ : z₁ ∈ subsystemGroup Tag.E6 Ω support13)
    (hz₂ : z₂ ∈ subsystemGroup Tag.E6 Ω support56) (S : Set (SL(3, Ω) × SL(3, Ω)))
    (hS : ∀ s ∈ S, (h * z₁ * z₂) * twoA2Mul Ω s = twoA2Mul Ω s * (h * z₁ * z₂))
    (g₁ g₂ : SL(3, Ω))
    (hT₁ : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∃ s ∈ S, s.1 = g₁ * Matrix.SpecialLinearGroup.transvection hij 1 * g₁⁻¹)
    (hT₂ : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∃ s ∈ S, s.2 = g₂ * Matrix.SpecialLinearGroup.transvection hij 1 * g₂⁻¹) :
    z₁ ∈ torusGroup Tag.E6 Ω ∧ z₂ ∈ torusGroup Tag.E6 Ω := by
  obtain ⟨χ, hχ, -⟩ := exists_simple_root_characters hh
  set s₁ := χ (e6Index 0)
  set t₁ := χ (e6Index 2)
  set s₂ := χ (e6Index 4)
  set t₂ := χ (e6Index 5)
  let D₁ : GL (Fin 3) Ω := ⟨_, _, (diagonal_inv_pair s₁ t₁).1, (diagonal_inv_pair s₁ t₁).2⟩
  let D₂ : GL (Fin 3) Ω := ⟨_, _, (diagonal_inv_pair s₂ t₂).1, (diagonal_inv_pair s₂ t₂).2⟩
  set ρz₁ := a2Rep₁ Ω ⟨z₁, hz₁⟩
  set ρz₂ := a2Rep₂ Ω ⟨z₂, hz₂⟩
  obtain ⟨M₁, hM₁⟩ : ∃ M : GL (Fin 3) Ω, M = D₁ * Matrix.SpecialLinearGroup.toGL ρz₁ :=
    ⟨_, rfl⟩
  obtain ⟨M₂, hM₂⟩ : ∃ M : GL (Fin 3) Ω, M = D₂ * Matrix.SpecialLinearGroup.toGL ρz₂ :=
    ⟨_, rfl⟩
  have hM₁v : (M₁ : Matrix (Fin 3) (Fin 3) Ω) =
      diagonal ![((s₁ * t₁ : Ωˣ) : Ω), (t₁ : Ω), 1] * a2Mat₁ z₁ := by
    rw [hM₁, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_a2Rep₁]
  have hM₂v : (M₂ : Matrix (Fin 3) (Fin 3) Ω) =
      diagonal ![((s₂ * t₂ : Ωˣ) : Ω), (t₂ : Ω), 1] * a2Mat₂ z₂ := by
    rw [hM₂, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_a2Rep₂]
  have hM₁i : (↑M₁⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₁ z₁⁻¹ * diagonal ![(((s₁ * t₁)⁻¹ : Ωˣ) : Ω), ((t₁⁻¹ : Ωˣ) : Ω), 1] := by
    rw [hM₁, _root_.mul_inv_rev, Units.val_mul, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv, coe_a2Rep₁]
    rfl
  have hM₂i : (↑M₂⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₂ z₂⁻¹ * diagonal ![(((s₂ * t₂)⁻¹ : Ωˣ) : Ω), ((t₂⁻¹ : Ωˣ) : Ω), 1] := by
    rw [hM₂, _root_.mul_inv_rev, Units.val_mul, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv, coe_a2Rep₂]
    rfl
  have hdisc : ∀ s ∈ S, ∃ c : Ω,
      (M₁ : Matrix (Fin 3) (Fin 3) Ω) * s.1 * (↑M₁⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
        c • (s.1 : Matrix (Fin 3) (Fin 3) Ω) ∧
      (M₂ : Matrix (Fin 3) (Fin 3) Ω) * s.2 * (↑M₂⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
        c • (s.2 : Matrix (Fin 3) (Fin 3) Ω) := by
    rintro ⟨X, Y⟩ hs
    set u := ((a2Equiv₁ Ω).symm X : ModGL Tag.E6 Ω)
    set v := ((a2Equiv₂ Ω).symm Y : ModGL Tag.E6 Ω)
    have hu : u ∈ subsystemGroup Tag.E6 Ω support13 := ((a2Equiv₁ Ω).symm X).2
    have hv : v ∈ subsystemGroup Tag.E6 Ω support56 := ((a2Equiv₂ Ω).symm Y).2
    have hau : a2Mat₁ u = X := by
      have := congrArg (fun A : SL(3, Ω) => (A : Matrix (Fin 3) (Fin 3) Ω))
        (MulEquiv.apply_symm_apply (a2Equiv₁ Ω) X)
      simpa only [a2Equiv₁_apply, coe_a2Rep₁] using this
    have hav : a2Mat₂ v = Y := by
      have := congrArg (fun A : SL(3, Ω) => (A : Matrix (Fin 3) (Fin 3) Ω))
        (MulEquiv.apply_symm_apply (a2Equiv₂ Ω) Y)
      simpa only [a2Equiv₂_apply, coe_a2Rep₂] using this
    obtain ⟨hu', hau'⟩ := a2Mat₁_conj_formula hh (hχ (e6Index 0)) (hχ (e6Index 2)) hz₁ hu
    obtain ⟨hv', hav'⟩ := a2Mat₂_conj_formula hh (hχ (e6Index 4)) (hχ (e6Index 5)) hz₂ hv
    set u' := h * (z₁ * u * z₁⁻¹) * h⁻¹
    set v' := h * (z₂ * v * z₂⁻¹) * h⁻¹
    have hcomm := hS (X, Y) hs
    rw [twoA2Mul_apply] at hcomm
    have c1 : z₂ * u = u * z₂ := (commute_Q₁_Q₂ hu hz₂).eq.symm
    have hzvz : z₂ * v * z₂⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 :=
      mul_mem (mul_mem hz₂ hv) (inv_mem hz₂)
    have c2 : z₁⁻¹ * (z₂ * v * z₂⁻¹) = (z₂ * v * z₂⁻¹) * z₁⁻¹ :=
      (commute_Q₁_Q₂ (inv_mem hz₁) hzvz).eq
    have huv : u' * v' = u * v := by
      calc u' * v' = h * z₁ * u * (z₁⁻¹ * (z₂ * v * z₂⁻¹)) * h⁻¹ := by
            simp only [u', v']
            group
        _ = h * z₁ * u * ((z₂ * v * z₂⁻¹) * z₁⁻¹) * h⁻¹ := by rw [c2]
        _ = h * z₁ * (u * z₂) * v * z₂⁻¹ * z₁⁻¹ * h⁻¹ := by group
        _ = h * z₁ * (z₂ * u) * v * z₂⁻¹ * z₁⁻¹ * h⁻¹ := by rw [c1]
        _ = (h * z₁ * z₂) * (u * v) * (h * z₁ * z₂)⁻¹ := by group
        _ = u * v := by rw [hcomm, mul_inv_cancel_right]
    have h1 : u⁻¹ * u' ∈ subsystemGroup Tag.E6 Ω support13 := mul_mem (inv_mem hu) hu'
    have h2 : v' * v⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 := mul_mem hv' (inv_mem hv)
    have hone : twoA2Mul Ω (a2Equiv₁ Ω ⟨_, h1⟩, a2Equiv₂ Ω ⟨_, h2⟩) = 1 := by
      rw [twoA2Mul_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      change u⁻¹ * u' * (v' * v⁻¹) = 1
      calc u⁻¹ * u' * (v' * v⁻¹) = u⁻¹ * (u' * v') * v⁻¹ := by group
        _ = 1 := by rw [huv]; group
    obtain ⟨c, -, hc₁, hc₂⟩ := (twoA2Mul_eq_one_iff _ _).1 hone
    rw [a2Equiv₁_apply, coe_a2Rep₁] at hc₁
    rw [a2Equiv₂_apply, coe_a2Rep₂] at hc₂
    change a2Mat₁ (u⁻¹ * u') = scalar (Fin 3) c at hc₁
    change a2Mat₂ (v' * v⁻¹) = scalar (Fin 3) c at hc₂
    rw [a2Mat₁_mul (inv_mem hu) hu'] at hc₁
    rw [a2Mat₂_mul hv' (inv_mem hv)] at hc₂
    have hinvu : a2Mat₁ u * a2Mat₁ u⁻¹ = 1 := by
      rw [← a2Mat₁_mul hu (inv_mem hu), mul_inv_cancel, a2Mat₁_one]
    have hinvv : a2Mat₂ v⁻¹ * a2Mat₂ v = 1 := by
      rw [← a2Mat₂_mul (inv_mem hv) hv, inv_mul_cancel, a2Mat₂_one]
    refine ⟨c, ?_, ?_⟩
    ·
      change (M₁ : Matrix (Fin 3) (Fin 3) Ω) * X * (↑M₁⁻¹ : Matrix (Fin 3) (Fin 3) Ω) = _
      rw [hM₁v, hM₁i, ← hau, ← hau']
      calc a2Mat₁ u' = a2Mat₁ u * (a2Mat₁ u⁻¹ * a2Mat₁ u') := by
            rw [← Matrix.mul_assoc, hinvu, Matrix.one_mul]
        _ = c • a2Mat₁ u := by
            rw [hc₁, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
              Matrix.mul_one]
    · change (M₂ : Matrix (Fin 3) (Fin 3) Ω) * Y * (↑M₂⁻¹ : Matrix (Fin 3) (Fin 3) Ω) = _
      rw [hM₂v, hM₂i, ← hav, ← hav']
      calc a2Mat₂ v' = (a2Mat₂ v' * a2Mat₂ v⁻¹) * a2Mat₂ v := by
            rw [Matrix.mul_assoc, hinvv, Matrix.mul_one]
        _ = c • a2Mat₂ v := by
            rw [hc₂, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
              Matrix.one_mul]
  obtain ⟨c₁, hc₁⟩ := exists_eq_scalar_of_discrepancy M₁ g₁ (Prod.fst '' S)
    (fun X hX => by
      obtain ⟨s, hs, rfl⟩ := hX
      obtain ⟨c, hc, -⟩ := hdisc s hs
      exact ⟨c, hc⟩)
    (fun i j hij => by
      obtain ⟨s, hs, hs1⟩ := hT₁ i j hij
      exact ⟨s, hs, hs1⟩)
  obtain ⟨c₂, hc₂⟩ := exists_eq_scalar_of_discrepancy M₂ g₂ (Prod.snd '' S)
    (fun Y hY => by
      obtain ⟨s, hs, rfl⟩ := hY
      obtain ⟨c, -, hc⟩ := hdisc s hs
      exact ⟨c, hc⟩)
    (fun i j hij => by
      obtain ⟨s, hs, hs2⟩ := hT₂ i j hij
      exact ⟨s, hs, hs2⟩)
  rw [hM₁v] at hc₁
  rw [hM₂v] at hc₂
  exact ⟨mem_torusGroup_of_diagonal_mul_eq_scalar hz₁ s₁ t₁ hc₁,
    mem_torusGroup_of_diagonal_mul_eq_scalar₂ hz₂ s₂ t₂ hc₂⟩

section TransferFix

variable {Fr : Ω →+* Ω}

theorem map_conj_inf_phi3FixedGroup {w : WeylGroup Tag.E6} {S : Set (Fin Tag.E6.rank → ℤ)}
    {Q' : Subgroup (ModGL Tag.E6 Ω)}
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom = Q')
    (θ : ↥Q' ≃* ↥Q') (hθ : ∀ g, (θ g : ModGL Tag.E6 Ω) = phi3ThetaConj Ω Fr w g) :
    (rootSpan Tag.E6 Ω S ⊓ phi3FixedGroup Ω Fr).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      (fixSubgroup θ).map Q'.subtype := by
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w
  ext y
  constructor
  · rintro ⟨x, ⟨hxS, hxR⟩, rfl⟩
    have hy : (MulAut.conj n).toMonoidHom x ∈ Q' := by
      rw [← hQ]
      exact ⟨x, hxS, rfl⟩
    refine ⟨⟨_, hy⟩, ?_, rfl⟩
    change θ ⟨_, hy⟩ = ⟨_, hy⟩
    apply Subtype.ext
    rw [hθ]
    change phi3ThetaConj Ω Fr w (n * x * n⁻¹) = n * x * n⁻¹
    rw [phi3ThetaConj_conj, (mem_phi3FixedGroup_iff.1 hxR).2]
  · rintro ⟨g, hg, rfl⟩
    have hgQ : (g : ModGL Tag.E6 Ω) ∈ (rootSpan Tag.E6 Ω S).map (MulAut.conj n).toMonoidHom := by
      rw [hQ]
      exact g.2
    obtain ⟨x, hxS, hx⟩ := hgQ
    change n * x * n⁻¹ = (g : ModGL Tag.E6 Ω) at hx
    have hθg : phi3ThetaConj Ω Fr w g = g := by
      rw [← hθ]
      exact congrArg Subtype.val (hg : θ g = g)
    rw [← hx, phi3ThetaConj_conj] at hθg
    refine ⟨x, ⟨hxS, mem_phi3FixedGroup_iff.2 ⟨rootSpan_le_adjointGroup Ω S hxS,
      mul_left_cancel (mul_right_cancel hθg)⟩⟩, ?_⟩
    change n * x * n⁻¹ = g
    exact hx

end TransferFix

theorem invTransposeMapSL_transvection_neg_one (Fr : Ω →+* Ω) {i j : Fin 3} (hij : i ≠ j) :
    invTransposeMapSL Fr 3 (Matrix.SpecialLinearGroup.transvection hij.symm (-1)) =
      Matrix.SpecialLinearGroup.transvection hij 1 := by
  apply Subtype.ext
  rw [coe_invTransposeMapSL]
  change ((Matrix.transvection j i (-1 : Ω)).map Fr)⁻¹ᵀ = Matrix.transvection i j 1
  have hmap : (Matrix.transvection j i (-1 : Ω)).map Fr = Matrix.transvection j i (-1) := by
    rw [Matrix.transvection, Matrix.map_add _ (map_add _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single, map_neg, map_one]
  have hinv : (Matrix.transvection j i (-1 : Ω))⁻¹ = Matrix.transvection j i 1 :=
    Matrix.inv_eq_left_inv (by
      rw [Matrix.transvection_mul_transvection_same j i hij.symm, add_neg_cancel,
        Matrix.transvection_zero])
  rw [hmap, hinv, Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, Matrix.transvection]

section A2A2Case

variable {K : Type} [Field K] {σ : K →+* K} [Algebra K Ω] {Fr : Ω →+* Ω}

theorem phi3_A2A2_case [IsAlgClosure K Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ phi3TStar K σ Ω Fr g) (hxp : orderOf x = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    (∃ k₂ : Subfield Ω, (∀ c, c ∈ k₂ ↔ c ^ (ℓ ^ f) ^ 2 = c) ∧
      ∃ ψ : SL(3, k₂) →* ModGL Tag.E6 Ω,
        ψ.range = ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
          rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆ ∧
        (∀ A : SL(3, k₂), ψ A = 1 ↔ ∃ c : k₂, c ^ 3 = 1 ∧ c ^ (ℓ ^ f + 1) = 1 ∧
          (A : Matrix (Fin 3) (Fin 3) k₂) = scalar (Fin 3) c) ∧
        Nat.card ψ.ker = Nat.gcd 3 (ℓ ^ f + 1) ∧
        Nonempty (SL(3, k₂) ⧸ ψ.ker ≃*
          ↥⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
            rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆)) ∧
    (∀ a ∈ rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
      ∀ b ∈ rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
        a * b * a⁻¹ * b⁻¹ ∈ ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
          rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆) ∧
    (⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
        rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆).relIndex
      (rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr) ∣ Nat.gcd 3 (ℓ ^ f + 1) ∧
    Nat.card (Subgroup.center ↥⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
        rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆) =
      Nat.gcd 3 ((ℓ ^ f) ^ 2 - 1) / Nat.gcd 3 (ℓ ^ f + 1) ∧
    CFSG.IsQuasisimple ↥⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
        rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆ ∧
    ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
        rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆ ≤ phi3CStar K σ Ω g ∧
    (CFSG.perfectResidual ↥(phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x})).map
        (phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x}).subtype =
      ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
        rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆ ∧
    (torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel x)) ⊓
        Subgroup.centralizer
          (↑⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
            rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆ :
            Set (ModGL Tag.E6 Ω)) ≤ torusGroup Tag.E6 Ω ∧
    (phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x}) ⊓
        Subgroup.centralizer
          (↑⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
            rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆ :
            Set (ModGL Tag.E6 Ω)) ≤ phi3Torus Ω Fr := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, hr⟩ := phi3_prime_setup (Ω := Ω) hf hp hpq
  obtain ⟨-, hder, hCR, -, -, -, -, -⟩ := phi3_rational_layer hℓ hf hK hσ hFr hg hgn
  have hRG : phi3FixedGroup Ω Fr ≤ adjointGroup Tag.E6 Ω := fun y hy =>
    (mem_phi3FixedGroup_iff.1 hy).1
  have hxT0 : x ∈ phi3Torus Ω Fr := hx.1
  have hxH : x ∈ torusGroup Tag.E6 Ω := hxT0.1
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi3TorusTorsion Ω Fr p := ⟨hxT0, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hQ₁₂, π, π', h12, h21⟩ := phi3_A2A2_transport hp3 hFr hζ hr hxT hx1 hA2A2
  obtain ⟨θ, hθ, a, b, hab⟩ := exists_exchanged_layer hFrs (phi3ThetaConj Ω Fr w)
    (phi3ThetaConj_injective w) π π' h12 h21
  set k₀ := RingHom.eqLocusField σ (RingHom.id K)
  have : Module.Finite k₀ K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic k₀ K := Algebra.IsAlgebraic.of_finite k₀ K
  have : IsAlgClosure k₀ Ω := IsAlgClosure.ofAlgebraic k₀ K Ω
  have hk₀card : Nat.card k₀ = ℓ ^ f := natCard_eqLocusField hℓ hf hK hσ
  set k₂ : Subfield Ω := RingHom.eqLocusField (Fr.comp Fr) (RingHom.id Ω)
  have hk₂ : ∀ c, c ∈ k₂ ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [RingHom.mem_eqLocusField, RingHom.comp_apply, hFr, hFr, RingHom.id_apply, ← pow_mul, sq]
  have hτ : ∀ X : SL(3, Ω), ((invTransposeMapSL Fr 3 X : SL(3, Ω)) :
      Matrix (Fin 3) (Fin 3) Ω) = (((X : Matrix (Fin 3) (Fin 3) Ω).map (· ^ (ℓ ^ f)))⁻¹)ᵀ :=
    fun X => by
      rw [coe_invTransposeMapSL]
      congr 3
      exact funext hFr
  obtain ⟨h₁, h₂, ψ, hψ, -, -, hqs9, hker9, hcardker9, -, hcardcenter9, -, -, hindex9,
      hder9⟩ := negative_exchanged_SL3_central_product_fixed_layer hk₀card k₂ hk₂
    (invTransposeMapSL Fr 3) hτ twoA2MulSup twoA2MulSup_surjective twoA2MulSup_eq_one_iff θ a b
    hab
  set Y := rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr with hYdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hYF : Y.map (MulAut.conj n).toMonoidHom =
      (fixSubgroup θ).map (subsystemGroup Tag.E6 Ω support13 ⊔
        subsystemGroup Tag.E6 Ω support56).subtype :=
    map_conj_inf_phi3FixedGroup hQ₁₂ θ hθ
  let F : ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) →*
      ModGL Tag.E6 Ω := (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _)
  have hF : Function.Injective F := (MulAut.conj n).symm.injective.comp Subtype.val_injective
  have hFapp : ∀ y, F y = n⁻¹ * (y : ModGL Tag.E6 Ω) * n := fun y => by
    simp [F, MulAut.conj_symm_apply]
  have hYf : (fixSubgroup θ).map F = Y := by
    have hid : (MulAut.conj n).symm.toMonoidHom.comp (MulAut.conj n).toMonoidHom =
        MonoidHom.id _ := MonoidHom.ext fun y => by simp
    rw [show F = (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _) from rfl,
      ← Subgroup.map_map, ← hYF, Subgroup.map_map, hid, Subgroup.map_id]
  set ψ' : SL(3, k₂) →* ModGL Tag.E6 Ω := F.comp ψ with hψ'def
  have hrange : ψ'.range = ⁅Y, Y⁆ := by
    rw [← hYf, ← Subgroup.map_commutator, hder9, MonoidHom.range_comp]
  have hψ'1 : ∀ A, ψ' A = 1 ↔ ψ A = 1 := fun A => map_eq_one_iff F hF
  have hker' : ψ'.ker = ψ.ker := by
    ext A
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψ'1]
  let E : ↥ψ.range ≃* ↥⁅Y, Y⁆ := (Subgroup.equivMapOfInjective ψ.range F hF).trans
    (MulEquiv.subgroupCongr (by rw [← MonoidHom.range_comp]; exact hrange))
  have hqsP : CFSG.IsQuasisimple ↥⁅Y, Y⁆ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv E hqs9
  have hidx : ⁅Y, Y⁆.relIndex Y = (ψ.range.subgroupOf (fixSubgroup θ)).index := by
    rw [← hrange, ← hYf, MonoidHom.range_comp, Subgroup.relIndex_map_map_of_injective _ _ hF]
    rfl
  have hPY : ⁅Y, Y⁆ ≤ Y := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hPC : ⁅Y, Y⁆ ≤ phi3CStar K σ Ω g := by
    rw [← hder]
    exact Subgroup.commutator_mono inf_le_right inf_le_right
  have hPD : ⁅Y, Y⁆ ≤ phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x} :=
    le_inf hPC (hPY.trans (inf_le_left.trans (rootSpan_torusRootKernel_le_centralizer hxH)))
  have hp7 := (phi3_prime_facts hp hp3 hpq).2.2
  have hCG := centralizer_eq_sup_of_pow_eq_one (by omega : 5 < p) hpΩ hxH hxp'
  have hDle : phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x} ≤
      torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel x) := by
    rw [← hCG]
    exact le_inf (inf_le_left.trans (hCR.trans hRG)) inf_le_right
  have hHN : torusGroup Tag.E6 Ω ≤
      Subgroup.normalizer (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) :=
    torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hD'Y : ⁅phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x},
      phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x}⁆ ≤ Y := by
    refine le_inf ?_ ?_
    · exact (Subgroup.commutator_mono hDle hDle).trans
        (commutator_sup_le_of_comm hHN fun a ha b hb => torusGroup_E6_comm ha hb)
    · refine (Subgroup.commutator_mono (inf_le_left.trans hCR) (inf_le_left.trans hCR)).trans ?_
      rw [hder]
      exact hCR
  have hres : (CFSG.perfectResidual ↥(phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x})).map
      (phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x}).subtype = ⁅Y, Y⁆ :=
    le_antisymm ((map_perfectResidual_le _).trans (Subgroup.commutator_mono hD'Y hD'Y))
      (le_map_perfectResidual hqsP.1 hPD)
  have hC6 : (torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel x)) ⊓
      Subgroup.centralizer (↑⁅Y, Y⁆ : Set (ModGL Tag.E6 Ω)) ≤ torusGroup Tag.E6 Ω := by
    rintro y ⟨hyHQ, hyc⟩
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN
    have hy' : y ∈ (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) *
        (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) := by
      rw [← hmul]
      exact hyHQ
    obtain ⟨h, hh, z, hz, rfl⟩ := hy'
    have hnN := canonicalRep_mem_normalizer (R := Ω) w
    have hh' : n * h * n⁻¹ ∈ torusGroup Tag.E6 Ω := (Subgroup.mem_normalizer_iff.1 hnN h).1 hh
    have hz' : n * z * n⁻¹ ∈ (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) *
        (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) := by
      rw [← coe_sup_subsystemGroup, ← hQ₁₂]
      exact ⟨z, hz, rfl⟩
    obtain ⟨z₁, hz₁, z₂, hz₂, hz12⟩ := hz'
    replace hz12 : z₁ * z₂ = n * z * n⁻¹ := hz12
    set S : Set (SL(3, Ω) × SL(3, Ω)) := Set.range fun A : SL(3, k₂) =>
      (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * invTransposeMapSL Fr 3 (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹)
      with hSdef
    have hS : ∀ s ∈ S, (n * h * n⁻¹ * z₁ * z₂) * twoA2Mul Ω s =
        twoA2Mul Ω s * (n * h * n⁻¹ * z₁ * z₂) := by
      rintro _ ⟨A, rfl⟩
      have hPA : twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
          h₂ * invTransposeMapSL Fr 3 (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹) =
          (ψ A : ModGL Tag.E6 Ω) := by
        rw [hψ A]
        rfl
      rw [hPA]
      have hmem : ψ' A ∈ ⁅Y, Y⁆ := hrange ▸ ⟨A, rfl⟩
      have hc0 := (Subgroup.mem_centralizer_iff.1 hyc (ψ' A) hmem).symm
      change h * z * F (ψ A) = F (ψ A) * (h * z) at hc0
      rw [hFapp] at hc0
      have key : n * h * n⁻¹ * z₁ * z₂ = n * (h * z) * n⁻¹ := by
        rw [mul_assoc (n * h * n⁻¹) z₁ z₂, hz12]
        group
      rw [key]
      calc n * (h * z) * n⁻¹ * (ψ A : ModGL Tag.E6 Ω) =
          n * (h * z * (n⁻¹ * (ψ A : ModGL Tag.E6 Ω) * n)) * n⁻¹ := by group
        _ = n * (n⁻¹ * (ψ A : ModGL Tag.E6 Ω) * n * (h * z)) * n⁻¹ := by rw [hc0]
        _ = (ψ A : ModGL Tag.E6 Ω) * (n * (h * z) * n⁻¹) := by group
    have hT₁ : ∀ (i j : Fin 3) (hij : i ≠ j),
        ∃ s ∈ S, s.1 = h₁ * Matrix.SpecialLinearGroup.transvection hij 1 * h₁⁻¹ :=
      fun i j hij => ⟨_, ⟨Matrix.SpecialLinearGroup.transvection hij 1, rfl⟩, by
        dsimp only
        rw [Matrix.SpecialLinearGroup.map_transvection, map_one]⟩
    have hT₂ : ∀ (i j : Fin 3) (hij : i ≠ j),
        ∃ s ∈ S, s.2 = h₂ * Matrix.SpecialLinearGroup.transvection hij 1 * h₂⁻¹ :=
      fun i j hij => ⟨_, ⟨Matrix.SpecialLinearGroup.transvection hij.symm (-1), rfl⟩, by
        dsimp only
        rw [Matrix.SpecialLinearGroup.map_transvection, map_neg, map_one,
          invTransposeMapSL_transvection_neg_one]⟩
    obtain ⟨hz₁H, hz₂H⟩ := mem_torusGroup_of_centralizes_twoA2 hh' hz₁ hz₂ S hS h₁ h₂ hT₁ hT₂
    have hz'H : n * z * n⁻¹ ∈ torusGroup Tag.E6 Ω := hz12 ▸ mul_mem hz₁H hz₂H
    have hzH : z ∈ torusGroup Tag.E6 Ω := by
      have h3 := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) (n * z * n⁻¹)).1 hz'H
      rwa [show n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ = z by group] at h3
    exact mul_mem hh hzH
  refine ⟨⟨k₂, hk₂, ψ', hrange, fun A => (hψ'1 A).trans (hker9 A), by rw [hker']; exact hcardker9,
      ⟨(QuotientGroup.quotientKerEquivRange ψ').trans (MulEquiv.subgroupCongr hrange)⟩⟩,
    fun a ha b hb => ?_, ?_, (natCard_center_eq_of_mulEquiv E.symm).trans hcardcenter9, hqsP,
    hPC, hres, hC6, fun y hy => ⟨hC6 ⟨hDle hy.1, hy.2⟩, hCR hy.1.1⟩⟩
  · have h := Subgroup.commutator_mem_commutator ha hb
    rwa [commutatorElement_def] at h
  · rw [hidx]
    exact hindex9

end A2A2Case

end CFSG.RankThree.Classical2

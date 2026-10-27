module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.Invariant
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddCountSU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

@[expose] def bMonoid (σ : F ≃+* F) : Submonoid (SU σ 3) where
  carrier := {x | mat σ 3 x 1 0 = 0 ∧ mat σ 3 x 2 0 = 0}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    simp only [Set.mem_setOf_eq, map_mul, Matrix.mul_apply, Fin.sum_univ_three, hx1, hx2, hy1, hy2,
      zero_mul, mul_zero, add_zero, zero_add, and_self]
  one_mem' := by simp

@[expose] def bSU (σ : F ≃+* F) : Subgroup (SU σ 3) :=
  { bMonoid σ with
    inv_mem' := fun {x} hx => by
      have hpos : 0 < orderOf x := orderOf_pos x
      have : x⁻¹ = x ^ (orderOf x - 1) := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
      rw [this]
      exact (bMonoid σ).pow_mem hx _ }

theorem mem_bSU {σ : F ≃+* F} {x : SU σ 3} :
    x ∈ bSU σ ↔ mat σ 3 x 1 0 = 0 ∧ mat σ 3 x 2 0 = 0 := Iff.rfl

variable (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem rootU_le_bSU : rootU hF ≤ bSU (unitaryInvolution F p f) := by
  intro x hx
  have hm := (mat_of_mem_rootU hF hx).2
  rw [mem_bSU, hm]
  simp

theorem range_tSU_le_bSU : (tSU hF).range ≤ bSU (unitaryInvolution F p f) := by
  rintro _ ⟨μ, rfl⟩
  rw [mem_bSU, mat_tSU hF μ]
  simp

theorem fix_B {u h : SU (unitaryInvolution F p f) 3} (hu : u ∈ rootU hF) (hu1 : u ≠ 1)
    (hh : h⁻¹ * u * h ∈ bSU (unitaryInvolution F p f)) : h ∈ bSU (unitaryInvolution F p f) := by
  obtain ⟨hm1, hm2⟩ := hh
  have hmat : mat (unitaryInvolution F p f) 3 u * mat (unitaryInvolution F p f) 3 h =
      mat (unitaryInvolution F p f) 3 h * mat (unitaryInvolution F p f) 3 (h⁻¹ * u * h) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  have hux := (mat_of_mem_rootU hF hu).2
  have E : ∀ i, (mat (unitaryInvolution F p f) 3 u * mat (unitaryInvolution F p f) 3 h) i 0 =
      (mat (unitaryInvolution F p f) 3 h * mat (unitaryInvolution F p f) 3 (h⁻¹ * u * h)) i 0 :=
    fun i => by rw [hmat]
  have e0 := E 0
  have e1 := E 1
  have e2 := E 2
  rw [hux] at e0 e1 e2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hm1, hm2, mul_zero, add_zero, of_apply,
    cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val', cons_val_fin_one, head_cons,
    head_fin_const, tail_cons, one_mul, zero_mul, zero_add] at e0 e1 e2
  generalize mat (unitaryInvolution F p f) 3 (h⁻¹ * u * h) 0 0 = l at e0 e1 e2
  have iso := sum_mat_mul_mat h 0 0
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r1 : Fin.rev (1 : Fin 3) = 1 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  simp only [Fin.sum_univ_three, r0, r1, r2] at iso
  rw [ite_eq_right (by decide)] at iso
  show mat (unitaryInvolution F p f) 3 h 1 0 = 0 ∧ mat (unitaryInvolution F p f) 3 h 2 0 = 0
  by_cases hv2 : mat (unitaryInvolution F p f) 3 h 2 0 = 0
  · refine ⟨?_, hv2⟩
    simp only [hv2, map_zero, mul_zero, zero_mul, add_zero, zero_add] at iso
    rcases mul_eq_zero.1 iso with h1 | h1
    · exact (map_eq_zero (unitaryInvolution F p f)).1 h1
    · exact h1
  · exfalso
    have hl : l = 1 := by
      have : mat (unitaryInvolution F p f) 3 h 2 0 * (l - 1) = 0 := by linear_combination -e2
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 hv2
      · linear_combination h1
    have ha : ca u = 0 := by
      rw [hl] at e1
      have : unitaryInvolution F p f (ca u) * mat (unitaryInvolution F p f) 3 h 2 0 = 0 := by
        linear_combination -e1
      rcases mul_eq_zero.1 this with h1 | h1
      · exact (map_eq_zero (unitaryInvolution F p f)).1 h1
      · exact absurd h1 hv2
    have hb : cb u = 0 := by
      rw [hl] at e0
      rw [ha] at e0
      have : cb u * mat (unitaryInvolution F p f) 3 h 2 0 = 0 := by linear_combination e0
      rcases mul_eq_zero.1 this with h1 | h1
      · exact h1
      · exact absurd h1 hv2
    exact hu1 (eq_of_ca_cb hF hu (one_mem _) (ha.trans ca_one.symm) (hb.trans cb_one.symm))

theorem exists_mul_tSU {x : SU (unitaryInvolution F p f) 3}
    (hx : x ∈ bSU (unitaryInvolution F p f)) :
    ∃ μ : Fˣ, x * (tSU hF μ)⁻¹ ∈ rootU hF := by
  obtain ⟨hx1, hx2⟩ := hx
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r1 : Fin.rev (1 : Fin 3) = 1 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  have i02 := sum_mat_mul_mat x 0 2
  have i01 := sum_mat_mul_mat x 0 1
  simp only [Fin.sum_univ_three, r0, r1, r2, hx1, hx2, map_zero, zero_mul, add_zero, zero_add]
    at i02 i01
  rw [if_pos trivial] at i02
  rw [if_neg (by decide)] at i01
  have ha : mat (unitaryInvolution F p f) 3 x 0 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at i02
    exact zero_ne_one i02
  have h21 : mat (unitaryInvolution F p f) 3 x 2 1 = 0 := by
    rcases mul_eq_zero.1 i01 with h | h
    · exact absurd ((map_eq_zero _).1 h) ha
    · exact h
  have hdet : (mat (unitaryInvolution F p f) 3 x).det = 1 := by rw [mat_apply]; exact x.2.1
  rw [Matrix.det_fin_three, hx1, hx2, h21] at hdet
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hσa : unitaryInvolution F p f (mat (unitaryInvolution F p f) 3 x 0 0) =
      mat (unitaryInvolution F p f) 3 x 0 0 ^ p ^ f := unitaryInvolution_apply F p f _
  have h22 : mat (unitaryInvolution F p f) 3 x 2 2 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at i02; exact zero_ne_one i02
  have h11 : mat (unitaryInvolution F p f) 3 x 1 1 =
      mat (unitaryInvolution F p f) 3 x 0 0 ^ (p ^ f - 1) := by
    have e1 : mat (unitaryInvolution F p f) 3 x 0 0 * mat (unitaryInvolution F p f) 3 x 1 1 *
        mat (unitaryInvolution F p f) 3 x 2 2 = 1 := by linear_combination hdet
    have e2 : mat (unitaryInvolution F p f) 3 x 0 0 ^ p ^ f *
        mat (unitaryInvolution F p f) 3 x 2 2 = 1 := by rw [← hσa]; exact i02
    have e3 : mat (unitaryInvolution F p f) 3 x 0 0 * mat (unitaryInvolution F p f) 3 x 1 1 =
        mat (unitaryInvolution F p f) 3 x 0 0 ^ p ^ f := by
      refine mul_right_cancel₀ h22 ?_
      rw [e2, e1]
    have e4 : mat (unitaryInvolution F p f) 3 x 0 0 ^ p ^ f =
        mat (unitaryInvolution F p f) 3 x 0 0 * mat (unitaryInvolution F p f) 3 x 0 0 ^ (p ^ f - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hq1]
    exact mul_left_cancel₀ ha (e3.trans e4)
  refine ⟨Units.mk0 _ ha, mem_rootU_of_unitriangular hF ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
    rw [map_mul, ← map_inv, mat_tSU hF, Matrix.mul_diagonal]
  · simp [hx1]
  · simp [hx2]
  · simp [h21]
  · simp [ha]
  · simp [h11, ha]
  · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, inv_pow, inv_inv,
      Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [mul_comm, ← hσa]
    exact i02

theorem inf_rootU_range_tSU : rootU hF ⊓ (tSU hF).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxU, μ, rfl⟩
  have h1 := (mat_of_mem_rootU hF hxU).2
  have h00 : (μ : F) = 1 := by
    have := congrFun (congrFun ((mat_tSU hF μ).symm.trans h1) 0) 0
    simpa using this
  have hμ : μ = 1 := Units.ext (by simpa using h00)
  rw [Subgroup.mem_bot, hμ, map_one]

theorem card_bSU :
    Nat.card (bSU (unitaryInvolution F p f)) = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) := by
  have h := card_mul_inf_eq (rootU hF) (tSU hF).range (bSU (unitaryInvolution F p f))
    (rootU_le_bSU hF) (range_tSU_le_bSU hF) (fun b hb => by
      obtain ⟨μ, hμ⟩ := exists_mul_tSU hF hb
      exact ⟨_, hμ, tSU hF μ, ⟨μ, rfl⟩, (inv_mul_cancel_right b _).symm⟩)
  rw [inf_rootU_range_tSU hF, Subgroup.card_bot, mul_one, card_rootGroup_three hF,
    card_range_tSU hF] at h
  exact h

@[expose] def zU : Subgroup (SU (unitaryInvolution F p f) 3) where
  carrier := {x | x ∈ rootU hF ∧ ca x = 0}
  mul_mem' := fun {x y} hx hy =>
    ⟨(rootU hF).mul_mem hx.1 hy.1, by rw [ca_mul hF hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  one_mem' := ⟨one_mem _, ca_one⟩
  inv_mem' := fun {x} hx =>
    ⟨(rootU hF).inv_mem hx.1, by rw [ca_inv hF hx.1, hx.2, neg_zero]⟩

theorem mem_zU {x : SU (unitaryInvolution F p f) 3} : x ∈ zU hF ↔ x ∈ rootU hF ∧ ca x = 0 :=
  Iff.rfl

theorem zU_le_rootU : zU hF ≤ rootU hF := fun _ hx => hx.1

theorem zU_central {x y : SU (unitaryInvolution F p f) 3} (hx : x ∈ zU hF) (hy : y ∈ rootU hF) :
    x * y = y * x := by
  refine eq_of_ca_cb hF ((rootU hF).mul_mem hx.1 hy) ((rootU hF).mul_mem hy hx.1) ?_ ?_
  · rw [ca_mul hF hx.1 hy, ca_mul hF hy hx.1, add_comm]
  · rw [cb_mul hF hx.1 hy, cb_mul hF hy hx.1, hx.2, map_zero]
    ring

theorem zU_le_range_embSU : zU hF ≤ (embSU (unitaryInvolution F p f)).range := by
  intro x hx
  have hm := (mat_of_mem_rootU hF hx.1).2
  rw [hx.2] at hm
  refine mem_range_embSU_of_blockForm ?_ ?_ ?_ ?_ ?_ <;> show mat _ 3 x _ _ = _ <;> rw [hm] <;> simp

theorem conj_mem_zU {b z : SU (unitaryInvolution F p f) 3}
    (hb : b ∈ bSU (unitaryInvolution F p f)) (hz : z ∈ zU hF) : b * z * b⁻¹ ∈ zU hF := by
  obtain ⟨μ, hμ⟩ := exists_mul_tSU hF hb
  have hb' : b = (b * (tSU hF μ)⁻¹) * tSU hF μ := (inv_mul_cancel_right b _).symm
  have h1 : tSU hF μ * z * (tSU hF μ)⁻¹ ∈ zU hF :=
    ⟨tSU_conj_mem_rootU hF μ hz.1, by rw [ca_tSU_conj hF μ hz.1, hz.2]; ring⟩
  have h2 : b * z * b⁻¹ = (b * (tSU hF μ)⁻¹) * (tSU hF μ * z * (tSU hF μ)⁻¹) *
      (b * (tSU hF μ)⁻¹)⁻¹ := by group
  have h3 := zU_central hF h1 hμ
  rw [h2, mul_inv_eq_iff_eq_mul.2 h3.symm]
  exact h1

theorem exists_ca_ne_zero : ∃ x ∈ rootU hF, ca x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let φ : rootU hF → traceZero (unitaryInvolution F p f) := fun x =>
    ⟨cb x.1, cb_add_of_ca_eq_zero hF x.2 (hcon _ x.2)⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    exact Subtype.ext (eq_of_ca_cb hF x.2 y.2 ((hcon _ x.2).trans (hcon _ y.2).symm)
      (congrArg Subtype.val hxy))
  have h1 := Nat.card_le_card_of_injective φ hφ
  rw [card_rootGroup_three hF, card_traceZero hF] at h1
  have hq2 := two_le_prime_pow_of_card hF
  have h3 : (p ^ f) ^ 3 = p ^ f * (p ^ f) ^ 2 := by ring
  have h4 : 4 ≤ (p ^ f) ^ 2 := by nlinarith
  nlinarith

theorem card_zU (hq3 : p ^ f % 3 = 1) : Nat.card (zU hF) = p ^ f := by
  obtain ⟨x₀, hx₀, ha₀⟩ := exists_ca_ne_zero hF
  let φ : zU hF → traceZero (unitaryInvolution F p f) := fun x =>
    ⟨cb x.1, cb_add_of_ca_eq_zero hF x.2.1 x.2.2⟩
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y hxy
      exact Subtype.ext (eq_of_ca_cb hF x.2.1 y.2.1 (x.2.2.trans y.2.2.symm)
        (congrArg Subtype.val hxy))
    · rintro ⟨d, hd⟩
      obtain ⟨x, hx, hxa, hxb⟩ := mem_zSet hF hq3 (le_refl (rootU hF))
        (fun μ _ x hx => tSU_conj_mem_rootU hF μ hx) hx₀ ha₀ hd
      exact ⟨⟨x, hx, hxa⟩, Subtype.ext hxb⟩
  rw [Nat.card_congr (Equiv.ofBijective φ hbij), card_traceZero hF]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

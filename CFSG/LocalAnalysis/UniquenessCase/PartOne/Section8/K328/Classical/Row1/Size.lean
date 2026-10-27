module

import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped commutatorElement
open CFSG.Blueprint (LieModel)

private def k328r1s_emb2 {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F) :
    Matrix (Fin 4) (Fin 4) F :=
  Matrix.of fun i j => Fin.lastCases (motive := fun _ => F)
    (Fin.lastCases (motive := fun _ => F) d (fun _ => 0) j)
    (fun i' => Fin.lastCases (motive := fun _ => F) 0 (fun j' => A i' j') j) i

private theorem k328r1s_emb2_cc {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F)
    (i j : Fin 3) : k328r1s_emb2 A d i.castSucc j.castSucc = A i j := by
  simp only [k328r1s_emb2, Matrix.of_apply, Fin.lastCases_castSucc]

private theorem k328r1s_emb2_cl {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F)
    (i : Fin 3) : k328r1s_emb2 A d i.castSucc (Fin.last 3) = 0 := by
  simp only [k328r1s_emb2, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem k328r1s_emb2_lc {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F)
    (j : Fin 3) : k328r1s_emb2 A d (Fin.last 3) j.castSucc = 0 := by
  simp only [k328r1s_emb2, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem k328r1s_emb2_ll {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F) :
    k328r1s_emb2 A d (Fin.last 3) (Fin.last 3) = d := by
  simp only [k328r1s_emb2, Matrix.of_apply, Fin.lastCases_last]

private theorem k328r1s_emb2_mul {F : Type} [Field F] (A B : Matrix (Fin 3) (Fin 3) F) (d e : F) :
    k328r1s_emb2 A d * k328r1s_emb2 B e = k328r1s_emb2 (A * B) (d * e) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [k328r1s_emb2_cc, k328r1s_emb2_cl, k328r1s_emb2_lc, k328r1s_emb2_ll,
      Matrix.mul_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add]

private theorem k328r1s_emb2_one {F : Type} [Field F] :
    k328r1s_emb2 (1 : Matrix (Fin 3) (Fin 3) F) 1 = 1 := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [k328r1s_emb2_ll, Matrix.one_apply_eq]
  · rw [k328r1s_emb2_lc, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
  · rw [k328r1s_emb2_cl, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  · simp only [k328r1s_emb2_cc, Matrix.one_apply, Fin.castSucc_inj]

private theorem k328r1s_emb2_det {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F) :
    (k328r1s_emb2 A d).det = A.det * d := by
  have hsub : (k328r1s_emb2 A d).submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j
    exact k328r1s_emb2_cc A d i j
  rw [Matrix.det_succ_row _ (Fin.last 3), Fin.sum_univ_castSucc]
  simp only [k328r1s_emb2_lc, k328r1s_emb2_ll, mul_zero, zero_mul, Finset.sum_const_zero,
    zero_add, Fin.succAbove_last, hsub, Fin.val_last]
  norm_num [mul_comm]

private def k328r1s_embHom (F : Type) [Field F] :
    Matrix (Fin 3) (Fin 3) F →* Matrix (Fin 4) (Fin 4) F where
  toFun A := k328r1s_emb2 A 1
  map_one' := k328r1s_emb2_one
  map_mul' A B := by rw [k328r1s_emb2_mul, mul_one]

private theorem k328r1s_embHom_injective (F : Type) [Field F] :
    Function.Injective (k328r1s_embHom F) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i.castSucc) j.castSucc
  simpa only [k328r1s_embHom, MonoidHom.coe_mk, OneHom.coe_mk, k328r1s_emb2_cc] using this

private def k328r1s_iota (F : Type) [Field F] : GL (Fin 3) F →* GL (Fin 4) F :=
  Units.map (k328r1s_embHom F)

private theorem k328r1s_iota_coe {F : Type} [Field F] (B : GL (Fin 3) F) :
    ((k328r1s_iota F B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      k328r1s_emb2 (B : Matrix (Fin 3) (Fin 3) F) 1 :=
  rfl

private theorem k328r1s_iota_injective (F : Type) [Field F] :
    Function.Injective (k328r1s_iota F) :=
  Units.map_injective (k328r1s_embHom_injective F)

private def k328r1s_Y (F : Type) [Field F] : Subgroup (GL (Fin 4) F) :=
  (StatedSL 3 F).map (k328r1s_iota F)

private theorem k328r1s_mem_Y_of_emb2 {F : Type} [Field F] (M : Matrix (Fin 3) (Fin 3) F)
    (hdet : M.det = 1) {g : GL (Fin 4) F}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = k328r1s_emb2 M 1) : g ∈ k328r1s_Y F := by
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hdet]; exact isUnit_one)
  refine Subgroup.mem_map.2 ⟨hu.unit, CFSG.Open.StatedAPI.mem_statedSL_of_det
    (by rw [IsUnit.unit_spec, hdet]), ?_⟩
  exact Units.ext (by rw [hg, k328r1s_iota_coe, IsUnit.unit_spec])

private theorem k328r1s_shape {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {g : Matrix (Fin 4) (Fin 4) F}
    (h : Matrix.diagonal ![ω, ω, ω, 1] * g = g * Matrix.diagonal ![ω, ω, ω, 1]) :
    g = k328r1s_emb2 (g.submatrix Fin.castSucc Fin.castSucc) (g (Fin.last 3) (Fin.last 3)) := by
  have hcs : ∀ j : Fin 3, (![ω, ω, ω, 1] : Fin 4 → F) (Fin.castSucc j) = ω := fun j => by
    fin_cases j <;> rfl
  have hl : (![ω, ω, ω, 1] : Fin 4 → F) (Fin.last 3) = 1 := rfl
  have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [k328r1s_emb2_ll]
  · rw [k328r1s_emb2_lc]
    have := congrFun (congrFun h (Fin.last 3)) j.castSucc
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hl, hcs] at this
    exact (mul_eq_zero.mp (by linear_combination -this :
      (ω - 1) * g (Fin.last 3) j.castSucc = 0)).resolve_left hne
  · rw [k328r1s_emb2_cl]
    have := congrFun (congrFun h i.castSucc) (Fin.last 3)
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hl, hcs] at this
    exact (mul_eq_zero.mp (by linear_combination this :
      (ω - 1) * g i.castSucc (Fin.last 3) = 0)).resolve_left hne
  · rw [k328r1s_emb2_cc]
    rfl

private theorem k328r1s_mem_C_comm {F : Type} [Field F] {z₀ g : GL (Fin 4) F}
    (hg : g ∈ StatedSL 4 F ⊓ Subgroup.centralizer {z₀}) :
    (z₀ : Matrix (Fin 4) (Fin 4) F) * g = g * z₀ := by
  have h : g * z₀ = z₀ * g := Subgroup.mem_centralizer_singleton_iff.mp hg.2
  exact (congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) h).symm

private theorem k328r1s_exists_emb2 {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {z₀ g : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (hg : g ∈ StatedSL 4 F ⊓ Subgroup.centralizer {z₀}) :
    ∃ (A : Matrix (Fin 3) (Fin 3) F) (d : F),
      (g : Matrix (Fin 4) (Fin 4) F) = k328r1s_emb2 A d := by
  have h := k328r1s_mem_C_comm hg
  rw [hz] at h
  exact ⟨_, _, k328r1s_shape hω1 h⟩

private theorem k328r1s_last_of_mul_inv {F : Type} [Field F] {A A' : Matrix (Fin 3) (Fin 3) F}
    {d d' : F} {a : GL (Fin 4) F} (hA : (a : Matrix (Fin 4) (Fin 4) F) = k328r1s_emb2 A d)
    (hA' : ((a⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = k328r1s_emb2 A' d') :
    d * d' = 1 := by
  have h : (a : Matrix (Fin 4) (Fin 4) F) * ((a⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hA, hA', k328r1s_emb2_mul] at h
  have := congrFun (congrFun h (Fin.last 3)) (Fin.last 3)
  rwa [k328r1s_emb2_ll, Matrix.one_apply_eq] at this

private theorem k328r1s_comm_mem_Y {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {z₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    {a b : GL (Fin 4) F} (ha : a ∈ StatedSL 4 F ⊓ Subgroup.centralizer {z₀})
    (hb : b ∈ StatedSL 4 F ⊓ Subgroup.centralizer {z₀}) : ⁅a, b⁆ ∈ k328r1s_Y F := by
  obtain ⟨A, d, hA⟩ := k328r1s_exists_emb2 hω1 hz ha
  obtain ⟨B, e, hB⟩ := k328r1s_exists_emb2 hω1 hz hb
  obtain ⟨A', d', hA'⟩ := k328r1s_exists_emb2 hω1 hz (Subgroup.inv_mem _ ha)
  obtain ⟨B', e', hB'⟩ := k328r1s_exists_emb2 hω1 hz (Subgroup.inv_mem _ hb)
  have h1 := k328r1s_last_of_mul_inv hA hA'
  have h2 := k328r1s_last_of_mul_inv hB hB'
  have hc : ((⁅a, b⁆ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      k328r1s_emb2 (A * B * A' * B') (d * e * d' * e') := by
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, hA, hB, hA', hB',
      k328r1s_emb2_mul, k328r1s_emb2_mul, k328r1s_emb2_mul]
  have hde : d * e * d' * e' = 1 := by
    calc d * e * d' * e' = (d * d') * (e * e') := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have hH : ⁅a, b⁆ ∈ StatedSL 4 F :=
    stdComp_le (StatedSL 4 F) z₀ (Subgroup.commutator_mem_commutator ha hb)
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL hH
  rw [hc, k328r1s_emb2_det, hde, mul_one] at hdet
  exact k328r1s_mem_Y_of_emb2 _ hdet (by rw [hc, hde])

private theorem k328r1s_stdComp_le_Y {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {z₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    stdComp (StatedSL 4 F) z₀ ≤ k328r1s_Y F :=
  Subgroup.commutator_le.2 fun _ ha _ hb => k328r1s_comm_mem_Y hω1 hz ha hb

private theorem k328r1s_omega_ne_one {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  rintro rfl
  exact one_ne_zero (by linear_combination hω - h2)

private theorem k328r1s_card_stdComp_le {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) {ω : F} (hω1 : ω ≠ 1) {z₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    Nat.card (stdComp (StatedSL 4 F) z₀) ≤ 60480 := by
  have h1 : Nat.card (stdComp (StatedSL 4 F) z₀) ≤ Nat.card (k328r1s_Y F) :=
    Subgroup.card_le_of_le (k328r1s_stdComp_le_Y hω1 hz)
  have h2 : Nat.card (k328r1s_Y F) = Nat.card (StatedSL 3 F) :=
    Subgroup.card_map_of_injective (k328r1s_iota_injective F)
  have h3 := CFSG.Open.StatedAPI.card_statedSL_three F
  have hcard : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  rw [hcard] at h3
  norm_num at h3
  omega

private theorem k328r1s_card_of_lie {K : Type} [Group K]
    (hcen : Nat.card (Subgroup.center K) = 3)
    (hlie : LieModel (K ⧸ Subgroup.center K) .PSL 3 2 2 ∨
      LieModel (K ⧸ Subgroup.center K) .PSU 3 2 3) :
    Nat.card K = 60480 ∨ Nat.card K = 16547328 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hcen]
  rcases hlie with h | h
  · have := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four
      (h.statedClassicalModel (by decide))
    omega
  · have := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (h.statedClassicalModel (by decide))
    omega

theorem row1_size (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    SizeLeaf (StatedSL 4 F) z₀ := by
  have _ := ht
  intro hz₀ X hXs hP
  obtain ⟨-, -, -, -, -, hcen, hlie⟩ := hP
  have hω1 := k328r1s_omega_ne_one hF hω
  have hXH : X ≤ StatedSL 4 F := hXs.trans (stdComp_le _ _)
  have hcardX : Nat.card (X.subgroupOf (StatedSL 4 F)) = Nat.card X :=
    card_subgroupOf_of_le hXH
  have hX := k328r1s_card_of_lie hcen hlie
  have hle : Nat.card X ≤ Nat.card (stdComp (StatedSL 4 F) z₀) := Subgroup.card_le_of_le hXs
  have hup := k328r1s_card_stdComp_le hF hω1 hz
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

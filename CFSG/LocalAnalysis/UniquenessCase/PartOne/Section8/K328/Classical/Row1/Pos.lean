module

import CFSG.Adapters.StatedQuasisimple
import CFSG.Open.StatedCenterThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped commutatorElement
open CFSG.Blueprint (LieModel)

private def k328r1p_emb2 {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F) :
    Matrix (Fin 4) (Fin 4) F :=
  Matrix.of fun i j => Fin.lastCases (motive := fun _ => F)
    (Fin.lastCases (motive := fun _ => F) d (fun _ => 0) j)
    (fun i' => Fin.lastCases (motive := fun _ => F) 0 (fun j' => A i' j') j) i

private theorem k328r1p_emb2_cc {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F)
    (i j : Fin 3) : k328r1p_emb2 A d i.castSucc j.castSucc = A i j := by
  simp only [k328r1p_emb2, Matrix.of_apply, Fin.lastCases_castSucc]

private theorem k328r1p_emb2_cl {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F)
    (i : Fin 3) : k328r1p_emb2 A d i.castSucc (Fin.last 3) = 0 := by
  simp only [k328r1p_emb2, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem k328r1p_emb2_lc {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F)
    (j : Fin 3) : k328r1p_emb2 A d (Fin.last 3) j.castSucc = 0 := by
  simp only [k328r1p_emb2, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem k328r1p_emb2_ll {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F) :
    k328r1p_emb2 A d (Fin.last 3) (Fin.last 3) = d := by
  simp only [k328r1p_emb2, Matrix.of_apply, Fin.lastCases_last]

private theorem k328r1p_emb2_mul {F : Type} [Field F] (A B : Matrix (Fin 3) (Fin 3) F) (d e : F) :
    k328r1p_emb2 A d * k328r1p_emb2 B e = k328r1p_emb2 (A * B) (d * e) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [k328r1p_emb2_cc, k328r1p_emb2_cl, k328r1p_emb2_lc, k328r1p_emb2_ll,
      Matrix.mul_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add]

private theorem k328r1p_emb2_one {F : Type} [Field F] :
    k328r1p_emb2 (1 : Matrix (Fin 3) (Fin 3) F) 1 = 1 := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [k328r1p_emb2_ll, Matrix.one_apply_eq]
  · rw [k328r1p_emb2_lc, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
  · rw [k328r1p_emb2_cl, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  · simp only [k328r1p_emb2_cc, Matrix.one_apply, Fin.castSucc_inj]

private theorem k328r1p_emb2_det {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (d : F) :
    (k328r1p_emb2 A d).det = A.det * d := by
  have hsub : (k328r1p_emb2 A d).submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j
    exact k328r1p_emb2_cc A d i j
  rw [Matrix.det_succ_row _ (Fin.last 3), Fin.sum_univ_castSucc]
  simp only [k328r1p_emb2_lc, k328r1p_emb2_ll, mul_zero, zero_mul, Finset.sum_const_zero,
    zero_add, Fin.succAbove_last, hsub, Fin.val_last]
  norm_num [mul_comm]

private def k328r1p_embHom (F : Type) [Field F] :
    Matrix (Fin 3) (Fin 3) F →* Matrix (Fin 4) (Fin 4) F where
  toFun A := k328r1p_emb2 A 1
  map_one' := k328r1p_emb2_one
  map_mul' A B := by rw [k328r1p_emb2_mul, mul_one]

private theorem k328r1p_embHom_injective (F : Type) [Field F] :
    Function.Injective (k328r1p_embHom F) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i.castSucc) j.castSucc
  simpa only [k328r1p_embHom, MonoidHom.coe_mk, OneHom.coe_mk, k328r1p_emb2_cc] using this

private def k328r1p_iota (F : Type) [Field F] : GL (Fin 3) F →* GL (Fin 4) F :=
  Units.map (k328r1p_embHom F)

private theorem k328r1p_iota_coe {F : Type} [Field F] (B : GL (Fin 3) F) :
    ((k328r1p_iota F B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      k328r1p_emb2 (B : Matrix (Fin 3) (Fin 3) F) 1 :=
  rfl

private theorem k328r1p_iota_injective (F : Type) [Field F] :
    Function.Injective (k328r1p_iota F) :=
  Units.map_injective (k328r1p_embHom_injective F)

private def k328r1p_Y (F : Type) [Field F] : Subgroup (GL (Fin 4) F) :=
  (StatedSL 3 F).map (k328r1p_iota F)

private theorem k328r1p_mem_Y_of_emb2 {F : Type} [Field F] (M : Matrix (Fin 3) (Fin 3) F)
    (hdet : M.det = 1) {g : GL (Fin 4) F}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = k328r1p_emb2 M 1) : g ∈ k328r1p_Y F := by
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hdet]; exact isUnit_one)
  refine Subgroup.mem_map.2 ⟨hu.unit, CFSG.Open.StatedAPI.mem_statedSL_of_det
    (by rw [IsUnit.unit_spec, hdet]), ?_⟩
  exact Units.ext (by rw [hg, k328r1p_iota_coe, IsUnit.unit_spec])

private theorem k328r1p_shape {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {g : Matrix (Fin 4) (Fin 4) F}
    (h : Matrix.diagonal ![ω, ω, ω, 1] * g = g * Matrix.diagonal ![ω, ω, ω, 1]) :
    g = k328r1p_emb2 (g.submatrix Fin.castSucc Fin.castSucc) (g (Fin.last 3) (Fin.last 3)) := by
  have hcs : ∀ j : Fin 3, (![ω, ω, ω, 1] : Fin 4 → F) (Fin.castSucc j) = ω := fun j => by
    fin_cases j <;> rfl
  have hl : (![ω, ω, ω, 1] : Fin 4 → F) (Fin.last 3) = 1 := rfl
  have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [k328r1p_emb2_ll]
  · rw [k328r1p_emb2_lc]
    have := congrFun (congrFun h (Fin.last 3)) j.castSucc
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hl, hcs] at this
    exact (mul_eq_zero.mp (by linear_combination -this :
      (ω - 1) * g (Fin.last 3) j.castSucc = 0)).resolve_left hne
  · rw [k328r1p_emb2_cl]
    have := congrFun (congrFun h i.castSucc) (Fin.last 3)
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hl, hcs] at this
    exact (mul_eq_zero.mp (by linear_combination this :
      (ω - 1) * g i.castSucc (Fin.last 3) = 0)).resolve_left hne
  · rw [k328r1p_emb2_cc]
    rfl

private theorem k328r1p_mem_C_comm {F : Type} [Field F] {z₀ g : GL (Fin 4) F}
    (hg : g ∈ StatedSL 4 F ⊓ Subgroup.centralizer {z₀}) :
    (z₀ : Matrix (Fin 4) (Fin 4) F) * g = g * z₀ := by
  have h : g * z₀ = z₀ * g := Subgroup.mem_centralizer_singleton_iff.mp hg.2
  exact (congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) h).symm

private theorem k328r1p_exists_emb2 {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {z₀ g : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (hg : g ∈ StatedSL 4 F ⊓ Subgroup.centralizer {z₀}) :
    ∃ (A : Matrix (Fin 3) (Fin 3) F) (d : F),
      (g : Matrix (Fin 4) (Fin 4) F) = k328r1p_emb2 A d := by
  have h := k328r1p_mem_C_comm hg
  rw [hz] at h
  exact ⟨_, _, k328r1p_shape hω1 h⟩

private theorem k328r1p_last_of_mul_inv {F : Type} [Field F] {A A' : Matrix (Fin 3) (Fin 3) F}
    {d d' : F} {a : GL (Fin 4) F} (hA : (a : Matrix (Fin 4) (Fin 4) F) = k328r1p_emb2 A d)
    (hA' : ((a⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = k328r1p_emb2 A' d') :
    d * d' = 1 := by
  have h : (a : Matrix (Fin 4) (Fin 4) F) * ((a⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hA, hA', k328r1p_emb2_mul] at h
  have := congrFun (congrFun h (Fin.last 3)) (Fin.last 3)
  rwa [k328r1p_emb2_ll, Matrix.one_apply_eq] at this

private theorem k328r1p_comm_mem_Y {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {z₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    {a b : GL (Fin 4) F} (ha : a ∈ StatedSL 4 F ⊓ Subgroup.centralizer {z₀})
    (hb : b ∈ StatedSL 4 F ⊓ Subgroup.centralizer {z₀}) : ⁅a, b⁆ ∈ k328r1p_Y F := by
  obtain ⟨A, d, hA⟩ := k328r1p_exists_emb2 hω1 hz ha
  obtain ⟨B, e, hB⟩ := k328r1p_exists_emb2 hω1 hz hb
  obtain ⟨A', d', hA'⟩ := k328r1p_exists_emb2 hω1 hz (Subgroup.inv_mem _ ha)
  obtain ⟨B', e', hB'⟩ := k328r1p_exists_emb2 hω1 hz (Subgroup.inv_mem _ hb)
  have h1 := k328r1p_last_of_mul_inv hA hA'
  have h2 := k328r1p_last_of_mul_inv hB hB'
  have hc : ((⁅a, b⁆ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      k328r1p_emb2 (A * B * A' * B') (d * e * d' * e') := by
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, hA, hB, hA', hB',
      k328r1p_emb2_mul, k328r1p_emb2_mul, k328r1p_emb2_mul]
  have hde : d * e * d' * e' = 1 := by
    calc d * e * d' * e' = (d * d') * (e * e') := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have hH : ⁅a, b⁆ ∈ StatedSL 4 F :=
    stdComp_le (StatedSL 4 F) z₀ (Subgroup.commutator_mem_commutator ha hb)
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL hH
  rw [hc, k328r1p_emb2_det, hde, mul_one] at hdet
  exact k328r1p_mem_Y_of_emb2 _ hdet (by rw [hc, hde])

private theorem k328r1p_stdComp_le_Y {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {z₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    stdComp (StatedSL 4 F) z₀ ≤ k328r1p_Y F :=
  Subgroup.commutator_le.2 fun _ ha _ hb => k328r1p_comm_mem_Y hω1 hz ha hb

private theorem k328r1p_diag_z {F : Type} [Field F] (ω : F) :
    (Matrix.diagonal ![ω, ω, ω, 1] : Matrix (Fin 4) (Fin 4) F) =
      k328r1p_emb2 (Matrix.scalar (Fin 3) ω) 1 := by
  have hcs : ∀ j : Fin 3, (![ω, ω, ω, 1] : Fin 4 → F) (Fin.castSucc j) = ω := fun j => by
    fin_cases j <;> rfl
  have hl : (![ω, ω, ω, 1] : Fin 4 → F) (Fin.last 3) = 1 := rfl
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [k328r1p_emb2_ll, Matrix.diagonal_apply_eq, hl]
  · rw [k328r1p_emb2_lc, Matrix.diagonal_apply_ne _ (Fin.castSucc_lt_last j).ne']
  · rw [k328r1p_emb2_cl, Matrix.diagonal_apply_ne _ (Fin.castSucc_lt_last i).ne]
  · simp only [k328r1p_emb2_cc, Matrix.diagonal_apply, Fin.castSucc_inj, Matrix.scalar_apply,
      hcs]

private theorem k328r1p_Y_le_C {F : Type} [Field F] {ω : F} {z₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    k328r1p_Y F ≤ StatedSL 4 F ⊓ Subgroup.centralizer {z₀} := by
  rintro _ ⟨B, hB, rfl⟩
  refine ⟨CFSG.Open.StatedAPI.mem_statedSL_of_det ?_, ?_⟩
  · rw [k328r1p_iota_coe, k328r1p_emb2_det, mul_one]
    exact CFSG.Open.StatedAPI.det_of_mem_statedSL hB
  · show k328r1p_iota F B ∈ Subgroup.centralizer {z₀}
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hz, k328r1p_diag_z, k328r1p_iota_coe, k328r1p_emb2_mul,
      k328r1p_emb2_mul, mul_one, (Matrix.scalar_commute ω (fun _ => Commute.all _ _) _).eq]

private theorem k328r1p_Y_le_stdComp {F : Type} [Field F] {ω : F} {z₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (hperf : commutator ↥(StatedSL 3 F) = ⊤) :
    k328r1p_Y F ≤ stdComp (StatedSL 4 F) z₀ := by
  have h1 := Subgroup.map_commutator (StatedSL 3 F) (StatedSL 3 F) (k328r1p_iota F)
  rw [commutator_self_of_perfect hperf] at h1
  exact h1.le.trans (Subgroup.commutator_mono (k328r1p_Y_le_C hz) (k328r1p_Y_le_C hz))

private theorem k328r1p_stdComp_eq_Y {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {z₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (hperf : commutator ↥(StatedSL 3 F) = ⊤) :
    stdComp (StatedSL 4 F) z₀ = k328r1p_Y F :=
  le_antisymm (k328r1p_stdComp_le_Y hω1 hz) (k328r1p_Y_le_stdComp hz hperf)

private theorem k328r1p_z_mem_Y {F : Type} [Field F] {ω : F} (hω3 : ω ^ 3 = 1)
    {z₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    z₀ ∈ k328r1p_Y F :=
  k328r1p_mem_Y_of_emb2 (Matrix.scalar (Fin 3) ω)
    (by simp [Matrix.scalar_apply, Matrix.det_diagonal, hω3]) (hz.trans (k328r1p_diag_z ω))

private theorem k328r1p_omega_facts {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  refine ⟨by linear_combination (ω - 1) * hω, ?_⟩
  rintro rfl
  exact one_ne_zero (by linear_combination hω - h2)

private theorem k328r1p_orderOf_diag {F : Type} [Field F] (g : GL (Fin 4) F) (v : Fin 4 → F)
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal v) (h3 : ∀ i, v i ^ 3 = 1)
    (i : Fin 4) (hi : v i ≠ 1) : orderOf g = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hg, Matrix.diagonal_pow, Units.val_one]
    have : v ^ 3 = 1 := funext fun j => by simpa using h3 j
    rw [this, Matrix.diagonal_one']
  · intro h1
    apply hi
    have := congrArg (fun m : GL (Fin 4) F => (m : Matrix (Fin 4) (Fin 4) F) i i) h1
    simpa [hg] using this

private theorem k328r1p_pos_basic {G : Type} [Group G] {H : Subgroup G} {z₀ : G} (hz₀ : z₀ ∈ H)
    (hzC : z₀ ∈ stdComp H z₀) (ho : orderOf z₀ = 3) :
    Nat.card (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) = 3 ∧
    Subgroup.zpowers (⟨z₀, hz₀⟩ : H) ≤ (stdComp H z₀).subgroupOf H ∧
    (stdComp H z₀).subgroupOf H ≤
      Subgroup.centralizer (Subgroup.zpowers (⟨z₀, hz₀⟩ : H) : Set H) ∧
    (((stdComp H z₀).subgroupOf H).subgroupOf
      (Subgroup.centralizer (Subgroup.zpowers (⟨z₀, hz₀⟩ : H) : Set H))).IsSubnormal := by
  have hle : ∀ x : H, x ∈ (stdComp H z₀).subgroupOf H →
      (x : G) ∈ H ⊓ Subgroup.centralizer {z₀} :=
    fun x hx => Subgroup.commutator_le_of_le le_rfl le_rfl hx
  have hXC : (stdComp H z₀).subgroupOf H ≤
      Subgroup.centralizer (Subgroup.zpowers (⟨z₀, hz₀⟩ : H) : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h1 : (x : G) * z₀ = z₀ * x := Subgroup.mem_centralizer_singleton_iff.1 (hle x hx).2
    have hcomm : Commute (⟨z₀, hz₀⟩ : H) x := Subtype.ext h1.symm
    exact (hcomm.zpow_left n).eq
  refine ⟨?_, Subgroup.zpowers_le.2 hzC, hXC, ?_⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    exact ho
  · refine Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 ?_)
    intro k hk
    have hk1 : (⟨z₀, hz₀⟩ : H) * k = k * ⟨z₀, hz₀⟩ :=
      Subgroup.mem_centralizer_iff.1 hk _ (Subgroup.mem_zpowers _)
    have hkC : (k : G) ∈ H ⊓ Subgroup.centralizer {z₀} :=
      ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hk1).symm⟩
    have hN := Subgroup.normalizer_commutator_ge_left (H ⊓ Subgroup.centralizer {z₀})
      (H ⊓ Subgroup.centralizer {z₀}) hkC
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro h
    exact hN (h : G)

private theorem k328r1p_quasi_fields {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {K : Type} [Group K] (X : Subgroup K) (he : Nonempty (↥(StatedSL 3 F) ≃* ↥X)) :
    CFSG.Open.IsQuasisimple ↥X ∧ Nat.card (Subgroup.center ↥X) = 3 ∧
      (LieModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
        LieModel (↥X ⧸ Subgroup.center ↥X) .PSU 3 2 3) := by
  obtain ⟨e⟩ := he
  have hq := CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) (by norm_num) F
  have hcard : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  refine ⟨isQuasisimple_of_mulEquiv' e ⟨hq.1.1, hq.2.1⟩, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.Open.StatedCenterThree.card_center_statedSL_three (by rw [hcard])
  · have hcen : Subgroup.center (StatedSL 3 F) =
        (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) := by
      rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 3 F,
        Subgroup.map_center_eq (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)]
    refine Or.inl (Or.inl ⟨by decide, ⟨by unfold StatedLieAdmissible; decide, ?_⟩⟩)
    refine ⟨F, inferInstance, inferInstance, by rw [hcard]; norm_num, ⟨?_⟩⟩
    exact (QuotientGroup.congr (Subgroup.center (StatedSL 3 F)) (Subgroup.center ↥X) e
      (Subgroup.map_center_eq e)).symm.trans (QuotientGroup.quotientMulEquivOfEq hcen)

theorem row1_pos (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    PosLeaf (StatedSL 4 F) z₀ := by
  have _ := ht
  intro hz₀
  obtain ⟨hω3, hω1⟩ := k328r1p_omega_facts hF hω
  have hq := CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) (by norm_num) F
  have hperf : commutator ↥(StatedSL 3 F) = ⊤ := hq.1.1
  have hstd := k328r1p_stdComp_eq_Y hω1 hz hperf
  have hzC : z₀ ∈ stdComp (StatedSL 4 F) z₀ := by
    rw [hstd]
    exact k328r1p_z_mem_Y hω3 hz
  have ho : orderOf z₀ = 3 :=
    k328r1p_orderOf_diag z₀ ![ω, ω, ω, 1] hz (fun i => by fin_cases i <;> simp [hω3]) 0
      (by simpa using hω1)
  obtain ⟨ha, hb, hc, hd⟩ := k328r1p_pos_basic hz₀ hzC ho
  have he : Nonempty (↥(StatedSL 3 F) ≃*
      ↥((stdComp (StatedSL 4 F) z₀).subgroupOf (StatedSL 4 F))) :=
    ⟨((Subgroup.equivMapOfInjective (StatedSL 3 F) (k328r1p_iota F)
      (k328r1p_iota_injective F)).trans (MulEquiv.subgroupCongr hstd.symm)).trans
      (Subgroup.subgroupOfEquivOfLe (stdComp_le _ _)).symm⟩
  obtain ⟨he1, he2, he3⟩ := k328r1p_quasi_fields hF _ he
  exact ⟨ha, hb, hc, hd, he1, he2, he3⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

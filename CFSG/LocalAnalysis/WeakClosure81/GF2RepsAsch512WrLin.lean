module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrAbs
public import CFSG.GH74.KGroups.L3EpsLinSyl
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.SL3Closure

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80Wr

open Subgroup Matrix CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Cycle

variable {F : Type} [Field F]

@[expose] def cycSL : SL(3, F) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem coe_cycSL :
    ((cycSL : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

theorem cycSL_pow_three : (cycSL : SL(3, F)) ^ 3 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [pow_succ, pow_zero, one_mul, Matrix.SpecialLinearGroup.coe_mul, coe_cycSL,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem cycSL_mul_torus (x y : Fˣ) :
    (cycSL : SL(3, F)) * torus (x, y) = torus ((x * y)⁻¹, x) * cycSL := by
  have h : ((x * y)⁻¹ * x)⁻¹ = y := by group
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_cycSL, coe_torus, h]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem cycSL_mul_transvection_zero_one (t : F) :
    (cycSL : SL(3, F)) * SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1) (by decide) t =
      SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide) t * cycSL := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_cycSL, CFSG.LinearGroups.coe_transvection]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem cycSL_mul_transvection_one_zero (t : F) :
    (cycSL : SL(3, F)) * SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 0) (by decide) t =
      SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide) t * cycSL := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_cycSL, CFSG.LinearGroups.coe_transvection]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem cycSL_mul_transvection_one_two (t : F) :
    (cycSL : SL(3, F)) * SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide) t =
      SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 0) (by decide) t * cycSL := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_cycSL, CFSG.LinearGroups.coe_transvection]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem cycSL_mul_transvection_two_one (t : F) :
    (cycSL : SL(3, F)) * SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide) t =
      SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 2) (by decide) t * cycSL := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_cycSL, CFSG.LinearGroups.coe_transvection]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem proj_cycSL_ne_one : proj 3 F cycSL ≠ 1 := by
  intro h
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 h
  have h10 := congrFun (congrFun hc 1) 0
  simp [coe_cycSL, Matrix.scalar_apply] at h10

theorem proj_cycSL_pow_three : proj 3 F cycSL ^ 3 = 1 := by
  rw [← map_pow, cycSL_pow_three, map_one]

end Cycle

section Model

variable {F : Type} [Field F]

@[expose] def Dexp (r : ℕ) : Subgroup (projectiveSL 3 F) :=
  ((thetaMu r : mu r F × mu r F →* projectiveSL 3 F).comp
    ((MonoidHom.id _).prod (MonoidHom.id _))).range

theorem theta_mem_Dexp (r : ℕ) (x : mu r F) : thetaMu r (x, x) ∈ Dexp (F := F) r := ⟨x, rfl⟩

theorem card_Dexp_le [Finite F] (r : ℕ) : Nat.card (Dexp (F := F) r) ≤ Nat.card (mu r F) :=
  Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)

theorem inf_centralizer_Pexp_le_Dexp {r : ℕ} (hr3 : ¬ 3 ∣ r) {m : mu r F} (hm : m ≠ 1) :
    Pexp (F := F) r ⊓ centralizer (Pexp (F := F) r : Set (projectiveSL 3 F)) ≤ Dexp r := by
  intro z hz
  obtain ⟨⟨j, hj, hzj⟩, hzC⟩ := mem_inf.mp hz
  obtain ⟨⟨a, b⟩, rfl⟩ := hj
  rcases hzj with rfl | rfl
  ·
    have hw := mem_centralizer_iff.mp hzC tauBar (tauBar_mem_Pexp r)
    rw [tauBar_mul_theta] at hw
    have hab := thetaMu_injective hr3 (mul_right_cancel hw)
    obtain rfl : a = b := congrArg Prod.snd hab
    exact theta_mem_Dexp r a
  ·
    exfalso
    have hw := mem_centralizer_iff.mp hzC (thetaMu r (m, 1)) (Jexp_le_Pexp r ⟨(m, 1), rfl⟩)
    have h : thetaMu r ((m, 1) * (a, b)) = thetaMu r ((a, b) * (1, m)) := by
      rw [map_mul, map_mul]
      calc thetaMu r (m, 1) * thetaMu r (a, b)
          = thetaMu r (m, 1) * (thetaMu r (a, b) * tauBar) * tauBar⁻¹ := by group
        _ = thetaMu r (a, b) * tauBar * thetaMu r (m, 1) * tauBar⁻¹ := by rw [hw]
        _ = thetaMu r (a, b) * (tauBar * thetaMu r (m, 1) * tauBar⁻¹) := by group
        _ = thetaMu r (a, b) * thetaMu r (1, m) := by rw [tauBar_conj_theta]
    have h1 := congrArg Prod.fst (thetaMu_injective hr3 h)
    simp only [Prod.fst_mul, mul_one] at h1
    exact hm (mul_eq_right.mp h1)

theorem proj_transvection_mem_centralizer_Dexp (r : ℕ) {a b : Fin 3} (hab : a ≠ b)
    (hab' : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) (t : F) :
    proj 3 F (SpecialLinearGroup.transvection hab t) ∈
      centralizer (Dexp (F := F) r : Set (projectiveSL 3 F)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  show thetaMu r (x, x) * _ = _ * thetaMu r (x, x)
  change proj 3 F (torus ((x : Fˣ), (x : Fˣ))) * _ = _ * proj 3 F (torus ((x : Fˣ), (x : Fˣ)))
  rw [← map_mul, ← map_mul]
  congr 1
  have hX : ∀ i j : Fin 3, i ≠ j →
      ((torus ((x : Fˣ), (x : Fˣ)) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
    intro i j hij
    rw [coe_torus, Matrix.diagonal_apply_ne _ hij]
  have hd : ((torus ((x : Fˣ), (x : Fˣ)) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) a a =
      ((torus ((x : Fˣ), (x : Fˣ)) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) b b := by
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [coe_torus]
  exact (CFSG.HardMathSupport.Malle.Coordinator.CoverThree.transvection_mul_comm_of_diag
    hX hab hd t).symm

theorem proj_cycSL_conj_theta (r : ℕ) (x y : mu r F) :
    proj 3 F cycSL * thetaMu r (x, y) * (proj 3 F cycSL)⁻¹ = thetaMu r ((x * y)⁻¹, x) := by
  have h : (cycSL : SL(3, F)) * torusMu r (x, y) = torusMu r ((x * y)⁻¹, x) * cycSL :=
    cycSL_mul_torus (x : Fˣ) (y : Fˣ)
  have h' : proj 3 F cycSL * thetaMu r (x, y) = thetaMu r ((x * y)⁻¹, x) * proj 3 F cycSL := by
    show proj 3 F cycSL * proj 3 F (torusMu r (x, y)) =
      proj 3 F (torusMu r ((x * y)⁻¹, x)) * proj 3 F cycSL
    rw [← map_mul, ← map_mul, h]
  rw [h', mul_assoc, mul_inv_cancel, mul_one]

theorem proj_cycSL_conj_mem_Jexp (r : ℕ) {j : projectiveSL 3 F} (hj : j ∈ Jexp (F := F) r) :
    proj 3 F cycSL * j * (proj 3 F cycSL)⁻¹ ∈ Jexp r := by
  obtain ⟨⟨x, y⟩, rfl⟩ := hj
  rw [proj_cycSL_conj_theta]
  exact ⟨((x * y)⁻¹, x), rfl⟩

theorem proj_cycSL_mem_normalizer_Jexp (r : ℕ) :
    proj 3 F cycSL ∈ normalizer (Jexp (F := F) r : Set (projectiveSL 3 F)) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨proj_cycSL_conj_mem_Jexp r, fun hk => ?_⟩
  have h2 := proj_cycSL_conj_mem_Jexp r (proj_cycSL_conj_mem_Jexp r hk)
  have h3 := proj_cycSL_pow_three (F := F)
  set c := proj 3 F (cycSL : SL(3, F))
  have hc3 : c * c * c = 1 := by rw [← h3, pow_three, mul_assoc]
  have : h = c * (c * (c * h * c⁻¹) * c⁻¹) * c⁻¹ := by
    calc h = (c * c * c) * h * (c * c * c)⁻¹ := by rw [hc3, one_mul, inv_one, mul_one]
      _ = c * (c * (c * h * c⁻¹) * c⁻¹) * c⁻¹ := by simp only [_root_.mul_inv_rev, mul_assoc]
  rw [this]
  exact h2

theorem normalizer_sup_normalizer_Pexp_eq_top {r : ℕ} (hr3 : ¬ 3 ∣ r) {m : mu r F}
    (hm : m ≠ 1) :
    normalizer ((Pexp (F := F) r ⊓ centralizer (Pexp (F := F) r : Set (projectiveSL 3 F)) :
        Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ⊔
      normalizer (Jexp (F := F) r : Set (projectiveSL 3 F)) = ⊤ := by
  set H := normalizer ((Pexp (F := F) r ⊓ centralizer (Pexp (F := F) r :
    Set (projectiveSL 3 F)) : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ⊔
      normalizer (Jexp (F := F) r : Set (projectiveSL 3 F)) with hH
  have hc : proj 3 F cycSL ∈ H := mem_sup_right (proj_cycSL_mem_normalizer_Jexp r)
  have hcent : ∀ {a b : Fin 3} (hab : a ≠ b), ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) → ∀ t : F,
      proj 3 F (SpecialLinearGroup.transvection hab t) ∈ H := by
    intro a b hab hab' t
    refine mem_sup_left (centralizer_le_normalizer _ ?_)
    exact centralizer_le (inf_centralizer_Pexp_le_Dexp hr3 hm)
      (proj_transvection_mem_centralizer_Dexp r hab hab' t)
  have hconj : ∀ {X Y : SL(3, F)}, cycSL * X = Y * cycSL → proj 3 F X ∈ H → proj 3 F Y ∈ H := by
    intro X Y hXY hX
    have : proj 3 F Y = proj 3 F cycSL * proj 3 F X * (proj 3 F cycSL)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul, hXY, mul_inv_cancel_right]
    rw [this]
    exact mul_mem (mul_mem hc hX) (inv_mem hc)
  have h01 : ∀ t : F, proj 3 F (SpecialLinearGroup.transvection
      (i := (0 : Fin 3)) (j := 1) (by decide) t) ∈ H := fun t => hcent _ (Or.inl ⟨rfl, rfl⟩) t
  have h10 : ∀ t : F, proj 3 F (SpecialLinearGroup.transvection
      (i := (1 : Fin 3)) (j := 0) (by decide) t) ∈ H := fun t => hcent _ (Or.inr ⟨rfl, rfl⟩) t
  have h12 : ∀ t : F, proj 3 F (SpecialLinearGroup.transvection
      (i := (1 : Fin 3)) (j := 2) (by decide) t) ∈ H :=
    fun t => hconj (cycSL_mul_transvection_zero_one t) (h01 t)
  have h21 : ∀ t : F, proj 3 F (SpecialLinearGroup.transvection
      (i := (2 : Fin 3)) (j := 1) (by decide) t) ∈ H :=
    fun t => hconj (cycSL_mul_transvection_one_zero t) (h10 t)
  have h20 : ∀ t : F, proj 3 F (SpecialLinearGroup.transvection
      (i := (2 : Fin 3)) (j := 0) (by decide) t) ∈ H :=
    fun t => hconj (cycSL_mul_transvection_one_two t) (h12 t)
  have h02 : ∀ t : F, proj 3 F (SpecialLinearGroup.transvection
      (i := (0 : Fin 3)) (j := 2) (by decide) t) ∈ H :=
    fun t => hconj (cycSL_mul_transvection_two_one t) (h21 t)
  have htop : H.comap (proj 3 F) = ⊤ := by
    refine CFSG.HardMathSupport.Malle.Coordinator.CoverThree.eq_top_of_transvections _ ?_
    intro a b hab t
    rw [mem_comap]
    fin_cases a <;> fin_cases b <;> (try exact absurd rfl hab)
    · exact h01 t
    · exact h02 t
    · exact h10 t
    · exact h12 t
    · exact h20 t
    · exact h21 t
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := proj_surjective 3 F y
  have hx : x ∈ H.comap (proj 3 F) := htop ▸ mem_top x
  exact hx

theorem proj_cycSL_not_mem_Pexp {r : ℕ} (h2 : IsPGroup 2 (Pexp (F := F) r)) :
    proj 3 F cycSL ∉ Pexp (F := F) r := by
  intro hc
  obtain ⟨k, hk⟩ := h2 ⟨_, hc⟩
  have hk' : proj 3 F cycSL ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hg := pow_gcd_eq_one.2 ⟨proj_cycSL_pow_three (F := F), hk'⟩
  rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one, pow_one] at hg
  exact proj_cycSL_ne_one hg

theorem wrModel_projectiveSL [Finite F] (hF2 : Nat.card F % 2 = 1)
    (hq4 : Nat.card F % 4 = 1) : WrModel (projectiveSL 3 F) := by
  set r := ordProj[2] (Nat.card F - 1) with hr
  have hrdvd : r ∣ Nat.card F - 1 := hr ▸ Nat.ordProj_dvd _ 2
  have hr3 : ¬ 3 ∣ r := by
    intro h3
    rw [hr] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hq1 : Nat.card F - 1 ≠ 0 := by
    have := Finite.one_lt_card (α := F)
    omega
  have hr4 : 4 ≤ r := by
    have h4 : 2 ^ 2 ∣ Nat.card F - 1 := by omega
    rw [Nat.prime_two.pow_dvd_iff_dvd_ordProj hq1] at h4
    exact Nat.le_of_dvd (Nat.ordProj_pos _ 2) h4
  have hmu : Nat.card (mu r F) = r := card_mu hrdvd
  have : Nontrivial (mu r F) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨m, hm⟩ := exists_ne (1 : mu r F)
  have hsyl := Pexp_sylow (F := F) hF2 hq4 hr
  have hJ : Nat.card (Jexp (F := F) r) = r ^ 2 := card_Jexp hr3 hmu
  have hP : Nat.card (Pexp (F := F) r) = 2 * r ^ 2 := by rw [card_Pexp, hJ]
  let P₀ : Sylow 2 (projectiveSL 3 F) :=
    { toSubgroup := Pexp r
      isPGroup' := hsyl.1
      is_maximal' := fun {Q} hQ hle => le_antisymm (hsyl.2 Q hQ hle) hle }
  refine ⟨P₀, Jexp r, Jexp_le_Pexp r, ⟨⟨fun a b => Subtype.ext (Jexp_comm r _ a.2 _ b.2)⟩⟩,
    ?_, ?_, normalizer_sup_normalizer_Pexp_eq_top hr3 hm, ?_⟩
  ·
    have h := relIndex_mul_card (H := Jexp (F := F) r) (K := Pexp r)
    rw [inf_of_le_left (Jexp_le_Pexp r), hJ, hP] at h
    have hpos : 0 < r ^ 2 := by positivity
    show (Jexp (F := F) r).relIndex (Pexp r) = 2
    exact Nat.eq_of_mul_eq_mul_right hpos h
  ·
    show 4 * Nat.card ↥(Pexp (F := F) r ⊓ centralizer (Pexp (F := F) r : Set _)) <
      Nat.card (Pexp (F := F) r)
    have hZ := card_le_of_le (inf_centralizer_Pexp_le_Dexp hr3 hm)
    have hD := card_Dexp_le (F := F) r
    rw [hP]
    nlinarith
  ·
    intro htop
    exact proj_cycSL_not_mem_Pexp hsyl.1 (show proj 3 F cycSL ∈ Pexp (F := F) r from
      (htop ▸ mem_top _ : proj 3 F cycSL ∈ (P₀ : Subgroup (projectiveSL 3 F))))

end Model

end CFSG.LocalAnalysis.WeakClosure81.Asch80Wr

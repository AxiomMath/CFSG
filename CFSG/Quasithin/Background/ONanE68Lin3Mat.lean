module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKL3Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.Quasithin.E6.E68Proof.Lin3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.QuasithinUnique.Lin2.L3Core CFSG.QuasithinUnique.Setup.X7a

variable {F : Type} [Field F]

theorem comm_mem_unitriangular {n : ℕ} {b₁ b₂ : SpecialLinearGroup (Fin n) F}
    (h₁ : b₁ ∈ upperTriangular n F) (h₂ : b₂ ∈ upperTriangular n F) :
    b₁ * b₂ * b₁⁻¹ * b₂⁻¹ ∈ unitriangular n F := by
  set x : upperTriangular n F := ⟨b₁, h₁⟩
  set y : upperTriangular n F := ⟨b₂, h₂⟩
  have h : x * y * x⁻¹ * y⁻¹ ∈ (diagHomLin n F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (diagHomLin n F x) (diagHomLin n F y)]
    group
  rw [ker_diagHomLin, Subgroup.mem_subgroupOf] at h
  exact h

theorem proj_mul_comm_iff {u M : SpecialLinearGroup (Fin 3) F} (hu : u ∈ unitriangular 3 F)
    (hM : M ∈ upperTriangular 3 F) :
    proj 3 F u * proj 3 F M = proj 3 F M * proj 3 F u ↔ u * M = M * u := by
  constructor
  · intro h
    have h1 : proj 3 F (M * u * M⁻¹) = proj 3 F u := by
      rw [map_mul, map_mul, map_inv, ← h, mul_inv_cancel_right]
    have h2 := proj_injOn_unitriangular 3 (LinearFlag.conj_mem_unitriangular hM hu) hu h1
    calc u * M = M * u * M⁻¹ * M := by rw [h2]
      _ = M * u := by group
  · intro h
    rw [← map_mul, ← map_mul, h]

theorem comm_entries {M : SpecialLinearGroup (Fin 3) F} (hM : M ∈ upperTriangular 3 F) {x y z : F}
    (h : (wMat z * xMat x * yMat y) * M = M * (wMat z * xMat x * yMat y)) :
    ((M : Matrix (Fin 3) (Fin 3) F) 0 0 - (M : Matrix (Fin 3) (Fin 3) F) 1 1) * x = 0 ∧
    ((M : Matrix (Fin 3) (Fin 3) F) 1 1 - (M : Matrix (Fin 3) (Fin 3) F) 2 2) * y = 0 ∧
    ((M : Matrix (Fin 3) (Fin 3) F) 0 0 - (M : Matrix (Fin 3) (Fin 3) F) 2 2) * (z + x * y) +
      (M : Matrix (Fin 3) (Fin 3) F) 0 1 * y - x * (M : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
  have hm : ((wMat z * xMat x * yMat y : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F) =
      (M : Matrix (Fin 3) (Fin 3) F) *
        ((wMat z * xMat x * yMat y : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun X : SpecialLinearGroup (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F)) h
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
  rw [coe_hei] at hm
  have h10 : (M : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := hM 1 0 (by decide)
  have h20 : (M : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := hM 2 0 (by decide)
  have h21 : (M : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := hM 2 1 (by decide)
  have e01 := congrFun (congrFun hm 0) 1
  have e12 := congrFun (congrFun hm 1) 2
  have e02 := congrFun (congrFun hm 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h21] at e01 e12 e02
  exact ⟨by linear_combination (-1 : F) * e01, by linear_combination (-1 : F) * e12,
    by linear_combination (-1 : F) * e02⟩

theorem proj_mem_projUnitriangular_of_diag {M : SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ upperTriangular 3 F)
    (h01 : (M : Matrix (Fin 3) (Fin 3) F) 0 0 = (M : Matrix (Fin 3) (Fin 3) F) 1 1)
    (h12 : (M : Matrix (Fin 3) (Fin 3) F) 1 1 = (M : Matrix (Fin 3) (Fin 3) F) 2 2) :
    proj 3 F M ∈ projUnitriangular 3 F := by
  have ha : (M : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := diag_ne_zero_of_upperTriangular hM 0
  have h10 : (M : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := hM 1 0 (by decide)
  have h20 : (M : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := hM 2 0 (by decide)
  have h21 : (M : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := hM 2 1 (by decide)
  have e1 : (M : Matrix (Fin 3) (Fin 3) F) 1 1 = (M : Matrix (Fin 3) (Fin 3) F) 0 0 := h01.symm
  have e2 : (M : Matrix (Fin 3) (Fin 3) F) 2 2 = (M : Matrix (Fin 3) (Fin 3) F) 0 0 :=
    h12.symm.trans h01.symm
  have hdet : (M : Matrix (Fin 3) (Fin 3) F) 0 0 ^ 3 = 1 := by
    have := M.2
    rw [Matrix.det_fin_three, h10, h20, h21, e1, e2] at this
    linear_combination this
  have hω : (Units.mk0 ((M : Matrix (Fin 3) (Fin 3) F) 0 0)⁻¹ (inv_ne_zero ha)) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, inv_pow, hdet, inv_one, Units.val_one]
  set ω : Fˣ := Units.mk0 ((M : Matrix (Fin 3) (Fin 3) F) 0 0)⁻¹ (inv_ne_zero ha) with hωdef
  have hentry : ∀ i j : Fin 3, ((scalarElement ω hω * M : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) i j = ((M : Matrix (Fin 3) (Fin 3) F) 0 0)⁻¹ *
        (M : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, Matrix.scalar_apply,
      Matrix.diagonal_mul]
    rfl
  have hdiag : ∀ i : Fin 3, (M : Matrix (Fin 3) (Fin 3) F) i i =
      (M : Matrix (Fin 3) (Fin 3) F) 0 0 := by
    intro i
    fin_cases i <;> simp [e1, e2]
  have hU : scalarElement ω hω * M ∈ unitriangular 3 F := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hentry, hM i j hij, mul_zero]
    · rw [hentry, hdiag i]
      exact inv_mul_cancel₀ ha
  have hp : proj 3 F (scalarElement ω hω * M) = proj 3 F M := by
    rw [map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars ω hω), one_mul]
  rw [← hp]
  exact Subgroup.mem_map_of_mem _ hU

theorem hei_comm_entries {M : SpecialLinearGroup (Fin 3) F} (hM : M ∈ upperTriangular 3 F)
    {x y z : F} (h : proj 3 F M * hei x y z = hei x y z * proj 3 F M) :
    ((M : Matrix (Fin 3) (Fin 3) F) 0 0 - (M : Matrix (Fin 3) (Fin 3) F) 1 1) * x = 0 ∧
    ((M : Matrix (Fin 3) (Fin 3) F) 1 1 - (M : Matrix (Fin 3) (Fin 3) F) 2 2) * y = 0 ∧
    ((M : Matrix (Fin 3) (Fin 3) F) 0 0 - (M : Matrix (Fin 3) (Fin 3) F) 2 2) * (z + x * y) +
      (M : Matrix (Fin 3) (Fin 3) F) 0 1 * y - x * (M : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
  rw [hei_eq_proj] at h
  exact comm_entries hM ((proj_mul_comm_iff (mem_unitriangular_hei x y z) hM).mp h.symm)

theorem card_solutions_le [Finite F] (a b d p s : F) (hns : ¬ (a = b ∧ b = d)) :
    Nat.card {t : F × F × F // (a - b) * t.1 = 0 ∧ (b - d) * t.2.1 = 0 ∧
      (a - d) * (t.2.2 + t.1 * t.2.1) + p * t.2.1 - t.1 * s = 0} ≤ Nat.card F := by
  rcases eq_or_ne a b with hab | hab
  · have hbd : b ≠ d := fun h => hns ⟨hab, h⟩
    have had : a - d ≠ 0 := sub_ne_zero.mpr (hab ▸ hbd)
    refine Nat.card_le_card_of_injective (fun t => t.1.1) fun t t' h => ?_
    have hy : t.1.2.1 = 0 :=
      (mul_eq_zero.mp t.2.2.1).resolve_left (sub_ne_zero.mpr hbd)
    have hy' : t'.1.2.1 = 0 :=
      (mul_eq_zero.mp t'.2.2.1).resolve_left (sub_ne_zero.mpr hbd)
    have h1 := t.2.2.2
    have h2 := t'.2.2.2
    rw [hy] at h1
    rw [hy'] at h2
    have hz : t.1.2.2 = t'.1.2.2 := by
      have : (a - d) * (t.1.2.2 - t'.1.2.2) = 0 := by
        have h' : t.1.1 = t'.1.1 := h
        rw [h'] at h1
        linear_combination h1 - h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left had)
    exact Subtype.ext (Prod.ext h (Prod.ext (hy.trans hy'.symm) hz))
  · rcases eq_or_ne b d with hbd | hbd
    · have had : a - d ≠ 0 := sub_ne_zero.mpr (hbd ▸ hab)
      refine Nat.card_le_card_of_injective (fun t => t.1.2.1) fun t t' h => ?_
      have hx : t.1.1 = 0 := (mul_eq_zero.mp t.2.1).resolve_left (sub_ne_zero.mpr hab)
      have hx' : t'.1.1 = 0 := (mul_eq_zero.mp t'.2.1).resolve_left (sub_ne_zero.mpr hab)
      have h1 := t.2.2.2
      have h2 := t'.2.2.2
      rw [hx] at h1
      rw [hx'] at h2
      have hz : t.1.2.2 = t'.1.2.2 := by
        have : (a - d) * (t.1.2.2 - t'.1.2.2) = 0 := by
          have h' : t.1.2.1 = t'.1.2.1 := h
          rw [h'] at h1
          linear_combination h1 - h2
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left had)
      exact Subtype.ext (Prod.ext (hx.trans hx'.symm) (Prod.ext h hz))
    · refine Nat.card_le_card_of_injective (fun t => t.1.2.2) fun t t' h => ?_
      have hx : t.1.1 = 0 := (mul_eq_zero.mp t.2.1).resolve_left (sub_ne_zero.mpr hab)
      have hx' : t'.1.1 = 0 := (mul_eq_zero.mp t'.2.1).resolve_left (sub_ne_zero.mpr hab)
      have hy : t.1.2.1 = 0 := (mul_eq_zero.mp t.2.2.1).resolve_left (sub_ne_zero.mpr hbd)
      have hy' : t'.1.2.1 = 0 :=
        (mul_eq_zero.mp t'.2.2.1).resolve_left (sub_ne_zero.mpr hbd)
      exact Subtype.ext (Prod.ext (hx.trans hx'.symm) (Prod.ext (hy.trans hy'.symm) h))

theorem card_inf_centralizer_le [Finite F] [CharP F 2] {M : SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ upperTriangular 3 F)
    (hns : ¬ ((M : Matrix (Fin 3) (Fin 3) F) 0 0 = (M : Matrix (Fin 3) (Fin 3) F) 1 1 ∧
      (M : Matrix (Fin 3) (Fin 3) F) 1 1 = (M : Matrix (Fin 3) (Fin 3) F) 2 2)) :
    Nat.card ↥(Subgroup.centralizer ({proj 3 F M} : Set (projectiveSL 3 F)) ⊓
      projUnitriangular 3 F) ≤ Nat.card F := by
  set C := Subgroup.centralizer ({proj 3 F M} : Set (projectiveSL 3 F)) ⊓
    projUnitriangular 3 F with hC
  let T : Type := {t : F × F × F // hei t.1 t.2.1 t.2.2 ∈ C}
  have hsurj : Function.Surjective
      (fun t : T => (⟨hei t.1.1 t.1.2.1 t.1.2.2, t.2⟩ : C)) := by
    rintro ⟨g, hgC⟩
    obtain ⟨x, y, z, rfl⟩ := exists_hei hgC.2
    exact ⟨⟨(x, y, z), hgC⟩, rfl⟩
  let E : Type := {t : F × F × F //
    ((M : Matrix (Fin 3) (Fin 3) F) 0 0 - (M : Matrix (Fin 3) (Fin 3) F) 1 1) * t.1 = 0 ∧
    ((M : Matrix (Fin 3) (Fin 3) F) 1 1 - (M : Matrix (Fin 3) (Fin 3) F) 2 2) * t.2.1 = 0 ∧
    ((M : Matrix (Fin 3) (Fin 3) F) 0 0 - (M : Matrix (Fin 3) (Fin 3) F) 2 2) *
      (t.2.2 + t.1 * t.2.1) + (M : Matrix (Fin 3) (Fin 3) F) 0 1 * t.2.1 -
      t.1 * (M : Matrix (Fin 3) (Fin 3) F) 1 2 = 0}
  have hTE : Function.Injective (fun t : T => (⟨t.1, hei_comm_entries hM
      (Subgroup.mem_centralizer_iff.mp t.2.1 (proj 3 F M) rfl)⟩ : E)) := by
    intro t t' h
    have h' := congrArg (fun e : E => e.1) h
    exact Subtype.ext h'
  calc Nat.card C ≤ Nat.card T := Nat.card_le_card_of_surjective _ hsurj
    _ ≤ Nat.card E := Nat.card_le_card_of_injective _ hTE
    _ ≤ Nat.card F := card_solutions_le _ _ _ _ _ hns

theorem isPGroup_projUnitriangular [Finite F] [CharP F 2] :
    IsPGroup 2 (projUnitriangular 3 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  rw [← hP]
  exact P.isPGroup'

theorem four_lt_relIndex [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) {c : projectiveSL 3 F}
    (hc : c ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F))) (h3 : orderOf c = 3) :
    4 < (projUnitriangular 3 F ⊓ Subgroup.centralizer ({c} : Set (projectiveSL 3 F))).relIndex
      (projUnitriangular 3 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnitriangular 2] at hc
  obtain ⟨M, hM, rfl⟩ := hc
  have hns : ¬ ((M : Matrix (Fin 3) (Fin 3) F) 0 0 = (M : Matrix (Fin 3) (Fin 3) F) 1 1 ∧
      (M : Matrix (Fin 3) (Fin 3) F) 1 1 = (M : Matrix (Fin 3) (Fin 3) F) 2 2) := by
    rintro ⟨h01, h12⟩
    have hU := proj_mem_projUnitriangular_of_diag hM h01 h12
    obtain ⟨k, hk⟩ := isPGroup_projUnitriangular (F := F) ⟨_, hU⟩
    have hk' : proj 3 F M ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hd : orderOf (proj 3 F M) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [h3] at hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  have hcard := card_inf_centralizer_le hM hns
  have hU3 : Nat.card (projUnitriangular 3 F) = Nat.card F ^ 3 := by
    rw [card_projUnitriangular]
  have hmul := Subgroup.relIndex_mul_card
    (H := Subgroup.centralizer ({proj 3 F M} : Set (projectiveSL 3 F)))
    (K := projUnitriangular 3 F)
  rw [Subgroup.inf_relIndex_left]
  rw [hU3] at hmul
  have hkpos : 0 < Nat.card ↥(Subgroup.centralizer ({proj 3 F M} : Set (projectiveSL 3 F)) ⊓
      projUnitriangular 3 F) := Nat.card_pos
  generalize (Subgroup.centralizer ({proj 3 F M} : Set (projectiveSL 3 F))).relIndex
    (projUnitriangular 3 F) = r at hmul ⊢
  generalize Nat.card ↥(Subgroup.centralizer ({proj 3 F M} : Set (projectiveSL 3 F)) ⊓
      projUnitriangular 3 F) = k at hmul hcard hkpos
  generalize Nat.card F = q at hq hmul hcard
  by_contra hle
  push Not at hle
  have h1 : q ^ 3 ≤ 4 * q := by
    calc q ^ 3 = r * k := hmul.symm
      _ ≤ 4 * k := Nat.mul_le_mul_right k hle
      _ ≤ 4 * q := Nat.mul_le_mul_left 4 hcard
  nlinarith [Nat.mul_le_mul hq hq]

theorem mem_omegaCenter_iff [CharP F 2] {z : projectiveSL 3 F} :
    (z ∈ projUnitriangular 3 F ∧ (∀ y ∈ projUnitriangular 3 F, z * y = y * z) ∧ z * z = 1) ↔
      ∃ c : F, z = hei 0 0 c := by
  constructor
  · rintro ⟨hz, hc, -⟩
    obtain ⟨x, y, c, rfl⟩ := exists_hei hz
    have h1 := hc (hei 0 1 0) (hei_mem 0 1 0)
    have h2 := hc (hei 1 0 0) (hei_mem 1 0 0)
    rw [hei_mul, hei_mul] at h1 h2
    have e1 := (hei_inj h1).2.2
    have e2 := (hei_inj h2).2.2
    have hx : x = 0 := by linear_combination (-1 : F) * e1
    have hy : y = 0 := by linear_combination e2
    exact ⟨c, by rw [hx, hy]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨hei_mem 0 0 c, fun y hy => ?_, ?_⟩
    · obtain ⟨a, b, c', rfl⟩ := exists_hei hy
      rw [hei_mul, hei_mul]
      exact hei_congr (by simp [add_comm]) (by simp [add_comm]) (by ring)
    · rw [hei_mul, ← hei_zero]
      exact hei_congr (by simp) (by simp) (by simp [CharTwo.add_self_eq_zero])

theorem exists_singer [Finite F] [CharP F 2] :
    ∃ x ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)),
      ∀ c₁ : F, c₁ ≠ 0 → ∀ c₂ : F, c₂ ≠ 0 →
        ∃ j : ℕ, x ^ j * hei 0 0 c₁ * (x ^ j)⁻¹ = hei 0 0 c₂ := by
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := Fˣ)
  set s : Fin 3 → F := ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1] with hs
  have hprod : s 0 * s 1 * s 2 = 1 := by simp [hs]
  have hact : ∀ (j : ℕ) (c : F), (proj 3 F (diagSL s hprod)) ^ j * hei 0 0 c *
      ((proj 3 F (diagSL s hprod)) ^ j)⁻¹ = hei 0 0 ((ω : F) ^ j * c) := by
    intro j c
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (proj 3 F (diagSL s hprod)) ^ (j + 1) * hei 0 0 c *
          ((proj 3 F (diagSL s hprod)) ^ (j + 1))⁻¹ = proj 3 F (diagSL s hprod) *
          ((proj 3 F (diagSL s hprod)) ^ j * hei 0 0 c * ((proj 3 F (diagSL s hprod)) ^ j)⁻¹) *
          (proj 3 F (diagSL s hprod))⁻¹ := by
        rw [pow_succ', _root_.mul_inv_rev]
        simp only [mul_assoc]
      rw [e, ih, torus_conj_hei]
      refine hei_congr (by simp) (by simp) ?_
      simp only [hs]
      simp
      ring
  refine ⟨proj 3 F (diagSL s hprod), torus_mem_normalizer s hprod, fun c₁ hc₁ c₂ hc₂ => ?_⟩
  have hu : Units.mk0 (c₂ / c₁) (div_ne_zero hc₂ hc₁) ∈ Submonoid.powers ω :=
    mem_powers_iff_mem_zpowers.mpr (hω _)
  obtain ⟨j, hj⟩ := hu
  have hj : ω ^ j = Units.mk0 (c₂ / c₁) (div_ne_zero hc₂ hc₁) := hj
  refine ⟨j, ?_⟩
  rw [hact]
  have hj' : (ω : F) ^ j = c₂ / c₁ := by
    rw [← Units.val_pow_eq_pow_val, hj, Units.val_mk0]
  rw [hj', div_mul_cancel₀ _ hc₁]

theorem entries_comm_wMat {c : F} (hc : c ≠ 0) {A : SpecialLinearGroup (Fin 3) F}
    (h : A * wMat c = wMat c * A) :
    (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have hm : (A : Matrix (Fin 3) (Fin 3) F) * wM c = wM c * (A : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun X : SpecialLinearGroup (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e12 := congrFun (congrFun hm 1) 2
  simp [wM, Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e12
  exact ⟨e12.resolve_right hc, e00.resolve_left hc, e01.resolve_left hc⟩

end CFSG.Quasithin.E6.E68Proof.Lin3

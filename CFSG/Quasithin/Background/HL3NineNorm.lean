module

public import CFSG.Quasithin.Background.HL3NineComm
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear

public section

namespace CFSG.Quasithin

namespace H

namespace L3Nine

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix SU3 Tri CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem rho_mk (hK : Nat.card K = (2 ^ n) ^ 2) {A : GL (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K).det = 1) :
    rho hK (⟨A, hA⟩ : SpecialLinearGroup (Fin 3) K) = rhoT hK A := by
  show rhoT hK (SpecialLinearGroup.toGL ⟨A, hA⟩) = rhoT hK A
  congr 1
  exact Units.ext rfl

theorem mem_scalars_of_rho_eq_one (hK : Nat.card K = (2 ^ n) ^ 2)
    {g : SpecialLinearGroup (Fin 3) K} (h : rho hK g = 1) : g ∈ LinearFlag.scalars 3 K := by
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK (B := SpecialLinearGroup.toGL g) h
  exact FourGroupOddBilinear.mem_scalars_of_coe_eq_smul (by norm_num) hd

theorem mem_scalars_of_comm (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {g : SpecialLinearGroup (Fin 3) K}
    (h : ∀ k : SpecialLinearGroup (Fin 3) K, rho hK g * rho hK k = rho hK k * rho hK g) :
    g ∈ LinearFlag.scalars 3 K := by
  obtain ⟨l, hl⟩ := exists_scalGL_of_commute hn hK (f := rho hK g) fun A hA => by
    rw [← rho_mk hK hA]
    exact h _
  have h1 : rhoT hK (SpecialLinearGroup.toGL g * (scalGL l)⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change rho hK g * (rhoT hK (scalGL l))⁻¹ = 1
    rw [hl, mul_inv_cancel]
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h1
  refine FourGroupOddBilinear.mem_scalars_of_coe_eq_smul (by norm_num) (a := d * l) ?_
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) =
      ((SpecialLinearGroup.toGL g * (scalGL l)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((scalGL l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, inv_mul_cancel_right]
    rfl
  rw [h2, hd, coe_scalGL, Matrix.smul_mul, Matrix.one_mul, smul_smul]

theorem mem_norm_of (hK : Nat.card K = (2 ^ n) ^ 2) {x : MulAut (HMod n K)}
    (h1 : ∀ g, x * rho hK g * x⁻¹ ∈ img hK) (h2 : ∀ g, x⁻¹ * rho hK g * x ∈ img hK) :
    x ∈ norm hK := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨g, rfl⟩
    exact h1 g
  · rintro ⟨g, hg⟩
    have := h2 g
    rw [hg] at this
    simpa [mul_assoc] using this

theorem rhoT_conj_rho (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K)
    (g : SpecialLinearGroup (Fin 3) K) :
    rhoT hK A * rho hK g * (rhoT hK A)⁻¹ ∈ img hK := by
  rw [← map_inv]
  change rhoT hK A * rhoT hK (SpecialLinearGroup.toGL g) * rhoT hK A⁻¹ ∈ img hK
  rw [← map_mul, ← map_mul]
  apply rhoT_mem_img
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
  exact g.2

theorem rhoT_mem_norm (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K) :
    rhoT hK A ∈ norm hK :=
  mem_norm_of hK (rhoT_conj_rho hK A) fun g => by
    rw [← map_inv, ← inv_inv (rhoT hK A⁻¹), ← map_inv]
    simpa using rhoT_conj_rho hK A⁻¹ g

theorem conj_rho_eq (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K) (σ : K ≃+* K)
    (k : SpecialLinearGroup (Fin 3) K) :
    (rhoT hK A * fldAut σ) * rho hK k * (rhoT hK A * fldAut σ)⁻¹ =
      rho hK (CatalogueBHigherLinearAction.slConjugation 3 K A
        (SpecialLinearGroup.map σ.toRingHom k)) := by
  change _ = rhoT hK (SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation 3 K A
    (SpecialLinearGroup.map σ.toRingHom k)))
  rw [CatalogueBHigherLinearAction.toGL_slConjugation]
  have e : SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom k) =
      mapGL σ (SpecialLinearGroup.toGL k) := Units.ext rfl
  rw [e, map_mul, map_mul, map_inv, ← fldAut_conj_rhoT]
  change rhoT hK A * fldAut σ * rhoT hK (SpecialLinearGroup.toGL k) * (rhoT hK A * fldAut σ)⁻¹ = _
  group

omit [Finite K] in
theorem transvection_mul_self {i j : Fin 3} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hij c = 1 := by
  have h : ((SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hij c :
      SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      ← Matrix.transvection, Matrix.transvection_mul_transvection_same _ _ hij,
      CharTwo.add_self_eq_zero, Matrix.transvection_zero, Matrix.SpecialLinearGroup.coe_one]
  exact Subtype.ext h

theorem rho_transvection (hK : Nat.card K = (2 ^ n) ^ 2) {i j : Fin 3} (hij : i ≠ j) (c : K) :
    rho hK (SpecialLinearGroup.transvection hij c) = rhoT hK (trGL i j hij c) := by
  change rhoT hK (SpecialLinearGroup.toGL _) = _
  congr 1
  exact Units.ext rfl

omit [Finite K] in
theorem dual_transvection {i j : Fin 3} (hij : i ≠ j) (c : K) :
    ((SpecialLinearGroup.transvection hij c)⁻¹).transpose =
      SpecialLinearGroup.transvection hij.symm c := by
  have hinv : (SpecialLinearGroup.transvection hij c)⁻¹ = SpecialLinearGroup.transvection hij c :=
    inv_eq_of_mul_eq_one_right (transvection_mul_self hij c)
  rw [hinv]
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

@[expose] noncomputable def diag12 (d : {b : K // bar n b = b} × {b : K // bar n b = b}) :
    HMod n K :=
  mkH (Matrix.diagonal ![0, d.1.1, d.2.1]) (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjM, d.1.2, d.2.2])

theorem rhoT_trGL_diag12 (hK : Nat.card K = (2 ^ n) ^ 2) {i : Fin 3} (hi : i ≠ 0) (a : K)
    (d : {b : K // bar n b = b} × {b : K // bar n b = b}) :
    rhoT hK (trGL i 0 hi a) (diag12 d) = diag12 d := by
  apply mat_injective
  rw [mat_rhoT, diag12, mat_mkH, coe_trGL, tw]
  ext j k
  fin_cases i
  · exact absurd rfl hi
  all_goals fin_cases j <;> fin_cases k <;>
    simp [transvection, Matrix.mul_apply, Fin.sum_univ_three, conjM, Matrix.single_apply]

theorem false_of_dual (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)}
    (hy : ∀ g : SpecialLinearGroup (Fin 3) K, y * rho hK g * y⁻¹ = rho hK ((g⁻¹).transpose)) :
    False := by
  classical
  have hfix : ∀ d, ∀ i j : Fin 3, ¬ (i = 0 ∧ j = 0) → mat (y⁻¹ (diag12 d)) i j = 0 := by
    intro d
    have key : ∀ {j : Fin 3} (hj : (0 : Fin 3) ≠ j) (a : K),
        rhoT hK (trGL 0 j hj a) (y⁻¹ (diag12 d)) = y⁻¹ (diag12 d) := by
      intro j hj a
      have h1 := hy (SpecialLinearGroup.transvection hj a)
      rw [dual_transvection, rho_transvection, rho_transvection] at h1
      have h2 : rhoT hK (trGL 0 j hj a) = y⁻¹ * rhoT hK (trGL j 0 hj.symm a) * y := by
        rw [← h1]
        group
      rw [h2, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self,
        rhoT_trGL_diag12 hK hj.symm a d]
    exact eq_zero_of_fix hn hK (key (by decide)) (key (by decide))
  let f : {b : K // bar n b = b} × {b : K // bar n b = b} → {b : K // bar n b = b} :=
    fun d => ⟨mat (y⁻¹ (diag12 d)) 0 0, herm_apply _ 0 0⟩
  have hf : Function.Injective f := by
    intro d d' h
    have h1 : y⁻¹ (diag12 d) = y⁻¹ (diag12 d') := by
      apply mat_injective
      ext i j
      by_cases hij : i = 0 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := hij
        exact congrArg Subtype.val h
      · rw [hfix d i j hij, hfix d' i j hij]
    have h2 := congrArg mat (y⁻¹.injective h1)
    have h3 := congrFun (congrFun h2 1) 1
    have h4 := congrFun (congrFun h2 2) 2
    simp only [diag12, mat_mkH, Matrix.diagonal_apply_eq] at h3 h4
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, card_fixed hn hK] at hle
  have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  nlinarith

theorem conj_eq_of_proj (hK : Nat.card K = (2 ^ n) ^ 2) {x : MulAut (HMod n K)}
    (A : GL (Fin 3) K) (σ : K ≃+* K)
    (D : SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) K)
    {gp : SpecialLinearGroup (Fin 3) K → SpecialLinearGroup (Fin 3) K}
    (hgp : ∀ g, rho hK (gp g) = x * rho hK g * x⁻¹)
    (hrel : ∀ g, LinearFlag.proj 3 K (gp g) = LinearFlag.proj 3 K
      (CatalogueBHigherLinearAction.slConjugation 3 K A (SpecialLinearGroup.map σ.toRingHom (D g))))
    (g : SpecialLinearGroup (Fin 3) K) :
    (rhoT hK A * fldAut σ)⁻¹ * x * rho hK g * ((rhoT hK A * fldAut σ)⁻¹ * x)⁻¹ = rho hK (D g) := by
  set P := rhoT hK A * fldAut σ with hP
  have hw : ∀ g, ∃ z ∈ LinearFlag.scalars 3 K,
      P⁻¹ * x * rho hK g * (P⁻¹ * x)⁻¹ = rho hK (D g) * (P⁻¹ * rho hK z * P) := by
    intro g
    set s := CatalogueBHigherLinearAction.slConjugation 3 K A
      (SpecialLinearGroup.map σ.toRingHom (D g)) with hs
    refine ⟨s⁻¹ * gp g, LinearFlag.proj_eq_proj_iff.mp (hrel g).symm, ?_⟩
    have h1 : rho hK s = P * rho hK (D g) * P⁻¹ := (conj_rho_eq hK A σ (D g)).symm
    have h2 : x * rho hK g * x⁻¹ = rho hK s * rho hK (s⁻¹ * gp g) := by
      rw [← map_mul, mul_inv_cancel_left, hgp]
    calc P⁻¹ * x * rho hK g * (P⁻¹ * x)⁻¹ = P⁻¹ * (x * rho hK g * x⁻¹) * P := by group
      _ = P⁻¹ * (rho hK s * rho hK (s⁻¹ * gp g)) * P := by rw [h2]
      _ = P⁻¹ * (P * rho hK (D g) * P⁻¹ * rho hK (s⁻¹ * gp g)) * P := by rw [h1]
      _ = rho hK (D g) * (P⁻¹ * rho hK (s⁻¹ * gp g) * P) := by group
  have htr : ∀ t ∈ Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct (Fin 3) K → SpecialLinearGroup (Fin 3) K),
      P⁻¹ * x * rho hK t * (P⁻¹ * x)⁻¹ = rho hK (D t) := by
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    rw [TransvectionStruct.toSpecialLinearGroup_mk]
    set t := SpecialLinearGroup.transvection hij c with ht
    obtain ⟨z, hz, he⟩ := hw t
    set w := P⁻¹ * rho hK z * P with hwdef
    have hz3 : z ^ 3 = 1 := by
      obtain ⟨c', hc', hzc⟩ := LinearFlag.mem_scalars.mp hz
      have h : ((z ^ 3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [Matrix.SpecialLinearGroup.coe_pow, hzc, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
          ← Units.val_pow_eq_pow_val, hc', Units.val_one, map_one]
      exact Subtype.ext h
    have hw3 : w ^ 3 = 1 := by
      have e : w = P⁻¹ * rho hK z * P⁻¹⁻¹ := by rw [hwdef, inv_inv]
      rw [e, conj_pow, ← map_pow, hz3, map_one, mul_one, mul_inv_cancel]
    have hzc : ∀ m, rho hK z * rho hK m = rho hK m * rho hK z := fun m => by
      rw [← map_mul, ← map_mul,
        (Subgroup.mem_center_iff.mp (LinearFlag.scalars_le_center 3 K hz) m).symm]
    have hwc : w * rho hK (D t) = rho hK (D t) * w := by
      have hm := conj_rho_eq hK A σ (D t)
      rw [← hP] at hm
      calc w * rho hK (D t) = P⁻¹ * (rho hK z * (P * rho hK (D t) * P⁻¹)) * P := by
            rw [hwdef]
            group
        _ = P⁻¹ * ((P * rho hK (D t) * P⁻¹) * rho hK z) * P := by rw [hm, hzc]
        _ = rho hK (D t) * w := by
            rw [hwdef]
            group
    have ht2 : t * t = 1 := transvection_mul_self hij c
    have hD2 : D t * D t = 1 := by rw [← map_mul, ht2, map_one]
    have h1 : (P⁻¹ * x * rho hK t * (P⁻¹ * x)⁻¹) * (P⁻¹ * x * rho hK t * (P⁻¹ * x)⁻¹) = 1 := by
      calc (P⁻¹ * x * rho hK t * (P⁻¹ * x)⁻¹) * (P⁻¹ * x * rho hK t * (P⁻¹ * x)⁻¹) =
          P⁻¹ * x * rho hK (t * t) * (P⁻¹ * x)⁻¹ := by
            rw [map_mul]
            group
        _ = 1 := by
            rw [ht2, map_one]
            group
    rw [he] at h1
    have h4 : (rho hK (D t) * w) * (rho hK (D t) * w) = w * w := by
      calc (rho hK (D t) * w) * (rho hK (D t) * w) = rho hK (D t) * (w * rho hK (D t)) * w := by
            group
        _ = rho hK (D t) * (rho hK (D t) * w) * w := by rw [hwc]
        _ = rho hK (D t * D t) * (w * w) := by
            rw [map_mul]
            group
        _ = w * w := by rw [hD2, map_one, one_mul]
    have h3 : w * w = 1 := h4 ▸ h1
    have hw1 : w = 1 := by
      have e : w = w ^ 3 * (w * w)⁻¹ := by group
      rw [e, hw3, h3, inv_one, one_mul]
    rw [he, hw1, mul_one]
  have hfun : (MulAut.conj (P⁻¹ * x)).toMonoidHom.comp (rho hK) = (rho hK).comp D :=
    MonoidHom.eq_of_eqOn_dense
      (SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 3)
        (K := K)) fun t ht => htr t ht
  have := congrArg (fun F => F g) hfun
  exact this

theorem exists_eq_rhoT_mul_fldAut (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {x : MulAut (HMod n K)} (hx : x ∈ norm hK) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K), x = rhoT hK A * fldAut σ := by
  classical
  have hxinv : x⁻¹ ∈ norm hK := inv_mem hx
  have hmem : ∀ g, ∃ g', rho hK g' = x * rho hK g * x⁻¹ := fun g =>
    (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨g, rfl⟩
  choose gp hgp using hmem
  have hmem' : ∀ h, ∃ g, rho hK g = x⁻¹ * rho hK h * x := fun h => by
    have := (Subgroup.mem_normalizer_iff.mp hxinv (rho hK h)).mp ⟨h, rfl⟩
    rwa [inv_inv] at this
  let α' : SpecialLinearGroup (Fin 3) K →* LinearFlag.projectiveSL 3 K :=
    { toFun := fun g => LinearFlag.proj 3 K (gp g)
      map_one' := by
        rw [LinearFlag.proj_eq_one_iff]
        apply mem_scalars_of_rho_eq_one hK
        rw [hgp, map_one, mul_one, mul_inv_cancel]
      map_mul' := fun g h => by
        rw [← map_mul, LinearFlag.proj_eq_proj_iff]
        apply mem_scalars_of_rho_eq_one hK
        rw [map_mul, map_inv, map_mul, hgp, hgp, hgp, map_mul]
        group }
  have hker : LinearFlag.scalars 3 K ≤ α'.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    change LinearFlag.proj 3 K (gp g) = 1
    rw [LinearFlag.proj_eq_one_iff]
    apply mem_scalars_of_comm hn hK
    intro k
    obtain ⟨k', hk'⟩ := hmem' k
    have hgc : rho hK g * rho hK k' = rho hK k' * rho hK g := by
      rw [← map_mul, ← map_mul,
        (Subgroup.mem_center_iff.mp (LinearFlag.scalars_le_center 3 K hg) k').symm]
    have e : rho hK k = x * rho hK k' * x⁻¹ := by
      rw [hk']
      group
    rw [hgp, e]
    calc x * rho hK g * x⁻¹ * (x * rho hK k' * x⁻¹) = x * (rho hK g * rho hK k') * x⁻¹ := by
          group
      _ = x * (rho hK k' * rho hK g) * x⁻¹ := by rw [hgc]
      _ = x * rho hK k' * x⁻¹ * (x * rho hK g * x⁻¹) := by group
  let α := QuotientGroup.lift (LinearFlag.scalars 3 K) α' hker
  have hαproj : ∀ g, α (LinearFlag.proj 3 K g) = LinearFlag.proj 3 K (gp g) := fun g => rfl
  have hαsurj : Function.Surjective α := by
    intro p
    obtain ⟨h, rfl⟩ := LinearFlag.proj_surjective 3 K p
    obtain ⟨g, hg⟩ := hmem' h
    refine ⟨LinearFlag.proj 3 K g, ?_⟩
    rw [hαproj, LinearFlag.proj_eq_proj_iff]
    apply mem_scalars_of_rho_eq_one hK
    rw [map_mul, map_inv, hgp, hg]
    group
  have hαinj : Function.Injective α := Finite.injective_iff_surjective.mpr hαsurj
  obtain ⟨A, σ, ε, hε, hαe⟩ := (LinearFlag.automorphism_generation (K := K) (n := 3) le_rfl).2
    (MulEquiv.ofBijective α ⟨hαinj, hαsurj⟩)
  have hrel0 : ∀ g, LinearFlag.proj 3 K (gp g) = (LinearFlag.conjAut 3 K A *
      LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε) (LinearFlag.proj 3 K g) :=
    fun g => by
      rw [← hαe]
      rfl
  set P := rhoT hK A * fldAut σ with hP
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    have hrel : ∀ g, LinearFlag.proj 3 K (gp g) = LinearFlag.proj 3 K
        (CatalogueBHigherLinearAction.slConjugation 3 K A
          (SpecialLinearGroup.map σ.toRingHom (MonoidHom.id _ g))) := fun g => by
      rw [hrel0, pow_zero, mul_one, MulAut.mul_apply, LinearFlag.fieldAut_proj,
        LinearFlag.conjAut_proj]
      rfl
    have hy := conj_eq_of_proj hK A σ (MonoidHom.id _) hgp hrel
    obtain ⟨l, hl⟩ := exists_scalGL_of_commute hn hK (f := P⁻¹ * x) fun B hB => by
      have h1 : P⁻¹ * x * rhoT hK B * (P⁻¹ * x)⁻¹ = rhoT hK B := by
        have := hy ⟨B, hB⟩
        change P⁻¹ * x * rho hK ⟨B, hB⟩ * (P⁻¹ * x)⁻¹ = rho hK ⟨B, hB⟩ at this
        rwa [rho_mk] at this
      calc P⁻¹ * x * rhoT hK B = P⁻¹ * x * rhoT hK B * (P⁻¹ * x)⁻¹ * (P⁻¹ * x) := by group
        _ = rhoT hK B * (P⁻¹ * x) := by rw [h1]
    refine ⟨A * mapGL σ (scalGL l), σ, ?_⟩
    have hx' : x = P * rhoT hK (scalGL l) := by
      rw [← hl]
      group
    rw [hx', hP, mul_assoc, fldAut_mul_rhoT, ← mul_assoc, ← map_mul]
  ·
    exfalso
    have hrel : ∀ g, LinearFlag.proj 3 K (gp g) = LinearFlag.proj 3 K
        (CatalogueBHigherLinearAction.slConjugation 3 K A
          (SpecialLinearGroup.map σ.toRingHom
            ((CatalogueBGraphForm.slGraphAut 3 K).toMonoidHom g))) := fun g => by
      rw [hrel0, pow_one, MulAut.mul_apply, MulAut.mul_apply, LinearFlag.dualAut_proj,
        LinearFlag.fieldAut_proj, LinearFlag.conjAut_proj]
      rfl
    have hy := conj_eq_of_proj hK A σ (CatalogueBGraphForm.slGraphAut 3 K).toMonoidHom hgp
      hrel
    exact false_of_dual hn hK (y := P⁻¹ * x) fun g => hy g

noncomputable abbrev linImg (hK : Nat.card K = (2 ^ n) ^ 2) : Subgroup (MulAut (HMod n K)) :=
  (rhoT hK).range

theorem img_le_linImg (hK : Nat.card K = (2 ^ n) ^ 2) : img hK ≤ linImg hK := by
  rintro _ ⟨g, rfl⟩
  exact ⟨_, rfl⟩

theorem conj_mem_linImg (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {x : MulAut (HMod n K)}
    (hx : x ∈ norm hK) {r : MulAut (HMod n K)} (hr : r ∈ linImg hK) :
    x * r * x⁻¹ ∈ linImg hK := by
  obtain ⟨A, σ, rfl⟩ := exists_eq_rhoT_mul_fldAut hn hK hx
  obtain ⟨B, rfl⟩ := hr
  refine ⟨A * mapGL σ B * A⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← fldAut_conj_rhoT]
  group

theorem rhoT_mul_fldAut_pow (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K) (σ : K ≃+* K)
    (k : ℕ) : ∃ C : GL (Fin 3) K, (rhoT hK A * fldAut σ) ^ k = rhoT hK C * fldAut (σ ^ k) := by
  induction k with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, fldAut_one, mul_one]⟩
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * mapGL (σ ^ k) A, ?_⟩
    rw [pow_succ, hC, pow_succ, fldAut_mul, map_mul, ← mul_assoc, mul_assoc (rhoT hK C),
      fldAut_mul_rhoT, ← mul_assoc]
    simp only [mul_assoc]

omit [Finite K] [CharP K 2] in
theorem card_ringAut (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card (K ≃+* K) = 2 * n := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega : 1 ≤ 2 * n)
      (SU3.card_eq_two_pow hK)
  exact hcard

theorem pow_mem_linImg (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {x : MulAut (HMod n K)}
    (hx : x ∈ norm hK) : x ^ (2 * n) ∈ linImg hK := by
  obtain ⟨A, σ, rfl⟩ := exists_eq_rhoT_mul_fldAut hn hK hx
  obtain ⟨C, hC⟩ := rhoT_mul_fldAut_pow hK A σ (2 * n)
  have hσ : σ ^ (2 * n) = 1 := by
    rw [← card_ringAut hn hK]
    exact pow_card_eq_one'
  rw [hC, hσ, fldAut_one, mul_one]
  exact ⟨C, rfl⟩

theorem eq_one_or_eq_bar (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : σ ^ 2 = 1) : σ = 1 ∨ σ = bar n := by
  obtain ⟨fr, hfr, hord, htop, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega : 1 ≤ 2 * n)
      (SU3.card_eq_two_pow hK)
  have hmem : σ ∈ Subgroup.zpowers fr := by
    rw [htop]
    exact Subgroup.mem_top σ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [card_ringAut hn hK]; omega)
  rw [← mem_powers_iff_mem_zpowers] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hk' : fr ^ k = σ := hk
  subst hk'
  have hdvd : 2 * n ∣ 2 * k := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    rw [mul_comm, pow_mul]
    exact hσ
  obtain ⟨j, hj⟩ : n ∣ k := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hpow : ∀ (m : ℕ) (x : K), (fr ^ m) x = x ^ 2 ^ m := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ]
      change (fr ^ m) (fr x) = _
      rw [ih, hfr, ← pow_mul, pow_succ, mul_comm]
  have hfrn : fr ^ n = bar n := by
    ext x
    rw [hpow, bar_apply]
  have hbar2 : bar n ^ 2 = (1 : K ≃+* K) := by
    ext x
    rw [pow_two]
    change bar n (bar n x) = x
    exact bar_bar hK x
  rw [hj, pow_mul, hfrn]
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
  · left
    rw [pow_mul, hbar2, one_pow]
  · right
    rw [pow_succ, pow_mul, hbar2, one_pow, one_mul]

theorem exists_of_involution (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {t : MulAut (HMod n K)} (ht : t ∈ norm hK) (ht2 : t * t = 1) :
    ∃ A : GL (Fin 3) K, t = rhoT hK A ∨ t = rhoT hK A * fldAut (bar n) := by
  obtain ⟨A, σ, rfl⟩ := exists_eq_rhoT_mul_fldAut hn hK ht
  obtain ⟨C, hC⟩ := rhoT_mul_fldAut_pow hK A σ 2
  have hσ : σ ^ 2 = 1 := by
    rw [pow_two, ht2] at hC
    have h1 : fldAut (σ ^ 2) = rhoT hK C⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right hC.symm
    exact eq_one_of_fldAut_eq_rhoT hK h1
  refine ⟨A, ?_⟩
  rcases eq_one_or_eq_bar hn hK hσ with rfl | rfl
  · left
    rw [fldAut_one, mul_one]
  · right
    rfl

end L3Nine

end H

end CFSG.Quasithin

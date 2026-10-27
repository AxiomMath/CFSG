module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofSLTypeThree

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedScalars)

open CFSG.Assembly.RankThreeEven (projImage)

open Matrix (ProjGenLinGroup)


namespace Res423Four

section Basic

theorem pow_conj_eq_of_conj {G : Type*} [Group G] {x y s : G} (hs : ∀ g : G, g * s = s * g)
    (h : y * x * y⁻¹ = s * x) (m : ℕ) : y ^ m * x * (y ^ m)⁻¹ = s ^ m * x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hys : y * s ^ m = s ^ m * y := (Commute.pow_right (show Commute y s from hs y) m).eq
    calc y ^ (m + 1) * x * (y ^ (m + 1))⁻¹ = y * (y ^ m * x * (y ^ m)⁻¹) * y⁻¹ := by group
      _ = y * (s ^ m * x) * y⁻¹ := by rw [ih]
      _ = (y * s ^ m) * x * y⁻¹ := by simp only [mul_assoc]
      _ = s ^ m * (y * x * y⁻¹) := by rw [hys]; simp only [mul_assoc]
      _ = s ^ (m + 1) * x := by rw [h, pow_succ, mul_assoc]

theorem diagonal_mul_eq_of_conj {K : Type*} [Field K] {d t : Fin 3 → K}
    {X : Matrix (Fin 3) (Fin 3) K} {ζ : K}
    (hX : Matrix.diagonal d * X = ζ • (X * Matrix.diagonal d))
    (ht : ∀ i j, t i = d i * t j ∨ d i ≠ ζ * d j) :
    Matrix.diagonal t * X = Matrix.diagonal d * X * Matrix.diagonal t := by
  ext i j
  have h := congrFun (congrFun hX i) j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at h ⊢
  by_cases hij : X i j = 0
  · rw [hij]; ring
  · have hd : d i = ζ * d j := by
      have h1 : (d i - ζ * d j) * X i j = 0 := by linear_combination h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hij)
    rcases ht i j with h2 | h2
    · rw [h2]; ring
    · exact absurd hd h2

end Basic

section Diag

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_diag_conj_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {X : GL (Fin 3) K} {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hDX : diagTau hτ3 * X * (diagTau hτ3)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * X) :
    ∃ T₀ ∈ glPi π 3 (p ^ f) K, T₀ * diagTau hτ3 = diagTau hτ3 * T₀ ∧
      T₀ * X * T₀⁻¹ = diagTau hτ3 * X := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ3
  have hs : 1 + τ + τ ^ 2 = 0 := one_add_tau_add_sq hτ3 hτ1
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    have h1 : τ * τ ^ 2 = τ := by rw [h, mul_one]
    rw [← pow_succ', hτ3] at h1
    exact h1.symm
  have hττ : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have h1 : τ * (τ - 1) = 0 := by linear_combination -h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hτ0)
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτuK : (τu : K) = τ := rfl
  have hτu3 : τu ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    refine cube_root_mem_qSubPi hq ?_
    rw [mem_rootsOfUnity]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hτuK, hτ3, Units.val_one])
  have h1u : (1 : Kˣ) ∈ rootsOfUnity (qSubPi π (p ^ f)) K := one_mem _
  have hX : Matrix.diagonal ![τ, τ ^ 2, 1] * (X : Matrix (Fin 3) (Fin 3) K) =
      (ζ : K) • ((X : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal ![τ, τ ^ 2, 1]) := by
    have h1 : diagTau hτ3 * X = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * X * diagTau hτ3 := by
      rw [← hDX]; group
    have h2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [Units.val_mul, coe_diagTau_eq_diagonal] at h2
    rw [h2, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  have hζ3 : ζ ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hDX
  have hζK : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hζK1 : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  have key : ∀ (u v w : Kˣ), (u ∈ rootsOfUnity (qSubPi π (p ^ f)) K) →
      (v ∈ rootsOfUnity (qSubPi π (p ^ f)) K) → (w ∈ rootsOfUnity (qSubPi π (p ^ f)) K) →
      (∀ i j, ![(u : K), v, w] i = ![τ, τ ^ 2, 1] i * ![(u : K), v, w] j ∨
        ![τ, τ ^ 2, 1] i ≠ (ζ : K) * ![τ, τ ^ 2, 1] j) →
      ∃ T₀ ∈ glPi π 3 (p ^ f) K, T₀ * diagTau hτ3 = diagTau hτ3 * T₀ ∧
        T₀ * X * T₀⁻¹ = diagTau hτ3 * X := by
    intro u v w hu hv hw ht
    refine ⟨diagUnits u v w, diagUnits_mem_glPi hK hu hv hw, ?_, ?_⟩
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_diagUnits, coe_diagTau_eq_diagonal,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    · have h3 := diagonal_mul_eq_of_conj hX ht
      have h4 : diagUnits u v w * X = diagTau hτ3 * X * diagUnits u v w := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_diagUnits, coe_diagTau_eq_diagonal]
        exact h3
      rw [h4, mul_inv_cancel_right]
  rcases eq_one_or_eq_tau_or_eq_tau_sq hτ3 hτ1 hζK with h | h | h
  · exact absurd h hζK1
  ·
    refine key τu 1 1 hτu3 h1u h1u fun i j => ?_
    rw [h]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Units.val_one, hτuK] <;>
      first
        | exact Or.inl (by ring1)
        | exact Or.inl (by linear_combination -hτ3)
        | exact Or.inr fun h' => hττ (by linear_combination h')
        | exact Or.inr fun h' => hττ (by linear_combination -h')
        | exact Or.inr fun h' => hτ2 (by linear_combination h' + hτ3)
        | exact Or.inr fun h' => hτ2 (by linear_combination -h')
  ·
    refine key 1 (τu ^ 2) 1 h1u (pow_mem hτu3 2) h1u fun i j => ?_
    rw [h]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Units.val_one, Units.val_pow_eq_pow_val, hτuK] <;>
      first
        | exact Or.inl (by ring1)
        | exact Or.inl (by linear_combination -hτ3)
        | exact Or.inr fun h' => hτ1 (by linear_combination h' + hτ3)
        | exact Or.inr fun h' => hττ (by linear_combination h')
        | exact Or.inr fun h' => hττ (by linear_combination -h' - τ * hτ3)
        | exact Or.inr fun h' => hτ1 (by linear_combination -h' - τ * hτ3)

end Diag

section Lifts

variable {H : Type} [Group H] {L : Subgroup H} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem isPGLAtP_inv_of {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {g : H} {y : GL (Fin 3) K}
    (hy : IsPGLAtP e g y) : IsPGLAtP e g⁻¹ y⁻¹ := by
  refine ⟨inv_mem hy.1, fun m => ?_⟩
  set m' := slAct e ⟨g⁻¹, mem_normalizer_of_normal g⁻¹⟩ m with hm'
  have h1 : slAct e ⟨g, mem_normalizer_of_normal g⟩ m' = m := by
    rw [hm', ← slAct_mul_applyP]
    have h2 : (⟨g * g⁻¹, mem_normalizer_of_normal _⟩ : Subgroup.normalizer (L : Set H)) = 1 :=
      Subtype.ext (mul_inv_cancel g)
    rw [h2, map_one]
    rfl
  have h3 := hy.2 m'
  rw [h1] at h3
  rw [map_inv, inv_inv]
  calc ((m' : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk y * m' * (ProjGenLinGroup.mk y)⁻¹) *
        ProjGenLinGroup.mk y := by group
    _ = (ProjGenLinGroup.mk y)⁻¹ * m * ProjGenLinGroup.mk y := by rw [← h3]

theorem exists_conj_eq_scalar_mul_of_commuteP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {g h : H} (hgh : g * h = h * g) {y z : GL (Fin 3) K} (hy : IsPGLAtP e g y)
    (hz : IsPGLAtP e h z) :
    ∃ κ : Kˣ, y * z * y⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) κ * z := by
  have h1 := isPGLAtP_mul e hy hz
  have h2 := isPGLAtP_mul e hz hy
  rw [← hgh] at h2
  have hm : ((y * z : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) =
      ((z * y : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) :=
    QuotientGroup.eq.mpr (isPGLAtP_inv_mul_mem hK hq h1 h2)
  refine exists_scalar_of_mk_mul_comm ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact hm

theorem det_ne_cube_of_not_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {a : H} (haLC : a ∉ L ⊔ Subgroup.centralizer (L : Set H)) {y : GL (Fin 3) K}
    (hy : IsPGLAtP e a y) :
    ∀ μ : rootsOfUnity (qSubPi π (p ^ f)) K,
      μ ^ 3 ≠ ⟨Matrix.GeneralLinearGroup.det y, det_mem_rootsOfUnity hK hy.1⟩ := by
  intro μ hμ
  apply haLC
  have h1 : ((μ : Kˣ) : K) ^ 3 = (y : Matrix (Fin 3) (Fin 3) K).det := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hμ]
    rfl
  obtain ⟨l, hl, -, hyl⟩ := exists_inner_of_det_eq_cube hK hy.1
    ((scalar_mem_glPi_iff hK (μ : Kˣ)).mpr μ.2) h1.symm
  obtain ⟨v, hv, -, hav⟩ := exists_inner_mem_of_innerP hK hq hy hl (fun m _ => hyl m)
  have h2 := mul_mem (Subgroup.mem_sup_right (S := L) hav)
    (Subgroup.mem_sup_left (T := Subgroup.centralizer (L : Set H)) hv)
  rwa [inv_mul_cancel_right] at h2

theorem exists_mem_of_det_eq_cube (hK : PiField π p f K)
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {w : GL (Fin 3) K} (hw : w ∈ glPi π 3 (p ^ f) K)
    {μ : Kˣ} (hμ : μ ∈ rootsOfUnity (qSubPi π (p ^ f)) K)
    (hdet : (w : Matrix (Fin 3) (Fin 3) K).det = (μ : K) ^ 3) :
    ∃ g ∈ L, IsPGLAtP e g w := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨l, hl, ⟨z, hz⟩, -⟩ := exists_inner_of_det_eq_cube hK hw
    ((scalar_mem_glPi_iff hK μ).mpr hμ) hdet
  set g : L := e.symm (projOf _ ⟨l, hl⟩) with hgdef
  have heg : ((e g : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk l := by
    rw [hgdef, MulEquiv.apply_symm_apply, coe_projOf]
  have hgl : IsPGLAtP e (g : H) l := isPGLAtP_of_mem e hπ g.2 hl heg
  have hzH : Matrix.GeneralLinearGroup.scalar (Fin 3) z ∈ glPi π 3 (p ^ f) K := by
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin 3) z = l⁻¹ * w := by rw [hz]; group
    rw [h1]
    exact mul_mem (inv_mem (slPi_le_glPi hπ hl)) hw
  refine ⟨g, g.2, ?_⟩
  rw [hz]
  exact isPGLAtP_mul_scalar hgl hzH

theorem exists_transvection (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    (hLC : L ⊓ Subgroup.centralizer (L : Set H) = ⊥)
    {E : Subgroup (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K)}
    (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    {b a : H} (hbL : b ∈ L) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (haLC : a ∉ L ⊔ Subgroup.centralizer (L : Set H))
    {Yb Ya : GL (Fin 3) K} (hYb : IsPGLAtP e b Yb) (hYa : IsPGLAtP e a Ya)
    (hYbE : (Yb : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E)
    (hYaE : (Ya : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : Yb * Ya * Yb⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * Ya) :
    ∃ g₀ ∈ L, g₀ * b * g₀⁻¹ = b ∧ g₀ * a * g₀⁻¹ = b * a := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hK hq
  have hbC : b ∉ Subgroup.centralizer (L : Set H) := fun h =>
    hb1 (Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr ⟨hbL, h⟩))
  have h1 : Type123 π (p ^ f) K Yb 1 := by
    rcases type13_of_heisP hK hq hEcomm hYbE hYaE hζ1 hζ hYb.1
      (not_mem_zPi_of_isPGLAtP hK hq hbC hYb) (pow_three_mem_zPiP hK hq hb3 hYb) hYbE with h | h
    · exact h
    · exact absurd (exists_inner_of_mem_supP hK hq (Subgroup.mem_sup_left hbL) hYb)
        (not_inner_of_type3 hK hq hYb.1 h)
  obtain ⟨τ, hτ3, hτ1, z, hz, g, hg, hD⟩ := h1
  have hzH : z ∈ glPi π 3 (p ^ f) K := by
    have h2 := hz
    rw [zPi_eq hπ hq' hτ₀ hτ₀1] at h2
    exact h2.1
  obtain ⟨μ, rfl⟩ := mem_statedScalars_of_mem_zPi hK hq hτ₀ hτ₀1 hz
  set Yb' := Yb * Matrix.GeneralLinearGroup.scalar (Fin 3) μ with hYb'def
  have hYb' : IsPGLAtP e b Yb' := isPGLAtP_mul_scalar hYb hzH
  have hζ' : Yb' * Ya * Yb'⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * Ya :=
    heis_of_mul_scalar (MonoidHom.mem_range.mpr ⟨μ, by rw [hYb'def, inv_mul_cancel_left]⟩)
      (MonoidHom.mem_range.mpr ⟨1, by rw [map_one, inv_mul_cancel]⟩) hζ
  have hDX : diagTau hτ3 * (g⁻¹ * Ya * g) * (diagTau hτ3)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (g⁻¹ * Ya * g) := by
    rw [← hD]
    have hsc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g⁻¹).eq
    calc g⁻¹ * Yb' * g * (g⁻¹ * Ya * g) * (g⁻¹ * Yb' * g)⁻¹ =
        g⁻¹ * (Yb' * Ya * Yb'⁻¹) * g := by group
      _ = g⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * Ya) * g := by rw [hζ']
      _ = (g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) ζ) * Ya * g := by
          simp only [mul_assoc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (g⁻¹ * Ya * g) := by
          rw [hsc]; simp only [mul_assoc]
  obtain ⟨T₀, hT₀H, hT₀D, hT₀X⟩ := exists_diag_conj_eq hK hq hτ3 hτ1 hζ1 hDX
  have hYb'g : Yb' = g * diagTau hτ3 * g⁻¹ := by rw [← hD]; group
  set T := g * T₀ * g⁻¹ with hTdef
  have hTH : T ∈ glPi π 3 (p ^ f) K := mul_mem (mul_mem hg hT₀H) (inv_mem hg)
  have hTb : T * Yb' * T⁻¹ = Yb' := by
    rw [hTdef, hYb'g]
    calc g * T₀ * g⁻¹ * (g * diagTau hτ3 * g⁻¹) * (g * T₀ * g⁻¹)⁻¹ =
        g * (T₀ * diagTau hτ3) * T₀⁻¹ * g⁻¹ := by group
      _ = g * (diagTau hτ3 * T₀) * T₀⁻¹ * g⁻¹ := by rw [hT₀D]
      _ = g * diagTau hτ3 * g⁻¹ := by group
  have hTa : T * Ya * T⁻¹ = Yb' * Ya := by
    rw [hTdef, hYb'g]
    calc g * T₀ * g⁻¹ * Ya * (g * T₀ * g⁻¹)⁻¹ =
        g * (T₀ * (g⁻¹ * Ya * g) * T₀⁻¹) * g⁻¹ := by group
      _ = g * (diagTau hτ3 * (g⁻¹ * Ya * g)) * g⁻¹ := by rw [hT₀X]
      _ = g * diagTau hτ3 * g⁻¹ * Ya := by group
  have hnc := det_ne_cube_of_not_mem hK hq haLC hYa
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  obtain ⟨m, ν, hmν⟩ := exists_mul_pow_eq_cube
    (⟨Matrix.GeneralLinearGroup.det T, det_mem_rootsOfUnity hK hTH⟩ :
      rootsOfUnity (qSubPi π (p ^ f)) K) hnc
  have hwH : T * Ya ^ m ∈ glPi π 3 (p ^ f) K := mul_mem hTH (pow_mem hYa.1 m)
  have hwdet : ((T * Ya ^ m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((ν : Kˣ) : K) ^ 3 := by
    have h2 := congrArg (fun t : rootsOfUnity (qSubPi π (p ^ f)) K => ((t : Kˣ) : K)) hmν
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.val_det_apply] at h2
    rw [Units.val_mul, Matrix.det_mul, Units.val_pow_eq_pow_val, Matrix.det_pow]
    exact h2
  obtain ⟨g₀, hg₀L, hg₀⟩ := exists_mem_of_det_eq_cube hK e hwH ν.2 hwdet
  refine ⟨g₀, hg₀L, ?_, ?_⟩
  ·
    have hs : ∀ w : GL (Fin 3) K, w * Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * w := fun w =>
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ⁻¹ w).eq
    have hYaYb : Ya * Yb' * Ya⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * Yb' := by
      have h2 : Yb' * Ya = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * Ya * Yb' := by
        rw [← hζ']; group
      have h3 : Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ *
          Matrix.GeneralLinearGroup.scalar (Fin 3) ζ = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      calc Ya * Yb' * Ya⁻¹ = (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ *
            Matrix.GeneralLinearGroup.scalar (Fin 3) ζ) * Ya * Yb' * Ya⁻¹ := by
            rw [h3, one_mul]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ *
            (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * Ya * Yb') * Ya⁻¹ := by
            simp only [mul_assoc]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * (Yb' * Ya) * Ya⁻¹ := by rw [← h2]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * Yb' := by group
    have hpow := pow_conj_eq_of_conj hs hYaYb m
    have hsm : T * Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ ^ m =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ ^ m * T :=
      (Commute.pow_right (show Commute T _ from hs T) m).eq
    have hlift : IsPGLAtP e (g₀ * b * g₀⁻¹ * b⁻¹)
        ((T * Ya ^ m) * Yb' * (T * Ya ^ m)⁻¹ * Yb'⁻¹) :=
      isPGLAtP_mul e (isPGLAtP_mul e (isPGLAtP_mul e hg₀ hYb') (isPGLAtP_inv_of hg₀))
        (isPGLAtP_inv_of hYb')
    have hsc : (T * Ya ^ m) * Yb' * (T * Ya ^ m)⁻¹ * Yb'⁻¹ ∈ StatedScalars (Fin 3) K := by
      have e1 : (T * Ya ^ m) * Yb' * (T * Ya ^ m)⁻¹ * Yb'⁻¹ =
          T * (Ya ^ m * Yb' * (Ya ^ m)⁻¹) * T⁻¹ * Yb'⁻¹ := by group
      have e2 : T * (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ ^ m * Yb') * T⁻¹ * Yb'⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ ^ m := by
        calc T * (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ ^ m * Yb') * T⁻¹ * Yb'⁻¹ =
            (T * Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ ^ m) * Yb' * T⁻¹ * Yb'⁻¹ := by
              simp only [mul_assoc]
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ ^ m * (T * Yb' * T⁻¹) * Yb'⁻¹ := by
              rw [hsm]; simp only [mul_assoc]
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ ^ m := by
              rw [hTb, mul_inv_cancel_right]
      rw [e1, hpow, e2]
      exact pow_mem (MonoidHom.mem_range.mpr ⟨ζ⁻¹, rfl⟩) m
    have hC := mem_centralizer_of_isPGLAtP_scalar hlift hsc
    have hL : g₀ * b * g₀⁻¹ * b⁻¹ ∈ L :=
      mul_mem (mul_mem (mul_mem hg₀L hbL) (inv_mem hg₀L)) (inv_mem hbL)
    have h2 : g₀ * b * g₀⁻¹ * b⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr ⟨hL, hC⟩)
    exact mul_inv_eq_one.mp h2
  ·
    have hlift : IsPGLAtP e (g₀ * a * g₀⁻¹ * a⁻¹ * b⁻¹)
        ((T * Ya ^ m) * Ya * (T * Ya ^ m)⁻¹ * Ya⁻¹ * Yb'⁻¹) :=
      isPGLAtP_mul e (isPGLAtP_mul e (isPGLAtP_mul e (isPGLAtP_mul e hg₀ hYa)
        (isPGLAtP_inv_of hg₀)) (isPGLAtP_inv_of hYa)) (isPGLAtP_inv_of hYb')
    have hsc : (T * Ya ^ m) * Ya * (T * Ya ^ m)⁻¹ * Ya⁻¹ * Yb'⁻¹ = 1 := by
      have e1 : (T * Ya ^ m) * Ya * (T * Ya ^ m)⁻¹ = T * Ya * T⁻¹ := by group
      rw [e1, hTa]
      group
    have hC := mem_centralizer_of_isPGLAtP_scalar hlift (by rw [hsc]; exact one_mem _)
    have hL : g₀ * a * g₀⁻¹ * a⁻¹ * b⁻¹ ∈ L := by
      have e1 : g₀ * a * g₀⁻¹ * a⁻¹ * b⁻¹ = g₀ * (a * g₀⁻¹ * a⁻¹) * b⁻¹ := by group
      rw [e1]
      exact mul_mem (mul_mem hg₀L (hLn.conj_mem _ (inv_mem hg₀L) a)) (inv_mem hbL)
    have h2 : g₀ * a * g₀⁻¹ * a⁻¹ * b⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr ⟨hL, hC⟩)
    calc g₀ * a * g₀⁻¹ = (g₀ * a * g₀⁻¹ * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [h2, one_mul]

end Lifts

section PGL

variable {H : Type} [Group H] [Finite H] {L : Subgroup H} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

omit [Finite H] hLn in
theorem pow_eq_one_of_pow_mem {S : Subgroup H} {a : H} (ha3 : a ^ 3 = 1) (haS : a ∉ S) {k : ℕ}
    (hk : a ^ k ∈ S) : a ^ k = 1 := by
  have hk' : a ^ k = a ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, ha3, one_pow, one_mul]
  rw [hk'] at hk ⊢
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
  · rw [h, pow_zero]
  · rw [h, pow_one] at hk
    exact absurd hk haS
  · rw [h] at hk
    exfalso
    apply haS
    have h4 : a = (a ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, ha3, one_mul, pow_one]
    rw [h4]
    exact pow_mem hk 2

theorem isZ3PGLThreePi_sup (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    (hLC : L ⊓ Subgroup.centralizer (L : Set H) = ⊥) {A : Subgroup H} {c a : H}
    (hc3 : orderOf c = 3) (hcC : c ∈ Subgroup.centralizer (L : Set H)) (hca : c * a = a * c)
    (ha3 : a ^ 3 = 1) (haLC : a ∉ L ⊔ Subgroup.centralizer (L : Set H)) {Ya : GL (Fin 3) K}
    (hYa : IsPGLAtP e a Ya)
    (hAL : A ⊔ L = Subgroup.zpowers c ⊔ (L ⊔ Subgroup.zpowers a)) :
    Sec8.IsZ3PGLThreePi ↥(A ⊔ L) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set N := L ⊔ Subgroup.zpowers a with hNdef
  have hdecomp : ∀ x ∈ N, ∃ l ∈ L, ∃ k : ℕ, x = l * a ^ k := by
    intro x hx
    obtain ⟨l, hl, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hw
    exact ⟨l, hl, k, rfl⟩
  have hliftL : ∀ l ∈ L, ∃ s, IsPGLAtP e l s := by
    intro l hl
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
    exact ⟨s, isPGLAtP_of_mem e hπ hl hs hse.symm⟩
  have hN : ∀ x ∈ N, ∃ y, IsPGLAtP e x y := by
    intro x hx
    obtain ⟨l, hl, k, rfl⟩ := hdecomp x hx
    obtain ⟨s, hs⟩ := hliftL l hl
    exact ⟨s * Ya ^ k, isPGLAtP_mul e hs (isPGLAtP_pow hYa k)⟩
  have hNC : ∀ x ∈ N, x ∈ Subgroup.centralizer (L : Set H) → x = 1 := by
    intro x hx hxC
    obtain ⟨l, hl, k, rfl⟩ := hdecomp x hx
    have hak : a ^ k ∈ L ⊔ Subgroup.centralizer (L : Set H) := by
      have h1 := mul_mem (Subgroup.mem_sup_left (T := Subgroup.centralizer (L : Set H))
        (inv_mem hl)) (Subgroup.mem_sup_right (S := L) hxC)
      rwa [inv_mul_cancel_left] at h1
    have hk1 := pow_eq_one_of_pow_mem ha3 haLC hak
    rw [hk1, mul_one] at hxC ⊢
    exact Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr ⟨hl, hxC⟩)
  have hSZ : StatedScalars (Fin 3) K = Subgroup.center (GL (Fin 3) K) :=
    Matrix.GeneralLinearGroup.center_eq_range_scalar.symm
  have hSk : StatedScalars (Fin 3) K ≤
      (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).ker := by
    rw [ProjGenLinGroup.ker_mk, hSZ]
  set Q := QuotientGroup.lift (StatedScalars (Fin 3) K)
    (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K) hSk with hQ
  set φ : N →* ProjGenLinGroup (Fin 3) K := Q.comp (pglHomP hK hq N hN) with hφ
  have hφapp : ∀ (x : N) {y : GL (Fin 3) K}, IsPGLAtP e x y → φ x = ProjGenLinGroup.mk y := by
    intro x y hy
    rw [hφ, MonoidHom.comp_apply, pglHomP_apply x hy, hQ, QuotientGroup.lift_mk]
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨y, hy⟩ := hN x x.2
    rw [hφapp x hy, ProjGenLinGroup.mk_eq_one, ← hSZ] at hx
    exact Subtype.ext (hNC x x.2 (mem_centralizer_of_isPGLAtP_scalar hy hx))
  have hφrange : φ.range = projImage (glPi π 3 (p ^ f) K) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := hN x x.2
      rw [hφapp x hy]
      exact ⟨y, hy.1, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hnc := det_ne_cube_of_not_mem hK hq haLC hYa
      have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
      obtain ⟨k, ν, hkν⟩ := exists_mul_pow_eq_cube
        (⟨Matrix.GeneralLinearGroup.det w, det_mem_rootsOfUnity hK hw⟩ :
          rootsOfUnity (qSubPi π (p ^ f)) K) hnc
      have hwH : w * Ya ^ k ∈ glPi π 3 (p ^ f) K := mul_mem hw (pow_mem hYa.1 k)
      have hwdet : ((w * Ya ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
          ((ν : Kˣ) : K) ^ 3 := by
        have h2 := congrArg (fun t : rootsOfUnity (qSubPi π (p ^ f)) K => ((t : Kˣ) : K)) hkν
        simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
          Matrix.GeneralLinearGroup.val_det_apply] at h2
        rw [Units.val_mul, Matrix.det_mul, Units.val_pow_eq_pow_val, Matrix.det_pow]
        exact h2
      obtain ⟨g₁, hg₁L, hg₁⟩ := exists_mem_of_det_eq_cube hK e hwH ν.2 hwdet
      have hxN : g₁ * (a ^ k)⁻¹ ∈ N := mul_mem (Subgroup.mem_sup_left hg₁L)
        (inv_mem (pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)) k))
      have hxl : IsPGLAtP e (g₁ * (a ^ k)⁻¹) (w * Ya ^ k * (Ya ^ k)⁻¹) :=
        isPGLAtP_mul e hg₁ (isPGLAtP_inv_of (isPGLAtP_pow hYa k))
      rw [mul_inv_cancel_right] at hxl
      exact ⟨⟨_, hxN⟩, hφapp ⟨_, hxN⟩ hxl⟩
  have eN : N ≃* projImage (glPi π 3 (p ^ f) K) :=
    (MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hφrange)
  set Z := Subgroup.zpowers c with hZdef
  have hZC : Z ≤ Subgroup.centralizer (L : Set H) := Subgroup.zpowers_le.mpr hcC
  have hNZ : N ≤ Subgroup.centralizer (Z : Set H) := by
    refine sup_le (fun l hl => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((Subgroup.mem_centralizer_iff.mp (hZC hz)) l hl).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hle : Z ≤ Subgroup.centralizer ({a} : Set H) := by
        rw [hZdef, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hca
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
  have hcomm : ∀ (z : Z) (n : N), Commute (Z.subtype z) (N.subtype n) := fun z n =>
    ((Subgroup.mem_centralizer_iff.mp (hNZ n.2)) z z.2)
  let F : Z × N →* H := MonoidHom.noncommCoprod Z.subtype N.subtype hcomm
  have hF : ∀ y : Z × N, F y = (y.1 : H) * y.2 := fun y => rfl
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro ⟨z, n⟩ hzn
    rw [hF] at hzn
    have hnz : (n : H) = (z : H)⁻¹ := eq_inv_of_mul_eq_one_right hzn
    have hn1 : (n : H) = 1 := hNC n n.2 (by rw [hnz]; exact inv_mem (hZC z.2))
    have hz1 : (z : H) = 1 := by rw [hn1, mul_one] at hzn; exact hzn
    exact Prod.ext (Subtype.ext hz1) (Subtype.ext hn1)
  have hFr : F.range = A ⊔ L := by
    rw [hAL]
    apply le_antisymm
    · rintro _ ⟨⟨z, n⟩, rfl⟩
      rw [hF]
      exact mul_mem (Subgroup.mem_sup_left z.2) (Subgroup.mem_sup_right n.2)
    · refine sup_le (fun z hz => ⟨(⟨z, hz⟩, 1), by rw [hF]; simp⟩)
        (fun n hn => ⟨(1, ⟨n, hn⟩), by rw [hF]; simp⟩)
  have hZ3 : Nat.card Z = 3 := by rw [hZdef, Nat.card_zpowers, hc3]
  have hC3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let eZ : Z ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hZ3 hC3
  exact ⟨π, p, f, K, inferInstance, hK, hq, ⟨(MulEquiv.subgroupCongr hFr.symm).trans
    ((MonoidHom.ofInjective hFinj).symm.trans (MulEquiv.prodCongr eZ eN))⟩⟩

end PGL

end Res423Four

open Res423Four

theorem k423L3TypeThreeFrame_holds : K423L3TypeThreeFrame := by
  intro H _ _ L hLn π p f K _ hLq hK hq e A c hA hA27 hc3 hAc hpgl hheis hbex
  obtain ⟨x₁, hx₁, x₂, hx₂, y₁, y₂, ζ, hy₁, hy₂, hζ1, hζ⟩ := hheis
  obtain ⟨b, hAL, hb3⟩ := hbex
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect L := hLq.1
  have := isPerfect_projImage_of_equiv e
  have h3K := hK.three_ne_zero hq
  have hLC := inf_centralizer_eq_bot_proj hK hq e
  have hAe := hA.prop
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set H) := hAc ▸ Subgroup.mem_zpowers c
  have hcA : c ∈ A := hcAC.1
  have hcC : c ∈ Subgroup.centralizer (L : Set H) := hcAC.2
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc3
    norm_num at hc3
  have hbAL : b ∈ A ⊓ L := hAL ▸ Subgroup.mem_zpowers b
  have hbA : b ∈ A := hbAL.1
  have hbL : b ∈ L := hbAL.2
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb3
    norm_num at hb3
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hEcomm := range_pglHomP_comm (hK := hK) (hq := hq) (hA' := hpgl) hAcomm
  obtain ⟨Yb, hYb⟩ := hpgl b hbA
  obtain ⟨a, haA, Ya, hYa, ζ', hζ'1, hζ'⟩ : ∃ a ∈ A, ∃ Ya, IsPGLAtP e a Ya ∧ ∃ ζ' : Kˣ,
      ζ' ≠ 1 ∧ Yb * Ya * Yb⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ' * Ya := by
    obtain ⟨κ₁, hκ₁⟩ := exists_conj_eq_scalar_mul_of_commuteP hK hq (hAcomm b hbA x₁ hx₁) hYb hy₁
    obtain ⟨κ₂, hκ₂⟩ := exists_conj_eq_scalar_mul_of_commuteP hK hq (hAcomm b hbA x₂ hx₂) hYb hy₂
    by_cases h1 : κ₁ = 1
    · by_cases h2 : κ₂ = 1
      · exfalso
        rw [h1, map_one, one_mul] at hκ₁
        rw [h2, map_one, one_mul] at hκ₂
        have hc₁ : Yb * y₁ = y₁ * Yb := by
          calc Yb * y₁ = (Yb * y₁ * Yb⁻¹) * Yb := by group
            _ = y₁ * Yb := by rw [hκ₁]
        have hc₂ : Yb * y₂ = y₂ * Yb := by
          calc Yb * y₂ = (Yb * y₂ * Yb⁻¹) * Yb := by group
            _ = y₂ * Yb := by rw [hκ₂]
        have hs := mem_statedScalars_of_commute_heis h3K hζ1
          (pow_three_eq_one_of_conj_eq_scalar_mul hζ) hζ hc₁ hc₂
        exact hb1 (Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr
          ⟨hbL, mem_centralizer_of_isPGLAtP_scalar hYb hs⟩))
      · exact ⟨x₂, hx₂, y₂, hy₂, κ₂, h2, hκ₂⟩
    · exact ⟨x₁, hx₁, y₁, hy₁, κ₁, h1, hκ₁⟩
  have hζ'3 : ζ' ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hζ'
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have haLC : a ∉ L ⊔ Subgroup.centralizer (L : Set H) := by
    intro h
    obtain ⟨l, hl, u, hu, hlu⟩ := Subgroup.mem_sup_of_normal_left.mp h
    have hal : a * l⁻¹ ∈ Subgroup.centralizer (L : Set H) := by
      have hCn : (Subgroup.centralizer (L : Set H)).Normal := inferInstance
      rw [← hlu]
      exact hCn.conj_mem u hu l
    have hlA := mem_of_mul_inv_mem_centralizer hA hLC haA hl hal
    have hlb : l ∈ Subgroup.zpowers b := hAL ▸ Subgroup.mem_inf.mpr ⟨hlA, hl⟩
    obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hlb
    have hlift : IsPGLAtP e a (Yb ^ k) := by
      have h1 := isPGLAtP_mul e (isPGLAtP_of_mem_centralizer e hal) (isPGLAtP_pow hYb k)
      rwa [inv_mul_cancel_right, one_mul] at h1
    obtain ⟨w, hw⟩ := isPGLAtP_inv_mul_mem hK hq hYa hlift
    have hYbk : Yb ^ k = Ya * Matrix.GeneralLinearGroup.scalar (Fin 3) w := by rw [hw]; group
    have hcomm : Yb * Yb ^ k * Yb⁻¹ = Yb ^ k := by
      rw [(Commute.self_pow Yb k).eq, mul_inv_cancel_right]
    have hsc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar w Yb⁻¹).eq
    have e1 : Yb * (Ya * Matrix.GeneralLinearGroup.scalar (Fin 3) w) * Yb⁻¹ =
        (Yb * Ya * Yb⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 3) w := by
      calc Yb * (Ya * Matrix.GeneralLinearGroup.scalar (Fin 3) w) * Yb⁻¹ =
          Yb * Ya * (Matrix.GeneralLinearGroup.scalar (Fin 3) w * Yb⁻¹) := by
            simp only [mul_assoc]
        _ = Yb * Ya * (Yb⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) w) := by rw [hsc]
        _ = (Yb * Ya * Yb⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 3) w := by
            simp only [mul_assoc]
    rw [hYbk, e1, hζ'] at hcomm
    apply hζ'1
    apply eq_one_of_scalar_mul_eq (z := Ya * Matrix.GeneralLinearGroup.scalar (Fin 3) w)
    rw [← mul_assoc]
    exact hcomm
  have hbc : b ∉ Subgroup.zpowers c := fun h => hb1 (Subgroup.mem_bot.mp
    (hLC ▸ Subgroup.mem_inf.mpr ⟨hbL, Subgroup.zpowers_le.mpr hcC h⟩))
  have h9 : Nat.card (Subgroup.closure ({c, b} : Set H)) = 9 :=
    Item424Proof.card_closure_pair_eq_nine hAe hA27 hcA hbA hc1 hbc
  have hclLC : Subgroup.closure ({c, b} : Set H) ≤ L ⊔ Subgroup.centralizer (L : Set H) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact Subgroup.mem_sup_right hcC
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.mem_sup_left hbL
  have hAeq : A = Subgroup.closure ({c, b, a} : Set H) :=
    Item424Proof.eq_closure_triple hA27 hcA hbA haA h9 fun h => haLC (hclLC h)
  obtain ⟨g₀, hg₀L, hg₀b, hg₀a⟩ := exists_transvection hK hq hLC hEcomm hbL hb1 hb3' haLC
    hYb hYa (mk_mem_range_pglHomP hbA hYb) (mk_mem_range_pglHomP haA hYa) hζ'1 hζ'
  have hLc : ∀ g ∈ L, g * c * g⁻¹ = c := fun g hg => by
    rw [Subgroup.mem_centralizer_iff.mp hcC g hg, mul_inv_cancel_right]
  have hg₀bc : Commute g₀ b := by
    show g₀ * b = b * g₀
    calc g₀ * b = g₀ * b * g₀⁻¹ * g₀ := by group
      _ = b * g₀ := by rw [hg₀b]
  have hg₀pow : ∀ k : ℕ, g₀ ^ k * a * (g₀ ^ k)⁻¹ = b ^ k * a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hbk : g₀ * b ^ k * g₀⁻¹ = b ^ k := by
        rw [(hg₀bc.pow_right k).eq, mul_inv_cancel_right]
      calc g₀ ^ (k + 1) * a * (g₀ ^ (k + 1))⁻¹ = g₀ * (g₀ ^ k * a * (g₀ ^ k)⁻¹) * g₀⁻¹ := by
            group
        _ = g₀ * (b ^ k * a) * g₀⁻¹ := by rw [ih]
        _ = (g₀ * b ^ k * g₀⁻¹) * (g₀ * a * g₀⁻¹) := by group
        _ = b ^ (k + 1) * a := by rw [hbk, hg₀a, pow_succ, mul_assoc]
  have hg₀N : g₀ ∈ Subgroup.normalizer (A : Set H) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hle : A ≤ A.comap (MulAut.conj g₀).toMonoidHom := by
      conv_lhs => rw [hAeq]
      rw [Subgroup.closure_le]
      intro y hy
      change g₀ * y * g₀⁻¹ ∈ A
      rcases hy with hy | hy | hy
      · rw [hy, hLc g₀ hg₀L]
        exact hcA
      · rw [hy, hg₀b]
        exact hbA
      · rw [Set.mem_singleton_iff.mp hy, hg₀a]
        exact mul_mem hbA haA
    exact hle hx
  set σ₀ : MulAut A := A.normalizerMonoidHom ⟨g₀, hg₀N⟩ with hσ₀
  have hσ₀In : σ₀ ∈ autIn L A := mem_autIn_iff.mpr ⟨g₀, hg₀N, hg₀L, rfl⟩
  have hpowN : ∀ k : ℕ, σ₀ ^ k = A.normalizerMonoidHom ⟨g₀ ^ k, pow_mem hg₀N k⟩ := by
    intro k
    rw [hσ₀, ← map_pow]
    rfl
  have hagree : ∀ (g : H) (hgN : g ∈ Subgroup.normalizer (A : Set H)), g ∈ L →
      g * b * g⁻¹ = b → ∀ k : ℕ, g * a * g⁻¹ = b ^ k * a →
        A.normalizerMonoidHom ⟨g, hgN⟩ = σ₀ ^ k := by
    intro g hgN hgL hgb k hga
    rw [hpowN k]
    refine normalizerMonoidHom_eq_of_closure hAeq hgN (pow_mem hg₀N k) fun x hx => ?_
    rcases hx with hx | hx | hx
    · rw [hx, hLc g hgL, hLc _ (pow_mem hg₀L k)]
    · rw [hx, hgb, (hg₀bc.pow_left k).eq, mul_inv_cancel_right]
    · rw [Set.mem_singleton_iff.mp hx, hga, hg₀pow k]
  have hσ₀3 : σ₀ ^ 3 = 1 := by
    have h1 := hagree 1 (one_mem _) (one_mem _) (by group) 3 (by rw [hb3']; group)
    rw [← h1]
    exact map_one _
  have hσ₀1 : σ₀ ≠ 1 := by
    intro h
    have h1 := congrArg (fun φ : MulAut A => ((φ ⟨a, haA⟩ : A) : H)) h
    change g₀ * a * g₀⁻¹ = a at h1
    rw [hg₀a] at h1
    exact hb1 (mul_eq_right.mp h1)
  have hσ₀ord : orderOf σ₀ = 3 := orderOf_eq_prime hσ₀3 hσ₀1
  have hsub : autIn L A ≤ Subgroup.zpowers σ₀ := by
    intro σ hσ
    obtain ⟨g, hgN, hgL, rfl⟩ := mem_autIn_iff.mp hσ
    have hgA : ∀ x ∈ A, g * x * g⁻¹ ∈ A := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
    have hgbz : g * b * g⁻¹ ∈ Subgroup.zpowers b := by
      rw [← hAL]
      exact Subgroup.mem_inf.mpr ⟨hgA b hbA, hLn.conj_mem _ hbL g⟩
    have hgaz : g * a * g⁻¹ * a⁻¹ ∈ Subgroup.zpowers b := by
      rw [← hAL]
      refine Subgroup.mem_inf.mpr ⟨A.mul_mem (hgA a haA) (A.inv_mem haA), ?_⟩
      have e1 : g * a * g⁻¹ * a⁻¹ = g * (a * g⁻¹ * a⁻¹) := by group
      rw [e1]
      exact L.mul_mem hgL (hLn.conj_mem _ (L.inv_mem hgL) a)
    obtain ⟨j, hj'⟩ := mem_powers_iff_mem_zpowers.mpr hgbz
    obtain ⟨k, hk'⟩ := mem_powers_iff_mem_zpowers.mpr hgaz
    have hj : b ^ j = g * b * g⁻¹ := hj'
    have hk : b ^ k = g * a * g⁻¹ * a⁻¹ := hk'
    have hga : g * a * g⁻¹ = b ^ k * a := by rw [hk]; group
    have hmod := modEq_of_heis hK hq hgL hYb hYa hζ'1 hζ'3 hζ'
      (show g * b * g⁻¹ = b ^ j * a ^ 0 by rw [pow_zero, mul_one, hj])
      (show g * a * g⁻¹ = b ^ k * a ^ 1 by rw [pow_one, hga])
    have hj1 : j % 3 = 1 := by
      have h1 : (1 + 0 * k) % 3 = (j * 1) % 3 := hmod
      simp only [zero_mul, add_zero, mul_one] at h1
      omega
    have hgb : g * b * g⁻¹ = b := by
      rw [← hj, ← pow_mod_orderOf, hb3, hj1, pow_one]
    rw [hagree g hgN hgL hgb k hga]
    exact Subgroup.npow_mem_zpowers σ₀ k
  have hAut : autIn L A = Subgroup.zpowers σ₀ :=
    le_antisymm hsub (Subgroup.zpowers_le.mpr hσ₀In)
  have hcard : Nat.card (autIn L A) = 3 := by rw [hAut, Nat.card_zpowers, hσ₀ord]
  have hZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hca : c * a = a * c := hAcomm c hcA a haA
  have hALeq : A ⊔ L = Subgroup.zpowers c ⊔ (L ⊔ Subgroup.zpowers a) := by
    apply le_antisymm
    · refine sup_le ?_ (le_sup_left.trans le_sup_right)
      rw [hAeq, Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx | hx
      · rw [hx]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
      · rw [hx]
        exact Subgroup.mem_sup_right (Subgroup.mem_sup_left hbL)
      · rw [Set.mem_singleton_iff.mp hx]
        exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    · refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hcA))
        (sup_le le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left haA)))
  exact ⟨isZ3PGLThreePi_sup hK hq hLC hc3 hcC hca ha3 haLC hYa hALeq,
    ⟨mulEquivOfPrimeCardEq hcard hZ3⟩⟩

section Certs


theorem k423SLThree_of_typeC (h45 : Item4_5) (hC : K423TypeCAlpha) (hCSL : K423TypeCAlphaSL) :
    K423SLThree :=
  k423SLThree_of h45 hC hCSL k423L3HeisFrame_holds k423L3TypeThreeFrame_holds
    k423SL3TypeThreeFrame_holds

end Certs

end CFSG.RankThree.PartTwo.Sec4

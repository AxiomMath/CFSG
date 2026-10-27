module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec14

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

namespace L3PGL

variable {K : Type} [Field K]

theorem eq_zero_of_mul_eq_mul {x a b : K} (hab : a ≠ b) (h : x * a = b * x) : x = 0 := by
  have h' : x * (a - b) = 0 := by rw [mul_sub, h, mul_comm, sub_self]
  exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr hab)

theorem shape_of_mul_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {w : Matrix (Fin 3) (Fin 3) K}
    (h : w * diagonal ![τ, τ ^ 2, 1] = τ ^ 2 • (diagonal ![τ, τ ^ 2, 1] * w)) :
    w = !![0, 0, w 0 2; w 1 0, 0, 0; 0, w 2 1, 0] := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h2
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h2, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h2
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h2, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have e : ∀ i j, w i j * ![τ, τ ^ 2, 1] j = τ ^ 2 * ![τ, τ ^ 2, 1] i * w i j := by
    intro i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_mul, smul_eq_mul] at this
    rw [this]
    ring
  have h4 : τ ^ 4 = τ := by rw [show τ ^ 4 = τ ^ 3 * τ by ring, hτ, one_mul]
  have v0 : (![τ, τ ^ 2, 1] : Fin 3 → K) 0 = τ := rfl
  have v1 : (![τ, τ ^ 2, 1] : Fin 3 → K) 1 = τ ^ 2 := rfl
  have v2 : (![τ, τ ^ 2, 1] : Fin 3 → K) 2 = 1 := rfl
  have m00 : w 0 0 = 0 := eq_zero_of_mul_eq_mul (b := 1) hτ1 (by
    have := e 0 0
    rw [v0] at this
    rw [this, show τ ^ 2 * τ = τ ^ 3 by ring, hτ])
  have m01 : w 0 1 = 0 := eq_zero_of_mul_eq_mul (b := 1) hτ2 (by
    have := e 0 1
    rw [v0, v1] at this
    rw [this, show τ ^ 2 * τ = τ ^ 3 by ring, hτ])
  have m11 : w 1 1 = 0 := eq_zero_of_mul_eq_mul (b := τ) (Ne.symm hττ2) (by
    have := e 1 1
    rw [v1] at this
    rw [this, show τ ^ 2 * τ ^ 2 = τ ^ 4 by ring, h4])
  have m12 : w 1 2 = 0 := eq_zero_of_mul_eq_mul (b := τ) (Ne.symm hτ1) (by
    have := e 1 2
    rw [v1, v2] at this
    rw [this, show τ ^ 2 * τ ^ 2 = τ ^ 4 by ring, h4])
  have m20 : w 2 0 = 0 := eq_zero_of_mul_eq_mul (b := τ ^ 2) hττ2 (by
    have := e 2 0
    rw [v0, v2] at this
    rw [this, mul_one])
  have m22 : w 2 2 = 0 := eq_zero_of_mul_eq_mul (b := τ ^ 2) (Ne.symm hτ2) (by
    have := e 2 2
    rw [v2] at this
    rw [this, mul_one])
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m00, m01, m11, m12, m20, m22]

variable {π : Bool} {p f : ℕ}

theorem mem_rootsOfUnity_qSubPi (hK : PiField π p f K) {u : Kˣ}
    (hu : ∀ h : UnitaryFieldData p f K, π = false → h.bar (u : K) * u = 1) :
    u ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  have := hK.finite
  have := Fintype.ofFinite K
  rw [mem_rootsOfUnity]
  cases π
  · have h := hK.unitary
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, qSubPi, Bool.cond_false, pow_succ,
      ← h.bar_apply]
    exact hu h rfl
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, qSubPi, Bool.cond_true]
    have hc : Fintype.card K = p ^ f := by
      rw [← Nat.card_eq_fintype_card, hK.card]
      rfl
    rw [← hc]
    exact FiniteField.pow_card_sub_one_eq_one _ u.ne_zero

theorem exists_std_form (hK : PiField π p f K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {w s g₁ z₀ : GL (Fin 3) K} (hw : w ∈ glPi π 3 (p ^ f) K) (hg₁ : g₁ ∈ glPi π 3 (p ^ f) K)
    (hz₀ : z₀ ∈ StatedScalars (Fin 3) K) (hD : g₁⁻¹ * (s * z₀) * g₁ = diagTau hτ)
    {τu : Kˣ} (hτu : (τu : K) = τ)
    (hws : w * s * w⁻¹ = GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * s) :
    ∃ (g : GL (Fin 3) K) (_ : g ∈ glPi π 3 (p ^ f) K) (β : K) (cβ : GL (Fin 3) K),
      cβ ∈ glPi π 3 (p ^ f) K ∧ (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β ∧
        g⁻¹ * w * g = cβ ∧ g⁻¹ * (s * z₀) * g = diagTau hτ := by
  set lu := τu ^ 2 with hlu
  set z := GeneralLinearGroup.scalar (Fin 3) lu with hz
  have hzc : ∀ x : GL (Fin 3) K, x * z = z * x := fun x =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar lu x).eq
  have hz₀c : ∀ x : GL (Fin 3) K, x * z₀ = z₀ * x := fun x =>
    commute_of_mem_statedScalars hz₀ x
  set w' := g₁⁻¹ * w * g₁ with hw'
  have hw'H : w' ∈ glPi π 3 (p ^ f) K := mul_mem (mul_mem (inv_mem hg₁) hw) hg₁
  set D := diagTau hτ with hDdef
  have hws' : w * (s * z₀) = z * ((s * z₀) * w) := by
    have h1 : w * s = z * (s * w) := by
      calc w * s = w * s * w⁻¹ * w := by group
        _ = z * (s * w) := by rw [hws]; group
    calc w * (s * z₀) = (w * s) * z₀ := by group
      _ = z * (s * w) * z₀ := by rw [h1]
      _ = z * (s * (w * z₀)) := by group
      _ = z * (s * (z₀ * w)) := by rw [hz₀c w]
      _ = z * ((s * z₀) * w) := by group
  have hsz : s * z₀ = g₁ * D * g₁⁻¹ := by rw [← hD]; group
  have hw'D : w' * D = z * (D * w') := by
    rw [hsz] at hws'
    calc w' * D = g₁⁻¹ * (w * (g₁ * D * g₁⁻¹)) * g₁ := by rw [hw']; group
      _ = g₁⁻¹ * (z * (g₁ * D * g₁⁻¹ * w)) * g₁ := by rw [hws']
      _ = g₁⁻¹ * z * g₁ * (D * w') := by rw [hw']; group
      _ = z * (D * w') := by
          rw [mul_assoc g₁⁻¹ z g₁, ← hzc g₁]
          group
  have hshape : (w' : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, (w' : Matrix (Fin 3) (Fin 3) K) 0 2; (w' : Matrix (Fin 3) (Fin 3) K) 1 0, 0, 0;
        0, (w' : Matrix (Fin 3) (Fin 3) K) 2 1, 0] := by
    refine shape_of_mul_diagTau hτ hτ1 ?_
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hw'D
    simp only [Units.val_mul] at this
    rw [hDdef, coe_diagTau_eq_diagonal] at this
    rw [this, hz, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul, hlu,
      Units.val_pow_eq_pow_val, hτu]
  set a := (w' : Matrix (Fin 3) (Fin 3) K) 1 0 with ha
  set b := (w' : Matrix (Fin 3) (Fin 3) K) 2 1 with hb
  set c := (w' : Matrix (Fin 3) (Fin 3) K) 0 2 with hc
  have hdet : (w' : Matrix (Fin 3) (Fin 3) K).det = a * b * c := by
    rw [hshape, Matrix.det_fin_three]
    simp
    ring
  have hdet0 : (w' : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (w'.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  rw [hdet] at hdet0
  have ha0 : a ≠ 0 := fun h0 => hdet0 (by rw [h0]; ring)
  have hb0 : b ≠ 0 := fun h0 => hdet0 (by rw [h0]; ring)
  have hnorm : ∀ h : UnitaryFieldData p f K, π = false →
      h.bar a * a = 1 ∧ h.bar b * b = 1 := by
    intro h hπ
    subst hπ
    have hu := (mem_glPi_false h).mp hw'H
    have e00 := congrFun (congrFun hu 0) 0
    have e11 := congrFun (congrFun hu 1) 1
    rw [hshape] at e00 e11
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] at e00 e11
    exact ⟨e00, e11⟩
  set au := Units.mk0 a ha0 with hau
  set bu := Units.mk0 b hb0 with hbu
  have haR : au ∈ rootsOfUnity (qSubPi π (p ^ f)) K :=
    mem_rootsOfUnity_qSubPi hK fun h hπ => (hnorm h hπ).1
  have hbR : bu ∈ rootsOfUnity (qSubPi π (p ^ f)) K :=
    mem_rootsOfUnity_qSubPi hK fun h hπ => (hnorm h hπ).2
  set t := diagUnits 1 au (au * bu) with ht
  have htH : t ∈ glPi π 3 (p ^ f) K :=
    diagUnits_mem_glPi hK (one_mem _) haR (mul_mem haR hbR)
  have htinv : t⁻¹ = diagUnits 1 au⁻¹ (au * bu)⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [ht, diagUnits_mul, mul_one, mul_inv_cancel, mul_inv_cancel]
    apply Units.ext
    rw [coe_diagUnits, Units.val_one, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> rfl
  set cβ := t⁻¹ * w' * t with hcβ
  refine ⟨g₁ * t, mul_mem hg₁ htH, a * b * c, cβ, mul_mem (mul_mem (inv_mem htH) hw'H) htH, ?_,
    ?_, ?_⟩
  · rw [hcβ, Units.val_mul, Units.val_mul, htinv, ht, coe_diagUnits, coe_diagUnits, hshape]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisC, Matrix.mul_apply, Matrix.diagonal_apply, hau, hbu] <;>
      field_simp
  · rw [hcβ, hw']
    group
  · have htD : t⁻¹ * D * t = D := by
      have h1 : D * t = t * D := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hDdef, coe_diagTau_eq_diagonal, ht, coe_diagUnits,
          Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        exact mul_comm _ _
      calc t⁻¹ * D * t = t⁻¹ * (D * t) := by group
        _ = t⁻¹ * (t * D) := by rw [h1]
        _ = D := by group
    calc (g₁ * t)⁻¹ * (s * z₀) * (g₁ * t) = t⁻¹ * (g₁⁻¹ * (s * z₀) * g₁) * t := by group
      _ = D := by rw [hD, htD]

theorem map_le_of_map_symm_le {M : Type*} [Group M] [Finite M] {σ : MulAut M}
    {X : Subgroup M} (h : X.map σ.symm.toMonoidHom ≤ X) : X.map σ.toMonoidHom ≤ X := by
  have heq : X.map σ.symm.toMonoidHom = X := Subgroup.eq_of_le_of_card_ge h (by
    rw [Subgroup.card_map_of_injective σ.symm.injective])
  rintro _ ⟨x, hx, rfl⟩
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem conjM'_inv (hπ : π = false → UnitaryFieldData p f K) {y : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K) :
    Res8Hess.conjM' hπ (inv_mem hy) = (Res8Hess.conjM' hπ hy).symm := by
  ext m
  rw [Res8Hess.coe_conjM', map_inv, inv_inv]
  rfl

theorem conjM'_comm (hπ : π = false → UnitaryFieldData p f K) {a b g : GL (Fin 3) K}
    (ha : a ∈ glPi π 3 (p ^ f) K) (hb : b ∈ glPi π 3 (p ^ f) K) (hg : g ∈ glPi π 3 (p ^ f) K)
    (h : ProjGenLinGroup.mk (a * g) = ProjGenLinGroup.mk (g * b))
    (m : projImage (slPi π 3 (p ^ f) K)) :
    Res8Hess.conjM' hπ ha (Res8Hess.conjM' hπ hg m) =
      Res8Hess.conjM' hπ hg (Res8Hess.conjM' hπ hb m) := by
  apply Subtype.ext
  rw [Res8Hess.coe_conjM', Res8Hess.coe_conjM', Res8Hess.coe_conjM', Res8Hess.coe_conjM']
  rw [map_mul, map_mul] at h
  calc ProjGenLinGroup.mk a * (ProjGenLinGroup.mk g * (m : ProjGenLinGroup (Fin 3) K) *
        (ProjGenLinGroup.mk g)⁻¹) * (ProjGenLinGroup.mk a)⁻¹ =
      (ProjGenLinGroup.mk a * ProjGenLinGroup.mk g) * (m : ProjGenLinGroup (Fin 3) K) *
        (ProjGenLinGroup.mk a * ProjGenLinGroup.mk g)⁻¹ := by group
    _ = (ProjGenLinGroup.mk g * ProjGenLinGroup.mk b) * (m : ProjGenLinGroup (Fin 3) K) *
        (ProjGenLinGroup.mk g * ProjGenLinGroup.mk b)⁻¹ := by rw [h]
    _ = _ := by group

theorem map_conjM'_mem_invSet142 (hπ : π = false → UnitaryFieldData p f K)
    {y s c d g : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K) (hs : s ∈ glPi π 3 (p ^ f) K)
    (hc : c ∈ glPi π 3 (p ^ f) K) (hd : d ∈ glPi π 3 (p ^ f) K) (hg : g ∈ glPi π 3 (p ^ f) K)
    (hyg : ProjGenLinGroup.mk (y * g) = ProjGenLinGroup.mk (g * c))
    (hsg : ProjGenLinGroup.mk (s * g) = ProjGenLinGroup.mk (g * d))
    {X : Subgroup (projImage (slPi π 3 (p ^ f) K))}
    (hX : X ∈ invSet142 (Res8Hess.conjM' hπ hc) (Res8Hess.conjM' hπ hd)) :
    X.map (Res8Hess.conjM' hπ hg).toMonoidHom ∈
      invSet142 (Res8Hess.conjM' hπ hy) (Res8Hess.conjM' hπ hs) := by
  obtain ⟨h3, hcX, hdX⟩ := hX
  refine ⟨?_, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective (Res8Hess.conjM' hπ hg).injective]
  · rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨Res8Hess.conjM' hπ hc m, hcX ⟨m, hm, rfl⟩, ?_⟩
    exact (conjM'_comm hπ hy hc hg hyg m).symm
  · rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨Res8Hess.conjM' hπ hd m, hdX ⟨m, hm, rfl⟩, ?_⟩
    exact (conjM'_comm hπ hs hd hg hsg m).symm

end L3PGL

open L3PGL in
theorem ks142L3PGLGenModel_of_std (hstd : KS142L3PGLGenStd) : KS142L3PGLGenModel := by
  intro π p f K _ hπ hK hq hperf y s hy hs hy3 hsSL hsZ hs3 hys
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hK.three_ne_zero hq
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hK hq
  obtain ⟨ℓ, hℓ⟩ := hys
  have hysl : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ * s := by
    rw [hℓ]
    group
  have hℓ3 : ℓ ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hysl
  have hsdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hsSL).2
  have hℓ1 : ℓ ≠ 1 := by
    intro h1
    refine Sec12.KS128NotHJTC.false_of_commute_irreducible hτ₀ hτ₀1 h3 hsdet hs3 hsZ ?_ hy3.2.2
    rw [h1, map_one, one_mul] at hysl
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [hysl]
  obtain ⟨τ, hτ, hτ1, z₀, hz₀, g₁, hg₁, hD⟩ := Proof142Res.type1_of_commute_mod_type3 hK hq hy3
    hsSL hsZ hs3 ⟨ℓ, hℓ⟩
  have hz₀S : z₀ ∈ StatedScalars (Fin 3) K := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz₀
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hτ, Units.val_one])
  have hτu1 : τu ≠ 1 := fun h => hτ1 (by
    have := congrArg Units.val h
    rwa [hτu, Units.val_mk0, Units.val_one] at this)
  have hdG : diagTau hτ ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ (diagTau_mem_slPi hπ hq' hτ)
  have hsg' : ∀ g : GL (Fin 3) K, g⁻¹ * (s * z₀) * g = diagTau hτ →
      ProjGenLinGroup.mk (s * g) = ProjGenLinGroup.mk (g * diagTau hτ) := by
    intro g hg
    have e : s * g = g * diagTau hτ * z₀⁻¹ := by
      rw [← hg]
      have hc := commute_of_mem_statedScalars hz₀S g
      calc s * g = s * (g * z₀) * z₀⁻¹ := by group
        _ = s * (z₀ * g) * z₀⁻¹ := by rw [hc]
        _ = g * (g⁻¹ * (s * z₀) * g) * z₀⁻¹ := by group
    rw [e, map_mul, map_inv, mk_eq_one_iff_mem_statedScalars.mpr hz₀S, inv_one, mul_one]
  have key : ∀ (w : GL (Fin 3) K) (hw : w ∈ glPi π 3 (p ^ f) K),
      w * s * w⁻¹ = GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * s →
      (∀ ν : K, (w : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν • 1 → ∀ μ : K, μ ^ 3 ≠ ν) →
      sSup (invSet142 (Res8Hess.conjM' hπ hw) (Res8Hess.conjM' hπ hs)) = ⊤ := by
    intro w hw hws hwc
    obtain ⟨g, hg, β, cβ, hcβH, hcβm, hgw, hgs⟩ :=
      exists_std_form hK hτ hτ1 hw hg₁ hz₀S hD rfl hws
    have hw3 : (w : Matrix (Fin 3) (Fin 3) K) ^ 3 = β • 1 := by
      have e : w = g * cβ * g⁻¹ := by rw [← hgw]; group
      rw [e, ← Units.val_pow_eq_pow_val, conj_pow, Units.val_mul, Units.val_mul,
        Units.val_pow_eq_pow_val, hcβm, heisC_pow_three, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hβ : ¬ ∃ μ : K, μ ^ 3 = β := fun ⟨μ, hμ⟩ => hwc β hw3 μ hμ
    have htop := hstd π p f K hπ hK hq hperf τ hτ hτ1 β cβ hcβH hdG hcβm hβ
    have hwg : ProjGenLinGroup.mk (w * g) = ProjGenLinGroup.mk (g * cβ) := by
      rw [← hgw]
      congr 1
      group
    rw [eq_top_iff, ← htop]
    have hle : (sSup (invSet142 (Res8Hess.conjM' hπ hcβH) (Res8Hess.conjM' hπ hdG))).map
        (Res8Hess.conjM' hπ hg).toMonoidHom ≤
        sSup (invSet142 (Res8Hess.conjM' hπ hw) (Res8Hess.conjM' hπ hs)) := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun X hX => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup (map_conjM'_mem_invSet142 hπ hw hs hcβH hdG hg hwg (hsg' g hgs) hX)
    intro m _
    have hm : (Res8Hess.conjM' hπ hg).symm m ∈ (⊤ : Subgroup _) := Subgroup.mem_top _
    rw [← htop] at hm
    have := hle ⟨_, hm, rfl⟩
    simpa using this
  have hy3' : ∀ ν : K, (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν • 1 → ∀ μ : K, μ ^ 3 ≠ ν :=
    fun ν hν => Sec12.KS128NotHJTC.not_cube_of_irreducible hτ₀ hτ₀1 h3 hν hy3.2.2
  rcases Res8Hess.mul_eq_one_or_of_cube hℓ3 hτu3 hℓ1 hτu1 with h | h
  ·
    have hℓτ : ℓ = τu ^ 2 := by
      have : ℓ = τu⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this, inv_eq_of_mul_eq_one_right (show τu * τu ^ 2 = 1 by rw [← pow_succ']; exact hτu3)]
    exact key y hy (by rw [hysl, hℓτ]) hy3'
  ·
    have hℓτ : ℓ⁻¹ = τu ^ 2 := by
      have : ℓ = (τu ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this, inv_inv]
    have hyi : y⁻¹ * s * y⁻¹⁻¹ = GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * s := by
      rw [← hℓτ, inv_inv, map_inv]
      have hsc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ℓ y⁻¹).eq
      calc y⁻¹ * s * y = y⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ℓ)⁻¹ *
            (y * s * y⁻¹) * y := by rw [hysl]; group
        _ = (GeneralLinearGroup.scalar (Fin 3) ℓ)⁻¹ * s := by
            rw [show y⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ℓ)⁻¹ =
              (GeneralLinearGroup.scalar (Fin 3) ℓ)⁻¹ * y⁻¹ by
                rw [← map_inv, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ℓ⁻¹ y⁻¹).eq]]
            group
    have hyic : ∀ ν : K, ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν • 1 →
        ∀ μ : K, μ ^ 3 ≠ ν := by
      intro ν hν μ hμ
      have hν0 : ν ≠ 0 := by
        rintro rfl
        have := congrArg Matrix.det hν
        rw [zero_smul, Matrix.det_zero, Matrix.det_pow] at this
        exact ((y⁻¹).isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
          (pow_eq_zero_iff (by norm_num) |>.mp this)
      have hy3m : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν⁻¹ • 1 := by
        have e : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 * ((y⁻¹ : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
          rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
            inv_pow, mul_inv_cancel, Units.val_one]
        rw [hν, Matrix.mul_smul, Matrix.mul_one] at e
        calc (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν⁻¹ • (ν • (y : Matrix (Fin 3) (Fin 3) K) ^ 3) :=
              by rw [smul_smul, inv_mul_cancel₀ hν0, one_smul]
          _ = ν⁻¹ • 1 := by rw [e]
      exact hy3' ν⁻¹ hy3m μ⁻¹ (by rw [inv_pow, hμ])
    have htop := key y⁻¹ (inv_mem hy) hyi hyic
    rw [eq_top_iff, ← htop]
    refine sSup_le fun X hX => le_sSup ⟨hX.1, ?_, hX.2.2⟩
    have h1 := hX.2.1
    rw [conjM'_inv hπ hy] at h1
    exact map_le_of_map_symm_le h1

end CFSG.RankThree.PartTwo.Sec14

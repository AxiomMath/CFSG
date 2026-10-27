module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseIb

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Two

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

variable {K : Type} [Field K]

theorem eq_zero_of_commute_diagonal {d : Fin 3 → K} (hd : Function.Injective d)
    {N : Matrix (Fin 3) (Fin 3) K} (hc : diagonal d * N = N * diagonal d) (hN : N * N = 0) :
    N = 0 := by
  have hoff : ∀ i j, i ≠ j → N i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hc i) j
    rw [diagonal_mul, mul_diagonal] at h
    have h' : (d i - d j) * N i j = 0 := by rw [sub_mul, h, mul_comm, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd (hd (sub_eq_zero.mp h0)) hij
    · exact h0
  ext i j
  by_cases hij : i = j
  · subst hij
    have h := congrFun (congrFun hN i) i
    rw [mul_apply, Fin.sum_univ_three] at h
    have hsq : N i i * N i i = 0 := by
      fin_cases i <;> simp [hoff _ _ (by decide : (0 : Fin 3) ≠ 1),
        hoff _ _ (by decide : (0 : Fin 3) ≠ 2), hoff _ _ (by decide : (1 : Fin 3) ≠ 0),
        hoff _ _ (by decide : (1 : Fin 3) ≠ 2), hoff _ _ (by decide : (2 : Fin 3) ≠ 0),
        hoff _ _ (by decide : (2 : Fin 3) ≠ 1)] at h ⊢ <;> exact h
    rw [Matrix.zero_apply]
    exact mul_self_eq_zero.mp hsq
  · rw [Matrix.zero_apply]
    exact hoff i j hij

theorem injective_diagTau_entries {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Function.Injective ![τ, τ ^ 2, (1 : K)] := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h12 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [mul_one, ← pow_two, ← h]
    exact (mul_left_cancel₀ hτ0 this)
  have h23 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem eq_zero_of_commute_type1 {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {x : GL (Fin 3) K} (hx : Type123 π (p ^ f) K x 1)
    {N : Matrix (Fin 3) (Fin 3) K} (hc : (x : Matrix (Fin 3) (Fin 3) K) * N = N * x)
    (hN : N * N = 0) : N = 0 := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, -, hD⟩ := hx
  obtain ⟨ζ, rfl⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  set M : Matrix (Fin 3) (Fin 3) K := ((x * GeneralLinearGroup.scalar (Fin 3) ζ :
    GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hMN : M * N = N * M := by
    rw [hM, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hc]
  set Gm : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) with hGm
  set Gi : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hGi
  have hgg : Gm * Gi = 1 := by rw [hGm, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgg' : Gi * Gm = 1 := by rw [hGm, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ X : Matrix (Fin 3) (Fin 3) K, Gm * (Gi * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]
  have hD' : Gi * M * Gm = diagonal ![τ, τ ^ 2, 1] := by
    rw [← coe_diagTau_eq_diagonal hτ, ← hD]
    simp [hM, hGm, hGi, Units.val_mul, Matrix.mul_assoc]
  set N' : Matrix (Fin 3) (Fin 3) K := Gi * N * Gm with hN'
  have hcomm' : diagonal ![τ, τ ^ 2, 1] * N' = N' * diagonal ![τ, τ ^ 2, 1] := by
    rw [← hD', hN']
    simp only [Matrix.mul_assoc, key]
    rw [← Matrix.mul_assoc M N Gm, hMN, Matrix.mul_assoc N M Gm]
  have hsq' : N' * N' = 0 := by
    rw [hN']
    simp only [Matrix.mul_assoc, key]
    rw [← Matrix.mul_assoc N N Gm, hN, Matrix.zero_mul, Matrix.mul_zero]
  have h0 := eq_zero_of_commute_diagonal (injective_diagTau_entries hτ hτ1) hcomm' hsq'
  calc N = Gm * N' * Gi := by
        rw [hN']
        simp only [Matrix.mul_assoc, key, hgg, Matrix.mul_one]
    _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]

theorem eq_zero_of_commute_type3 {π : Bool} {q : ℕ} {x : GL (Fin 3) K}
    (hx : Type123 π q K x 3) {N : Matrix (Fin 3) (Fin 3) K}
    (hc : (x : Matrix (Fin 3) (Fin 3) K) * N = N * x) (hN : N * N = 0) : N = 0 := by
  obtain ⟨-, -, hirr⟩ := hx
  set W : Submodule K (Fin 3 → K) := LinearMap.ker (Matrix.toLin' N) with hW
  have hmemW : ∀ v, v ∈ W ↔ N *ᵥ v = 0 := fun v => by
    rw [hW, LinearMap.mem_ker, Matrix.toLin'_apply]
  have hinv : ∀ v ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
    intro v hv
    rw [hmemW] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  by_contra hN0
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, N *ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hN0
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  rcases hirr W hinv with h | h
  · apply hv
    have hNv : N *ᵥ v ∈ W := by
      rw [hmemW, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
    rw [h] at hNv
    exact (Submodule.mem_bot K).mp hNv
  · apply hv
    have : v ∈ W := by rw [h]; exact Submodule.mem_top
    exact (hmemW v).mp this

theorem two_eq_zero_of_piField {π : Bool} {f : ℕ} (hK : PiField π 2 f K) : (2 : K) = 0 := by
  have := hK.finite
  have := Fintype.ofFinite K
  have hcard := FiniteField.cast_card_eq_zero K
  have hk : ∃ k : ℕ, 0 < k ∧ Fintype.card K = 2 ^ k := by
    have h := hK.card
    rw [Nat.card_eq_fintype_card] at h
    have hf := hK.one_le
    cases π
    · exact ⟨2 * f, by omega, by rw [h, piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
    · exact ⟨f, by omega, h⟩
  obtain ⟨k, hk0, hk⟩ := hk
  rw [hk, Nat.cast_pow, Nat.cast_ofNat] at hcard
  exact pow_eq_zero_iff (by omega) |>.mp hcard

theorem false_of_involution_commute {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (h2 : (2 : K) = 0) {y s : GL (Fin 3) K}
    (hy : Type123 π (p ^ f) K y 1 ∨ Type123 π (p ^ f) K y 3) (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hc : y * s = s * y) : False := by
  set N : Matrix (Fin 3) (Fin 3) K := (s : Matrix (Fin 3) (Fin 3) K) - 1 with hNdef
  have hN0 : N ≠ 0 := fun h => hs1 (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h))
  have hss : (s : Matrix (Fin 3) (Fin 3) K) * s = 1 := by
    rw [← Units.val_mul, hs2, Units.val_one]
  have hadd : ∀ X : Matrix (Fin 3) (Fin 3) K, X + X = 0 := fun X => by
    rw [← two_smul K X, h2, zero_smul]
  have hNN : N * N = 0 := by
    have : N * N = (1 + 1) - ((s : Matrix (Fin 3) (Fin 3) K) + s) := by
      rw [hNdef, sub_mul, mul_sub, mul_sub, hss, one_mul, mul_one, mul_one]
      abel
    rw [this, hadd, hadd, sub_zero]
  have hcN : (y : Matrix (Fin 3) (Fin 3) K) * N = N * y := by
    rw [hNdef, mul_sub, sub_mul, ← Units.val_mul, hc, Units.val_mul, mul_one, one_mul]
  rcases hy with hy | hy
  · exact hN0 (eq_zero_of_commute_type1 hK hq hy hcN hNN)
  · exact hN0 (eq_zero_of_commute_type3 hy hcN hNN)

theorem false_of_commute_mod_scalars {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (h2 : (2 : K) = 0) {y s : GL (Fin 3) K}
    (hy : Type123 π (p ^ f) K y 1 ∨ Type123 π (p ^ f) K y 3)
    (hs2 : s * s ∈ StatedScalars (Fin 3) K) (hs1 : s ∉ StatedScalars (Fin 3) K)
    (hc : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K) : False := by
  have := hK.finite
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hsc : ∀ (c : Kˣ) (g : GL (Fin 3) K),
      g * GeneralLinearGroup.scalar (Fin 3) c = GeneralLinearGroup.scalar (Fin 3) c * g :=
    fun c g => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c g).eq
  obtain ⟨ν, hν⟩ := hs2
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨l, hl⟩ := isSquare_of_charTwo' (ν : K)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hl
    exact ν.ne_zero hl
  set w : Kˣ := Units.mk0 l hl0 with hw
  have hνw : ν = w * w := Units.ext (by rw [Units.val_mul, hw, Units.val_mk0]; exact hl)
  set s' : GL (Fin 3) K := s * GeneralLinearGroup.scalar (Fin 3) w⁻¹ with hs'
  have hs's' : s' * s' = 1 := by
    rw [hs', show s * GeneralLinearGroup.scalar (Fin 3) w⁻¹ * (s *
        GeneralLinearGroup.scalar (Fin 3) w⁻¹) = (s * s) *
        (GeneralLinearGroup.scalar (Fin 3) w⁻¹ * GeneralLinearGroup.scalar (Fin 3) w⁻¹) by
      rw [mul_assoc, ← mul_assoc (GeneralLinearGroup.scalar (Fin 3) w⁻¹) s, ← hsc]
      group]
    rw [← hν, ← map_mul, ← map_mul, hνw]
    simp
  have hs'1 : s' ≠ 1 := by
    intro h
    apply hs1
    have : s = GeneralLinearGroup.scalar (Fin 3) w := by
      rw [hs'] at h
      calc s = s * GeneralLinearGroup.scalar (Fin 3) w⁻¹ * GeneralLinearGroup.scalar (Fin 3) w := by
            rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
        _ = GeneralLinearGroup.scalar (Fin 3) w := by rw [h, one_mul]
    rw [this]
    exact ⟨w, rfl⟩
  have hys : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * s := by
    rw [hμ]
    group
  have hys' : y * s' * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * s' := by
    have h1 : y * GeneralLinearGroup.scalar (Fin 3) w⁻¹ * y⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) w⁻¹ := by
      rw [hsc, mul_inv_cancel_right]
    rw [hs', show y * (s * GeneralLinearGroup.scalar (Fin 3) w⁻¹) * y⁻¹ =
        y * s * y⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) w⁻¹ * y⁻¹) by group, hys, h1,
      mul_assoc]
  have hμ2 : GeneralLinearGroup.scalar (Fin 3) (μ * μ) = 1 := by
    have h1 : (y * s' * y⁻¹) * (y * s' * y⁻¹) = 1 := by
      rw [show (y * s' * y⁻¹) * (y * s' * y⁻¹) = y * (s' * s') * y⁻¹ by group, hs's', mul_one,
        mul_inv_cancel]
    rw [hys', show GeneralLinearGroup.scalar (Fin 3) μ * s' *
        (GeneralLinearGroup.scalar (Fin 3) μ * s') = GeneralLinearGroup.scalar (Fin 3) μ *
          GeneralLinearGroup.scalar (Fin 3) μ * (s' * s') by
        rw [mul_assoc, ← mul_assoc s', hsc μ s']
        group, hs's', mul_one, ← map_mul] at h1
    exact h1
  have hμ1 : μ = 1 := by
    have h1 : (μ : K) * μ = 1 := by
      have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hμ2
      simpa [GeneralLinearGroup.coe_scalar] using this
    have h3 : ((μ : K) + 1) * ((μ : K) + 1) = 0 := by
      have : ((μ : K) + 1) * ((μ : K) + 1) = (μ : K) * μ + 1 + 2 * μ := by ring
      rw [this, h1, h2, zero_mul, add_zero, CharTwo.add_self_eq_zero]
    have h4 : (μ : K) + 1 = 0 := mul_self_eq_zero.mp h3
    exact Units.ext (by rw [Units.val_one, ← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]; exact h4)
  rw [hμ1, map_one, one_mul] at hys'
  have hcomm : y * s' = s' * y := by
    calc y * s' = y * s' * y⁻¹ * y := by group
      _ = s' * y := by rw [hys']
  exact false_of_involution_commute hK hq h2 hy hs's' hs'1 hcomm

section Normal

variable {H : Type} [Group H] {L : Subgroup H} [hLn : L.Normal] {π : Bool} {f : ℕ}

theorem eq_one_of_isPGLAt (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (e : L ≃* slPi π 3 (2 ^ f) K) {a : H} {y : GL (Fin 3) K} (hy : IsPGLAt e a y)
    (hyt : Type123 π (2 ^ f) K y 1 ∨ Type123 π (2 ^ f) K y 3) {t : H} (htL : t ∈ L)
    (ht2 : t * t = 1) (hat : a * t = t * a) : t = 1 := by
  by_contra ht1
  set s : slPi π 3 (2 ^ f) K := e ⟨t, htL⟩ with hsdef
  have hs := hy.2 s
  rw [coe_slAct_eq] at hs
  have heq : (⟨a * ((e.symm s : L) : H) * a⁻¹, hLn.conj_mem _ (e.symm s).2 a⟩ : L) =
      ⟨t, htL⟩ := by
    apply Subtype.ext
    rw [hsdef, MulEquiv.symm_apply_apply]
    change a * t * a⁻¹ = t
    rw [hat, mul_inv_cancel_right]
  rw [heq] at hs
  have hc : y * (s : GL (Fin 3) K) = (s : GL (Fin 3) K) * y := by
    calc y * (s : GL (Fin 3) K) = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [← hs]
  have hs2 : (s : GL (Fin 3) K) * s = 1 := by
    rw [← Subgroup.coe_mul, hsdef, ← map_mul,
      show (⟨t, htL⟩ * ⟨t, htL⟩ : L) = 1 from Subtype.ext ht2, map_one, Subgroup.coe_one]
  have hs1 : (s : GL (Fin 3) K) ≠ 1 := by
    intro h
    apply ht1
    have h1 : s = 1 := Subtype.ext h
    rw [hsdef, map_eq_one_iff _ e.injective] at h1
    exact congrArg Subtype.val h1
  exact false_of_involution_commute hK hq (two_eq_zero_of_piField hK) hyt hs2 hs1 hc

theorem eq_one_of_isPGLAtP (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (e : L ≃* projImage (slPi π 3 (2 ^ f) K)) {a : H} {y : GL (Fin 3) K} (hy : IsPGLAtP e a y)
    (hyt : Type123 π (2 ^ f) K y 1 ∨ Type123 π (2 ^ f) K y 3) {t : H} (htL : t ∈ L)
    (ht2 : t * t = 1) (hat : a * t = t * a) : t = 1 := by
  by_contra ht1
  set m : projImage (slPi π 3 (2 ^ f) K) := e ⟨t, htL⟩ with hmdef
  have hm := hy.2 m
  rw [coe_slAct_eqP] at hm
  have heq : (⟨a * ((e.symm m : L) : H) * a⁻¹, hLn.conj_mem _ (e.symm m).2 a⟩ : L) =
      ⟨t, htL⟩ := by
    apply Subtype.ext
    rw [hmdef, MulEquiv.symm_apply_apply]
    change a * t * a⁻¹ = t
    rw [hat, mul_inv_cancel_right]
  rw [heq] at hm
  obtain ⟨s, -, hsm⟩ := m.2
  have hmm : (m : ProjGenLinGroup (Fin 3) K) * m = 1 := by
    rw [← Subgroup.coe_mul, hmdef, ← map_mul,
      show (⟨t, htL⟩ * ⟨t, htL⟩ : L) = 1 from Subtype.ext ht2, map_one, Subgroup.coe_one]
  have hm1 : (m : ProjGenLinGroup (Fin 3) K) ≠ 1 := by
    intro h
    apply ht1
    have h1 : m = 1 := Subtype.ext h
    rw [hmdef, map_eq_one_iff _ e.injective] at h1
    exact congrArg Subtype.val h1
  have hs2 : s * s ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, hsm]
    exact hmm
  have hs1 : s ∉ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, hsm]
    exact hm1
  have hc : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, hsm,
      ← hm, mul_inv_cancel]
  exact false_of_commute_mod_scalars hK hq (two_eq_zero_of_piField hK) hyt hs2 hs1 hc

end Normal

section Split

variable {H : Type} [Group H] {L : Subgroup H} [hLn : L.Normal] {π : Bool} {f : ℕ}

theorem typeC_or_noInv_SL (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (e : L ≃* slPi π 3 (2 ^ f) K) {A : Subgroup H}
    (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : 27 ≤ Nat.card A) {c : H} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) :
    (∃ b ∈ A, b ∈ L ∧ b ∉ Subgroup.zpowers c) ∨
      ∀ a ∈ A, a ∉ Subgroup.zpowers c → ∀ t ∈ L, t * t = 1 → a * t = t * a → t = 1 := by
  classical
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, hE9⟩ := card_eq_of_pgl hK hq hA hA27 hc3 hAc hpgl
  by_cases hb : ∃ b ∈ A, b ∈ L ∧ b ∉ Subgroup.zpowers c
  · exact Or.inl hb
  right
  have hAL : A ⊓ L ≤ Subgroup.zpowers c := by
    intro b hb'
    by_contra hbc
    exact hb ⟨b, (Subgroup.mem_inf.mp hb').1, (Subgroup.mem_inf.mp hb').2, hbc⟩
  rcases frame_or_heis h3 hτ hτ1 (pglHom hK hq A hpgl).range (range_pglHom_comm hAcomm)
      (range_pglHom_pow hA.1.2) (by omega) with
    ⟨b, hb', hframe, z, hz, d, hd, hzb⟩ | ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  · exact (false_of_frame hK hq e hA hc3 hAc hpgl hAL hb' hframe hz hd hzb).elim
  intro a ha hac t htL ht2 hat
  have haC : a ∉ Subgroup.centralizer (L : Set H) := fun h => hac (hAc ▸ ⟨ha, h⟩)
  obtain ⟨y, hy⟩ := hpgl a ha
  exact eq_one_of_isPGLAt hK hq e hy
    (type13_of_heis hK hq hAcomm hy₁ hy₂ hζ1 hζ ha haC (hA.1.2 a ha) hy) htL ht2 hat

theorem frame_or_noInv_PSL [Finite H] (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (2 ^ f) K))] (hθ : aschbacherSolvableCore 3 L = ⊥)
    (e : L ≃* projImage (slPi π 3 (2 ^ f) K)) {A : Subgroup H}
    (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : 27 ≤ Nat.card A) {c : H} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAtP e a y) :
    (IsTypeCOn A L ∧ ∃ b : Fin 3 → (Fin 3 → K), LinearIndependent K b ∧
        ∀ a ∈ A, ∀ y, IsPGLAtP e a y → ∀ i, ∃ d : K,
          (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d • b i) ∨
      ∀ a ∈ A, a ∉ Subgroup.zpowers c → ∀ t ∈ L, t * t = 1 → a * t = t * a → t = 1 := by
  classical
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3K := hK.three_ne_zero hq
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hRcomm := range_pglHomP_comm (hK := hK) (hq := hq) (hA' := hpgl) hAcomm
  have hRexp := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hpgl) hA3
  have hcardA := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (hA' := hpgl)
  rw [hAc, Nat.card_zpowers, hc3] at hcardA
  have hR9 := card_le_nine_of_comm h3K hτ hτ1 _ hRcomm hRexp
  have hR9' : Nat.card (pglHomP hK hq A hpgl).range = 9 := by omega
  rcases frame_or_heis h3K hτ hτ1 _ hRcomm hRexp (by omega) with ⟨b, hb, hd, -⟩ |
    ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  · exact Or.inl ⟨isTypeCOn_of_frameP hK hq hθ hpgl hA3 hR9' hb hd, b, hb,
      fun a ha y hy => hd y (mk_mem_range_pglHomP ha hy)⟩
  right
  intro a ha hac t htL ht2 hat
  have haC : a ∉ Subgroup.centralizer (L : Set H) := fun h => hac (hAc ▸ ⟨ha, h⟩)
  obtain ⟨y, hy⟩ := hpgl a ha
  exact eq_one_of_isPGLAtP hK hq e hy
    (type13_of_heisP hK hq hRcomm hy₁ hy₂ hζ1 hζ hy.1 (not_mem_zPi_of_isPGLAtP hK hq haC hy)
      (pow_three_mem_zPiP hK hq (hA3 a ha) hy) (mk_mem_range_pglHomP ha hy)) htL ht2 hat

end Split

end CFSG.RankThree.PartTwo.Sec4.Res417Two

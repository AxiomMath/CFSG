module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAutQ8
public import CFSG.RankThree.PartTwo.KFacts.L34Sections

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix Module

namespace Res7

section Lin

variable {F : Type*} [Field F]

theorem coordImage_flagSpace (σ : F ≃+* F) {n : ℕ} (d : ℕ) :
    coordImage σ (flagSpace n F d) = flagSpace n F d := by
  ext v
  rw [mem_coordImage, mem_flagSpace, mem_flagSpace]
  refine forall_congr' fun j => imp_congr_right fun _ => ?_
  exact map_eq_zero_iff σ.symm σ.symm.injective

theorem finrank_coordImage (σ : F ≃+* F) {n : ℕ} (W : Submodule F (Fin n → F)) :
    finrank F (coordImage σ W) = finrank F W := by
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq W
  have hle : finrank F W ≤ n := by
    have := Submodule.finrank_le W
    rwa [finrank_fin_fun] at this
  have h1 : coordImage σ W = (flagSpace n F (finrank F W)).map
      (mulVecLin ((g : Matrix (Fin n) (Fin n) F).map σ)) := by
    conv_lhs => rw [← hg]
    rw [coordImage_map, coordImage_flagSpace]
  rw [h1]
  have h2 := LinearEquiv.finrank_map_eq
    (SpecialLinearGroup.toLin' (SpecialLinearGroup.map (σ : F →+* F) g))
    (flagSpace n F (finrank F W))
  rw [finrank_flagSpace hle] at h2
  exact h2

theorem finrank_map_gl {n : ℕ} (A : GL (Fin n) F) (W : Submodule F (Fin n → F)) :
    finrank F (W.map (mulVecLin (A : Matrix (Fin n) (Fin n) F))) = finrank F W := by
  let e : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    LinearEquiv.ofLinearMap (mulVecLin (A : Matrix (Fin n) (Fin n) F))
      (mulVecLin ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (by rw [← Matrix.mulVecLin_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.mulVecLin_one])
  exact LinearEquiv.finrank_map_eq e W

theorem map_mulAut_mul {P : Type*} [Group P] (φ ψ : MulAut P) (H : Subgroup P) :
    H.map ((φ * ψ : MulAut P) : P →* P) = (H.map (ψ : P →* P)).map (φ : P →* P) := by
  rw [Subgroup.map_map]
  rfl

theorem bot_lt_lt_top_iff {n : ℕ} (W : Submodule F (Fin n → F)) :
    (⊥ < W ∧ W < ⊤) ↔ (1 ≤ finrank F W ∧ finrank F W < n) := by
  constructor
  · rintro ⟨h0, h1⟩
    exact one_le_finrank_and_lt h0 h1
  · rintro ⟨h0, h1⟩
    refine ⟨bot_lt_iff_ne_bot.mpr fun h => ?_, lt_top_iff_ne_top.mpr fun h => ?_⟩
    · rw [h, finrank_bot] at h0
      omega
    · rw [h, finrank_top, finrank_fin_fun] at h1
      omega

end Lin

section Aut

variable {F : Type*} [Field F]

theorem exists_pow_conjAut_mul_fieldAut {n : ℕ} (A : GL (Fin n) F) (σ : F ≃+* F) (m : ℕ) :
    ∃ B : GL (Fin n) F,
      (conjAut n F A * fieldAut n F σ) ^ m = conjAut n F B * fieldAut n F (σ ^ m) := by
  induction m with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, one_mul]⟩
  | succ m ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B * Matrix.GeneralLinearGroup.map ((σ ^ m : F ≃+* F) : F →+* F) A, ?_⟩
    rw [pow_succ, hB, conjAut_mul_fieldAut_mul, pow_succ]

theorem exists_conj_eq_conjAut_of_cube (A : GL (Fin 3) F)
    (hcube : ∀ d : Fˣ, ∃ u : Fˣ, u ^ 3 = d) :
    ∃ y : projectiveSL 3 F, conjAut 3 F A = MulAut.conj y := by
  obtain ⟨u, hu⟩ := hcube (Matrix.GeneralLinearGroup.det A)
  set B : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A with hB
  have hdet : Matrix.GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, ← hu]
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  have hdet' : (B : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have := congrArg Units.val hdet
    simpa using this
  set g : SpecialLinearGroup (Fin 3) F := ⟨B, hdet'⟩ with hg
  have hgB : SpecialLinearGroup.toGL g = B := Units.ext rfl
  have hA : A = Matrix.GeneralLinearGroup.scalar (Fin 3) u * B := by
    rw [hB, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨proj 3 F g, ?_⟩
  rw [hA, map_mul, conjAut_scalar, one_mul, ← hgB, conjAut_toGL]

theorem coprime_two_pow_sub_one_three {n : ℕ} (hn : Odd n) : Nat.Coprime (2 ^ n - 1) 3 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  generalize 2 ^ (2 * k + 1) = x at h ⊢
  omega

theorem exists_cube_galoisField {n : ℕ} (hn : Odd n) (d : (GaloisField 2 n)ˣ) :
    ∃ u : (GaloisField 2 n)ˣ, u ^ 3 = d := by
  have hn0 : n ≠ 0 := by obtain ⟨k, rfl⟩ := hn; omega
  classical
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
      GaloisField.card 2 n hn0]
  have hcop : (Nat.card (GaloisField 2 n)ˣ).Coprime 3 := by
    rw [hcard]
    exact coprime_two_pow_sub_one_three hn
  obtain ⟨u, hu⟩ := (powCoprime hcop).surjective d
  exact ⟨u, hu⟩

theorem eq_one_of_pow_two_pow_eq_one {n : ℕ} (hn : Odd n)
    {σ : GaloisField 2 n ≃+* GaloisField 2 n} {a : ℕ} (ha : σ ^ 2 ^ a = 1) : σ = 1 := by
  have hn0 : n ≠ 0 := by obtain ⟨k, rfl⟩ := hn; omega
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (Nat.one_le_iff_ne_zero.mpr hn0) hF
  have h1 : orderOf σ ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf σ ∣ n := by
    have := orderOf_dvd_natCard σ
    rwa [hAut] at this
  have hcop : Nat.Coprime (2 ^ a) n := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hn)
  have h3 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

end Aut

theorem isMaxParabolicRankTwo_map {Q S : Type*} [Group Q] [Group S] [Finite Q] (ε : Q ≃* S)
    {X : Subgroup Q} (h : Sec18.IsMaxParabolicRankTwo X) :
    Sec18.IsMaxParabolicRankTwo (X.map ε.toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hX, T, hT⟩ := h
  have hs : Function.Surjective ε.toMonoidHom := fun y => by
    obtain ⟨a, ha⟩ := ε.surjective y
    exact ⟨a, ha⟩
  refine ⟨(OrderIso.isCoatom_iff (MulEquiv.mapSubgroup ε) X).mpr hX, T.mapSurjective hs, ?_⟩
  show Subgroup.normalizer (((T : Subgroup Q).map ε.toMonoidHom : Subgroup S) : Set S) ≤ _
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hT

end Res7

theorem kFactL3OddParabolicInner_holds : KFactL3OddParabolicInner := by
  intro n hn Y _ _ ⟨e₀⟩ X hX α ⟨a, ha⟩ hαX
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n with hFdef
  set e : Y ≃* projectiveSL 3 F := e₀.trans (KFacts.L34.projSLEquivProjectiveSL 3 F) with he
  set β : MulAut (projectiveSL 3 F) := MulAut.congr e α with hβ
  have hβ2 : β ^ 2 ^ a = 1 := by rw [hβ, ← map_pow, ha, map_one]
  set X' := X.map e.toMonoidHom with hX'
  have hX'par : Sec18.IsMaxParabolicRankTwo X' := Res7.isMaxParabolicRankTwo_map e hX
  have hX'mem : X' ∈ maximalParabolics (projectiveSL 3 F) 2 := by
    obtain ⟨hc, T, hT⟩ := hX'par
    exact ⟨hc, _, ⟨T, rfl⟩, hT⟩
  obtain ⟨hMP, hinj, -⟩ := maximal_parabolics (K := F) (n := 3) 2 (by norm_num)
  rw [hMP] at hX'mem
  obtain ⟨W, ⟨hW0, hWt⟩, hWX⟩ := hX'mem
  have hβX : X'.map (β : projectiveSL 3 F →* projectiveSL 3 F) = X' := by
    rw [hX', Subgroup.map_map]
    have : (β : projectiveSL 3 F →* projectiveSL 3 F).comp e.toMonoidHom =
        e.toMonoidHom.comp α.toMonoidHom := by
      ext y
      simp [hβ, MulAut.congr_apply]
    rw [this, ← Subgroup.map_map, hαX]
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hβeq⟩ := hform β
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  obtain ⟨hd1, hd2⟩ := one_le_finrank_and_lt hW0 hWt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hβeq
    obtain ⟨B, hB⟩ := Res7.exists_pow_conjAut_mul_fieldAut A σ (2 ^ a)
    rw [← hβeq, hβ2] at hB
    obtain ⟨hσ1, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) B (σ ^ 2 ^ a) hB.symm
    have hσ : σ = 1 := Res7.eq_one_of_pow_two_pow_eq_one hn hσ1
    rw [hσ, map_one, mul_one] at hβeq
    obtain ⟨y, hy⟩ := Res7.exists_conj_eq_conjAut_of_cube A (Res7.exists_cube_galoisField hn)
    refine ⟨e.symm y, ?_⟩
    have hβc : β = MulAut.conj y := hβeq.trans hy
    have hα : α = (MulAut.congr e).symm β := by rw [hβ, MulEquiv.symm_apply_apply]
    rw [hα, hβc]
    ext x
    simp [MulAut.conj_apply]
  ·
    exfalso
    rw [pow_one] at hβeq
    set W'' := (coordImage σ (dotOrth W)).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))
      with hW''
    have hmap : X'.map (β : projectiveSL 3 F →* projectiveSL 3 F) = projStabilizer W'' := by
      rw [← hWX, hβeq, Res7.map_mulAut_mul, Res7.map_mulAut_mul, htrans.2.2.2.2.2.2.2.2.1,
        htrans.2.2.2.2.2.2.2.1, htrans.2.2.2.2.2.2.1]
    have hfin : finrank F W'' = 3 - finrank F W := by
      rw [hW'', Res7.finrank_map_gl, Res7.finrank_coordImage, finrank_dotOrth]
    have hWW : ⊥ < W'' ∧ W'' < ⊤ := (Res7.bot_lt_lt_top_iff W'').mpr (by omega)
    have heq : W'' = W := hinj hWW ⟨hW0, hWt⟩ (by rw [← hmap, hβX, hWX])
    rw [heq] at hfin
    omega

end CFSG.RankThree.PartTwo.Sec20

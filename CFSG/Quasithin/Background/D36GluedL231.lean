module

public import CFSG.Quasithin.Background.D36GluedDim
import CFSG.Quasithin.Background.F918Z4bPrime

public section

namespace CFSG.Quasithin

open Matrix CFSG.Assembly.LowTwoRank

theorem zmod31_det : (!![0, -1; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 31)).det = 1 := by decide

theorem zmod31_pow16 : (!![0, -1; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 31)) ^ 16 = -1 := by
  decide

theorem zmod31_pow8 : ((!![0, -1; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 31)) ^ 8) 0 1 ≠ 0 := by
  decide

theorem exists_ringEquiv_zmod31 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 31) :
    Nonempty (ZMod 31 ≃+* K) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hcard : Fintype.card K = Fintype.card (ZMod 31) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  exact ⟨(FiniteField.ringEquivOfCardEq hcard).symm⟩

theorem exists_orderOf_sixteen_psl2_31 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 31) :
    ∃ x : ProjectiveSpecialLinearGroup (Fin 2) K, orderOf x = 16 := by
  obtain ⟨φ⟩ := exists_ringEquiv_zmod31 hK
  let g₀ : SpecialLinearGroup (Fin 2) (ZMod 31) := ⟨!![0, -1; 1, 4], zmod31_det⟩
  let g : SpecialLinearGroup (Fin 2) K := Matrix.SpecialLinearGroup.map φ.toRingHom g₀
  have hcoe : ∀ k : ℕ, ((g ^ k : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (((!![0, -1; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 31)) ^ k).map φ) := by
    intro k
    rw [← map_pow, Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_pow]
    rfl
  have hg16 : g ^ 16 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by simp [Fintype.card_fin], ?_⟩
    rw [hcoe]
    have e16 : ((!![0, -1; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 31)) ^ 16) = -1 := zmod31_pow16
    have hmap : ((!![0, -1; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 31)) ^ 16).map φ =
        (φ.toRingHom.mapMatrix : Matrix (Fin 2) (Fin 2) (ZMod 31) →+* Matrix (Fin 2) (Fin 2) K)
          ((!![0, -1; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 31)) ^ 16) := rfl
    rw [hmap, e16, map_neg, map_one, map_neg, map_one]
  have hg8 : g ^ 8 ∉ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    rintro ⟨r, -, hr⟩
    have h1 := congrFun (congrFun hr 0) 1
    rw [hcoe] at h1
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.map_apply] at h1
    have e8 : ((!![0, -1; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 31)) ^ 8) 0 1 ≠ 0 := zmod31_pow8
    exact e8 (φ.injective (by rw [← h1, map_zero]))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨QuotientGroup.mk g, ?_⟩
  have h1 : (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin 2) K) ^ 2 ^ 4 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simpa using hg16
  have h2 : ¬ (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin 2) K) ^ 2 ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simpa using hg8
  have := orderOf_eq_prime_pow (p := 2) h2 (by simpa using h1)
  simpa using this

theorem exists_orderOf_sixteen_of_psl2_31 {L : Type} [Group L] (hL : IsPSL 2 31 1 L) :
    ∃ x : L, orderOf x = 16 := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hL
  have hK31 : Nat.card K = 31 := by simpa using hK
  obtain ⟨x, hx⟩ := exists_orderOf_sixteen_psl2_31 hK31
  let e' : L ≃* ProjectiveSpecialLinearGroup (Fin 2) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  refine ⟨e'.symm x, ?_⟩
  rw [← hx]
  exact orderOf_injective e'.symm.toMonoidHom e'.symm.injective x

theorem matrix_pow_eight_eq_one {d : ℕ} (hd : d ≤ 8) {M : Matrix (Fin d) (Fin d) (ZMod 2)}
    (h : M ^ 16 = 1) : M ^ 8 = 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · exact Subsingleton.elim _ _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, hpos⟩⟩
  have h2 : (1 : Matrix (Fin d) (Fin d) (ZMod 2)) + 1 = 0 := by
    have : ((2 : ℕ) : Matrix (Fin d) (Fin d) (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
    simpa [one_add_one_eq_two] using this
  have hcomm : Commute M 1 := Commute.one_right M
  have h1 : (M + 1) ^ 16 = 0 := by
    have := add_pow_char_pow_of_commute (R := Matrix (Fin d) (Fin d) (ZMod 2)) (p := 2) (n := 4)
      hcomm
    simp only [show (2 : ℕ) ^ 4 = 16 by norm_num, one_pow, h] at this
    rw [this, h2]
  have hnil : IsNilpotent (M + 1) := ⟨16, h1⟩
  have hcp : (M + 1).charpoly = Polynomial.X ^ d := by
    have := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil
    have h0 := this.eq_zero
    simpa [sub_eq_zero, Fintype.card_fin] using h0
  have h3 : (M + 1) ^ d = 0 := by
    have := Matrix.aeval_self_charpoly (M + 1)
    rw [hcp] at this
    simpa using this
  have h4 : (M + 1) ^ 8 = 0 := by
    have : (M + 1) ^ 8 = (M + 1) ^ (8 - d) * (M + 1) ^ d := by
      rw [← pow_add]
      congr 1
      omega
    rw [this, h3, mul_zero]
  have h5 : M = (M + 1) + 1 := by
    rw [add_assoc, h2, add_zero]
  have hcomm' : Commute (M + 1) 1 := Commute.one_right _
  have := add_pow_char_pow_of_commute (R := Matrix (Fin d) (Fin d) (ZMod 2)) (p := 2) (n := 3)
    hcomm'
  simp only [show (2 : ℕ) ^ 3 = 8 by norm_num, one_pow, h4, zero_add] at this
  rw [h5]
  exact this

theorem no_embedding_psl2_31 {L : Type} [Group L] (hL : IsPSL 2 31 1 L) {d : ℕ} (hd : d ≤ 8)
    (ρ : L →* GL (Fin d) (ZMod 2)) (hρ : Function.Injective ρ) : False := by
  obtain ⟨x, hx⟩ := exists_orderOf_sixteen_of_psl2_31 hL
  have h16 : (ρ x) ^ 16 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have h8 : (ρ x) ^ 8 = 1 := by
    apply Units.ext
    have := matrix_pow_eight_eq_one hd (M := ((ρ x : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d)
      (ZMod 2))) (by simpa using congrArg Units.val h16)
    simpa using this
  have hdvd : orderOf (ρ x) ∣ 8 := orderOf_dvd_of_pow_eq_one h8
  rw [orderOf_injective ρ hρ x, hx] at hdvd
  omega

section Glued

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

theorem GluedSwap.false_of_psl2_31 (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u) (hL₀U : L₀ ≤ stabSub U)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) (hsimple : IsSimpleGroup ↥L₀)
    (hnonab : ∃ a b : ↥L₀, a * b ≠ b * a) (hL : IsPSL 2 31 1 ↥L₀) : False := by
  obtain ⟨d, hd, ρ, hρ⟩ := h.exists_gl hY hL₀ hL₀U hdiag hsimple
  have hu := h.ubar_le_of_autRankLe hY hL₀ hdiag hsimple hnonab
    (autRankLe_psl2_prime (by norm_num) (by norm_num) hL)
  exact no_embedding_psl2_31 hL (by omega) ρ hρ

end Glued

end CFSG.Quasithin

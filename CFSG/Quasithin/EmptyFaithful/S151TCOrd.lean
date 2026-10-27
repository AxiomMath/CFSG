module

public import CFSG.Quasithin.EmptyFaithful.S151TBBridge
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
  CFSG.Quasithin.S151TB

theorem sl3_card_not_dvd_1080 {n : ℕ} (hn : 1 ≤ n) :
    ¬ (2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) ∣ 1080) := by
  intro hd
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    norm_num at hd
  · have h1 := Nat.le_of_dvd (by norm_num) hd
    have ha : 2 ^ 6 ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb : 2 ^ 4 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 6 * ((2 ^ 6 - 1) * (2 ^ 4 - 1)) ≤
        2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) :=
      Nat.mul_le_mul ha (Nat.mul_le_mul (Nat.sub_le_sub_right ha 1) (Nat.sub_le_sub_right hb 1))
    norm_num at h2
    omega

theorem sl2_card_ne {n : ℕ} (hn : 1 < n) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 168 ∧ 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 1080 := by
  by_cases h4 : 4 ≤ n
  · have hd : 2 ^ 4 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Dvd.dvd.mul_right (pow_dvd_pow 2 h4) _
    constructor <;> intro h <;> rw [h] at hd <;> norm_num at hd
  · interval_cases n <;> norm_num

theorem alt_card_ne {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    n.factorial / 2 ≠ 168 ∧ n.factorial / 2 ≠ 1080 := by
  interval_cases n <;> decide

section Orders

variable {G : Type} [Group G]

theorem card_lStar_of_surjective {K : Subgroup G} {X : Type*} [Group X] (α : ↥K →* X)
    (hα : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥K) :
    Nat.card (LStar K) = Nat.card X :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv

theorem card_lStar_of_isLin2Type {K : Subgroup G} {n : ℕ} (h : IsLin2Type K n) :
    Nat.card (LStar K) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, α, hα, hk, -⟩ := h
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  rw [card_lStar_of_surjective α hα hk, CFSG.GorensteinWalter.sl2_card_formula, hFn]

theorem card_lStar_of_isAltType {K : Subgroup G} {m : ℕ} (hm : 2 ≤ m) (h : IsAltType K m) :
    Nat.card (LStar K) = m.factorial / 2 := by
  obtain ⟨α, hα, hk, -⟩ := h
  rw [card_lStar_of_surjective α hα hk, CFSG.Quasithin.Vol2.Ch10.SecA.card_alt m hm]

theorem card_lStar_of_isAltBlockTypeWith {K : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    {α : ↥K →* alternatingGroup (Fin m)} (h : IsAltBlockTypeWith K m α) :
    Nat.card (LStar K) = m.factorial / 2 := by
  obtain ⟨hα, hk, -⟩ := h
  rw [card_lStar_of_surjective α hα hk, CFSG.Quasithin.Vol2.Ch10.SecA.card_alt m hm]

theorem card_lStar_of_isExcA7Block {K : Subgroup G} (h : IsExcA7Block K) :
    Nat.card (LStar K) = 2520 := by
  obtain ⟨-, ⟨α, hα, hk⟩, -⟩ := h
  rw [card_lStar_of_surjective α hα hk, CFSG.Quasithin.Vol2.Ch10.SecA.card_alt 7 (by norm_num)]
  decide

theorem card_lStar_of_isSp4Block {K : Subgroup G} (h : IsSp4Block K) :
    Nat.card (LStar K) = 979200 := by
  obtain ⟨-, F, _, _, hF, α, hα, hk, -⟩ := h
  have hFn : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  rw [card_lStar_of_surjective α hα hk, CFSG.Quasithin.Vol2.Ch10.SecA.card_Sp4_pow hFn]
  norm_num

theorem card_lStar_of_isG2Block {K : Subgroup G} (h : IsG2Block K) :
    Nat.card (LStar K) = 6048 :=
  CFSG.Quasithin.H13.card_of_statedClassicalModel_psu_three_three h.2.1

theorem card_lStar_of_isHatA6Block {K : Subgroup G} (h : IsHatA6Block K) :
    Nat.card (LStar K) = 1080 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h.2.1
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (LStar K))
  rw [Nat.card_congr e.toEquiv, hZ, CFSG.Quasithin.Vol2.Ch10.SecA.card_alt 6 (by norm_num)]
    at h1
  rw [h1]
  decide

theorem card_dvd_lStar_of_epi {K : Subgroup G} {X : Type*} [Group X] (ψ : ↥K →* X)
    (hψ : Function.Surjective ψ) (hO2 : CFSG.pCore 2 ↥K ≤ ψ.ker) :
    Nat.card X ∣ Nat.card (LStar K) :=
  Subgroup.card_dvd_of_surjective (f := QuotientGroup.lift (CFSG.pCore 2 ↥K) ψ hO2) (by
    intro x
    obtain ⟨y, rfl⟩ := hψ x
    exact ⟨QuotientGroup.mk y, rfl⟩)

theorem card_dvd_lStar_of_autOn {K R V : Subgroup G} [Finite G] {X : Type*} [Group X]
    (hRN : R ≤ Subgroup.normalizer (K : Set G))
    (h1 : pCoreOf 2 (K ⊔ R) ≤ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ∧
      (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K ∧
      IsTwoReducedIn (K ⊔ R) V)
    (e : ↥(autOn K V) ≃* X) : Nat.card X ∣ Nat.card (LStar K) := by
  obtain ⟨ψ₀, hψ₀, hO2, -⟩ := exists_epi_autOn hRN h1
  exact card_dvd_lStar_of_epi (e.toMonoidHom.comp ψ₀) (e.surjective.comp hψ₀) (fun x hx => by
    have := hO2 hx
    simpa [MonoidHom.mem_ker] using this)

end Orders

theorem c27_g_of_card168 {G : Type} [Group G] [Finite G] (hC27 : ASC27Statement G)
    {H R M K : Subgroup G} (hyp : HypC23 H R M) (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (LStar K)) (hch : CharTwo K) (hnle : ¬ K ≤ M)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hcard : Nat.card (LStar K) = 168) :
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
        Nonempty (↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ≃*
          ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∧
      IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
        (autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ∧
      IsMSPair (K ⊔ R) R := by
  obtain ⟨h1, -, h3⟩ :=
    hC27 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hyp hK hq hch hnle hRN rfl
  rcases h3 with ⟨-, hcases⟩ | ⟨⟨n, α, hn5, hn8, -, hα, -⟩, -⟩ | ⟨hHat, -⟩ | ⟨hexc, -⟩ |
    ⟨hAS, -⟩ | ⟨hG2, -, -⟩ | hg | ⟨hh, -, -⟩
  · exfalso
    rcases hcases with ⟨⟨n, hn, hlin⟩, -⟩ | ⟨hA5, -⟩ | ⟨hA7, -⟩ | ⟨hA7, -⟩
    · exact (sl2_card_ne hn).1 ((card_lStar_of_isLin2Type hlin).symm.trans hcard)
    · rw [card_lStar_of_isAltType (by norm_num) hA5] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isAltType (by norm_num) hA7] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isAltType (by norm_num) hA7] at hcard
      revert hcard
      decide
  · exfalso
    exact (alt_card_ne hn5 hn8).1
      ((card_lStar_of_isAltBlockTypeWith (by omega) hα).symm.trans hcard)
  · exfalso
    rw [card_lStar_of_isHatA6Block hHat] at hcard
    revert hcard
    decide
  · exfalso
    rw [card_lStar_of_isExcA7Block hexc] at hcard
    revert hcard
    decide
  · exfalso
    rcases hAS with ⟨-, α, hα⟩ | hsp4
    · rw [card_lStar_of_isAltBlockTypeWith (by norm_num) hα] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isSp4Block hsp4] at hcard
      revert hcard
      decide
  · exfalso
    rw [card_lStar_of_isG2Block hG2] at hcard
    revert hcard
    decide
  · exact hg
  · exfalso
    rcases hh with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hd := card_dvd_lStar_of_autOn hRN h1 e
      rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
        CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_four_of_two (Nat.card_zmod 2)] at hd
      revert hd
      decide
    · have hd := card_dvd_lStar_of_autOn hRN h1 e
      rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
        CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_five_of_two (Nat.card_zmod 2)] at hd
      revert hd
      decide

theorem c27_c_of_card1080 {G : Type} [Group G] [Finite G] (hC27 : ASC27Statement G)
    {H R M K : Subgroup G} (hyp : HypC23 H R M) (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (LStar K)) (hch : CharTwo K) (hnle : ¬ K ≤ M)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hcard : Nat.card (LStar K) = 1080) :
    IsHatA6Block K ∧ M.relIndex K = 15 ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 4 ∧
        ∃ (ρ : ↥K →* Matrix.GeneralLinearGroup (Fin 3) F)
          (e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)),
          (∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
            Multiplicative.toAdd (e v) =
              ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
                (Multiplicative.toAdd (e u))) ∧
          ∃ W : Submodule F (Fin 3 → F), Module.finrank F W = 2 ∧
            ∀ k : ↥K, (k : G) ∈ M ↔ ∀ w ∈ W,
              ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w
                ∈ W := by
  obtain ⟨h1, -, h3⟩ :=
    hC27 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hyp hK hq hch hnle hRN rfl
  rcases h3 with ⟨-, hcases⟩ | ⟨⟨n, α, hn5, hn8, -, hα, -⟩, -⟩ | hc | ⟨hexc, -⟩ |
    ⟨hAS, -⟩ | ⟨hG2, -, -⟩ | ⟨⟨n, F, _, _, hn1, hF, ⟨e⟩⟩, -, -⟩ | ⟨hh, -, -⟩
  · exfalso
    rcases hcases with ⟨⟨n, hn, hlin⟩, -⟩ | ⟨hA5, -⟩ | ⟨hA7, -⟩ | ⟨hA7, -⟩
    · exact (sl2_card_ne hn).2 ((card_lStar_of_isLin2Type hlin).symm.trans hcard)
    · rw [card_lStar_of_isAltType (by norm_num) hA5] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isAltType (by norm_num) hA7] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isAltType (by norm_num) hA7] at hcard
      revert hcard
      decide
  · exfalso
    exact (alt_card_ne hn5 hn8).2
      ((card_lStar_of_isAltBlockTypeWith (by omega) hα).symm.trans hcard)
  · exact hc
  · exfalso
    rw [card_lStar_of_isExcA7Block hexc] at hcard
    revert hcard
    decide
  · exfalso
    rcases hAS with ⟨-, α, hα⟩ | hsp4
    · rw [card_lStar_of_isAltBlockTypeWith (by norm_num) hα] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isSp4Block hsp4] at hcard
      revert hcard
      decide
  · exfalso
    rw [card_lStar_of_isG2Block hG2] at hcard
    revert hcard
    decide
  · exfalso
    have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
    have hd := card_dvd_lStar_of_autOn hRN h1 e
    rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
      CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_three_pow hFn] at hd
    exact sl3_card_not_dvd_1080 hn1 hd
  · exfalso
    rcases hh with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hd := card_dvd_lStar_of_autOn hRN h1 e
      rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
        CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_four_of_two (Nat.card_zmod 2)] at hd
      revert hd
      decide
    · have hd := card_dvd_lStar_of_autOn hRN h1 e
      rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
        CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_five_of_two (Nat.card_zmod 2)] at hd
      revert hd
      decide

end CFSG.Quasithin.S151TC

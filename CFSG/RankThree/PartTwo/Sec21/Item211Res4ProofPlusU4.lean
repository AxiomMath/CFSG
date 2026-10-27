module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofPlusL4
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofMain
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcInner
import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projSU projImage)
open CFSG.Assembly.LowTwoRank (StatedSU StatedProj)
open CFSG.RankThree.PartOne.KFU
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg (fixedSubfield hypEquiv card_fixedSubfield)
open scoped MatrixGroups

namespace Item211Res4Proof

open Item228Census3Proof U4Lines

theorem eq_of_cube_eq_one {F : Type} [Field F] {α b : F} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hb3 : b ^ 3 = 1) : b = 1 ∨ b = α ∨ b = α ^ 2 := by
  have hq : α ^ 2 + α + 1 = 0 := by
    have : (α - 1) * (α ^ 2 + α + 1) = 0 := by linear_combination hα3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hα1)
  have h : (b - 1) * ((b - α) * (b - α ^ 2)) = 0 := by
    linear_combination hb3 + (b - 1) * hα3 + (b - b ^ 2) * hq
  rcases mul_eq_zero.mp h with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  rcases mul_eq_zero.mp h2 with h3 | h4
  · exact Or.inr (Or.inl (sub_eq_zero.mp h3))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h4))

section Unitary

variable {F : Type} [Field F] (σ : F ≃+* F)

theorem dec_long {α : Fˣ} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {t B : GL (Fin 4) F}
    (htS : t ∈ SU σ 4)
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![(α : F), 1, 1, ((α⁻¹ : Fˣ) : F)])
    (hB : B ∈ SU σ 4) (hB3 : B ^ 3 = 1) (hBt : B * t = t * B) :
    ∃ (j : ℕ) (M : SU σ 2), B = t ^ j * iotaL σ M := by
  have h1 : (α : F) ≠ 1 := fun h => hα1 (Units.ext h)
  have h2 : (α : F) ≠ ((α⁻¹ : Fˣ) : F) := ne_inv_of_cube hα3 hα1
  have h3 : (1 : F) ≠ ((α⁻¹ : Fˣ) : F) := fun h => hα1 (by
    have : α⁻¹ = 1 := Units.ext h.symm
    rw [← inv_inv α, this, inv_one])
  have hα3' : (α : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hα3, Units.val_one]
  set C := SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F)) with hC
  have hBC : B ∈ C := ⟨hB, mem_centralizer_zpowers_of_commute hBt⟩
  have htC : t ∈ C := ⟨htS, mem_centralizer_zpowers_of_commute rfl⟩
  let χ : C →* F :=
    { toFun := fun x => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0
      map_one' := by simp
      map_mul' := fun x y => by
        obtain ⟨h01, h02, h03, -⟩ := pattern_long_of_mem ht h1 h2 h3 x.2.2
        simp [Matrix.mul_apply, Fin.sum_univ_four, h01, h02, h03] }
  have hχt : χ ⟨t, htC⟩ = α := by
    change (t : Matrix (Fin 4) (Fin 4) F) 0 0 = α
    rw [ht]
    simp
  have hb3 : (χ ⟨B, hBC⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨B, hBC⟩ : C) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hB3)
    rw [this, map_one]
  have key : ∀ m : ℕ, (χ ⟨t, htC⟩) ^ m * χ ⟨B, hBC⟩ = 1 →
      ∃ (j : ℕ) (M : SU σ 2), B = t ^ j * iotaL σ M := by
    intro m hm
    have hk : t ^ m * B ∈ C := C.mul_mem (C.pow_mem htC m) hBC
    have hk00 : ((t ^ m * B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 = 1 := by
      have e : χ ⟨t ^ m * B, hk⟩ = (χ ⟨t, htC⟩) ^ m * χ ⟨B, hBC⟩ := by
        rw [← map_pow, ← map_mul]
        rfl
      rw [← hm, ← e]
      rfl
    obtain ⟨M, hM⟩ := mem_longSL_of σ hk.1 (pattern_long_of_mem ht h1 h2 h3 hk.2) hk00
    have ht3 : t ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ht, Matrix.diagonal_pow, Units.val_one,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [← Units.val_pow_eq_pow_val, hα3]
    refine ⟨2 * m, M, ?_⟩
    rw [hM]
    calc B = t ^ (3 * m) * B := by rw [pow_mul, ht3, one_pow, one_mul]
      _ = t ^ (2 * m) * (t ^ m * B) := by rw [← mul_assoc, ← pow_add]; ring_nf
  rw [hχt] at key
  rcases eq_of_cube_eq_one hα3' h1 hb3 with h | h | h
  · exact key 0 (by rw [pow_zero, one_mul, h])
  · exact key 2 (by rw [h, ← pow_succ, hα3'])
  · exact key 1 (by rw [h, pow_one, ← pow_succ', hα3'])

theorem dec_short {α : Fˣ} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {t B : GL (Fin 4) F}
    (htS : t ∈ SU σ 4)
    (ht : (t : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![(α : F), α, ((α⁻¹ : Fˣ) : F), ((α⁻¹ : Fˣ) : F)])
    (hB : B ∈ SU σ 4) (hB3 : B ^ 3 = 1) (hBt : B * t = t * B) :
    ∃ (j : ℕ) (S : SL(2, F)), B = t ^ j * iotaSo σ S := by
  have hne : (α : F) ≠ ((α⁻¹ : Fˣ) : F) := ne_inv_of_cube hα3 hα1
  have hα3' : (α : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hα3, Units.val_one]
  have h1 : (α : F) ≠ 1 := fun h => hα1 (Units.ext h)
  set C := SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F)) with hC
  have hBC : B ∈ C := ⟨hB, mem_centralizer_zpowers_of_commute hBt⟩
  have htC : t ∈ C := ⟨htS, mem_centralizer_zpowers_of_commute rfl⟩
  let χ : C →* F :=
    { toFun := fun x => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 *
        ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 1 -
        ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 1 *
        ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 0
      map_one' := by simp
      map_mul' := fun x y => by
        obtain ⟨h02, h03, h12, h13, -⟩ := pattern_short_of_mem ht hne x.2.2
        simp [Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]
        ring }
  have hχt : χ ⟨t, htC⟩ = α ^ 2 := by
    change (t : Matrix (Fin 4) (Fin 4) F) 0 0 * (t : Matrix (Fin 4) (Fin 4) F) 1 1 -
      (t : Matrix (Fin 4) (Fin 4) F) 0 1 * (t : Matrix (Fin 4) (Fin 4) F) 1 0 = (α : F) ^ 2
    rw [ht]
    simp [sq]
  have hb3 : (χ ⟨B, hBC⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨B, hBC⟩ : C) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hB3)
    rw [this, map_one]
  have key : ∀ m : ℕ, (χ ⟨t, htC⟩) ^ m * χ ⟨B, hBC⟩ = 1 →
      ∃ (j : ℕ) (S : SL(2, F)), B = t ^ j * iotaSo σ S := by
    intro m hm
    have hk : t ^ m * B ∈ C := C.mul_mem (C.pow_mem htC m) hBC
    have hkdet : ((t ^ m * B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 *
        ((t ^ m * B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 1 -
        ((t ^ m * B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 1 *
        ((t ^ m * B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 0 = 1 := by
      have e : χ ⟨t ^ m * B, hk⟩ = (χ ⟨t, htC⟩) ^ m * χ ⟨B, hBC⟩ := by
        rw [← map_pow, ← map_mul]
        rfl
      rw [← hm, ← e]
      rfl
    obtain ⟨S, hS⟩ := exists_iotaSo_eq σ hk.1 (pattern_short_of_mem ht hne hk.2) hkdet
    have ht3 : t ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ht, Matrix.diagonal_pow, Units.val_one,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [← Units.val_pow_eq_pow_val, hα3]
    refine ⟨2 * m, S, ?_⟩
    rw [hS]
    calc B = t ^ (3 * m) * B := by rw [pow_mul, ht3, one_pow, one_mul]
      _ = t ^ (2 * m) * (t ^ m * B) := by rw [← mul_assoc, ← pow_add]; ring_nf
  rw [hχt] at key
  rcases eq_of_cube_eq_one hα3' h1 hb3 with h | h | h
  · exact key 0 (by rw [pow_zero, one_mul, h])
  ·
    refine key 1 ?_
    rw [h, pow_one, ← pow_succ, hα3']
  ·
    refine key 2 ?_
    rw [h, ← pow_mul, ← pow_add]
    calc (α : F) ^ (2 * 2 + 2) = ((α : F) ^ 3) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hα3', one_pow]

end Unitary

theorem exists_three_mul_sq_eq_one_of_card {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] [CharP K p] (hp3 : 3 < p) (hK : Nat.card K = p ^ 2) :
    ∃ c : K, 3 * c ^ 2 = 1 := by
  have hp : p.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have h3 : (3 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K p 3).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    omega
  have hcard : Fintype.card K = p ^ 2 := by rw [Fintype.card_eq_nat_card, hK]
  have h3p : (3 : K) ^ p = 3 := by rw [← frobenius_def, map_ofNat]
  have h3p1 : (3 : K)⁻¹ ^ (p - 1) = 1 := by
    have e : (3 : K) ^ (p - 1) * 3 = 1 * 3 := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le, h3p, one_mul]
    rw [inv_pow, mul_right_cancel₀ h3 e, inv_one]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨r, hr⟩ := hodd
  have hdiv : Fintype.card K / 2 = (p - 1) * (r + 1) := by
    rw [hcard, hr]
    have e1 : (2 * r + 1) ^ 2 = 2 * (2 * r * (r + 1)) + 1 := by ring
    rw [e1, Nat.mul_add_div (by norm_num : 0 < 2), show (1 : ℕ) / 2 = 0 from rfl, add_zero,
      show 2 * r + 1 - 1 = 2 * r by omega]
  have hsq : IsSquare (3 : K)⁻¹ := by
    rw [FiniteField.isSquare_iff hchar (inv_ne_zero h3), hdiv, pow_mul, h3p1, one_pow]
  obtain ⟨c, hc⟩ := hsq
  refine ⟨c, ?_⟩
  rw [sq, ← hc, mul_inv_cancel₀ h3]

theorem exists_normal_form_U4 {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp1 : p % 3 = 1) (hK : Nat.card K = (p ^ 1) ^ 2)
    (A : SUid (unitaryInvolution K p 1) 4) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    ∃ (R : GL (Fin 4) K) (α : Kˣ),
      (∀ g, g ∈ SUid (unitaryInvolution K p 1) 4 ↔ R * g * R⁻¹ ∈ SU (unitaryInvolution K p 1) 4) ∧
      α ^ 3 = 1 ∧ α ≠ 1 ∧ (R * (A : GL (Fin 4) K) * R⁻¹ = diagU ![α, 1, 1, α⁻¹] ∨
        R * (A : GL (Fin 4) K) * R⁻¹ = diagU ![α, α, α⁻¹, α⁻¹]) := by
  let σ : K ≃+* K := unitaryInvolution K p 1
  obtain ⟨W, hW⟩ := exists_wittMatrix hK 4
  have hconjW := mem_SUid_iff_conj σ hW
  have hA3' : (A : GL (Fin 4) K) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hA3, Subgroup.coe_one]
  have hA''mem : W⁻¹ * (A : GL (Fin 4) K) * W⁻¹⁻¹ ∈ SU σ 4 := (hconjW A).mp A.2
  have hA''3 : (W⁻¹ * (A : GL (Fin 4) K) * W⁻¹⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hA3', mul_one W⁻¹, mul_inv_cancel]
  have hA''1 : W⁻¹ * (A : GL (Fin 4) K) * W⁻¹⁻¹ ≠ 1 := by
    intro h
    apply hA1
    apply Subtype.ext
    rw [Subgroup.coe_one]
    calc (A : GL (Fin 4) K) = W * (W⁻¹ * (A : GL (Fin 4) K) * W⁻¹⁻¹) * W⁻¹ := by group
      _ = 1 := by rw [h, mul_one W, mul_inv_cancel]
  have h3 : 3 ∣ p ^ 1 - 1 := by
    rw [pow_one]
    omega
  obtain ⟨P, α, hP, hα3, hα1, hD⟩ := exists_normal_form_SU hK h3 hA''mem hA''3 hA''1
  have hQ : ∀ g, g ∈ SUid σ 4 ↔ (P * W⁻¹) * g * (P * W⁻¹)⁻¹ ∈ SU σ 4 := fun g => by
    rw [hconjW g, hP]
    constructor <;> intro hh <;> convert hh using 1 <;> group
  refine ⟨P * W⁻¹, α, hQ, hα3, hα1, ?_⟩
  rcases hD with hD | hD
  · left
    rw [← hD]
    group
  · right
    rw [← hD]
    group

theorem sl2Datum_U4_long {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp3 : 3 < p) (hK : Nat.card K = (p ^ 1) ^ 2) {A : SUid (unitaryInvolution K p 1) 4}
    {R : GL (Fin 4) K} {α : Kˣ}
    (hQ : ∀ g, g ∈ SUid (unitaryInvolution K p 1) 4 ↔ R * g * R⁻¹ ∈ SU (unitaryInvolution K p 1) 4)
    (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) (hQA : R * (A : GL (Fin 4) K) * R⁻¹ = diagU ![α, 1, 1, α⁻¹]) :
    SL2Datum (SUid (unitaryInvolution K p 1) 4) (A : GL (Fin 4) K) := by
  have hp' : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by
    have : p ≠ 4 := by
      rintro rfl
      norm_num at hp'
    omega
  let σ : K ≃+* K := unitaryInvolution K p 1
  have ht : ((R * (A : GL (Fin 4) K) * R⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(α : K), 1, 1, ((α⁻¹ : Kˣ) : K)] := by
    rw [hQA, diagU_val]
    congr 1
    funext i
    fin_cases i <;> rfl
  have htS : R * (A : GL (Fin 4) K) * R⁻¹ ∈ SU σ 4 := (hQ _).mp A.2
  have h1 : (α : K) ≠ 1 := fun h => hα1 (Units.ext h)
  have h2 : (α : K) ≠ ((α⁻¹ : Kˣ) : K) := ne_inv_of_cube hα3 hα1
  have h3' : (1 : K) ≠ ((α⁻¹ : Kˣ) : K) := fun h => hα1 (by
    have : α⁻¹ = 1 := Units.ext h.symm
    rw [← inv_inv α, this, inv_one])
  obtain ⟨ζ, hζ0⟩ := exists_traceZero_ne_zero hK
  have hζ : unitaryInvolution K p 1 (ζ : K) = -ζ := by
    have := ζ.2
    rw [mem_traceZero] at this
    linear_combination this
  let eS := hypEquiv hζ0 hζ
  refine ⟨fixedSubfield K p 1, inferInstance, inferInstance, p, hp', hp5,
    by rw [card_fixedSubfield hK, pow_one], ?_⟩
  have hφ0 := (isCentData_long σ ht h1 h2 h3').conj hQ rfl
  have hφ := IsCentData.comp_surjective hφ0 eS.toMonoidHom eS.surjective
  refine ⟨_, hφ, ?_, fun B hB hB3 hBA => ?_⟩
  · rw [eq_bot_iff]
    intro s hs
    have hs' : eS s ∈ (ProjGenLinGroup.mk.comp
        ((MulAut.conj R⁻¹).toMonoidHom.comp (iotaL σ))).ker := hs
    rw [ker_mk_conj, ker_mk_iotaL, Subgroup.mem_bot] at hs'
    rw [Subgroup.mem_bot]
    exact eS.injective (hs'.trans (map_one eS).symm)
  · have hB'' : R * B * R⁻¹ ∈ SU σ 4 := (hQ B).mp hB
    have hB''3 : (R * B * R⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hB3, mul_one, mul_inv_cancel]
    have hB''t : (R * B * R⁻¹) * (R * (A : GL (Fin 4) K) * R⁻¹) =
        (R * (A : GL (Fin 4) K) * R⁻¹) * (R * B * R⁻¹) := by
      calc (R * B * R⁻¹) * (R * (A : GL (Fin 4) K) * R⁻¹) = R * (B * A) * R⁻¹ := by group
        _ = R * (A * B) * R⁻¹ := by rw [hBA]
        _ = _ := by group
    obtain ⟨j, M, hjM⟩ := dec_long σ hα3 hα1 htS ht hB'' hB''3 hB''t
    refine ⟨j, eS.symm M, ?_⟩
    change B = (A : GL (Fin 4) K) ^ j * (R⁻¹ * iotaL σ (eS (eS.symm M)) * R⁻¹⁻¹)
    rw [MulEquiv.apply_symm_apply, inv_inv]
    have e : B = R⁻¹ * (R * B * R⁻¹) * R := by group
    rw [e, hjM, conj_pow]
    group

theorem data_U4_short {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ 1) ^ 2) {A : SUid (unitaryInvolution K p 1) 4}
    {R : GL (Fin 4) K} {α : Kˣ}
    (hQ : ∀ g, g ∈ SUid (unitaryInvolution K p 1) 4 ↔ R * g * R⁻¹ ∈ SU (unitaryInvolution K p 1) 4)
    (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hQA : R * (A : GL (Fin 4) K) * R⁻¹ = diagU ![α, α, α⁻¹, α⁻¹]) :
    IsCentData (SUid (unitaryInvolution K p 1) 4) (A : GL (Fin 4) K)
        ((MulAut.conj R⁻¹).toMonoidHom.comp (iotaSo (unitaryInvolution K p 1))) ∧
      (ProjGenLinGroup.mk.comp ((MulAut.conj R⁻¹).toMonoidHom.comp
        (iotaSo (unitaryInvolution K p 1)))).ker = Subgroup.center SL(2, K) ∧
      ∀ B ∈ SUid (unitaryInvolution K p 1) 4, B ^ 3 = 1 → B * A = A * B →
        ∃ (j : ℕ) (S : SL(2, K)), B = (A : GL (Fin 4) K) ^ j *
          ((MulAut.conj R⁻¹).toMonoidHom.comp (iotaSo (unitaryInvolution K p 1))) S := by
  let σ : K ≃+* K := unitaryInvolution K p 1
  have hσ : ∀ c, σ (σ c) = c :=
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK).invol
  have ht : ((R * (A : GL (Fin 4) K) * R⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(α : K), α, ((α⁻¹ : Kˣ) : K), ((α⁻¹ : Kˣ) : K)] := by
    rw [hQA, diagU_val]
    congr 1
    funext i
    fin_cases i <;> rfl
  have htS : R * (A : GL (Fin 4) K) * R⁻¹ ∈ SU σ 4 := (hQ _).mp A.2
  refine ⟨(isCentData_shortOdd σ hσ ht (ne_inv_of_cube hα3 hα1)).conj hQ rfl, ?_,
    fun B hB hB3 hBA => ?_⟩
  · rw [ker_mk_conj, ker_mk_iotaSo]
  · have hB'' : R * B * R⁻¹ ∈ SU σ 4 := (hQ B).mp hB
    have hB''3 : (R * B * R⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hB3, mul_one, mul_inv_cancel]
    have hB''t : (R * B * R⁻¹) * (R * (A : GL (Fin 4) K) * R⁻¹) =
        (R * (A : GL (Fin 4) K) * R⁻¹) * (R * B * R⁻¹) := by
      calc (R * B * R⁻¹) * (R * (A : GL (Fin 4) K) * R⁻¹) = R * (B * A) * R⁻¹ := by group
        _ = R * (A * B) * R⁻¹ := by rw [hBA]
        _ = _ := by group
    obtain ⟨j, S, hjS⟩ := dec_short σ hα3 hα1 htS ht hB'' hB''3 hB''t
    refine ⟨j, S, ?_⟩
    change B = (A : GL (Fin 4) K) ^ j * (R⁻¹ * iotaSo σ S * R⁻¹⁻¹)
    rw [inv_inv]
    have e : B = R⁻¹ * (R * B * R⁻¹) * R := by group
    rw [e, hjS, conj_pow]
    group

theorem data_U4 {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp3 : 3 < p) (hp1 : p % 3 = 1) (hK : Nat.card K = (p ^ 1) ^ 2)
    (A : SUid (unitaryInvolution K p 1) 4) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    SL2Datum (SUid (unitaryInvolution K p 1) 4) (A : GL (Fin 4) K) ∨
      PSL2Datum (SUid (unitaryInvolution K p 1) 4) (A : GL (Fin 4) K) := by
  obtain ⟨R, α, hQ, hα3, hα1, hD | hD⟩ := exists_normal_form_U4 hp1 hK A hA3 hA1
  · exact Or.inl (sl2Datum_U4_long hp3 hK hQ hα3 hα1 hD)
  · right
    have hK2 : Nat.card K = p ^ 2 := by rw [hK, pow_one]
    have hF4 : 4 ≤ Nat.card K := by
      rw [hK2]
      have := Nat.pow_le_pow_left (show 2 ≤ p by omega) 2
      omega
    have h2F : (2 : K) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have h3F : (3 : K) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff K p 3).mp (by exact_mod_cast h)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    obtain ⟨hφ, hker, hdec⟩ := data_U4_short hK hQ hα3 hα1 hD
    exact ⟨K, inferInstance, inferInstance, hF4, h2F, h3F,
      exists_three_mul_sq_eq_one_of_card hp3 hK2, _, hφ, hker, hdec⟩

theorem center_projImage_SUid_eq_bot {p : ℕ} [Fact p.Prime] :
    Subgroup.center
      (projImage (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4)) = ⊥ := by
  have hK : Nat.card (GaloisField p (2 * 1)) = (p ^ 1) ^ 2 := by
    rw [GaloisField.card p (2 * 1) (by norm_num)]
    ring
  have hproj : projSU 4 p 1 =
      projImage (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) := by
    rw [SUid_eq_statedSU hK 4, CFSG.RankThree.PartTwo.Census.projImage_statedSU]
  have hne : (4, p ^ 1) ≠ (3, 2) := fun h => absurd (Prod.mk.inj h).1 (by norm_num)
  have hs : IsSimpleGroup (StatedProj (StatedSU 4 (p ^ 1) (GaloisField p (2 * 1)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU _ p 1 hK 4 (by norm_num) hne
  have : Group.IsPerfect (StatedSU 4 (p ^ 1) (GaloisField p (2 * 1))) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by norm_num) hne
  have hperf : Group.IsPerfect (StatedProj (StatedSU 4 (p ^ 1) (GaloisField p (2 * 1)))) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact Item211Lie2Proof.center_eq_bot_of_mulEquiv
    ((MulEquiv.subgroupCongr hproj).symm.trans (Sec4.projSUEquivStatedProj 4 p 1))
    (CFSG.RankThree.PartOne.KCUnitaryRegular.center_eq_bot_of_isSimpleGroup_of_isPerfect hperf)

end Item211Res4Proof

open Item211Res4Proof Item228Census3Proof

theorem ks211ExcPlusU4_holds : KS211ExcPlusU4 := by
  intro p _ hp3 hp1
  have hK : Nat.card (GaloisField p (2 * 1)) = (p ^ 1) ^ 2 := by
    rw [GaloisField.card p (2 * 1) (by norm_num)]
    ring
  have hproj : projSU 4 p 1 =
      projImage (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) := by
    rw [SUid_eq_statedSU hK 4, CFSG.RankThree.PartTwo.Census.projImage_statedSU]
  refine Item211Lie2Proof.excPlusFor_of_mulEquiv (MulEquiv.subgroupCongr hproj) ?_
  exact excPlusFor_projImage _ center_projImage_SUid_eq_bot
    (fun u hu => pow_four_eq_one_of_det_scalar (mem_SUid.1 hu).1)
    (fun A hA3 hA1 => data_U4 hp3 hp1 hK A hA3 hA1)

end CFSG.RankThree.PartTwo.Sec21

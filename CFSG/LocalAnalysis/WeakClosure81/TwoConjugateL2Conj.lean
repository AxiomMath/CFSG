module

public import CFSG.Quasithin.Background.SmithB45L2Row
public import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateL2Trace

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TwoConjL2

open Matrix CFSG.RankThree.PartOne.CTP

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_conj_u2_eq_l2 {μ : F} (hμ : μ ≠ 0) :
    ∃ γ : SpecialLinearGroup (Fin 2) F, ∀ a : F, γ⁻¹ * u2 a * γ = l2 (μ * a) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) μ
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hμ (by simpa using ht)
  have hdet : (!![0, t⁻¹; t, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination (-1 : F) * h2
  let γ : SpecialLinearGroup (Fin 2) F := ⟨!![0, t⁻¹; t, 0], hdet⟩
  have hγγ : γ * γ = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [γ, Matrix.mul_apply, Fin.sum_univ_two, ht0]
  refine ⟨γ, fun a => ?_⟩
  rw [inv_eq_of_mul_eq_one_right hγγ]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, u2_coe, l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [γ, Matrix.mul_apply, Fin.sum_univ_two, ht0, ht] <;> ring

theorem exists_conj_le_u2 {B : Subgroup (SpecialLinearGroup (Fin 2) F)} (hB : IsPGroup 2 B) :
    ∃ h : SpecialLinearGroup (Fin 2) F, ∀ b ∈ B, ∃ a : F, h⁻¹ * b * h = u2 a := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  set P := CFSG.Quasithin.B45L2.rootSub (⊤ : AddSubgroup F) with hP
  have hPc : Nat.card P = Nat.card F := by
    rw [CFSG.Quasithin.B45L2.card_rootSub]
    exact Nat.card_congr (AddSubgroup.topEquiv (G := F)).toEquiv
  have hcard := card_sl2 (F := F)
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hidx : P.index = Nat.card F ^ 2 - 1 := by
    have h := Subgroup.index_mul_card P
    rw [hPc, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (mul_comm _ _))
  have hodd : ¬ 2 ∣ P.index := by
    rw [hidx]
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    have hq : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
    obtain ⟨k, hk⟩ : Even (Nat.card F) := by
      rw [hq]
      exact Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩
    have hk1 : 1 ≤ k := by omega
    have e : Nat.card F ^ 2 = 4 * (k * k) := by rw [hk]; ring
    have hkk : 1 ≤ k * k := Nat.mul_pos hk1 hk1
    rw [e]
    omega
  have hP2 : IsPGroup 2 P := fun g =>
    ⟨1, Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      simpa using CFSG.Quasithin.B45L2.rootSub_sq (⊤ : AddSubgroup F) g.1 g.2)⟩
  let Pu : Sylow 2 (SpecialLinearGroup (Fin 2) F) := hP2.toSylow hodd
  obtain ⟨Q, hBQ⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) F) Pu Q
  refine ⟨g, fun b hb => ?_⟩
  have hbQ : b ∈ (Q : Subgroup (SpecialLinearGroup (Fin 2) F)) := hBQ hb
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hbQ
  obtain ⟨r, hr, hrb⟩ := Subgroup.mem_map.mp hbQ
  obtain ⟨t, -, rfl⟩ := hr
  refine ⟨t, ?_⟩
  have hu : CFSG.Quasithin.JonesParshall.uMat t = u2 t :=
    Subtype.ext (by rw [CFSG.Quasithin.JonesParshall.uMat_coe, u2_coe])
  have hrb' : g * CFSG.Quasithin.JonesParshall.uMat t * g⁻¹ = b := hrb
  rw [← hrb', hu]
  group

end CFSG.LocalAnalysis.WeakClosure81.TwoConjL2

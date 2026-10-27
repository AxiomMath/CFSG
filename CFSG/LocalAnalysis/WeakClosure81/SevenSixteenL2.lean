module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem finite_of_isL2Gp {S : Type} [Group S] {n : ℕ} (h : IsL2Gp S n) : Finite S := by
  obtain ⟨F, _, hF, -, ⟨e⟩⟩ := h
  haveI := hF
  exact Finite.of_equiv _ e.symm.toEquiv

theorem isL2Gp_of_mulEquiv {S T : Type} [Group S] [Group T] {n : ℕ} (h : IsL2Gp S n)
    (e : S ≃* T) : IsL2Gp T n := by
  obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := h
  exact ⟨F, hF, hfin, hcard, ⟨e.symm.trans f⟩⟩

theorem commutator_eq_top_of_isL2Gp {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n)
    (h : IsL2Gp S n) : commutator S = ⊤ := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  haveI : Group.IsPerfect S :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.IsPerfect.commutator_eq_top

theorem center_specialLinear_two_eq_bot {F : Type} [Field F] [Finite F] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hcard])
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨r, hr, hscal⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : r * r = 1 := by rw [← sq]; exact hr
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  have hez1 : ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← hscal, hr1, map_one]
  exact Subtype.ext hez1

theorem card_eq_of_isL2Gp {S : Type} [Group S] {n : ℕ} (h : IsL2Gp S n) :
    Nat.card S = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have h1 : Nat.card S = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL,
      CFSG.Open.StatedAPI.card_statedSL_two]
  rw [h1, hcard]
  have h2 : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h2]

theorem three_dvd_card_of_isL2Gp {S : Type} [Group S] {n : ℕ} (h : IsL2Gp S n) :
    3 ∣ Nat.card S := by
  rw [card_eq_of_isL2Gp h]
  exact Dvd.dvd.mul_left (by simpa using Nat.sub_one_dvd_pow_sub_one 4 n) _

theorem sixty_le_card_of_isL2Gp {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n) (h : IsL2Gp S n) :
    60 ≤ Nat.card S := by
  rw [card_eq_of_isL2Gp h]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 16 ≤ 4 ^ n := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  calc 60 = 4 * 15 := by norm_num
    _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h4 (by omega)

theorem isSimpleGroup_of_isL2Gp {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n) (h : IsL2Gp S n) :
    IsSimpleGroup S := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hZ := center_specialLinear_two_eq_bot (F := F) hcard
  have hsimp : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    have h4 : 4 ≤ Nat.card F := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  let e2 : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact (e.trans e2).isSimpleGroup

theorem mul_self_eq_one_of_mulVec_eq {F : Type} [Field F] [CharP F 2]
    {g : Matrix.SpecialLinearGroup (Fin 2) F} {v : Fin 2 → F} (hv : v ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : g * g = 1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe g
  have hker : ((g : Matrix (Fin 2) (Fin 2) F) - 1).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hg, sub_self]
  have hdet0 : ((g : Matrix (Fin 2) (Fin 2) F) - 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hker⟩
  rw [Matrix.det_fin_two] at hdet hdet0
  simp only [Matrix.sub_apply, Matrix.one_apply] at hdet0
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp at hdet0
  have hsum : (g : Matrix (Fin 2) (Fin 2) F) 0 0 + (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    linear_combination hdet - hdet0 + h2
  have hd : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    have : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = -(g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      linear_combination hsum
    rw [this, CharTwo.neg_eq]
  rw [hd] at hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
  · linear_combination hdet +
      ((g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0) * h2
  · linear_combination
      ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 1) * h2
  · linear_combination
      ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0) * h2
  · linear_combination hdet +
      ((g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0) * h2

theorem not_isPGroup_two_of_isL2Gp {S : Type} [Group S] {n : ℕ} (h : IsL2Gp S n) :
    ¬ IsPGroup 2 S := by
  haveI := finite_of_isL2Gp h
  intro h2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  have h3 := three_dvd_card_of_isL2Gp h
  rw [hk] at h3
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

theorem eq_bot_of_normal_isPGroup_of_isL2Gp {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n)
    (h : IsL2Gp S n) {N : Subgroup S} (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  haveI := isSimpleGroup_of_isL2Gp hn h
  rcases hN.eq_bot_or_eq_top with h0 | h1
  · exact h0
  · exfalso
    apply not_isPGroup_two_of_isL2Gp h
    rw [h1] at h2
    exact h2.of_equiv Subgroup.topEquiv

theorem not_isSolvable_of_isL2Gp {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n) (h : IsL2Gp S n) :
    ¬ Group.IsSolvable S := by
  intro hS
  haveI := finite_of_isL2Gp h
  haveI : Nontrivial S := by
    have h3 := three_dvd_card_of_isL2Gp h
    have := Nat.le_of_dvd Nat.card_pos h3
    exact Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial S
  rw [commutator_eq_top_of_isL2Gp hn h] at hlt
  exact lt_irrefl _ hlt

end CFSG.LocalAnalysis.WeakClosure81

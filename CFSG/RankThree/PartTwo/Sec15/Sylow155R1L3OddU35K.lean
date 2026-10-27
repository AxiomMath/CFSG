module

public import CFSG.Quasithin.Vol2.KGFact12614U35a
public import CFSG.Models.PGLOrders
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts CFSG.Quasithin.H13.U35A6
open CFSG.SignalizerFunctorTheorem.McBride

section Commute

variable {K : Type} [Field K]

private theorem exists_scalar_of_commute {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {S : GL (Fin 3) K} (hD : S * dU ω hω = dU ω hω * S) (hC : S * cU = cU * S) :
    ∃ c : Kˣ, S = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  have hD' : (S : Matrix (Fin 3) (Fin 3) K) * UnitaryHeisenberg.aMat ω =
      UnitaryHeisenberg.aMat ω * (S : Matrix (Fin 3) (Fin 3) K) := by
    rw [UnitaryHeisenberg.aMat_eq]
    exact congrArg Units.val hD
  have hC' : (S : Matrix (Fin 3) (Fin 3) K) * UnitaryHeisenberg.bMat =
      UnitaryHeisenberg.bMat * (S : Matrix (Fin 3) (Fin 3) K) := congrArg Units.val hC
  obtain ⟨a, ha⟩ := UnitaryHeisenberg.commutant hω hω1 hD' hC'
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact S.ne_zero (by rw [ha, zero_smul])
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, ha, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  rfl

end Commute

section Cube

private theorem pow_conj_eq_of_central {G : Type*} [Group G] {B g z : G}
    (hz : ∀ y : G, z * y = y * z) (hBg : B * g * B⁻¹ = z * g) (n : ℕ) :
    B ^ n * g * (B ^ n)⁻¹ = z ^ n * g := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hBz : B * z * B⁻¹ = z := by rw [← hz B, mul_inv_cancel_right]
    have e1 : B * z ^ n * B⁻¹ = z ^ n := by rw [← conj_pow, hBz]
    calc B ^ (n + 1) * g * (B ^ (n + 1))⁻¹ = B * (B ^ n * g * (B ^ n)⁻¹) * B⁻¹ := by group
      _ = B * (z ^ n * g) * B⁻¹ := by rw [ih]
      _ = (B * z ^ n * B⁻¹) * (B * g * B⁻¹) := by group
      _ = z ^ n * (z * g) := by rw [e1, hBg]
      _ = z ^ (n + 1) * g := by rw [pow_succ, mul_assoc]

private theorem pow_three_commute_of_central {G : Type*} [Group G] {B g z : G}
    (hz : ∀ y : G, z * y = y * z) (hz3 : z ^ 3 = 1) (hBg : B * g * B⁻¹ = z * g) :
    B ^ 3 * g = g * B ^ 3 := by
  have h := pow_conj_eq_of_central hz hBg 3
  rw [hz3, one_mul] at h
  exact mul_inv_eq_iff_eq_mul.1 h

variable {K : Type} [Field K] {h : UnitaryFieldData 5 1 K}

private theorem exists_scalar_conj_of_psuConj_fix (B : unitaryIsom3 h) (g : unitarySU 5 1 K 3)
    (hfix : psuConj h B (g : unitaryPSU h 3) = (g : unitaryPSU h 3)) :
    ∃ c : Kˣ, c ^ 3 = 1 ∧ (B : GL (Fin 3) K) * (g : GL (Fin 3) K) * (B : GL (Fin 3) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * (g : GL (Fin 3) K) := by
  rw [psuConj_mk] at hfix
  obtain ⟨c, -, hc3, hc⟩ := mem_unitaryScalars.1 (QuotientGroup.eq.1 hfix)
  refine ⟨c⁻¹, by rw [inv_pow, hc3, inv_one], ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_suConj] at hc
  have hX : (B : GL (Fin 3) K) * (g : GL (Fin 3) K) * (B : GL (Fin 3) K)⁻¹ =
      (g : GL (Fin 3) K) * (Matrix.GeneralLinearGroup.scalar (Fin 3) c)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← hc, mul_inv_cancel_left]
  rw [hX, ← map_inv]
  exact (Matrix.GeneralLinearGroup.scalar_commute c⁻¹ _).symm

private theorem psuConj_pow_three_eq_one_of_fix {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (B : unitaryIsom3 h) (h1 : psuConj h B (g₁ h hω : unitaryPSU h 3) = g₁ h hω)
    (h2 : psuConj h B (g₂ h : unitaryPSU h 3) = g₂ h) : psuConj h B ^ 3 = 1 := by
  obtain ⟨z₁, hz₁, e₁⟩ := exists_scalar_conj_of_psuConj_fix B _ h1
  obtain ⟨z₂, hz₂, e₂⟩ := exists_scalar_conj_of_psuConj_fix B _ h2
  have c₁ := pow_three_commute_of_central (B := (B : GL (Fin 3) K))
    (fun y => Matrix.GeneralLinearGroup.scalar_commute z₁ y)
    (by rw [← map_pow, hz₁, map_one]) e₁
  have c₂ := pow_three_commute_of_central (B := (B : GL (Fin 3) K))
    (fun y => Matrix.GeneralLinearGroup.scalar_commute z₂ y)
    (by rw [← map_pow, hz₂, map_one]) e₂
  obtain ⟨c, hc⟩ := exists_scalar_of_commute hω hω1 (S := (B : GL (Fin 3) K) ^ 3) c₁ c₂
  rw [← map_pow]
  exact psuConj_eq_one_of_coe_eq_scalar (c := c) (by rw [Subgroup.coe_pow]; exact hc)

end Cube

section Sylow

private theorem factorization_three_sq_mul {m : ℕ} (hm : ¬ 3 ∣ m) :
    (3 ^ 2 * m).factorization 3 = 2 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd hm]
  rfl

private theorem exists_conj_mem_of_card_nine {P : Type} [Group P] [Finite P]
    (hcard : Nat.card P = 126000) (E : Subgroup P) (hE : Nat.card E = 9) {x₁ x₂ : P}
    (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) :
    ∃ g : P, x₁ ∈ E.map (MulAut.conj g).toMonoidHom ∧ x₂ ∈ E.map (MulAut.conj g).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E₀ := Subgroup.closure ({x₁, x₂} : Set P) with hE₀def
  have hpair : ({x₁, x₂} : Set P).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact Commute.refl _
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact h12
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact h12.symm
    · rw [Set.mem_singleton_iff] at ha hb
      subst ha hb
      exact Commute.refl _
  have hcomm : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    have := (Subgroup.isMulCommutative_closure hpair).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have key : ∀ y ∈ E₀, y ^ 3 = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | hz
      · exact h1
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact h2
    | one => exact one_pow 3
    | mul a b ha hb iha ihb => rw [(Commute.mul_pow (hcomm a ha b hb) 3), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hE₀ : IsPGroup 3 ↥E₀ := fun y =>
    ⟨1, Subtype.ext (by rw [pow_one]; simpa using key y y.2)⟩
  obtain ⟨S₁, hS₁⟩ := hE₀.exists_le_sylow
  have hE' : Nat.card ↥E = 3 ^ (Nat.card P).factorization 3 := by
    rw [hE, hcard, show (126000 : ℕ) = 3 ^ 2 * 14000 by norm_num,
      factorization_three_sq_mul (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (Sylow.ofCard E hE') S₁
  have hmem : ∀ x ∈ E₀, x ∈ E.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have hx1 : x ∈ ((g • Sylow.ofCard E hE' : Sylow 3 P) : Subgroup P) := by
      rw [hg]
      exact hS₁ hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx1
    obtain ⟨y, hy, rfl⟩ := hx1
    exact ⟨y, hy, rfl⟩
  exact ⟨g, hmem _ (Subgroup.subset_closure (Set.mem_insert _ _)),
    hmem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩

end Sylow

section Model

variable {K : Type} [Field K]

private theorem exists_cube_root_of_unity (h : UnitaryFieldData 5 1 K) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  classical
  have := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have hU : Nat.card Kˣ = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, h.card]
    norm_num
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hU]; norm_num)
  refine ⟨(u : K), ?_, ?_⟩
  · have : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have := congrArg Units.val this
    simpa using this
  · intro h1
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    norm_num at hu

theorem model_eq_one_of_fix_card_nine (h : UnitaryFieldData 5 1 K)
    (hcard : Nat.card (unitaryPSU h 3) = 126000) (α : MulAut (unitaryPSU h 3))
    (hpow : ∃ n : ℕ, α ^ 2 ^ n = 1) {E : Subgroup (unitaryPSU h 3)} (hE : Nat.card E = 9)
    (hfix : ∀ x ∈ E, α x = x) : α = 1 := by
  classical
  have := h.finite
  obtain ⟨n, hn⟩ := hpow
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_unity h
  obtain ⟨g, hg1, hg2⟩ := exists_conj_mem_of_card_nine hcard E hE (x_comm h hω3) (x1_pow h hω3)
    (x2_pow h)
  set β := MulAut.conj g * α * (MulAut.conj g)⁻¹ with hβ
  have hβfix : ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, β x = x := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [hβ, MulAut.mul_apply, MulEquiv.coe_toMonoidHom, MulAut.inv_apply,
      MulEquiv.symm_apply_apply, hfix y hy]
  have hβn : β ^ 2 ^ n = 1 := by rw [hβ, conj_pow, hn, mul_one, mul_inv_cancel]
  obtain ⟨B, σ, hBσ⟩ := exists_psuConj_mul_psuField (h := h) (by norm_num) β
  have hσω : σ ω = ω := sigma_eq_of_fix h hω3 B σ (by rw [← hBσ]; exact hβfix _ hg1)
    (by rw [← hBσ]; exact hβfix _ hg2)
  have hσ1 : σ = 1 := eq_one_of_fix_omega h hω3 hω1 hσω
  rw [hσ1, map_one, mul_one] at hBσ
  have h3 : β ^ 3 = 1 := by
    rw [hBσ]
    exact psuConj_pow_three_eq_one_of_fix hω3 hω1 B (by rw [← hBσ]; exact hβfix _ hg1)
      (by rw [← hBσ]; exact hβfix _ hg2)
  have hβ1 : β = 1 := by
    have hd3 : orderOf β ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hd2 : orderOf β ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hβn
    have hd : orderOf β ∣ Nat.gcd 3 (2 ^ n) := Nat.dvd_gcd hd3 hd2
    rw [(Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)).gcd_eq_one] at hd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  calc α = (MulAut.conj g)⁻¹ * β * MulAut.conj g := by rw [hβ]; group
    _ = 1 := by rw [hβ1, mul_one, inv_mul_cancel]

end Model

theorem eq_one_of_pow_two_pow_of_fix_card_nine [Fact (Nat.Prime 5)] {L : Type} [Group L]
    [Finite L] (φ : L ≃* CFSG.Assembly.RankThreeEven.projSU 3 5 1) (σ : MulAut L)
    (hσ : ∃ k : ℕ, σ ^ 2 ^ k = 1) {E : Subgroup L} (hE : Nat.card E = 9)
    (hfix : ∀ x ∈ E, σ x = x) : σ = 1 := by
  have hS : CFSG.Open.StatedClassicalModel (CFSG.Assembly.RankThreeEven.projSU 3 5 1) .PSU 3 5 1 :=
    CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      ⟨Fact.out, le_rfl, le_rfl, by decide⟩ (MulEquiv.refl _)
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := hS
  have h : UnitaryFieldData 5 1 K := ⟨Nat.prime_five, le_rfl, by rw [hKcard]; norm_num⟩
  let f : L ≃* unitaryPSU h 3 := (φ.trans e).trans (unitaryPSUEquiv h (by norm_num)).symm
  have hcard : Nat.card (unitaryPSU h 3) = 126000 := by
    rw [← Nat.card_congr f.toEquiv, Nat.card_congr φ.toEquiv,
      CFSG.PGLModel.card_projSU_three_five]
  have h1 : MulAut.congr f σ = 1 := by
    refine model_eq_one_of_fix_card_nine h hcard (MulAut.congr f σ) ?_
      (E := E.map f.toMonoidHom) ?_ ?_
    · obtain ⟨k, hk⟩ := hσ
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    · rw [Subgroup.card_map_of_injective f.injective]
      exact hE
    · rintro _ ⟨y, hy, rfl⟩
      simp [hfix y hy]
  have h2 : σ = (MulAut.congr f).symm (MulAut.congr f σ) := by
    rw [MulEquiv.symm_apply_apply]
  rw [h2, h1, map_one]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

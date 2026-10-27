module

public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL coe_diagGL)
open Matrix
open scoped commutatorElement

variable {k : Type*} [Field k]

section Torus

variable {u : kˣ}

private theorem s23Mat_mul_hSL_mul_s23Mat [CharP k 2] (hk : Nat.card k = 4) (hu : u ≠ 1) :
    LinearFieldFour.s₂₃Mat * hSL u * LinearFieldFour.s₂₃Mat⁻¹ =
      zSL (u⁻¹) * (hSL u)⁻¹ := by
  rw [show LinearFieldFour.s₂₃Mat⁻¹ = LinearFieldFour.s₂₃Mat from
    inv_eq_of_mul_eq_one_right LinearFieldFour.s₂₃Mat_mul_self]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  simp only [coe_hSL hk, coe_zSL hk, coe_hSL_inv hk hu, Matrix.smul_mul, Matrix.one_mul]
  change LinearFieldFour.s₂₃M * LinearFieldFour.hM (u : k) * LinearFieldFour.s₂₃M =
    ((u⁻¹ : kˣ) : k) • hiM (u : k)
  have hu₂ : ((u⁻¹ : kˣ) : k) = (u : k) * u := val_inv_eq hk
  have hω : (u : k) * u + u + 1 = 0 := val_mul_self_add hk hu
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearFieldFour.s₂₃M, LinearFieldFour.hM, hiM, hu₂, Matrix.smul_apply,
      Matrix.mul_fin_three]
  all_goals grind

theorem xDiag_torus (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    xDiag u ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
      ∃ t : projectiveSL 3 k, xDiag u t = t ∧ t * aP u * t⁻¹ = (aP u)⁻¹ := by
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  refine ⟨?_, ⟨proj 3 k LinearFieldFour.s₂₃Mat, ?_, ?_⟩⟩
  · intro h
    change conjAut 3 k (diagGL u) ∈
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range at h
    have hdet := (LinearThreeFourOuter.conjAut_mem_range_conj_iff hk (diagGL u)).mp h
    rw [LinearThreeFourOuter.det_diagGL] at hdet
    exact hu hdet
  · rw [xDiag, conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    have hGL : diagGL u * LinearThreeFourOuter.s23GL * (diagGL u)⁻¹ =
        LinearThreeFourOuter.s23GL := by
      rw [LinearThreeFourOuter.diagGL_mul_s23GL, mul_assoc, mul_inv_cancel, mul_one]
    have h := congrArg (fun A : GL (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k)) hGL
    simpa [LinearThreeFourOuter.coe_s23GL, LinearFieldFour.s₂₃Mat] using h
  · have hs23 := s23Mat_mul_hSL_mul_s23Mat (k := k) hk hu
    calc proj 3 k LinearFieldFour.s₂₃Mat * aP u * (proj 3 k LinearFieldFour.s₂₃Mat)⁻¹
        = proj 3 k (LinearFieldFour.s₂₃Mat * hSL u * LinearFieldFour.s₂₃Mat⁻¹) := by
          rw [aP, ← map_inv, ← map_mul, ← map_mul]
      _ = proj 3 k (zSL (u⁻¹) * (hSL u)⁻¹) := by rw [hs23]
      _ = (aP u)⁻¹ := by rw [map_mul, map_inv, proj_zSL hk, one_mul, aP]

end Torus

variable {X : Type*} [Group X]

theorem pow_three_eq_one_of_isPGroup_zpowers (hk : Nat.card k = 4)
    (χ : X ≃* projectiveSL 3 k) {α : MulAut X}
    (hα : IsPGroup 3 (Subgroup.zpowers α)) : α ^ 3 = 1 := by
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  haveI : Finite (projectiveSL 3 k) :=
    Nat.finite_of_card_ne_zero (by rw [card_projectiveSL hk]; norm_num)
  haveI : Finite X := Finite.of_injective χ χ.injective
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  haveI : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  obtain ⟨hS, -⟩ := pglSylow_transposition (k := k) hk hu
  have hfac : (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 = 3 := by
    rw [card_mulAut hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 241920 = 3 ^ 3 * 8960 by norm_num) (by norm_num)
  have hP : Nat.card (pglSylow (k := k) u) =
      3 ^ (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 := by
    rw [hS, hfac]
    norm_num
  let α' : MulAut (projectiveSL 3 k) := MulAut.congr χ α
  have hmap : (Subgroup.zpowers α).map (MulAut.congr χ).toMonoidHom =
      Subgroup.zpowers α' := by
    simpa [α'] using MonoidHom.map_zpowers (MulAut.congr χ).toMonoidHom α
  have hα' : IsPGroup 3 (Subgroup.zpowers α') := by
    rw [← hmap]
    exact IsPGroup.map hα _
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le (L :=
    MulAut (projectiveSL 3 k)) (p := 3) (P := pglSylow (k := k) u) hP hα'
  obtain ⟨hx, hy, -, hzx, hzy, -⟩ := sylowGen_props (k := k) hk hu
  have hmem : MulAut.conj g α' ∈ pglSylow (k := k) u :=
    hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (Subgroup.mem_zpowers α'))
  have hcube : MulAut.conj g α' ^ 3 = 1 :=
    CFSG.RankThree.Asc83Table.pow_three_eq_one_of_mem (x := xDiag u) (y := yInn)
      hx hzx hzy hy hmem
  have hα'3 : α' ^ 3 = 1 := by
    apply (MulAut.conj g).injective
    rw [map_pow, hcube, map_one]
  apply (MulAut.congr χ).injective
  rw [map_pow, show MulAut.congr χ α = α' from rfl, hα'3, map_one]

theorem card_dvd_27_of_isPGroup (hk : Nat.card k = 4) (χ : X ≃* projectiveSL 3 k)
    {R : Subgroup (MulAut X)} (hR : IsPGroup 3 R) : Nat.card R ∣ 27 := by
  haveI : Finite (projectiveSL 3 k) :=
    Nat.finite_of_card_ne_zero (by rw [card_projectiveSL hk]; norm_num)
  haveI : Finite X := Finite.of_injective χ χ.injective
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
  have hdvd : Nat.card R ∣ Nat.card (MulAut X) := Subgroup.card_subgroup_dvd_card R
  have hAut : Nat.card (MulAut X) = 241920 := by
    rw [Nat.card_congr (MulAut.congr χ).toEquiv, card_mulAut hk]
  rw [hn, hAut] at hdvd
  have hcop : Nat.Coprime (3 ^ n) 8960 := (by norm_num : Nat.Coprime 3 8960).pow_left n
  have h27 : 3 ^ n ∣ 27 := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rwa [show 27 * 8960 = 241920 by norm_num]
  rwa [hn]

theorem card_dvd_9_of_isPGroup (hk : Nat.card k = 4) (χ : X ≃* projectiveSL 3 k)
    {Q : Subgroup X} (hQ : IsPGroup 3 Q) : Nat.card Q ∣ 9 := by
  haveI : Finite (projectiveSL 3 k) :=
    Nat.finite_of_card_ne_zero (by rw [card_projectiveSL hk]; norm_num)
  haveI : Finite X := Finite.of_injective χ χ.injective
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hdvd : Nat.card Q ∣ Nat.card X := Subgroup.card_subgroup_dvd_card Q
  have hX : Nat.card X = 20160 := by
    rw [Nat.card_congr χ.toEquiv, card_projectiveSL hk]
  rw [hn, hX] at hdvd
  have hcop : Nat.Coprime (3 ^ n) 2240 := (by norm_num : Nat.Coprime 3 2240).pow_left n
  have h9 : 3 ^ n ∣ 9 := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rwa [show 9 * 2240 = 20160 by norm_num]
  rwa [hn]

theorem exists_inverting_of_card_eq_nine (hk : Nat.card k = 4)
    (χ : X ≃* projectiveSL 3 k) {E : Subgroup X} (hE : Nat.card E = 9) :
    ∃ t : X, ∀ e ∈ E, t * e * t⁻¹ = e⁻¹ := by
  have hE' : Nat.card (E.map χ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective χ.injective, hE]
  obtain ⟨t₀, -, -, hinv⟩ := exists_involution_inverting hk hE'
  refine ⟨χ.symm t₀, ?_⟩
  intro e he
  apply χ.injective
  calc χ (χ.symm t₀ * e * (χ.symm t₀)⁻¹)
      = t₀ * χ e * t₀⁻¹ := by rw [map_mul, map_mul, map_inv]; simp
    _ = (χ e)⁻¹ := hinv (χ e) (Subgroup.mem_map_of_mem χ.toMonoidHom he)
    _ = χ (e⁻¹) := by rw [map_inv]

end CFSG.RankThree.PartTwo.KFacts.L34

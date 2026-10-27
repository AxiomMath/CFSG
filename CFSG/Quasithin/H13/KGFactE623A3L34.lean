module

public import CFSG.Quasithin.Background.ONanE68Lin3Mat
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.Quasithin.H13.KGE623A3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Lin2.L3Core

variable {F : Type} [Field F]

theorem exists_conjAut_of_pow_three [Finite F] (hF2 : ∀ σ : F ≃+* F, σ * σ = 1)
    {τ : MulAut (projectiveSL 3 F)} (hτ3 : τ ^ 3 = 1) :
    ∃ A : GL (Fin 3) F, τ = conjAut 3 F A := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) (by norm_num)
  obtain ⟨A, σ, ε, hε, hτ⟩ := hgen τ
  obtain ⟨-, hff, hfc, hδδ, hδc, hδf, -⟩ := standard_automorphism_transport (K := F) (n := 3)
  have hf2 : fieldAut 3 F σ * fieldAut 3 F σ = 1 := by
    rw [hff, hF2 σ]
    exact map_one _
  have hδinv : (dualAut 3 F)⁻¹ = dualAut 3 F := inv_eq_of_mul_eq_one_right hδδ
  set w := fieldAut 3 F σ * dualAut 3 F ^ ε with hw
  have hw2 : w * w = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rw [hw, pow_zero, mul_one, hf2]
    · rw [hw, pow_one]
      calc fieldAut 3 F σ * dualAut 3 F * (fieldAut 3 F σ * dualAut 3 F)
          = fieldAut 3 F σ * (dualAut 3 F * fieldAut 3 F σ * dualAut 3 F) := by group
        _ = 1 := by rw [hδf, hf2]
  have hwc : ∀ B : GL (Fin 3) F, ∃ B' : GL (Fin 3) F, w * conjAut 3 F B = conjAut 3 F B' * w := by
    intro B
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · refine ⟨GeneralLinearGroup.map (σ : F →+* F) B, ?_⟩
      rw [hw, pow_zero, mul_one, ← hfc σ B]
      group
    · refine ⟨GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.inverseTranspose B), ?_⟩
      have e1 : dualAut 3 F * conjAut 3 F B =
          conjAut 3 F (GeneralLinearGroup.inverseTranspose B) * dualAut 3 F := by
        rw [← hδc B]
        calc dualAut 3 F * conjAut 3 F B
            = dualAut 3 F * conjAut 3 F B * (dualAut 3 F * dualAut 3 F) := by rw [hδδ, mul_one]
          _ = dualAut 3 F * conjAut 3 F B * dualAut 3 F * dualAut 3 F := by group
      have e2 : fieldAut 3 F σ * conjAut 3 F (GeneralLinearGroup.inverseTranspose B) =
          conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F)
            (GeneralLinearGroup.inverseTranspose B)) * fieldAut 3 F σ := by
        rw [← hfc σ]
        group
      rw [hw, pow_one]
      calc fieldAut 3 F σ * dualAut 3 F * conjAut 3 F B
          = fieldAut 3 F σ * (dualAut 3 F * conjAut 3 F B) := by group
        _ = fieldAut 3 F σ * conjAut 3 F (GeneralLinearGroup.inverseTranspose B) * dualAut 3 F := by
            rw [e1]; group
        _ = _ := by rw [e2]; group
  obtain ⟨A', hA'⟩ := hwc A
  have h3 : τ ^ 3 = conjAut 3 F (A * A' * A) * w := by
    rw [hτ, pow_three, map_mul, map_mul]
    calc conjAut 3 F A * w * (conjAut 3 F A * w * (conjAut 3 F A * w))
        = conjAut 3 F A * (w * conjAut 3 F A) * w * conjAut 3 F A * w := by group
      _ = conjAut 3 F A * (conjAut 3 F A' * w) * w * conjAut 3 F A * w := by rw [hA']
      _ = conjAut 3 F A * conjAut 3 F A' * (w * w) * conjAut 3 F A * w := by group
      _ = conjAut 3 F A * conjAut 3 F A' * conjAut 3 F A * w := by rw [hw2]; group
  rw [hτ3] at h3
  have hwA : w = conjAut 3 F (A * A' * A)⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right h3.symm
  refine ⟨A * (A * A' * A)⁻¹, ?_⟩
  rw [hτ, mul_assoc, ← hw, hwA, ← map_mul]

theorem mul_comm_of_conjAut_fix {A : GL (Fin 3) F} {g : Matrix.SpecialLinearGroup (Fin 3) F}
    (htr : Matrix.trace (g : Matrix (Fin 3) (Fin 3) F) ≠ 0)
    (h : conjAut 3 F A (proj 3 F g) = proj 3 F g) :
    (A : Matrix (Fin 3) (Fin 3) F) * g = g * A := by
  rw [conjAut_proj, proj_eq_proj_iff] at h
  obtain ⟨ω, -, hω⟩ := h
  set C := ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g with hC
  have hCm : (C : Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) * g *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := coe_slConjugation A g
  have hg : (g : Matrix (Fin 3) (Fin 3) F) = (ω : F) • (C : Matrix (Fin 3) (Fin 3) F) := by
    have h1 : ((C⁻¹ * g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.scalar (Fin 3) (ω : F) := hω
    have h2 : (g : Matrix (Fin 3) (Fin 3) F) = (C : Matrix (Fin 3) (Fin 3) F) *
        ((C⁻¹ * g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [h2, h1]
    ext i j
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]
  have htrC : Matrix.trace (C : Matrix (Fin 3) (Fin 3) F) =
      Matrix.trace (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [hCm]
    exact Matrix.trace_units_conj A g
  have hω1 : (ω : F) = 1 := by
    have h1 := congrArg Matrix.trace hg
    rw [Matrix.trace_smul, htrC, smul_eq_mul] at h1
    have h2 : ((ω : F) - 1) * Matrix.trace (g : Matrix (Fin 3) (Fin 3) F) = 0 := by
      linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right htr)
  rw [hω1, one_smul, hCm] at hg
  calc (A : Matrix (Fin 3) (Fin 3) F) * g
      = (A : Matrix (Fin 3) (Fin 3) F) * g *
          (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * A) := by
        rw [Units.inv_mul, mul_one]
    _ = g * A := by rw [← mul_assoc, ← hg]

omit [Field F] in
theorem entries_of_comm_wM [Field F] {A : Matrix (Fin 3) (Fin 3) F} {c : F} (hc : c ≠ 0)
    (h : A * wM c = wM c * A) : A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 ∧ A 0 0 = A 2 2 := by
  have e := fun i j => congrFun (congrFun h i) j
  have e12 := e 1 2
  have e22 := e 2 2
  have e01 := e 0 1
  have e02 := e 0 2
  simp [wM, Matrix.mul_apply, Fin.sum_univ_three] at e12 e22 e01 e02
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases e12 with h1 | h1
    · exact h1
    · exact absurd h1 hc
  · rcases e22 with h1 | h1
    · exact h1
    · exact absurd h1 hc
  · rcases e01 with h1 | h1
    · exact absurd h1 hc
    · exact h1
  · exact mul_left_cancel₀ hc (by linear_combination e02)

theorem comm_entries_mat {A : Matrix (Fin 3) (Fin 3) F} (h10 : A 1 0 = 0) (h21 : A 2 1 = 0)
    {x y z : F}
    (h : A * !![1, x, z + x * y; 0, 1, y; 0, 0, 1] = !![1, x, z + x * y; 0, 1, y; 0, 0, 1] * A) :
    (A 0 0 - A 1 1) * x = 0 ∧ (A 1 1 - A 2 2) * y = 0 ∧
      (A 0 0 - A 2 2) * (z + x * y) + A 0 1 * y - x * A 1 2 = 0 := by
  have e01 := congrFun (congrFun h 0) 1
  have e12 := congrFun (congrFun h 1) 2
  have e02 := congrFun (congrFun h 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h21] at e01 e12 e02
  exact ⟨by linear_combination e01, by linear_combination e12, by linear_combination e02⟩

theorem conjAut_eq_one_of_scalar {B : GL (Fin 3) F} {l : F}
    (hB : (B : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) l) : conjAut 3 F B = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have hc : Commute (B : Matrix (Fin 3) (Fin 3) F) (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [hB]
    exact Matrix.scalar_commute l (fun r => mul_comm l r) _
  calc (B : Matrix (Fin 3) (Fin 3) F) * g * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = g * B * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [hc.eq]
    _ = g := by rw [mul_assoc, Units.mul_inv, mul_one]

variable [CharP F 2]

theorem pow_four_eq_scalar {A : Matrix (Fin 3) (Fin 3) F} (h10 : A 1 0 = 0) (h20 : A 2 0 = 0)
    (h21 : A 2 1 = 0) (h01 : A 0 0 = A 1 1) (h02 : A 0 0 = A 2 2) :
    A ^ 4 = Matrix.scalar (Fin 3) (A 0 0 ^ 4) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hA2 : A ^ 2 = !![A 0 0 ^ 2, 0, A 0 1 * A 1 2; 0, A 0 0 ^ 2, 0; 0, 0, A 0 0 ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, ← h01, ← h02] <;>
      (ring_nf; simp [h2])
  rw [show A ^ 4 = A ^ 2 * A ^ 2 by rw [← pow_add], hA2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    (ring_nf <;> simp [h2])

theorem card_projUnitriangular_eq [Finite F] :
    Nat.card (projUnitriangular 3 F) = Nat.card F ^ 3 := by
  have hbij : Function.Bijective (fun t : F × F × F =>
      (⟨hei t.1 t.2.1 t.2.2, hei_mem _ _ _⟩ : projUnitriangular 3 F)) := by
    constructor
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
      obtain ⟨rfl, rfl, rfl⟩ := hei_inj (congrArg Subtype.val h)
      rfl
    · rintro ⟨s, hs⟩
      obtain ⟨a, b, c, rfl⟩ := exists_hei hs
      exact ⟨(a, b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, Nat.card_prod]
  ring

theorem trace_hei_ne_zero (a b c : F) : Matrix.trace
    ((wMat c * xMat a * yMat b : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
  rw [coe_hei]
  have h : (1 : F) + 1 + 1 = 1 := by rw [CharTwo.add_self_eq_zero, zero_add]
  simp [Matrix.trace, Fin.sum_univ_three, h]

theorem false_of_aut_projSL3_four [Finite F] (hF : Nat.card F = 4)
    {τ : MulAut (projectiveSL 3 F)} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {c : F} (hc : c ≠ 0)
    (hτc : τ (proj 3 F (wMat c)) = proj 3 F (wMat c)) {E : Finset (projectiveSL 3 F)}
    (hE : E.card ≤ 4) (hbd : ∀ u ∈ projUnitriangular 3 F, τ u * u⁻¹ ∈ E) : False := by
  classical
  have hF2 : ∀ σ : F ≃+* F, σ * σ = 1 := by
    obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality (F := F)
      (p := 2) (n := 2) Nat.prime_two (by norm_num) (by rw [hF]; norm_num)
    intro σ
    have h1 : σ ^ Nat.card (F ≃+* F) = 1 := pow_card_eq_one'
    rw [hcard] at h1
    rw [← pow_two]
    exact h1
  obtain ⟨A, rfl⟩ := exists_conjAut_of_pow_three hF2 hτ3
  have htrw : Matrix.trace ((wMat c : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
    show Matrix.trace (wM c) ≠ 0
    have h : (1 : F) + 1 + 1 = 1 := by rw [CharTwo.add_self_eq_zero, zero_add]
    simp [wM, Matrix.trace, Fin.sum_univ_three, h]
  have hAw := mul_comm_of_conjAut_fix htrw hτc
  obtain ⟨h10, h20, h21, h02⟩ := entries_of_comm_wM hc hAw
  set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
  by_cases hab : M 0 0 = M 1 1
  ·
    apply hτ1
    have h4 : conjAut 3 F A ^ 4 = 1 := by
      rw [← map_pow]
      refine conjAut_eq_one_of_scalar (l := M 0 0 ^ 4) ?_
      rw [Units.val_pow_eq_pow_val]
      exact pow_four_eq_scalar h10 h20 h21 hab h02
    calc conjAut 3 F A = conjAut 3 F A ^ 4 * (conjAut 3 F A ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hτ3]; group
  ·
    set U := projUnitriangular 3 F with hU
    have : Fintype ↥U := Fintype.ofFinite _
    have hCcard : Nat.card {u : U // conjAut 3 F A u = u} ≤ 4 := by
      have hns : ¬ (M 0 0 = M 1 1 ∧ M 1 1 = M 2 2) := fun h => hab h.1
      refine le_trans ?_ (le_of_le_of_eq (CFSG.Quasithin.E6.E68Proof.Lin3.card_solutions_le
        (M 0 0) (M 1 1) (M 2 2) (M 0 1) (M 1 2) hns) hF)
      have hcoord : ∀ u : {u : U // conjAut 3 F A u = u}, ∃ t : F × F × F,
          (u : projectiveSL 3 F) = hei t.1 t.2.1 t.2.2 := fun u => by
        obtain ⟨a, b, z, h⟩ := exists_hei u.1.2
        exact ⟨(a, b, z), h⟩
      choose t ht using hcoord
      refine Nat.card_le_card_of_injective (fun u => ⟨t u, ?_⟩) fun u v huv => ?_
      · have hfix := u.2
        rw [ht u, hei_eq_proj] at hfix
        have hcomm := mul_comm_of_conjAut_fix (trace_hei_ne_zero _ _ _) hfix
        rw [coe_hei] at hcomm
        exact comm_entries_mat h10 h21 hcomm
      · have h1 : t u = t v := congrArg Subtype.val huv
        apply Subtype.ext
        apply Subtype.ext
        rw [ht u, ht v, h1]
    have hfib : ∀ e ∈ E, (Finset.univ.filter (fun u : U =>
        conjAut 3 F A u * (u : projectiveSL 3 F)⁻¹ = e)).card ≤ 4 := by
      intro e _
      set Fib := Finset.univ.filter (fun u : U =>
        conjAut 3 F A u * (u : projectiveSL 3 F)⁻¹ = e) with hFib
      rcases Fib.eq_empty_or_nonempty with h0 | ⟨u₀, hu₀⟩
      · rw [h0, Finset.card_empty]
        omega
      · have hu₀e : conjAut 3 F A u₀ * (u₀ : projectiveSL 3 F)⁻¹ = e :=
          (Finset.mem_filter.mp hu₀).2
        refine le_trans ?_ hCcard
        rw [← Nat.card_eq_finsetCard]
        refine Nat.card_le_card_of_injective (fun u => ⟨u₀⁻¹ * u.1, ?_⟩) fun u v huv => ?_
        · have hue : conjAut 3 F A u.1 * ((u.1 : U) : projectiveSL 3 F)⁻¹ = e :=
            (Finset.mem_filter.mp u.2).2
          show conjAut 3 F A ((u₀⁻¹ * u.1 : U) : projectiveSL 3 F) = _
          rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
          have h1 : conjAut 3 F A (u₀ : projectiveSL 3 F) = e * u₀ := by
            rw [← hu₀e]; group
          have h2 : conjAut 3 F A ((u.1 : U) : projectiveSL 3 F) = e * u.1 := by
            rw [← hue]; group
          rw [h1, h2]
          group
        · have h1 : u₀⁻¹ * u.1 = u₀⁻¹ * v.1 := congrArg Subtype.val huv
          exact Subtype.ext (mul_left_cancel h1)
    have hcount := Finset.card_le_mul_card_image_of_maps_to (s := (Finset.univ : Finset U))
      (t := E) (f := fun u : U => conjAut 3 F A u * (u : projectiveSL 3 F)⁻¹)
      (fun u _ => hbd u u.2) 4 hfib
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hU, card_projUnitriangular_eq, hF] at hcount
    omega

end CFSG.Quasithin.H13.KGE623A3

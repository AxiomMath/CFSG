module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU4Lo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open Matrix CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor diagU diagU_val permGL_conj_diagU
  permGL_mem_SU)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD weyl₂ shortSL coe_iotaS blkS
  coe_torusD perfectResidual_short perfectResidual_conj conj_weyl₂
  nonempty_shortSL_mulEquiv_galois
  entry_eq_zero_of_commute commute_of_mem_centralizer)
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

omit [Finite F] [CharP F 2] in
private theorem diagonal_of_commute_two {g : Matrix (Fin 4) (Fin 4) F}
    {d₁ d₂ : Fin 4 → F}
    (h₁ : g * Matrix.diagonal d₁ = Matrix.diagonal d₁ * g)
    (h₂ : g * Matrix.diagonal d₂ = Matrix.diagonal d₂ * g)
    (hsep : ∀ i j : Fin 4, i ≠ j → d₁ i ≠ d₁ j ∨ d₂ i ≠ d₂ j) :
    g = Matrix.diagonal (fun i => g i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rcases hsep i j hij with h | h
    · rw [entry_eq_zero_of_commute h₁ h]
      simp [hij]
    · rw [entry_eq_zero_of_commute h₂ h]
      simp [hij]

omit [Finite F] [CharP F 2] in
private theorem eq_diagonal_of_mem_centralizer_d8Tor {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    {g : GL (Fin 4) F}
    (hg : g ∈ Subgroup.centralizer (d8Tor 3 F 4 : Set (GL (Fin 4) F))) :
    (g : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (fun i => (g : Matrix (Fin 4) (Fin 4) F) i i) := by
  let a : F := ((ω : Fˣ) : F)
  have ha3 : a ^ 3 = 1 := by
    change ((ω : Fˣ) : F) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by
    rw [h] at ha3
    norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    calc a = a ^ 3 * a⁻¹ * a⁻¹ := by field_simp
      _ = 1 := by rw [ha3, one_mul, ← h, h2]
  have hinv1 : a⁻¹ ≠ 1 := fun h => ha1 (by rw [← inv_inv a, h, inv_one])
  let d1 : Fin 4 → F := ![a, 1, 1, a⁻¹]
  let d2 : Fin 4 → F := ![1, a, a⁻¹, 1]
  have ht1 : ((torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d1 := by
    rw [coe_torusD]
    simp [d1, a, Units.val_inv_eq_inv_val]
  have ht2 : ((torusD ((1, ω) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d2 := by
    rw [coe_torusD]
    simp [d2, a, Units.val_inv_eq_inv_val]
  have hmem1 : torusD ((ω, 1) : D8Mod 3 F) ∈ d8Tor 3 F 4 := ⟨(ω, 1), rfl⟩
  have hmem2 : torusD ((1, ω) : D8Mod 3 F) ∈ d8Tor 3 F 4 := ⟨(1, ω), rfl⟩
  have hgc1 : g ∈ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F)) :=
    Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hmem1) hg
  have hgc2 : g ∈ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F)) :=
    Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hmem2) hg
  have hc1 := commute_of_mem_centralizer hgc1
  have hc2 := commute_of_mem_centralizer hgc2
  rw [ht1] at hc1
  rw [ht2] at hc2
  refine diagonal_of_commute_two hc1 hc2 ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [d1, d2, hainv.symm]

omit [Finite F] [CharP F 2] in
private theorem commute_diagU_of_mem_centralizer_d8Tor {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    (v : Fin 4 → Fˣ) {g : GL (Fin 4) F}
    (hg : g ∈ Subgroup.centralizer (d8Tor 3 F 4 : Set (GL (Fin 4) F))) :
    Commute (diagU v) g := by
  have hgdiag := eq_diagonal_of_mem_centralizer_d8Tor hω hg
  have hmat : Commute ((diagU v : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [diagU_val, hgdiag]
    exact Matrix.commute_diagonal _ _
  apply Units.ext
  change ((diagU v : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((diagU v : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  exact hmat.eq

omit [Finite F] [CharP F 2] in
private theorem diagU_four_mem_shortSL {σ : F ≃+* F} {ν : Fˣ} {a : F}
    (hνa : ((ν : Fˣ) : F) = a) (hσa : σ a = a⁻¹) :
    (diagU ![ν, ν⁻¹, ν⁻¹, ν] : GL (Fin 4) F) ∈ shortSL σ := by
  have ha0 : a ≠ 0 := by
    rw [← hνa]
    exact Units.ne_zero ν
  have hνinva : (((ν⁻¹ : Fˣ) : F)) = a⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hνa]
  have hσainv : σ a⁻¹ = a := by
    rw [map_inv₀, hσa, inv_inv]
  let B : Matrix (Fin 2) (Fin 2) F := Matrix.diagonal ![a, a⁻¹]
  have hBdet : B.det = 1 := by
    simp [B, Matrix.det_diagonal, Fin.prod_univ_two, ha0]
  let Bs : SpecialLinearGroup (Fin 2) F := ⟨B, hBdet⟩
  refine ⟨Bs, ?_⟩
  apply Units.ext
  rw [coe_iotaS, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bs, B, blkS, hνa, hνinva, hσa, hσainv]

omit [Finite F] [CharP F 2] in
private theorem permGL_swap_fix_diagU_four (ν : Fˣ) :
    weyl₂ * (diagU ![ν, ν⁻¹, ν⁻¹, ν] : GL (Fin 4) F) * weyl₂⁻¹ =
      (diagU ![ν, ν⁻¹, ν⁻¹, ν] : GL (Fin 4) F) := by
  rw [weyl₂, permGL_conj_diagU, Equiv.symm_swap]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [Finite F] [CharP F 2] in
private theorem torusD_three_diag {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) :
    ∃ a : F, a ≠ a⁻¹ ∧
      ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        Matrix.diagonal ![a, a, a⁻¹, a⁻¹] := by
  let a : F := ((ω : Fˣ) : F)
  have ha3 : a ^ 3 = 1 := by
    change ((ω : Fˣ) : F) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by
    rw [h] at ha3
    norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    calc a = a ^ 3 * a⁻¹ * a⁻¹ := by field_simp
      _ = 1 := by rw [ha3, one_mul, ← h, h2]
  refine ⟨a, hainv, ?_⟩
  rw [coe_torusD]
  simp [a, Units.val_inv_eq_inv_val]

private theorem exists_diagU_four_centP (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ b + 1) :
    ∃ d : GL (Fin 4) F, orderOf d = p ∧
      d ∈ shortSL (unitaryInvolution F 2 b) ∧
      d ∈ (shortSL (unitaryInvolution F 2 b)).map
        (MulAut.conj weyl₂).toMonoidHom ∧
      d ∈ Subgroup.centralizer
        (((SU (unitaryInvolution F 2 b) 4 ⊓
          Subgroup.centralizer (d8Tor 3 F 4 : Set (GL (Fin 4) F))) :
            Subgroup (GL (Fin 4) F)) : Set (GL (Fin 4) F)) := by
  have hdvd : p ∣ (2 ^ b) ^ 2 - 1 := by
    have hsq : (2 ^ b) ^ 2 - 1 = ((2 ^ b) - 1) * (2 ^ b + 1) := by
      have h1 : (1 : ℕ) = 1 ^ 2 := by norm_num
      rw [h1, Nat.sq_sub_sq, mul_comm]
      norm_num
    rw [hsq]
    exact Dvd.dvd.mul_left hpq _
  have hpF : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    exact hdvd
  obtain ⟨ν, hν⟩ := @exists_prime_orderOf_dvd_card' (Fˣ) _ _ p ⟨hp⟩ hpF
  have hνpow : ν ^ (2 ^ b + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hν]; exact hpq)
  have hνp : ν ^ p = 1 := by
    rw [← hν]
    exact pow_orderOf_eq_one ν
  have hνinvp : (ν⁻¹ : Fˣ) ^ p = 1 := by
    rw [inv_pow, hνp, inv_one]
  have hν1 : ν ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hν
    exact hp.one_lt.ne' hν.symm
  let a : F := ((ν : Fˣ) : F)
  have hνa : ((ν : Fˣ) : F) = a := rfl
  have hmul : ((ν ^ 2 ^ b : Fˣ) : F) * ((ν : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, ← pow_succ]
    exact congrArg (fun u : Fˣ => (u : F)) hνpow
  have hσa : unitaryInvolution F 2 b a = a⁻¹ := by
    change unitaryInvolution F 2 b ((ν : Fˣ) : F) = (((ν : Fˣ) : F))⁻¹
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← Units.val_pow_eq_pow_val]
    exact eq_inv_of_mul_eq_one_left hmul
  let d : GL (Fin 4) F := diagU ![ν, ν⁻¹, ν⁻¹, ν]
  have hd_shortSL : d ∈ shortSL (unitaryInvolution F 2 b) :=
    diagU_four_mem_shortSL hνa hσa
  have hfix : weyl₂ * d * weyl₂⁻¹ = d := by
    change weyl₂ * diagU ![ν, ν⁻¹, ν⁻¹, ν] * weyl₂⁻¹ = diagU ![ν, ν⁻¹, ν⁻¹, ν]
    exact permGL_swap_fix_diagU_four ν
  have hd_shortSL4 : d ∈ (shortSL (unitaryInvolution F 2 b)).map
      (MulAut.conj weyl₂).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨d, hd_shortSL, hfix⟩
  refine ⟨d, ?_, hd_shortSL, hd_shortSL4, ?_⟩
  · exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.orderOf_diagU_four
      hp hνp hνinvp hν1
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (commute_diagU_of_mem_centralizer_d8Tor hω ![ν, ν⁻¹, ν⁻¹, ν] hg.2).symm.eq

theorem u4_exists_centP (hb : 0 < b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ b + 1)
    {ℓ : Subgroup (GL (Fin 4) F)}
    (hℓ : ℓ = zpowers (torusD ((ω, ω) : D8Mod 3 F)) ∨
      ℓ = zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) :
    ∃ D₀ : Subgroup (GL (Fin 4) F), D₀ ≤ F08.KOf8103 (SU (unitaryInvolution F 2 b) 4) ℓ ∧
      Nat.card D₀ = p ∧
      D₀ ≤ centralizer ((SU (unitaryInvolution F 2 b) 4 ⊓
        centralizer (d8Tor 3 F 4 : Set (GL (Fin 4) F)) : Subgroup (GL (Fin 4) F)) :
          Set (GL (Fin 4) F)) := by
  have hσσ : ∀ c, unitaryInvolution F 2 b (unitaryInvolution F 2 b c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨d, hdord, hd_shortSL, hd_shortSL4, hd_cent⟩ :=
    exists_diagU_four_centP hF hω hp hpq
  obtain ⟨eS⟩ := nonempty_shortSL_mulEquiv_galois (unitaryInvolution F 2 b) hb hF
  have hperfS : ⁅shortSL (unitaryInvolution F 2 b),
      shortSL (unitaryInvolution F 2 b)⁆ = shortSL (unitaryInvolution F 2 b) :=
    Subgroup.isPerfect_iff.mp
      (CFSG.RankThree.PartTwo.Sec21.isPerfect_of_mulEquiv_projSL (by omega) eS)
  obtain ⟨a, hainv, ht3⟩ := torusD_three_diag hω
  have hS3 : inSubgroup perfectResidual
      (SU (unitaryInvolution F 2 b) 4 ⊓ Subgroup.centralizer
        (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
      shortSL (unitaryInvolution F 2 b) :=
    perfectResidual_short (unitaryInvolution F 2 b) hσσ ht3 hainv hperfS
  have hw2 : weyl₂ ∈ SU (unitaryInvolution F 2 b) 4 :=
    permGL_mem_SU (unitaryInvolution F 2 b) _ (by decide)
  have hL4 : Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) =
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
        (MulAut.conj weyl₂).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₂ ((ω, ω) : D8Mod 3 F)).symm
  have hS4 : inSubgroup perfectResidual
      (SU (unitaryInvolution F 2 b) 4 ⊓ Subgroup.centralizer
        (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
      (shortSL (unitaryInvolution F 2 b)).map (MulAut.conj weyl₂).toMonoidHom := by
    rw [hL4, perfectResidual_conj hw2, hS3]
  have hK3 : F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))) =
      shortSL (unitaryInvolution F 2 b) := hS3
  have hK4 : F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
      (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) =
      (shortSL (unitaryInvolution F 2 b)).map (MulAut.conj weyl₂).toMonoidHom := hS4
  refine ⟨Subgroup.zpowers d, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    rcases hℓ with hℓ | hℓ
    · rw [hℓ, hK3]
      exact hd_shortSL
    · rw [hℓ, hK4]
      exact hd_shortSL4
  · rw [Nat.card_zpowers, hdord]
  · rw [Subgroup.zpowers_le]
    exact hd_cent

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

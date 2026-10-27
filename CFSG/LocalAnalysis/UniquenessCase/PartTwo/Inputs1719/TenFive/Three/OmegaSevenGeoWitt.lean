module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenGeoDefs
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Witt

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Open QuadraticMap

private theorem omSevenGW_polarNondegOn_inf_ker {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) {W : Submodule K V}
    (hW : PolarNondegOn Q W) {x : V} (hxW : x ∈ W) (hQx : Q x ≠ 0) :
    PolarNondegOn Q (W ⊓ LinearMap.ker (polarBilin Q x)) := by
  intro y hy hyperp
  rw [Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply] at hy
  apply hW y hy.1
  intro z hz
  have hxx : polar Q x x ≠ 0 := by
    rw [polar_self_eq_two_mul]
    exact mul_ne_zero h2 hQx
  have hmem : z - (polar Q x z / polar Q x x) • x ∈ W ⊓ LinearMap.ker (polarBilin Q x) := by
    refine ⟨W.sub_mem hz (W.smul_mem _ hxW), ?_⟩
    show polarBilin Q x (z - (polar Q x z / polar Q x x) • x) = 0
    rw [polarBilin_apply_apply, polar_sub_right, polar_smul_right_eq,
      div_mul_cancel₀ _ hxx, sub_self]
  have h1 : polar Q y (z - (polar Q x z / polar Q x x) • x) = 0 := hyperp _ hmem
  have hyx : polar Q y x = 0 := by rw [polar_comm]; exact hy.2
  have hsplit : polar Q y z = polar Q y (z - (polar Q x z / polar Q x x) • x) +
      (polar Q x z / polar Q x x) * polar Q y x := by
    rw [polar_sub_right, polar_smul_right_eq]
    ring
  rw [hsplit, h1, hyx, mul_zero, add_zero]

private noncomputable def omSevenGW_stdPair (K : Type) [Field K] (i : Fin 3) :
    HypPair (quadOdd 3 K) where
  e := Pi.single (Sum.inl i) 1
  f := Pi.single (Sum.inr (Sum.inl i)) 1
  Q_e := by
    rw [quadOdd_apply]
    simp [Pi.single_apply]
  Q_f := by
    rw [quadOdd_apply]
    simp [Pi.single_apply]
  polar_ef := by
    rw [polar_quadOdd]
    simp [Pi.single_apply]

@[simp] private theorem omSevenGW_stdPair_e (K : Type) [Field K] (i : Fin 3) :
    (omSevenGW_stdPair K i).e = Pi.single (Sum.inl i) 1 := rfl

@[simp] private theorem omSevenGW_stdPair_f (K : Type) [Field K] (i : Fin 3) :
    (omSevenGW_stdPair K i).f = Pi.single (Sum.inr (Sum.inl i)) 1 := rfl

private theorem omSevenGW_stdPair_orth {K : Type} [Field K] {i j : Fin 3} (hij : i ≠ j) :
    (omSevenGW_stdPair K i).Orth (omSevenGW_stdPair K j) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [omSevenGW_stdPair_e, omSevenGW_stdPair_f, polar_quadOdd]
      simp [Pi.single_apply, hij, Ne.symm hij]

private theorem omSevenGW_exists_hypPairs {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (h2 : (2 : K) ≠ 0)
    {u w : OmegaSevenIdx → K} (h : OmegaSevenShortPair u w) :
    ∃ T₁ T₂ : HypPair (quadOdd 3 K), T₁.e = u ∧ T₁.Orth T₂ ∧ T₂.e + T₂.f = w := by
  classical
  let Q := quadOdd 3 K
  have hQ : (polarBilin Q).Nondegenerate := nondegenerate_polarBilin_quadOdd 3 K h2
  haveI : Invertible (2 : K) := invertibleOfNonzero h2
  set W : Submodule K (OmegaSevenIdx → K) := LinearMap.ker (polarBilin Q w) with hWdef
  have huW : u ∈ W := by
    rw [hWdef, LinearMap.mem_ker, polarBilin_apply_apply, polar_comm]
    exact h.2.2.1
  have hW : PolarNondegOn Q W := by
    intro x hx hxperp
    rw [hWdef, LinearMap.mem_ker, polarBilin_apply_apply] at hx
    apply eq_zero_of_polar_eq_zero hQ
    intro y
    have hww : polar Q w w ≠ 0 := by
      rw [polar_self_eq_two_mul]
      exact mul_ne_zero h2 (by rw [h.2.2.2]; norm_num)
    have hmem : y - (polar Q w y / polar Q w w) • w ∈ W := by
      rw [hWdef, LinearMap.mem_ker, polarBilin_apply_apply, polar_sub_right,
        polar_smul_right_eq, div_mul_cancel₀ _ hww, sub_self]
    have h1 : polar Q x (y - (polar Q w y / polar Q w w) • w) = 0 := hxperp _ hmem
    have hxw : polar Q x w = 0 := by rw [polar_comm]; exact hx
    have hsplit : polar Q x y = polar Q x (y - (polar Q w y / polar Q w w) • w) +
        (polar Q w y / polar Q w w) * polar Q x w := by
      rw [polar_sub_right, polar_smul_right_eq]; ring
    rw [hsplit, h1, hxw, mul_zero, add_zero]
  obtain ⟨h', hh'W, hh'⟩ := hW.exists_polar_ne_zero huW h.2.1
  have h1' : polar Q u ((polar Q u h')⁻¹ • h') = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hh']
  set T₁ : HypPair Q := HypPair.ofPolarEqOne h.1 h1' with hT₁def
  have hT₁e : T₁.e = u := by rw [hT₁def]; rfl
  have hT₁f : T₁.f = (polar Q u h')⁻¹ • h' - Q ((polar Q u h')⁻¹ • h') • u := by
    rw [hT₁def]; rfl
  have hh'w : polar Q h' w = 0 := by
    rw [polar_comm]; exact (LinearMap.mem_ker.mp hh'W)
  have hT₁fw : polar Q T₁.f w = 0 := by
    rw [hT₁f, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hh'w, h.2.2.1]
    ring
  have hM : PolarNondegOn Q T₁.perp := T₁.polarNondegOn_perp hQ
  have hwM : w ∈ T₁.perp := by
    rw [HypPair.mem_perp]
    exact ⟨by rw [hT₁e]; exact h.2.2.1, hT₁fw⟩
  have hP' : PolarNondegOn Q (T₁.perp ⊓ W) :=
    omSevenGW_polarNondegOn_inf_ker h2 hM hwM (by rw [h.2.2.2]; norm_num)
  have hP'nd : (Q.restrict (T₁.perp ⊓ W)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_restrict hP')
  let φ : (OmegaSevenIdx → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := fun v => ![polar Q u v, polar Q T₁.f v, polar Q w v]
      map_add' := by
        intro a b
        ext i
        fin_cases i <;> simp [polar_add_right]
      map_smul' := by
        intro c a
        ext i
        fin_cases i <;> simp [polar_smul_right_eq] }
  have hker : LinearMap.ker φ = T₁.perp ⊓ W := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_inf, HypPair.mem_perp, hT₁e, hWdef,
      polarBilin_apply_apply]
    constructor
    · intro hv
      have h0 := congrFun hv 0
      have h1 := congrFun hv 1
      have h2 := congrFun hv 2
      simp at h0 h1 h2
      exact ⟨⟨h0, h1⟩, h2⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      ext i
      fin_cases i <;> simp [φ, h0, h1, h2]
  have hfin : 2 ≤ Module.finrank K ↥(T₁.perp ⊓ W) := by
    set d : ℕ := Module.finrank K ↥(T₁.perp ⊓ W) with hd
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hker] at h1
    have h1d : Module.finrank K (LinearMap.range φ) + d =
        Module.finrank K (OmegaSevenIdx → K) := by
      rw [hd]; exact h1
    have h2' : Module.finrank K (LinearMap.range φ) ≤ 3 := by
      have hle := Submodule.finrank_mono (le_top : LinearMap.range φ ≤ ⊤)
      rwa [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
    have h3 : Module.finrank K (OmegaSevenIdx → K) = 7 := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp [OmegaSevenIdx]
    rw [h3] at h1d
    omega
  obtain ⟨s, hsP', hsQ⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_mem_eq_unit hodd hP'nd hfin
      (Units.mk0 (-1) (by norm_num))
  have hsQ' : Q s = -1 := by simpa using hsQ
  have hsW : polar Q w s = 0 := by
    have := LinearMap.mem_ker.mp hsP'.2
    rwa [polarBilin_apply_apply] at this
  have hsM : s ∈ T₁.perp := hsP'.1
  have hsu : polar Q u s = 0 := by
    have := (HypPair.mem_perp.mp hsM).1
    rwa [hT₁e] at this
  have hsf : polar Q T₁.f s = 0 := (HypPair.mem_perp.mp hsM).2
  set e₁ : OmegaSevenIdx → K := (2 : K)⁻¹ • (w + s) with he₁def
  set f₁ : OmegaSevenIdx → K := (2 : K)⁻¹ • (w - s) with hf₁def
  have hQe₁ : Q e₁ = 0 := by
    rw [he₁def, map_smul_eq_sq, QuadraticMap.map_add Q, h.2.2.2, hsQ', hsW]
    ring
  have hQf₁ : Q f₁ = 0 := by
    rw [hf₁def, map_smul_eq_sq, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      polar_neg_right, h.2.2.2, hsQ', hsW]
    ring
  have hef : polar Q e₁ f₁ = 1 := by
    rw [he₁def, hf₁def, polar_smul_left_eq, polar_smul_right_eq, polar_sub_right, polar_add_left,
      polar_add_left, polar_self_eq_two_mul, polar_self_eq_two_mul, polar_comm Q s w, hsW,
      h.2.2.2, hsQ']
    field_simp
    ring
  refine ⟨T₁, ⟨e₁, f₁, hQe₁, hQf₁, hef⟩, hT₁e, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change polar Q T₁.e e₁ = 0
      rw [hT₁e, he₁def, polar_smul_right_eq, polar_add_right, h.2.2.1, hsu]
      ring
    · change polar Q T₁.e f₁ = 0
      rw [hT₁e, hf₁def, polar_smul_right_eq, polar_sub_right, h.2.2.1, hsu]
      ring
    · change polar Q T₁.f e₁ = 0
      rw [he₁def, polar_smul_right_eq, polar_add_right, hT₁fw, hsf]
      ring
    · change polar Q T₁.f f₁ = 0
      rw [hf₁def, polar_smul_right_eq, polar_sub_right, hT₁fw, hsf]
      ring
  · change e₁ + f₁ = w
    rw [he₁def, hf₁def, ← smul_add]
    have h2w : (w + s) + (w - s) = (2 : K) • w := by rw [two_smul]; abel
    rw [h2w, smul_smul, inv_mul_cancel₀ h2, one_smul]

private theorem omSevenGW_exists_mem_elementaryGroup {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) (h2 : (2 : K) ≠ 0)
    {u w u' w' : OmegaSevenIdx → K} (h : OmegaSevenShortPair u w)
    (h' : OmegaSevenShortPair u' w') :
    ∃ g ∈ elementaryGroup (quadOdd 3 K), g u = u' ∧ g w = w' := by
  classical
  have hodd : Odd (Nat.card K) := by rw [hK]; norm_num
  have hQ : (polarBilin (quadOdd 3 K)).Nondegenerate := nondegenerate_polarBilin_quadOdd 3 K h2
  obtain ⟨T₁, T₂, hT₁e, hT₁T₂, hT₂sum⟩ := omSevenGW_exists_hypPairs hodd h2 h
  obtain ⟨T₁', T₂', hT₁'e, hT₁'T₂', hT₂'sum⟩ := omSevenGW_exists_hypPairs hodd h2 h'
  have hS12 : (omSevenGW_stdPair K 0).Orth (omSevenGW_stdPair K 1) :=
    omSevenGW_stdPair_orth (by decide)
  have hS13 : (omSevenGW_stdPair K 0).Orth (omSevenGW_stdPair K 2) :=
    omSevenGW_stdPair_orth (by decide)
  have hS23 : (omSevenGW_stdPair K 1).Orth (omSevenGW_stdPair K 2) :=
    omSevenGW_stdPair_orth (by decide)
  obtain ⟨g₁, hg₁, hg₁a, hg₁b, hg₁c, hg₁d⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2.exists_mem_elementaryGroup_two hQ
      hS12 hS13 hS23 hT₁T₂
  obtain ⟨g₂, hg₂, hg₂a, hg₂b, hg₂c, hg₂d⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2.exists_mem_elementaryGroup_two hQ
      hS12 hS13 hS23 hT₁'T₂'
  refine ⟨g₂ * g₁⁻¹, mul_mem hg₂ (inv_mem hg₁), ?_, ?_⟩
  · rw [LinearEquiv.mul_apply]
    have h1 : g₁⁻¹ u = (omSevenGW_stdPair K 0).e := by
      rw [← hT₁e, ← hg₁a, LinearEquiv.inv_apply_apply']
    rw [h1, hg₂a, hT₁'e]
  · rw [LinearEquiv.mul_apply]
    have h1 : g₁⁻¹ w = (omSevenGW_stdPair K 1).e + (omSevenGW_stdPair K 1).f := by
      rw [← hT₂sum, ← hg₁c, ← hg₁d, ← map_add, LinearEquiv.inv_apply_apply']
    rw [h1, map_add, hg₂c, hg₂d, hT₂'sum]

theorem exists_inner_conj_eichlerProj {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (h2 : (2 : K) ≠ 0) {u w u' w' : OmegaSevenIdx → K} (h : OmegaSevenShortPair u w)
    (h' : OmegaSevenShortPair u' w') :
    ∃ g : StatedProj (StatedOmega (StatedQuadOdd 3 K)),
      g * eichlerProj h2 u w * g⁻¹ = eichlerProj h2 u' w' := by
  obtain ⟨g, hg, hgu, hgw⟩ := omSevenGW_exists_mem_elementaryGroup hK h2 h h'
  let A : Matrix.GeneralLinearGroup OmegaSevenIdx K := (toLinEquiv OmegaSevenIdx K).symm g
  have hAmem : A ∈ StatedOmega (StatedQuadOdd 3 K) := by
    rw [statedOmega_quadOdd_eq_map h2 le_rfl]
    exact Subgroup.mem_map_of_mem _ hg
  let gΩ : StatedOmega (StatedQuadOdd 3 K) := ⟨A, hAmem⟩
  refine ⟨QuotientGroup.mk gΩ, ?_⟩
  have hA : ∀ v, quadOdd 3 K (A.val.mulVec v) = quadOdd 3 K v := by
    intro v
    rw [← toLinEquiv_apply]
    simp only [A, MulEquiv.apply_symm_apply]
    exact map_of_mem (elementaryGroup_le_orthogonalGroup (quadOdd 3 K) hg) v
  have hβ : ∀ x : StatedOmega (StatedQuadOdd 3 K), ∃ y : StatedOmega (StatedQuadOdd 3 K),
      (y : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
          A * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) * A⁻¹ ∧
        MulAut.conj (QuotientGroup.mk gΩ : StatedProj (StatedOmega (StatedQuadOdd 3 K)))
          (QuotientGroup.mk x) = QuotientGroup.mk y := by
    intro x
    refine ⟨⟨A * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) * A⁻¹, ?_⟩, rfl, ?_⟩
    · exact (StatedOmega (StatedQuadOdd 3 K)).mul_mem
        ((StatedOmega (StatedQuadOdd 3 K)).mul_mem hAmem x.2)
        ((StatedOmega (StatedQuadOdd 3 K)).inv_mem hAmem)
    · rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul]
      congr 1
  have hmap := map_eichlerProj_of_isometry h2 hA hβ u w
  rw [MulAut.conj_apply] at hmap
  have hAu : A.val.mulVec u = u' := by
    rw [← toLinEquiv_apply]
    simp only [A, MulEquiv.apply_symm_apply]
    exact hgu
  have hAw : A.val.mulVec w = w' := by
    rw [← toLinEquiv_apply]
    simp only [A, MulEquiv.apply_symm_apply]
    exact hgw
  rw [hAu, hAw] at hmap
  exact hmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

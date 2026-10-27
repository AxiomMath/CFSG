module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public section

namespace CFSG.RankThree.Classical2

open scoped commutatorElement
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly CFSG.Assembly.RankThreeEven

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem orthogonal_defining_prime_central_cover_two_local_rank {G : Type*} [Group G] [Finite G]
    (Y : Subgroup G) {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hV7 : 7 ≤ Module.finrank K V) (hB : (polarBilin Q).Nondegenerate)
    (φ : Y →* ProjOrthDerived Q) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ (4 * f) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hKodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hKodd' : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hKodd
  obtain ⟨W, -, hWreg, ⟨wb, hwo, hw1⟩, hR0, -⟩ :=
    CFSG.RankThree.Classical.exists_regular_six_frame hKodd hV7 Q hB
  set v : Fin 6 → V := fun i => (wb i : V) with hvdef
  have hvW : ∀ i, v i ∈ W := fun i => (wb i).2
  have hpol : ∀ i j, polar Q (v i) (v j) = if i = j then 2 else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      rw [polar_self_eq_two_mul, show Q (v i) = 1 from hw1 i, mul_one]
    · exact hwo i j hij
  have hQv : ∀ i, Q (v i) = 1 := hw1
  obtain ⟨x, y, hxy⟩ := CFSG.SectionRank.OddCover.exists_sq_add_sq hKodd' (-1 : K)
  set c : K := 2⁻¹ with hcdef
  have hc : 2 * c = 1 := mul_inv_cancel₀ h2
  set e : V := x • v 0 + y • v 1 + v 2 with hedef
  set h : V := c • v 2 - c ^ 2 • e with hhdef
  set d₀ : V := y • v 0 - x • v 1 with hd₀def
  have hQa : Q (x • v 0 + y • v 1) = x ^ 2 + y ^ 2 := by
    rw [CFSG.RankThree.Classical.quad_smul_add_smul Q (by rw [hpol]; simp), hQv, hQv]
    ring
  have hpa : ∀ j, polar Q (x • v 0 + y • v 1) (v j) =
      x * (if (0 : Fin 6) = j then 2 else 0) + y * (if (1 : Fin 6) = j then 2 else 0) := by
    intro j
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hpol, hpol]
  have hev : ∀ j, polar Q e (v j) =
      x * (if (0 : Fin 6) = j then 2 else 0) + y * (if (1 : Fin 6) = j then 2 else 0) +
        (if (2 : Fin 6) = j then 2 else 0) := by
    intro j
    rw [hedef, polar_add_left, hpa, hpol]
  have he : Q e = 0 := by
    rw [hedef, QuadraticMap.map_add Q, hQa, hQv, hpa]
    simp only [Fin.reduceEq, ite_false, mul_zero, add_zero]
    linear_combination hxy
  have hee : polar Q e e = 0 := polar_self_eq_zero he
  have hev2 : polar Q e (v 2) = 2 := by
    rw [hev]
    simp
  have hh : Q h = 0 := by
    have hpve : polar Q (v 2) e = 2 := by rw [polar_comm, hev2]
    rw [hhdef, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, QuadraticMap.map_smul,
      QuadraticMap.map_smul, hQv, he, polar_smul_left_eq, polar_smul_right_eq, hpve,
      smul_eq_mul, smul_eq_mul]
    linear_combination (-c ^ 2) * hc
  have heh : polar Q e h = 1 := by
    rw [hhdef, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hev2, hee]
    linear_combination hc
  let fD : Fin 4 → V := ![d₀, v 3, v 4, v 5]
  have hQd₀ : Q d₀ = -1 := by
    rw [hd₀def, sub_eq_add_neg, ← neg_smul,
      CFSG.RankThree.Classical.quad_smul_add_smul Q (by rw [hpol]; simp), hQv, hQv]
    linear_combination hxy
  have hd₀v : ∀ j : Fin 6, 3 ≤ (j : ℕ) → polar Q d₀ (v j) = 0 := by
    intro j hj
    have h0 : (0 : Fin 6) ≠ j := fun h' => by rw [← h'] at hj; simp at hj
    have h1 : (1 : Fin 6) ≠ j := fun h' => by rw [← h'] at hj; simp at hj
    rw [hd₀def, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hpol, hpol]
    simp [h0, h1]
  have hed₀ : polar Q e d₀ = 0 := by
    rw [hd₀def, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hev, hev]
    simp
    ring
  have hv2d₀ : polar Q (v 2) d₀ = 0 := by
    rw [hd₀def, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hpol, hpol]
    simp
  have hfo : ∀ i j, i ≠ j → polar Q (fD i) (fD j) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [fD, hpol, hd₀v, polar_comm Q _ d₀]
  have hfQ : ∀ i, Q (fD i) ≠ 0 := by
    intro i
    fin_cases i <;> simp [fD, hQd₀, hQv]
  obtain ⟨hfli, hDreg⟩ := CFSG.RankThree.Classical.nondegenerate_restrict_span h2 Q hfo hfQ
  set D := Submodule.span K (Set.range fD) with hDdef
  have hDdim : Module.finrank K D = 4 := by
    rw [hDdef, finrank_span_eq_card hfli, Fintype.card_fin]
  have hspan_ker : ∀ a : V, (∀ i, polar Q a (fD i) = 0) → ∀ w ∈ D, polar Q a w = 0 := by
    intro a ha w hw
    have hle : D ≤ LinearMap.ker ((polarBilin Q) a) := by
      rw [hDdef, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply]
      exact ha i
    have := hle hw
    rwa [LinearMap.mem_ker, polarBilin_apply_apply] at this
  have hfe : ∀ i, polar Q e (fD i) = 0 := by
    intro i
    fin_cases i
    · exact hed₀
    all_goals
      show polar Q e (v _) = 0
      rw [hev]
      simp
  have hfv2 : ∀ i, polar Q (v 2) (fD i) = 0 := by
    intro i
    fin_cases i
    · exact hv2d₀
    all_goals
      show polar Q (v 2) (v _) = 0
      rw [hpol]
      simp
  have hDe : ∀ w ∈ D, polar Q e w = 0 := hspan_ker e hfe
  have hDh : ∀ w ∈ D, polar Q h w = 0 := by
    intro w hw
    rw [hhdef, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hDe w hw,
      hspan_ker (v 2) hfv2 w hw, mul_zero, mul_zero, sub_zero]
  obtain ⟨U₀, hU₀, hU₀Ω, -, hUab, hUcard, hpre⟩ :=
    orthogonal_isotropic_line_unipotent_core hp hp3 hf hK Q he hh heh hDe hDh hDreg hDdim
      (le_refl 4)
  have hDW : D ≤ W := by
    rw [hDdef, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact W.sub_mem (W.smul_mem _ (hvW 0)) (W.smul_mem _ (hvW 1))
    all_goals exact hvW _
  have heW : e ∈ W := W.add_mem (W.add_mem (W.smul_mem _ (hvW 0)) (W.smul_mem _ (hvW 1)))
    (hvW 2)
  have hQ1 : ∀ i, Q (v i) = 1 := hQv
  obtain ⟨ε₀, hε₀Ω, hε₀a, hε₀b, hε₀x⟩ :=
    exists_mem_orthDerived_double_sign h2 (hQ1 0) (hQ1 1) (by rw [hpol]; simp)
  obtain ⟨ε₁, hε₁Ω, hε₁a, hε₁b, hε₁x⟩ :=
    exists_mem_orthDerived_double_sign h2 (hQ1 2) (hQ1 3) (by rw [hpol]; simp)
  obtain ⟨ε₂, hε₂Ω, hε₂a, hε₂b, hε₂x⟩ :=
    exists_mem_orthDerived_double_sign h2 (hQ1 4) (hQ1 5) (by rw [hpol]; simp)
  set z₀ : V ≃ₗ[K] V := ε₀ * ε₁ * ε₂ with hz₀def
  have hz₀Ω : z₀ ∈ orthDerived Q := mul_mem (mul_mem hε₀Ω hε₁Ω) hε₂Ω
  have hpvv : ∀ i j : Fin 6, i ≠ j → polar Q (v i) (v j) = 0 := fun i j hij => by
    rw [hpol]
    simp [hij]
  have hzv : ∀ i, z₀ (v i) = -v i := by
    intro i
    rw [hz₀def, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    fin_cases i
    · change ε₀ (ε₁ (ε₂ (v 0))) = -v 0
      rw [hε₂x _ (hpvv 4 0 (by decide)) (hpvv 5 0 (by decide)),
        hε₁x _ (hpvv 2 0 (by decide)) (hpvv 3 0 (by decide)), hε₀a]
    · change ε₀ (ε₁ (ε₂ (v 1))) = -v 1
      rw [hε₂x _ (hpvv 4 1 (by decide)) (hpvv 5 1 (by decide)),
        hε₁x _ (hpvv 2 1 (by decide)) (hpvv 3 1 (by decide)), hε₀b]
    · change ε₀ (ε₁ (ε₂ (v 2))) = -v 2
      rw [hε₂x _ (hpvv 4 2 (by decide)) (hpvv 5 2 (by decide)), hε₁a, map_neg,
        hε₀x _ (hpvv 0 2 (by decide)) (hpvv 1 2 (by decide))]
    · change ε₀ (ε₁ (ε₂ (v 3))) = -v 3
      rw [hε₂x _ (hpvv 4 3 (by decide)) (hpvv 5 3 (by decide)), hε₁b, map_neg,
        hε₀x _ (hpvv 0 3 (by decide)) (hpvv 1 3 (by decide))]
    · change ε₀ (ε₁ (ε₂ (v 4))) = -v 4
      rw [hε₂a, map_neg, map_neg, hε₁x _ (hpvv 2 4 (by decide)) (hpvv 3 4 (by decide)),
        hε₀x _ (hpvv 0 4 (by decide)) (hpvv 1 4 (by decide))]
    · change ε₀ (ε₁ (ε₂ (v 5))) = -v 5
      rw [hε₂b, map_neg, map_neg, hε₁x _ (hpvv 2 5 (by decide)) (hpvv 3 5 (by decide)),
        hε₀x _ (hpvv 0 5 (by decide)) (hpvv 1 5 (by decide))]
  have hzW : ∀ w ∈ W, z₀ w = -w := by
    have hle : W ≤ LinearMap.ker ((z₀ : V →ₗ[K] V) + LinearMap.id) := by
      intro w hw
      obtain ⟨w', rfl⟩ : ∃ w' : W, (w' : V) = w := ⟨⟨w, hw⟩, rfl⟩
      rw [← wb.sum_repr w', Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, LinearMap.mem_ker, LinearMap.add_apply, LinearEquiv.coe_coe,
        map_smul, LinearMap.id_apply, ← smul_add]
      change _ • (z₀ (v i) + v i) = 0
      rw [hzv, neg_add_cancel, smul_zero]
    intro w hw
    have := hle hw
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  have hzR : ∀ r ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W, z₀ r = r := by
    intro r hr
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hr
    have hvr : ∀ i, polar Q (v i) r = 0 := fun i => by
      have := hr (v i) (hvW i)
      rwa [polarBilin_apply_apply] at this
    rw [hz₀def, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hε₂x r (hvr 4) (hvr 5),
      hε₁x r (hvr 2) (hvr 3), hε₀x r (hvr 0) (hvr 1)]
  have hcompl : IsCompl W (LinearMap.BilinForm.orthogonal (polarBilin Q) W) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (CFSG.RankThree.Classical.isSymm_polarBilin Q).isRefl hWreg
  have hz₀2 : z₀ ^ 2 = 1 := by
    have hle : W ⊔ LinearMap.BilinForm.orthogonal (polarBilin Q) W ≤
        LinearMap.ker (((z₀ ^ 2 : V ≃ₗ[K] V) : V →ₗ[K] V) - LinearMap.id) := by
      refine sup_le (fun w hw => ?_) (fun r hr => ?_)
      · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
          pow_two, LinearEquiv.mul_apply, hzW w hw, map_neg, hzW w hw, neg_neg, sub_self]
      · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
          pow_two, LinearEquiv.mul_apply, hzR r hr, hzR r hr, sub_self]
    rw [hcompl.sup_eq_top] at hle
    refine LinearEquiv.ext fun x => ?_
    have := hle (Submodule.mem_top (x := x))
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero] at this
    exact this
  set ρ := QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρdef
  set z : ProjOrthDerived Q := ρ ⟨z₀, hz₀Ω⟩ with hzdef
  have hz1 : z ≠ 1 := by
    intro hz
    have hmem := (QuotientGroup.eq_one_iff (N := (scalars K V).subgroupOf (orthDerived Q))
      (⟨z₀, hz₀Ω⟩ : orthDerived Q)).mp hz
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨c, hc⟩ := mem_scalars.mp hmem
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR0
    have hv0 : v 0 ≠ 0 := fun h0 => by
      have := hQv 0
      rw [h0, QuadraticMap.map_zero] at this
      exact zero_ne_one this
    have hc1 : c = -1 := by
      have h1 := hc (v 0)
      rw [hzv] at h1
      have h1' : (c + 1) • v 0 = 0 := by rw [add_smul, one_smul, ← h1, neg_add_cancel]
      rcases smul_eq_zero.mp h1' with h1' | h1'
      · exact eq_neg_of_add_eq_zero_left h1'
      · exact absurd h1' hv0
    have h2r := hc r
    rw [hzR r hr, hc1, neg_one_smul] at h2r
    have : (2 : K) • r = 0 := by rw [two_smul]; nth_rewrite 1 [h2r]; exact neg_add_cancel r
    rcases smul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hr0 h'
  have hz2 : z ^ 2 = 1 := by
    rw [hzdef, ← map_pow]
    have : (⟨z₀, hz₀Ω⟩ : orthDerived Q) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hz₀2)
    rw [this, map_one]
  have hzU : ∀ x ∈ (U₀.subgroupOf (orthDerived Q)).map ρ, Commute z x := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : (g : V ≃ₗ[K] V) ∈ (U₀ : Set (V ≃ₗ[K] V)) := hg
    rw [hU₀] at hg'
    obtain ⟨w, hw, hgw⟩ := hg'
    have hgE : (g : V ≃ₗ[K] V) = eichler Q e w := LinearEquiv.ext fun t => by
      rw [eichler_apply he (hDe w hw)]
      exact LinearMap.congr_fun hgw t
    have hcomm : (⟨z₀, hz₀Ω⟩ : orthDerived Q) * g = g * ⟨z₀, hz₀Ω⟩ := by
      apply Subtype.ext
      change z₀ * (g : V ≃ₗ[K] V) = (g : V ≃ₗ[K] V) * z₀
      have hconj := eichler_conj (Q := Q) (g := z₀) (Subgroup.commutator_le.mpr (fun g₁ h₁ g₂ h₂ =>
        by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)) hz₀Ω) e w
      rw [hzW e heW, hzW w (hDW hw), ← neg_one_smul K e, eichler_smul_left, neg_one_smul,
        neg_neg, ← hgE] at hconj
      exact mul_inv_eq_iff_eq_mul.mp hconj
    show z * ρ g = ρ g * z
    rw [hzdef, ← map_mul, ← map_mul, hcomm]
  have hcard : p ^ (4 * f) ≤ Nat.card ((U₀.subgroupOf (orthDerived Q)).map ρ) := by
    rw [hUcard, mul_comm]
  exact exists_involution_elemAbelian_of_cover Y hφ hker hp hp2 hUab.2
    (hpre Y φ hφ hker) hcard hz1 hz2 hzU

theorem le_localRank_of_orthogonal_defining_prime {G : Type*} [Group G] [Finite G]
    (Y : Subgroup G) {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hV7 : 7 ≤ Module.finrank K V) (hB : (polarBilin Q).Nondegenerate)
    (φ : Y →* ProjOrthDerived Q) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) : 4 * f ≤ localRank p G := by
  obtain ⟨u, -, hu, A, hA, hAab, hAcard⟩ :=
    orthogonal_defining_prime_central_cover_two_local_rank Y hp hp3 hf hK Q hV7 hB φ hφ hker
  exact le_localRank_of_involution_elemAbelian hp hu (le_inf_iff.mp hA).2 hAab hAcard

end CFSG.RankThree.Classical2

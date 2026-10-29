module

public import CFSG.RankThree.GF2n.Smith81.S81UTrans

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

private theorem u6f_ιMulti_ne_zero {v : Fin 3 → Fin 6 → F} (h : LinearIndependent F v) :
    exteriorPower.ιMulti F 3 v ≠ 0 := by
  have hinj : LinearMap.ker (Fintype.linearCombination F v) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (LinearIndependent.fintypeLinearCombination_injective h)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F v) hinj
  have hφv : ∀ j, φ (v j) = Pi.single j 1 := by
    intro j
    have := LinearMap.congr_fun hφ (Pi.single j 1)
    simpa [Fintype.linearCombination_apply_single] using this
  let Λ : (Fin 6 → F) [⋀^Fin 3]→ₗ[F] F :=
    (Matrix.detRowAlternating : (Fin 3 → F) [⋀^Fin 3]→ₗ[F] F).compLinearMap φ
  intro h0
  have h1 : (exteriorPower.alternatingMapLinearEquiv Λ) (exteriorPower.ιMulti F 3 v) = Λ v :=
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti Λ v
  rw [h0, map_zero] at h1
  have h2 : Λ v = 1 := by
    show Matrix.det (Matrix.of fun j => φ (v j)) = 1
    have : (Matrix.of fun j => φ (v j)) = (1 : Matrix (Fin 3) (Fin 3) F) := by
      ext j i
      rw [Matrix.of_apply, hφv j, Pi.single_apply, Matrix.one_apply]
      simp [eq_comm]
    rw [this, Matrix.det_one]
  rw [h2] at h1
  exact one_ne_zero h1.symm

private theorem u6f_linIndep3 {a b c : Fin 6 → F}
    (h : ∀ α β γ : F, α • a + β • b + γ • c = 0 → α = 0 ∧ β = 0 ∧ γ = 0) :
    LinearIndependent F ![a, b, c] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • a + g 1 • b + g 2 • c = 0 := by simpa [Fin.sum_univ_three] using hg
  obtain ⟨h0, h1, h2⟩ := h (g 0) (g 1) (g 2) hg'
  intro i
  fin_cases i
  exacts [h0, h1, h2]

private theorem u6f_mem_of_perp {T : Submodule F (Fin 6 → F)} (hT : Module.finrank F T = 3)
    (hTiso : ∀ x ∈ T, ∀ y ∈ T, herm σ x y = 0) {v : Fin 3 → Fin 6 → F}
    (hv : LinearIndependent F v) (hvT : ∀ i, v i ∈ T) {x : Fin 6 → F}
    (hx : ∀ i, herm σ (v i) x = 0) : x ∈ T := by
  have hsurj : Function.Surjective (hermL σ v) := hermL_surjective (u6f_ιMulti_ne_zero hv)
  have hker : T ≤ LinearMap.ker (hermL σ v) := by
    intro t ht
    rw [LinearMap.mem_ker]
    funext i
    exact hTiso (v i) (hvT i) t ht
  have hrank : Module.finrank F (LinearMap.ker (hermL σ v)) = 3 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (hermL σ v)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h1
    simp only [Module.finrank_fin_fun] at h1
    omega
  have hTeq : T = LinearMap.ker (hermL σ v) :=
    Submodule.eq_of_le_of_finrank_eq hker (hT.trans hrank.symm)
  rw [hTeq, LinearMap.mem_ker]
  funext i
  exact hx i

private theorem u6f_extend3 {U : Submodule F (Fin 6 → F)} (hU : Module.finrank F U = 3)
    {a : Fin 6 → F} (ha : a ∈ U) (ha0 : a ≠ 0) :
    ∃ b c : Fin 6 → F, b ∈ U ∧ c ∈ U ∧
      ∀ α β γ : F, α • a + β • b + γ • c = 0 → α = 0 ∧ β = 0 ∧ γ = 0 := by
  obtain ⟨b, hbU, hb⟩ : ∃ b ∈ U, ∀ α : F, b ≠ α • a := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ Submodule.span F {a} := by
      intro x hx
      obtain ⟨α, rfl⟩ := hcon x hx
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton ha0, hU] at h1
    omega
  obtain ⟨c, hcU, hc⟩ : ∃ c ∈ U, ∀ α β : F, c ≠ α • a + β • b := by
    by_contra hcon
    push Not at hcon
    have ha_mem : a ∈ Submodule.span F (Set.range ![a, b]) :=
      Submodule.subset_span ⟨0, by simp⟩
    have hb_mem : b ∈ Submodule.span F (Set.range ![a, b]) :=
      Submodule.subset_span ⟨1, by simp⟩
    have hle : U ≤ Submodule.span F (Set.range ![a, b]) := by
      intro x hx
      obtain ⟨α, β, rfl⟩ := hcon x hx
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha_mem) (Submodule.smul_mem _ _ hb_mem)
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_range_le_card (R := F) ![a, b]
    rw [hU] at h1
    unfold Set.finrank at h2
    simp only [Fintype.card_fin] at h2
    omega
  refine ⟨b, c, hbU, hcU, fun α β γ h => ?_⟩
  have hγ : γ = 0 := by
    by_contra hγ
    apply hc (-(γ⁻¹ * α)) (-(γ⁻¹ * β))
    have e1 : γ • c = -(α • a + β • b) := by
      linear_combination (norm := module) h
    calc c = γ⁻¹ • (γ • c) := (inv_smul_smul₀ hγ c).symm
      _ = γ⁻¹ • (-(α • a + β • b)) := by rw [e1]
      _ = -(γ⁻¹ * α) • a + -(γ⁻¹ * β) • b := by module
  subst hγ
  have h' : α • a + β • b = 0 := by simpa only [zero_smul, add_zero] using h
  have hβ : β = 0 := by
    by_contra hβ
    apply hb (-(β⁻¹ * α))
    have e2 : β • b = -(α • a) := by
      linear_combination (norm := module) h'
    calc b = β⁻¹ • (β • b) := (inv_smul_smul₀ hβ b).symm
      _ = β⁻¹ • (-(α • a)) := by rw [e2]
      _ = -(β⁻¹ * α) • a := by module
  subst hβ
  have hα : α • a = 0 := by simpa only [zero_smul, add_zero] using h'
  exact ⟨(smul_eq_zero.mp hα).resolve_right ha0, rfl, rfl⟩

private theorem u6f_five_indep {S T : Submodule F (Fin 6 → F)} {a b c d₀ e₀ d e : Fin 6 → F}
    {p q r s : F} (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hd₀T : d₀ ∈ T) (he₀T : e₀ ∈ T)
    (hline : ∀ x ∈ S ⊓ T, ∃ κ : F, κ • a = x)
    (hbc : ∀ α β γ : F, α • a + β • b + γ • c = 0 → α = 0 ∧ β = 0 ∧ γ = 0)
    (hde : ∀ α β γ : F, α • a + β • d₀ + γ • e₀ = 0 → α = 0 ∧ β = 0 ∧ γ = 0)
    (hd : d = p • d₀ - q • e₀) (he : e = r • d₀ - s • e₀) (hΔ : p * s - q * r ≠ 0) :
    LinearIndependent F ![a, b, c, d, e] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • a + g 1 • b + g 2 • c + g 3 • d + g 4 • e = 0 := by
    simpa [Fin.sum_univ_five] using hg
  have hdT : d ∈ T := by
    rw [hd]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hd₀T) (Submodule.smul_mem _ _ he₀T)
  have heT : e ∈ T := by
    rw [he]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hd₀T) (Submodule.smul_mem _ _ he₀T)
  have hxS : g 0 • a + g 1 • b + g 2 • c ∈ S :=
    Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ haS)
      (Submodule.smul_mem _ _ hbS)) (Submodule.smul_mem _ _ hcS)
  have hxT : g 0 • a + g 1 • b + g 2 • c ∈ T := by
    have hx : g 0 • a + g 1 • b + g 2 • c = -(g 3 • d + g 4 • e) := by
      linear_combination (norm := module) hg'
    rw [hx]
    exact Submodule.neg_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hdT)
      (Submodule.smul_mem _ _ heT))
  obtain ⟨κ, hκ⟩ := hline _ (Submodule.mem_inf.mpr ⟨hxS, hxT⟩)
  obtain ⟨-, h1, h2⟩ :=
    hbc (g 0 - κ) (g 1) (g 2) (by linear_combination (norm := module) -hκ)
  have hg'' : g 0 • a + g 3 • d + g 4 • e = 0 := by
    simpa only [h1, h2, zero_smul, add_zero, zero_add] using hg'
  rw [hd, he] at hg''
  obtain ⟨h0, h3, h4⟩ := hde (g 0) (g 3 * p + g 4 * r) (-(g 3 * q + g 4 * s))
    (by linear_combination (norm := module) hg'')
  have hA : g 3 * (p * s - q * r) = 0 := by linear_combination s * h3 + r * h4
  have hB : g 4 * (p * s - q * r) = 0 := by linear_combination -p * h4 - q * h3
  have hg3 : g 3 = 0 := (mul_eq_zero.mp hA).resolve_right hΔ
  have hg4 : g 4 = 0 := (mul_eq_zero.mp hB).resolve_right hΔ
  intro i
  fin_cases i
  exacts [h0, h1, h2, hg3, hg4]

theorem u6_exists_five (hσ : IsUnitaryInvolution σ) {S T : Submodule F (Fin 6 → F)}
    (hS : Module.finrank F S = 3) (hT : Module.finrank F T = 3)
    (hSiso : ∀ x ∈ S, ∀ y ∈ S, herm σ x y = 0) (hTiso : ∀ x ∈ T, ∀ y ∈ T, herm σ x y = 0)
    (hST : Module.finrank F ↥(S ⊓ T) = 1) :
    ∃ a b c d e : Fin 6 → F, LinearIndependent F ![a, b, c, d, e] ∧
      a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ∈ T ∧ d ∈ T ∧ e ∈ T ∧ herm σ b d = 0 ∧ herm σ c e = 0 := by
  obtain ⟨⟨a, haST⟩, ha0', hline0⟩ := finrank_eq_one_iff'.mp hST
  have ha0 : a ≠ 0 := fun h => ha0' (Subtype.ext h)
  have haS : a ∈ S := (Submodule.mem_inf.mp haST).1
  have haT : a ∈ T := (Submodule.mem_inf.mp haST).2
  have hline : ∀ x ∈ S ⊓ T, ∃ κ : F, κ • a = x := by
    intro x hx
    obtain ⟨κ, hκ⟩ := hline0 ⟨x, hx⟩
    exact ⟨κ, congrArg Subtype.val hκ⟩
  obtain ⟨b, c, hbS, hcS, hbc⟩ := u6f_extend3 hS haS ha0
  obtain ⟨d₀, e₀, hd₀T, he₀T, hde⟩ := u6f_extend3 hT haT ha0
  have hli_T : LinearIndependent F ![a, d₀, e₀] := u6f_linIndep3 hde
  have hvT : ∀ i, (![a, d₀, e₀] : Fin 3 → Fin 6 → F) i ∈ T := by
    intro i
    fin_cases i
    exacts [haT, hd₀T, he₀T]
  have hΔ : herm σ b d₀ * herm σ c e₀ - herm σ b e₀ * herm σ c d₀ ≠ 0 := by
    intro hΔ0
    have hdet : (!![herm σ b d₀, herm σ c d₀; herm σ b e₀, herm σ c e₀] :
        Matrix (Fin 2) (Fin 2) F).det = 0 := by
      rw [Matrix.det_fin_two_of]
      linear_combination hΔ0
    obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have h0 : herm σ b d₀ * v 0 + herm σ c d₀ * v 1 = 0 := by
      have := congrFun hMv 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have h1 : herm σ b e₀ * v 0 + herm σ c e₀ * v 1 = 0 := by
      have := congrFun hMv 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    obtain ⟨μ, hσμ⟩ : ∃ μ : F, σ μ = v 0 := ⟨σ.symm (v 0), σ.apply_symm_apply (v 0)⟩
    obtain ⟨ν, hσν⟩ : ∃ ν : F, σ ν = v 1 := ⟨σ.symm (v 1), σ.apply_symm_apply (v 1)⟩
    have hbnS : μ • b + ν • c ∈ S :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hbS) (Submodule.smul_mem _ _ hcS)
    have hd₀ : herm σ (μ • b + ν • c) d₀ = 0 := by
      rw [CFSG.ClassicalGroups.Unitary.herm_add_left σ, CFSG.ClassicalGroups.Unitary.herm_smul_left σ,
        CFSG.ClassicalGroups.Unitary.herm_smul_left σ, hσμ, hσν]
      linear_combination h0
    have he₀ : herm σ (μ • b + ν • c) e₀ = 0 := by
      rw [CFSG.ClassicalGroups.Unitary.herm_add_left σ, CFSG.ClassicalGroups.Unitary.herm_smul_left σ,
        CFSG.ClassicalGroups.Unitary.herm_smul_left σ, hσμ, hσν]
      linear_combination h1
    have hmemT : μ • b + ν • c ∈ T := by
      apply u6f_mem_of_perp hT hTiso hli_T hvT
      intro i
      fin_cases i
      · exact hSiso a haS _ hbnS
      · show herm σ d₀ _ = 0
        rw [CFSG.ClassicalGroups.Unitary.herm_conj σ hσ.invol, hd₀, map_zero]
      · show herm σ e₀ _ = 0
        rw [CFSG.ClassicalGroups.Unitary.herm_conj σ hσ.invol, he₀, map_zero]
    obtain ⟨κ, hκ⟩ := hline _ (Submodule.mem_inf.mpr ⟨hbnS, hmemT⟩)
    obtain ⟨-, hμ0, hν0⟩ := hbc (-κ) μ ν (by linear_combination (norm := module) -hκ)
    have hv0' : v 0 = 0 := by rw [← hσμ, hμ0, map_zero]
    have hv1' : v 1 = 0 := by rw [← hσν, hν0, map_zero]
    apply hv0
    funext i
    fin_cases i
    · exact hv0'
    · exact hv1'
  have hΔ' : herm σ b e₀ * herm σ c d₀ - herm σ b d₀ * herm σ c e₀ ≠ 0 :=
    fun h => hΔ (by linear_combination -h)
  obtain ⟨dd, hdd⟩ : ∃ x : Fin 6 → F, x = herm σ b e₀ • d₀ - herm σ b d₀ • e₀ := ⟨_, rfl⟩
  obtain ⟨ee, hee⟩ : ∃ x : Fin 6 → F, x = herm σ c e₀ • d₀ - herm σ c d₀ • e₀ := ⟨_, rfl⟩
  refine ⟨a, b, c, dd, ee, ?_, haS, hbS, hcS, haT, ?_, ?_, ?_, ?_⟩
  · exact u6f_five_indep haS hbS hcS hd₀T he₀T hline hbc hde hdd hee hΔ'
  · rw [hdd]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hd₀T) (Submodule.smul_mem _ _ he₀T)
  · rw [hee]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hd₀T) (Submodule.smul_mem _ _ he₀T)
  · rw [hdd, CFSG.ClassicalGroups.Unitary.herm_sub_right σ,
      CFSG.ClassicalGroups.Unitary.herm_smul_right σ, CFSG.ClassicalGroups.Unitary.herm_smul_right σ]
    ring
  · rw [hee, CFSG.ClassicalGroups.Unitary.herm_sub_right σ,
      CFSG.ClassicalGroups.Unitary.herm_smul_right σ, CFSG.ClassicalGroups.Unitary.herm_smul_right σ]
    ring

end CFSG.RankThree.GF2n.Smith81.U6Cube

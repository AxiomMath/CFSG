module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatCtx
public import CFSG.RankThree.GF2n.Stroth80.Sec310Elation

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.not_le_QB_of_natural {R V : Subgroup G} (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    (hLR : LB M Q B ≤ R) (hZV : Z ≤ V) (hBV : B ≤ V) (hVQ : V ≤ Q)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h4 : 4 ≤ Fintype.card ι)
    (φ : ↥R →* GL ι K) (hsec : SectionAct K R V Z φ (fun g => (g : Matrix ι ι K)))
    (β : LinearMap.BilinForm K (ι → K))
    (hform : ∀ A ∈ φ.range, ∀ u : ι → K, u ≠ 0 →
      (∀ x, ∃ c : K, (A : Matrix ι ι K) *ᵥ x - x = c • u) →
        ∃ c : K, ∀ x, (A : Matrix ι ι K) *ᵥ x - x = (c * β x u) • u) :
    ¬ V ≤ QB B := by
  classical
  intro hVQB
  obtain ⟨hVR, hnorm, ψ, hψ⟩ := hsec
  haveI := hnorm
  let D : AddSubgroup (ι → K) :=
    { carrier := {x | ∃ b : ↥V, (b : G) ∈ (B ⊔ Z : Subgroup G) ∧ secVec ψ b = x}
      zero_mem' := ⟨1, (B ⊔ Z).one_mem, (secVec_eq_zero_iff ψ 1).mpr Z.one_mem⟩
      add_mem' := by
        rintro _ _ ⟨b₁, hb₁, rfl⟩ ⟨b₂, hb₂, rfl⟩
        exact ⟨b₁ * b₂, (B ⊔ Z).mul_mem hb₁ hb₂, secVec_mul ψ b₁ b₂⟩
      neg_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b⁻¹, (B ⊔ Z).inv_mem hb, secVec_inv ψ b⟩ }
  have hD : Nat.card D ≤ Nat.card K := by
    have hsurj : Function.Surjective (fun b : ↥B =>
        (⟨secVec ψ ⟨b, hBV b.2⟩, ⟨b, hBV b.2⟩, Subgroup.mem_sup_left b.2, rfl⟩ : D)) := by
      rintro ⟨x, b', hb', rfl⟩
      obtain ⟨c₀, hc₀B, z, hzZ, hcz⟩ := exists_mul_of_mem_sup
        (fun x hx z hz => hc.Z_central hz (hc.le hx)) hb'
      refine ⟨⟨c₀, hc₀B⟩, Subtype.ext ?_⟩
      show secVec ψ ⟨c₀, hBV hc₀B⟩ = secVec ψ b'
      have e : b' = ⟨c₀, hBV hc₀B⟩ * ⟨z, hZV hzZ⟩ := Subtype.ext hcz
      rw [e, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hZV hzZ⟩).mpr hzZ, add_zero]
    calc Nat.card D ≤ Nat.card B := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card Z := by
        obtain ⟨g, hg⟩ := hc.conj
        rw [hg, card_conjSubgroup]
      _ = Nat.card K := hK.symm
  let Γ : Set (Matrix ι ι K) := {A | ∃ (l : G) (hl : l ∈ LB M Q B),
    A = ((φ ⟨l, hLR hl⟩ : GL ι K) : Matrix ι ι K)}
  have hΓD : ∀ A ∈ Γ, ∀ x, A *ᵥ x - x ∈ D := by
    rintro _ ⟨l, hl, rfl⟩ x
    obtain ⟨v, rfl⟩ := exists_secVec_eq ψ x
    have hc' := secVec_comm φ ψ hψ hVR ⟨l, hLR hl⟩ v
    rw [← hc']
    refine ⟨⟨⁅l, (v : G)⁆, comm_mem_of_le_normalizer hVR ⟨l, hLR hl⟩ v⟩, ?_, rfl⟩
    have := hc.comm_LB_inf_QB_mem_sup hl ⟨hVQ v.2, hVQB v.2⟩
    rwa [sup_comm] at this
  have hfix : ∀ x, (∀ A ∈ Γ, A *ᵥ x = x) → x ∈ D := by
    intro x hx
    obtain ⟨v, rfl⟩ := exists_secVec_eq ψ x
    refine ⟨v, ?_, rfl⟩
    have hvC : (v : G) ∈ CQt Q Z (LB M Q B) := by
      refine ⟨hVQ v.2, fun l hl => ?_⟩
      have h1 := hx _ ⟨l, hl, rfl⟩
      have hc' := secVec_comm φ ψ hψ hVR ⟨l, hLR hl⟩ v
      rw [h1, sub_self] at hc'
      exact (secVec_eq_zero_iff ψ _).mp hc'
    rw [h35] at hvC
    exact hvC
  refine ela_core β h4 D hD Γ hΓD (fun A hA u hu hrank => ?_) hfix
  obtain ⟨l, hl, rfl⟩ := hA
  exact hform _ ⟨⟨l, hLR hl⟩, rfl⟩ u hu hrank

theorem mem_statedOmega_preserves {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) {A : GL ι K}
    (hA : A ∈ StatedOmega Q₀) (x : ι → K) : Q ((A : Matrix ι ι K) *ᵥ x) = Q x := by
  rw [statedOmega_eq_comap hQ] at hA
  have h1 : toLinEquiv ι K A ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := hA
  have h2 : toLinEquiv ι K A ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => by
      rw [commutatorElement_def]
      exact (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
        ((TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
          ((TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem hg₁ hg₂)
          ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hg₁))
        ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hg₂)) h1
  have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp h2 x
  simpa using this

theorem omega_hform {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hnd : (polarBilin Q).Nondegenerate) {A : GL ι K} (hA : A ∈ StatedOmega Q₀)
    {u : ι → K} (hu : u ≠ 0) (hrank : ∀ x, ∃ c : K, (A : Matrix ι ι K) *ᵥ x - x = c • u) :
    ∃ c : K, ∀ x, (A : Matrix ι ι K) *ᵥ x - x = (c * polarBilin Q x u) • u := by
  have hnd' : ∀ u : ι → K, u ≠ 0 → ∃ x, polar Q x u ≠ 0 := by
    intro u hu
    by_contra h
    push Not at h
    exact hu (hnd.2 u fun x => by simpa [QuadraticMap.polarBilin_apply_apply] using h x)
  obtain ⟨c, hc⟩ := elation_form_orth Q hnd' (A : Matrix ι ι K) (mem_statedOmega_preserves hQ hA)
    hu hrank
  exact ⟨c, fun x => by rw [hc x]; simp [QuadraticMap.polarBilin_apply_apply]⟩

theorem stroth310NotQB_of_34 (h34 : Stroth34Statement) : Stroth310NotQBStatement := by
  intro G _ _ M Q Z B hc n t hs hnat
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV := hc.B_le_Vt hs.mem
  have hVQ := hc.Vt_le_Q t
  rcases hnat with ⟨K, _, _, hK, m, hm, φ, hφr, -, hsec⟩ |
    ⟨K, _, _, hK, ⟨m, hm, φ, hφr, -, hsec⟩ | ⟨m, b, c, hm, hirr, φ, hφr, -, hsec⟩⟩
  · refine hc.not_le_QB_of_natural h35 hLR hZV hBV hVQ hK (ι := Fin m ⊕ Fin m) ?_ φ hsec
      (spForm m K) ?_
    · simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    · rintro A ⟨s, rfl⟩ u hu hrank
      have hA : φ s ∈ StatedSp m K := by
        rw [← hφr]
        exact ⟨s, rfl⟩
      have hβ : ∀ u : Fin m ⊕ Fin m → K, u ≠ 0 → ∃ x, spForm m K x u ≠ 0 := by
        intro u hu
        by_contra h
        push Not at h
        exact hu (spForm_nondegenerate.2 u h)
      exact elation_form_sp (spForm m K) hβ spForm_self _ ((mem_statedSp_iff_forall _).mp hA)
        hu hrank
  · refine hc.not_le_QB_of_natural h35 hLR hZV hBV hVQ hK (ι := Fin m ⊕ Fin m) ?_ φ hsec
      (polarBilin (quadPlus m K)) ?_
    · simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    · rintro A ⟨s, rfl⟩ u hu hrank
      have hA : φ s ∈ StatedOmega (StatedQuadPlus m K) := by
        rw [← hφr]
        exact ⟨s, rfl⟩
      exact omega_hform (coe_quadPlus m K) (nondegenerate_polarBilin_quadPlus m K) hA hu hrank
  · refine hc.not_le_QB_of_natural h35 hLR hZV hBV hVQ hK
      (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) ?_ φ hsec (polarBilin (quadMinus m K b c)) ?_
    · simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    · rintro A ⟨s, rfl⟩ u hu hrank
      have hA : φ s ∈ StatedOmega (StatedQuadMinus m K b c) := by
        rw [← hφr]
        exact ⟨s, rfl⟩
      exact omega_hform (coe_quadMinus m K b c)
        (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) hA hu hrank

theorem stroth310Chi_of_34 (h34 : Stroth34Statement) : Stroth310ChiStatement :=
  stroth310Chi_of_not_le_QB h34 (stroth310NotQB_of_34 h34)

end CFSG.RankThree.GF2n.Stroth80

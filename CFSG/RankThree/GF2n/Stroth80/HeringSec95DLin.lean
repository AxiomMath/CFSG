module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CLin

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9

open Module

variable {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {B : LinearMap.BilinForm K E} {Qf : E → K}

theorem selfAdj_sub_one95 (hQ : IsQuadSpace B Qf) (T : E ≃ₗ[K] E) (hT : ∀ e, Qf (T e) = Qf e)
    (hT2 : ∀ e, T (T e) = e) (e e' : E) :
    B (((T : E →ₗ[K] E) - 1) e) e' = B e (((T : E →ₗ[K] E) - 1) e') := by
  have h := hQ.B_iso T hT e (T e')
  rw [hT2] at h
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub,
    LinearMap.map_sub₂, h]

theorem finrank_range_eq_inf_orth_add95 (hQ : IsQuadSpace B Qf) (Φ : E →ₗ[K] E)
    (hΦ : ∀ e e', B (Φ e) e' = B e (Φ e')) (V : Submodule K E) :
    finrank K (LinearMap.range Φ) =
      finrank K ↥(LinearMap.range Φ ⊓ B.orthogonal V) + finrank K ↥(V.map Φ) := by
  classical
  set S : Submodule K E := B.orthogonal (V.map Φ) with hS
  have hperp : ∀ S' : Submodule K E,
      finrank K ↥(B.orthogonal S') = finrank K E - finrank K S' := fun S' =>
    LinearMap.BilinForm.finrank_orthogonal hQ.nondegenerate S'
  have h1 : LinearMap.range Φ ⊓ B.orthogonal V = S.map Φ := by
    ext y
    simp only [Submodule.mem_inf, LinearMap.mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨⟨e, rfl⟩, hy⟩
      refine ⟨e, ?_, rfl⟩
      rw [hS, LinearMap.BilinForm.mem_orthogonal_iff]
      rintro _ ⟨v, hv, rfl⟩
      rw [hΦ v e]
      exact LinearMap.BilinForm.mem_orthogonal_iff.mp hy v hv
    · rintro ⟨e, he, rfl⟩
      refine ⟨⟨e, rfl⟩, ?_⟩
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro v hv
      rw [← hΦ v e]
      exact LinearMap.BilinForm.mem_orthogonal_iff.mp he _ ⟨v, hv, rfl⟩
  have hker : LinearMap.ker Φ ⊓ S = LinearMap.ker Φ := by
    refine inf_eq_left.mpr fun e he => ?_
    rw [hS, LinearMap.BilinForm.mem_orthogonal_iff]
    rintro _ ⟨v, hv, rfl⟩
    rw [hΦ v e, LinearMap.mem_ker.mp he, map_zero]
  have h2 := finrank_map_add_finrank_inf_ker Φ S
  rw [hker] at h2
  have h3 := LinearMap.finrank_range_add_finrank_ker Φ
  have h4 := hperp (V.map Φ)
  have h5 : finrank K ↥(V.map Φ) ≤ finrank K E := Submodule.finrank_le _
  rw [h1]
  rw [← hS] at h4
  omega


theorem map_orth_le_of_finrank_range_le95 (hQ : IsQuadSpace B Qf) (Φ : E →ₗ[K] E)
    (hΦ : ∀ e e', B (Φ e) e' = B e (Φ e')) {V : Submodule K E}
    (hVV : ∀ v ∈ V, ∀ v' ∈ V, B v v' = 0) (hΦV : V.map Φ ≤ V)
    (hrank : finrank K (LinearMap.range Φ) ≤ 2 * finrank K ↥(V.map Φ)) :
    (B.orthogonal V).map Φ ≤ V := by
  classical
  set W := B.orthogonal V with hW
  have hWmem : ∀ e, e ∈ W ↔ ∀ v ∈ V, B v e = 0 := fun e =>
    LinearMap.BilinForm.mem_orthogonal_iff
  have hVW : V ≤ W := fun v hv => (hWmem v).mpr fun v' hv' => hVV v' hv' v hv
  have hΦW : W.map Φ ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ W := hw
    rw [hWmem] at hw' ⊢
    intro v hv
    rw [← hΦ v w]
    exact hw' _ (hΦV ⟨v, hv, rfl⟩)
  by_contra hcon
  set Y := W.map Φ with hY
  have hΦVY : V.map Φ ≤ Y := Submodule.map_mono hVW
  have h1 := finrank_range_eq_inf_orth_add95 hQ Φ hΦ V
  rw [← hW] at h1
  have hYle : Y ≤ LinearMap.range Φ ⊓ W :=
    le_inf (by rintro _ ⟨w, _, rfl⟩; exact ⟨w, rfl⟩) hΦW
  have h2 : finrank K Y ≤ finrank K ↥(LinearMap.range Φ ⊓ W) := Submodule.finrank_mono hYle
  have hlt : Y ⊓ V < Y :=
    lt_of_le_of_ne inf_le_left fun h => hcon (h ▸ inf_le_right)
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  have h4 : finrank K ↥(V.map Φ) ≤ finrank K ↥(Y ⊓ V) :=
    Submodule.finrank_mono (le_inf hΦVY hΦV)
  omega

theorem finrank_range_le_of_map_le95 (Φ : E →ₗ[K] E) (F P : Submodule K E) (hP : F.map Φ ≤ P) :
    finrank K (LinearMap.range Φ) ≤ finrank K P + (finrank K E - finrank K F) := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl F
  have hrange : LinearMap.range Φ = F.map Φ ⊔ C.map Φ := by
    rw [← Submodule.map_sup, hC.sup_eq_top, Submodule.map_top]
  have h1 : finrank K ↥(LinearMap.range Φ) ≤ finrank K ↥(F.map Φ) + finrank K ↥(C.map Φ) := by
    rw [hrange]
    exact Submodule.finrank_add_le_finrank_add_finrank _ _
  have h2 : finrank K ↥(C.map Φ) ≤ finrank K C := Submodule.finrank_map_le _ _
  have h3 : finrank K ↥(F.map Φ) ≤ finrank K P := Submodule.finrank_mono hP
  have h4 := Submodule.finrank_add_eq_of_isCompl hC
  omega

theorem orthogonal_sup_eq95 (S₁ S₂ : Submodule K E) :
    B.orthogonal (S₁ ⊔ S₂) = B.orthogonal S₁ ⊓ B.orthogonal S₂ := by
  ext e
  simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_sup]
  constructor
  · intro h
    exact ⟨fun y hy => h y ⟨y, hy, 0, S₂.zero_mem, add_zero y⟩,
      fun y hy => h y ⟨0, S₁.zero_mem, y, hy, zero_add y⟩⟩
  · rintro ⟨h1, h2⟩ y ⟨a, ha, b, hb, rfl⟩
    have e1 := h1 a ha
    have e2 := h2 b hb
    rw [map_add, LinearMap.add_apply, e1, e2, add_zero]


theorem map_orth_le_of_two_points95 (hQ : IsQuadSpace B Qf) (T : E ≃ₗ[K] E)
    (hT : ∀ e, Qf (T e) = Qf e) (hT2 : ∀ e, T (T e) = e)
    {V V' U₁ U₂ : Submodule K E} {b c : E}
    (hVV : ∀ v ∈ V, ∀ v' ∈ V, B v v' = 0) (hTV : ∀ v ∈ V, T v ∈ V)
    (hPdim : finrank K ↥(V.map ((T : E →ₗ[K] E) - 1)) = 2)
    (hU₁ : B.orthogonal U₁ = U₁) (hU₂ : B.orthogonal U₂ = U₂)
    (hbD : b ∈ V' ⊓ U₁ ⊓ U₂) (hcD : c ∈ V' ⊓ U₁ ⊓ U₂)
    (hW' : ∀ e, (∀ v ∈ V', B v e = 0) → T e - e ∈ V')
    (hb : ∀ e, B b e = 0 → T e - e ∈ U₁)
    (hb' : ∀ u ∈ U₁, T u - u ∈ Submodule.span K {b})
    (hc : ∀ e, B c e = 0 → T e - e ∈ U₂)
    (hc' : ∀ u ∈ U₂, T u - u ∈ Submodule.span K {c})
    (hdim : finrank K ↥(V' ⊓ U₁ ⊓ U₂) ≤ 2) :
    ∀ w, (∀ v ∈ V, B v w = 0) → T w - w ∈ V := by
  classical
  set Φ : E →ₗ[K] E := (T : E →ₗ[K] E) - 1 with hΦdef
  have hΦe : ∀ e, Φ e = T e - e := fun e => by
    simp [hΦdef]
  have hΦ : ∀ e e', B (Φ e) e' = B e (Φ e') := selfAdj_sub_one95 hQ T hT hT2
  set D₀ : Submodule K E := V' ⊓ U₁ ⊓ U₂ with hD₀
  set F₀ : Submodule K E := B.orthogonal V' ⊔ U₁ ⊔ U₂ with hF₀
  have hspanb : Submodule.span K {b} ≤ D₀ := Submodule.span_le.mpr (by simpa using hbD)
  have hspanc : Submodule.span K {c} ≤ D₀ := Submodule.span_le.mpr (by simpa using hcD)
  have hmapF : F₀.map Φ ≤ D₀ := by
    rw [hF₀, Submodule.map_sup, Submodule.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨e, he, rfl⟩
      have he' : ∀ v ∈ V', B v e = 0 := LinearMap.BilinForm.mem_orthogonal_iff.mp he
      rw [hΦe]
      exact ⟨⟨hW' e he', hb e (he' b (Submodule.mem_inf.mp (Submodule.mem_inf.mp hbD).1).1)⟩,
        hc e (he' c (Submodule.mem_inf.mp (Submodule.mem_inf.mp hcD).1).1)⟩
    · rintro _ ⟨u, hu, rfl⟩
      rw [hΦe]
      exact hspanb (hb' u hu)
    · rintro _ ⟨u, hu, rfl⟩
      rw [hΦe]
      exact hspanc (hc' u hu)
  have hperp : B.orthogonal F₀ = D₀ := by
    rw [hF₀, orthogonal_sup_eq95, orthogonal_sup_eq95, hU₁, hU₂,
      LinearMap.BilinForm.orthogonal_orthogonal hQ.nondegenerate
        (LinearMap.BilinForm.IsAlt.isRefl hQ.alt)]
  have hdimF : finrank K ↥(B.orthogonal F₀) = finrank K E - finrank K F₀ :=
    LinearMap.BilinForm.finrank_orthogonal hQ.nondegenerate F₀
  have hrk := finrank_range_le_of_map_le95 Φ F₀ D₀ hmapF
  rw [hperp] at hdimF
  have hrange4 : finrank K (LinearMap.range Φ) ≤ 2 * finrank K ↥(V.map Φ) := by
    have : finrank K ↥(V.map Φ) = 2 := hPdim
    omega
  have hΦV : V.map Φ ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hΦe]
    exact V.sub_mem (hTV v hv) hv
  have key := map_orth_le_of_finrank_range_le95 hQ Φ hΦ hVV hΦV hrange4
  intro w hw
  have hw' : w ∈ B.orthogonal V := LinearMap.BilinForm.mem_orthogonal_iff.mpr hw
  have := key ⟨w, hw', rfl⟩
  rwa [hΦe] at this

end CFSG.RankThree.GF2n.Stroth80.HS9

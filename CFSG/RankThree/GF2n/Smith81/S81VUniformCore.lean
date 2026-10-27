module

public import CFSG.RankThree.GF2n.Smith81.S81VPointClause

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {F : Type} [Field F] [Finite F] [CharP F 2]
  {σ : F ≃+* F}

theorem exists_su_smul_of_pts (hσ : IsUnitaryInvolution σ) {W₁ W₂ : Submodule F (Fin 6 → F)}
    (h₁ : IsPt σ W₁) (h₂ : IsPt σ W₂) : ∃ h : SUid σ 6, ∀ v, v ∈ W₂ ↔ ∃ w ∈ W₁, h • w = v := by
  obtain ⟨g₁, hg₁⟩ := exists_su_smul_W₀ hσ h₁.1 h₁.2
  obtain ⟨g₂, hg₂⟩ := exists_su_smul_W₀ hσ h₂.1 h₂.2
  refine ⟨g₂ * g₁⁻¹, fun v => ?_⟩
  rw [hg₂ v]
  constructor
  · rintro ⟨w₀, hw₀, rfl⟩
    refine ⟨g₁ • w₀, (hg₁ _).2 ⟨w₀, hw₀, rfl⟩, ?_⟩
    rw [← mul_smul, inv_mul_cancel_right]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨w₀, hw₀, rfl⟩ := (hg₁ w).1 hw
    refine ⟨w₀, hw₀, ?_⟩
    rw [← mul_smul, inv_mul_cancel_right]

theorem uniform_of_core_U (hσ : IsUnitaryInvolution σ) (e₀ : K ≃+* Fσ σ) (hq : 4 ≤ Nat.card K)
    (hF : Nat.card F = Nat.card K ^ 2) (hV : finrank K M₀.E = 20)
    (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (hTker : ∀ s : Lgen M (LB M Q B), T s = 1 ↔ (s : G) ∈ Q)
    (hnorm : Lgen M (LB M Q B) ≤ Subgroup.normalizer (Q : Set G))
    (hTiso : ∀ (s : Lgen M (LB M Q B)) (u w : M₀.E), M₀.B (T s u) (T s w) = M₀.B u w)
    (A : SUid σ 6 →* (M₀.E ≃ₗ[K] M₀.E))
    (hAT1 : ∀ s : Lgen M (LB M Q B), ∃ h : SUid σ 6, ∀ v, T s v = A h v)
    (hAT2 : ∀ h : SUid σ 6, ∃ s : Lgen M (LB M Q B), ∀ v, T s v = A h v)
    (hpts : ∀ A' : Subgroup G, IsZConjugate Z A' → A' ≤ Q → A' ≠ Z →
      ∃ W : Submodule F (Fin 6 → F), IsTotIso σ W ∧ finrank F W = 3 ∧
        finrank K (fixAt σ A W) = 1 ∧ (∀ v, v ∈ fixAt σ A W ↔ ∃ x ∈ A', M₀.π x = v) ∧
        (∀ u ∈ PtStab σ W, ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB A' ∧ ∀ v, T t v = A u v) ∧
        ∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A' → ∃ u ∈ PtStab σ W, ∀ v, A u v = T s v)
    (hB : IsZConjugate Z B ∧ B ≤ Q ∧ B ≠ Z)
    (hspan : ∀ v : M₀.E, v ∈ ⨆ A' : {A' : Subgroup G // IsZConjugate Z A' ∧ A' ≤ Q ∧ A' ≠ Z},
        Submodule.span K ((fun x : G => M₀.π x) '' ((A'.1 : Subgroup G) : Set G)))
    (hV1 : ∀ W : Submodule F (Fin 6 → F), (∀ v, v ∈ fixAt σ A W ↔ ∃ x ∈ B, M₀.π x = v) →
      (∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q B → ∃ u ∈ PtStab σ W, ∀ v, A u v = T s v) →
      finrank K (V1At σ A M₀.B W) ≤ 10) :
    ∃ (e' : K ≃+* Fσ σ) (ψ : M₀.E ≃ₗ[K] E3UWspace σ e')
      (φ : Lgen M (LB M Q B) →* (E3UWspace σ e' ≃ₗ[K] E3UWspace σ e')),
      EUniData M Q Z B M₀ ψ φ (e3uGam σ e') (e3uP0 σ e') (e3uU0 σ e') := by
  classical
  obtain ⟨WB, hti, h3, hline, hFixB, -, hU'B⟩ := hpts B hB.1 hB.2.1 hB.2.2
  have hWBpt : IsPt σ WB := ⟨hti, h3⟩
  have hspanW : ⨆ g : SUid σ 6, (fixAt σ A WB).map (A g : M₀.E →ₗ[K] M₀.E) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hle : (⨆ A' : {A' : Subgroup G // IsZConjugate Z A' ∧ A' ≤ Q ∧ A' ≠ Z},
        Submodule.span K ((fun x : G => M₀.π x) '' ((A'.1 : Subgroup G) : Set G))) ≤
        ⨆ g : SUid σ 6, (fixAt σ A WB).map (A g : M₀.E →ₗ[K] M₀.E) := by
      apply iSup_le
      intro A'
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨W', hti', h3', -, hFix', -, -⟩ := hpts A'.1 A'.2.1 A'.2.2.1 A'.2.2.2
      obtain ⟨h, hh⟩ := exists_su_smul_of_pts hσ hWBpt (⟨hti', h3'⟩ : IsPt σ W')
      have hmem : M₀.π x ∈ (fixAt σ A WB).map (A h : M₀.E →ₗ[K] M₀.E) := by
        rw [← fixAt_map A h hh]
        exact (hFix' _).2 ⟨x, hx, rfl⟩
      exact Submodule.mem_iSup_of_mem h hmem
    exact hle (hspan v)
  have hβA : ∀ g u w, M₀.B (A g u) (A g w) = M₀.B u w := by
    intro g u w
    obtain ⟨s, hs⟩ := hAT2 g
    rw [← hs u, ← hs w]
    exact hTiso s u w
  obtain ⟨e', ψ, gB, hψA, hgB, hψB⟩ := core_main_U_at hσ e₀ hq hF hV A M₀.B M₀.alt hβA hWBpt hline
    hspanW (hV1 WB hFixB hU'B)
  obtain ⟨φ, hφT, hφrange, hφker, hφeq⟩ := exists_phiU e' ψ T hTe hTker A hψA hAT1 hAT2
  refine ⟨e', ψ, φ, ⟨hφrange, hφker, hnorm, hφeq, ?_⟩⟩
  intro A' hA'Z hA'Q hA'ne
  obtain ⟨W', hti', h3', -, hFix', hU', -⟩ := hpts A' hA'Z hA'Q hA'ne
  obtain ⟨g, hg, hset, hunip⟩ := point_clauseU hσ e' ψ T A hψA hgB hψB hti' h3' hFix' hU'
  refine ⟨g, hg, hset, fun u hu => ?_⟩
  obtain ⟨t, htQB, htu⟩ := hunip u hu
  exact ⟨t, htQB, by rw [hφT t]; exact htu⟩

end CFSG.RankThree.GF2n.Smith81.S81V

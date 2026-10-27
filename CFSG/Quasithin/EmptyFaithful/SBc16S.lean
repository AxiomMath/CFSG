module

public import CFSG.Quasithin.EmptyFaithful.S146P4
public import CFSG.Quasithin.EmptyFaithful.SBc13ACComp
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.Quasithin.EmptyFaithful.SBc16SAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc16

section Aux

variable {G : Type} [Group G] [Finite G]

theorem sup_le_normalizer_of_mem_cComp {Y K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ cComp Y)
    (h₂ : K₂ ∈ cComp Y) : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set G) :=
  sup_le Subgroup.le_normalizer
    ((le_cCompSpan h₂).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_cCompSpan h₁)).mp (cComp_normal_span_of_le h₁).2))

theorem conjSub_conjSub_eq_of_mem_cComp {Y K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp Y)
    (hK₂ : conjSub s K₁ ∈ cComp Y) (hsY : s ∈ Y) (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hYN : Y ≤ Subgroup.normalizer ((K₁ ⊔ conjSub s K₁ : Subgroup G) : Set G)) :
    conjSub s (conjSub s K₁) = K₁ := by
  have hK₃ : conjSub s (conjSub s K₁) ∈ cComp Y := conjSub_mem_cComp_of_mem hK₂ hsY
  have hle : conjSub s (conjSub s K₁) ≤ K₁ ⊔ conjSub s K₁ :=
    calc conjSub s (conjSub s K₁) ≤ conjSub s (K₁ ⊔ conjSub s K₁) := conjSub_mono s le_sup_right
      _ = K₁ ⊔ conjSub s K₁ := conjSub_eq_of_mem_normalizer (hYN hsY)
  rcases SBc13.eq_or_eq_of_mem_cComp_of_le_sup hK₁ hK₂ hK₃ hle with h | h
  · exact h
  · exfalso
    have h' : conjSub s (conjSub s K₁) = conjSub s K₁ := h
    exact hsN (CosetGeom.mem_normalizer_of_conjSub_eq ((conjSub_inj s).mp h'))

end Aux

section Conj

variable {G : Type} [Group G]

noncomputable def oTwoQuotConjEquiv (s : G) (K₁ : Subgroup G) :
    OTwoQuot K₁ ≃* OTwoQuot (conjSub s K₁) :=
  QuotientGroup.congr _ _
    (K₁.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective)
    (map_pCore_mulEquiv 2 _)

end Conj

@[expose] def Input14615SetupFourR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) → conjSub s K₁ ∈ cComp (mcOf T) →
          s ∈ T → s ∉ Subgroup.normalizer (K₁ : Set G) →
          conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ →
          mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T →
          Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) →
            ∃ K₁' : Subgroup G, (K₁' = K₁ ∨ K₁' = conjSub s K₁) ∧ oTwoUpper H₁ ≤ K₁' ∧
              oTwoUpper H₂ ≤ conjSub s K₁' ∧
              ⁅uHi T M H H₁, conjSub s K₁'⁆ ≤ quasithinOmegaOneCenter T

theorem input14615SetupFourP_of_R (h : Input14615SetupFourR) : Input14615SetupFourP := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx hC4
  obtain ⟨-, K₁, s, hK₁, hsT, hsN, hK, hII, -, hiso₁⟩ := hC4
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hTG : T ≤ mcOf T := hTH.trans hHG
  have hsG : s ∈ mcOf T := hTG hsT
  have hKzN : mcOf T ≤ Subgroup.normalizer
      ((conjClosure (oTwoUpper H) (mcOf T) : Subgroup G) : Set G) :=
    le_normalizer_conjClosure _ _
  have hK₂ : conjSub s K₁ ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hK₁ hsG
  have hss : conjSub s (conjSub s K₁) = K₁ :=
    conjSub_conjSub_eq_of_mem_cComp hK₁ hK₂ hsG hsN (by rw [← hK]; exact hKzN)
  obtain ⟨K₁', hK₁'eq, h1, h2, h3⟩ := h G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ s hK₁
    hK₂ hsT hsN hK hII hiso₁
  have key : K₁' ∈ cComp (mcOf T) ∧ conjSub s K₁' ∈ cComp (mcOf T) ∧
      conjClosure (oTwoUpper H) (mcOf T) = K₁' ⊔ conjSub s K₁' ∧
      s ∉ Subgroup.normalizer (K₁' : Set G) ∧ Nonempty (OTwoQuot K₁' ≃* L216) := by
    rcases hK₁'eq with h₀ | h₀
    · rw [h₀]
      exact ⟨hK₁, hK₂, hK, hsN, hiso₁⟩
    · rw [h₀]
      refine ⟨hK₂, by rw [hss]; exact hK₁, by rw [hss, sup_comm]; exact hK, ?_, ?_⟩
      · intro hN
        apply hsN
        have h4 := conjSub_eq_of_mem_normalizer hN
        rw [hss] at h4
        exact CosetGeom.mem_normalizer_of_conjSub_eq h4.symm
      · obtain ⟨e₁⟩ := hiso₁
        exact ⟨(oTwoQuotConjEquiv s K₁).symm.trans e₁⟩
  exact ⟨K₁', conjSub s K₁', s,
    { kz := key.2.2.1
      s_mem := hsT
      s_not := key.2.2.2.1
      conj := rfl
      oTwo₁ := h1
      oTwo₂ := h2
      cent := h3
      perf₂ := C2Nine.oTwoUpper_eq_of_perfect (perfect_of_mem_cComp key.2.1)
      shape := Or.inl ⟨key.1, key.2.1, hII, key.2.2.2.2⟩ }⟩

end SBc16

end CFSG.Quasithin

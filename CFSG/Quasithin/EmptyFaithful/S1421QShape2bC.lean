module

public import CFSG.Quasithin.EmptyFaithful.S1421QShape2bB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bI
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bH

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Final

variable {G : Type} [Group G] [Finite G]

theorem case2b_shape_of_central {T M H K : Subgroup G}
    (hmin : MinParabolic H T (H ⊓ M)) (hK : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hker : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    {m : ℕ} (hm : 2 ≤ m)
    (hty : IsPSL 3 2 m ↥(E2.star (H ⊓ M) H K) ∨ E2.IsSp4Prime m ↥(E2.star (H ⊓ M) H K))
    (hdiag : E2.IsDiagramNontrivial (E2.star (H ⊓ M) H T) (E2.star (H ⊓ M) H K)
      (E2.star (H ⊓ M) H (T ⊓ K)))
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)))
    (hcen : IsCentralL3Sp4 m (OTwoQuot K)) :
    ∃ K1 : Subgroup G, Notation1428 T M H K1 ∧ Shape1428 T H K1 := by
  classical
  have c : Case2a.Setting T M H K := ⟨hmin, hK, hHK, hTK, hker⟩
  have hty' : IsPSL 3 2 m ↥(E2.star (H ⊓ M) H K) ∨ IsPSp4 2 m ↥(E2.star (H ⊓ M) H K) := by
    rcases hty with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      have hm1 : m ≠ 1 := by omega
      simpa [E2.IsSp4Prime, hm1] using h
  have hUs : IsSylowTwoOf (E2.star (H ⊓ M) H (T ⊓ K)) (E2.star (H ⊓ M) H K) :=
    Case2a.isSylowTwoOf_star c.le_H c.sylow_inf
  obtain ⟨F, hF, hFin, P, hP⟩ := parabolics_ambient hm hty' hUs
  obtain ⟨g, hg, hk⟩ := hP.levi 1
  obtain ⟨-, -, -, hL2⟩ := isL2Quot_K1 (c := c) (hP.le 1) hm hP.card g hg hk
  have hUP : E2.star (H ⊓ M) H (T ⊓ K) ≤ P 1 := hP.sylow_le 1
  have hltK : K1 c (P 1) < K := by
    refine lt_of_le_of_ne (K1_le _) fun h => ?_
    have h1 : E2.star (H ⊓ M) H (K1 c (P 1)) = perfectCore (P 1) := star_K1 (hP.le 1)
    rw [h] at h1
    exact (hP.maxPar 1).2.1 (le_antisymm (hP.le 1) (h1.le.trans (perfectCore_le _)))
  have hlt : K1 c (P 1) < oTwoUpper H := by
    rw [c.oTwoUpper_eq]
    exact hltK
  refine ⟨K1 c (P 1),
    { le_K := (K1_le _).trans c.oTwoUpper_eq.ge
      inf_le := by
        rw [c.oTwoUpper_eq]
        exact inf_le_normalizer_K1 hUP
      pCore_le := pCore_le_normalizer_K1 _
      sylow := sylow_K1 hUP
      bender := ⟨m, hm, Or.inl hL2⟩
      cComp_mem := cComp_K1 (hP.le 1) hm hP.card g hg hk
      not_le := not_le_K1 (hP.le 1) hB hUs (hP.perf 1) hm hP.card g hg
      index := Or.inr ⟨hlt, relIndex_sOf_K1 hm hP hdiag⟩
      borel_inf := by
        rw [c.oTwoUpper_eq]
        exact Case2a.borel_inf c hB
      borel_le := borel_le_K1 (hP.le 1) hB hUs hUP (hP.perf 1) }, ?_⟩
  refine ⟨Or.inr (Or.inr ⟨?_, hlt, ?_⟩)⟩
  · rw [c.oTwoUpper_eq]
    exact hK
  · rw [c.oTwoUpper_eq]
    exact ⟨⟨m, hm, hL2, hcen⟩, Shape.diag_of_parabData c hP hdiag,
      Shape.parabolic_of_parabData c hP⟩

end Final

end CFSG.Quasithin.F146Field.Case2b

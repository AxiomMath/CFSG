module

public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open

theorem catalog_of_faithful_empty
    (h14 : UniqueCentralizerRecognitionStatement)
    (h15 : MultipleCentralizerRecognitionStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.QuasithinUnique.quasithinIsQTKECat G) (T : Sylow 2 G)
    (hMT : ∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₁ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₂ ∧
      (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂)
    (hLf : ∀ L : Subgroup G,
      ¬ CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L) :
    CFSG.Blueprint.Catalog G := by
  classical
  have hTne := sylow_ne_bot hnonab T
  have hsyl : quasithinIsSylowTwo (T : Subgroup G) := ⟨T.isPGroup', T.not_dvd_index⟩
  have hLf' : ∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal (T : Subgroup G) L := fun L h =>
    hLf L (quasithinIsFaithfulLocal_assembly_iff_open.mpr h)
  set Z := quasithinOmegaOneCenter (T : Subgroup G) with hZ
  have hCN : Subgroup.centralizer (Z : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.centralizer_le_normalizer _
  obtain ⟨Mc, hMc, hNMc⟩ := exists_maxTwoLocal_ge (isTwoLocal_normalizer_omegaOneCenter
    T.isPGroup' hTne)
  have hCMc := hCN.trans hNMc
  have hTC : (T : Subgroup G) ≤ Subgroup.centralizer (Z : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ (T : Subgroup G) ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) := by
      have : Z ≤ (T : Subgroup G) ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) :=
        (Subgroup.closure_le _).mpr fun w hw => hw.1
      exact this hz
    exact (Subgroup.mem_centralizer_iff.mp hz'.2 x hx).symm
  by_cases huniq : ∀ M : Subgroup G, quasithinIsMaxTwoLocal M →
      Subgroup.centralizer (Z : Set G) ≤ M → M = Mc
  ·
    apply catalog_of_theoremE_alternatives_native g2TwoDerivedUnitaryTransport_holds
    left
    refine h14 G (T : Subgroup G) Mc ⟨‹_›, hnonab, hqtke, hsyl, hLf', hMc, hTC.trans hCMc, hCMc,
      huniq, ?_⟩
    obtain ⟨M₁, M₂, hne, hM₁, hM₂, hTM₁, hTM₂⟩ := hMT
    by_cases h₁ : M₁ = Mc
    · exact ⟨M₂, hM₂, hTM₂, fun h => hne (h₁.trans h.symm)⟩
    · exact ⟨M₁, hM₁, hTM₁, h₁⟩
  ·
    push Not at huniq
    obtain ⟨M, hM, hCM, hMne⟩ := huniq
    apply catalog_of_theoremE_alternatives_native g2TwoDerivedUnitaryTransport_holds
    right
    exact h15 G (T : Subgroup G) ⟨‹_›, hnonab, hqtke, hsyl, hLf',
      ⟨M, Mc, hMne, hM, hMc, hCM, hCMc⟩⟩

end CFSG.Quasithin.EmptyFaithfulMultiple

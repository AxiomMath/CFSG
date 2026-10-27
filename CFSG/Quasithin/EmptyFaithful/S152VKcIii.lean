module

public import CFSG.Quasithin.EmptyFaithful.S152VPsl
public import CFSG.Quasithin.EmptyFaithful.S152VKc

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.LieType.BorelTits

namespace S152V

theorem no_m22_section_of_isL2 {G : Type} [Group G] [Finite G]
    (L : Subgroup G)
    (hL : (∃ f : ℕ, Even f ∧ IsL2Quot f (OTwoQuot L)) ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Prime p (OTwoQuot L))
    (B : Subgroup G) (hB : B ≤ L) (g : B →* NativeSporadic.Carrier .M22)
    (hg : Function.Surjective g) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isSimpleGroup_M22
  obtain ⟨C, g₁, hg₁⟩ := exists_section_subgroupOf hB g hg
  have hZ : IsPGroup 2 (CFSG.Open.pCore 2 ↥L) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have : (CFSG.Open.pCore 2 ↥L).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  obtain ⟨C', g₂, hg₂⟩ := exists_quotient_section not_isPGroup_M22 (CFSG.Open.pCore 2 ↥L) hZ C g₁ hg₁
  rcases hL with ⟨f, -, ⟨e⟩⟩ | ⟨p, hp, hp2, ⟨e⟩⟩
  · obtain ⟨C'', g₃, hg₃⟩ := exists_section_of_mulEquiv e C' g₂ hg₂
    refine no_m22_section_psl2 (Or.inl ?_) C'' g₃ hg₃
    have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    obtain ⟨n, -, hn⟩ := FiniteField.card (GaloisField 2 f) 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨C'', g₃, hg₃⟩ := exists_section_of_mulEquiv e C' g₂ hg₂
    refine no_m22_section_psl2 (Or.inr ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, ?_⟩) C'' g₃ hg₃
    rw [Nat.card_zmod, pow_one]

end S152V

theorem tail15215KcIii_proof : Tail15215KcIii := by
  intro G _ _ T Mc K hxi hiii hsec
  obtain ⟨L, t, -, -, -, -, hKc, hcomm, hL⟩ := hiii
  obtain ⟨A, N, hN, hAX, ⟨e⟩⟩ := hsec
  let f : A →* NativeSporadic.Carrier .M22 := (e : (↥A ⧸ N) →* _).comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hAL : A ≤ L ⊔ conjSub t L := hKc ▸ hAX
  have := S152V.isSimpleGroup_M22
  rcases S152V.sec_of_sup S152V.not_isPGroup_M22 L (conjSub t L) ⁅L, conjSub t L⁆
      (S152V.le_normalizer_commutator_left _ _) (S152V.le_normalizer_commutator_right _ _)
      ((pCoreOf_isPGroup 2 Mc).to_le hcomm) le_rfl A hAL f hf with
    ⟨B, g, hB, hg⟩ | ⟨B, g, hB, hg⟩
  · exact S152V.no_m22_section_of_isL2 L hL B hB g hg
  · obtain ⟨B', g', hB', hg'⟩ := S152V.exists_section_of_le_map (MulAut.conj t) hB g hg
    exact S152V.no_m22_section_of_isL2 L hL B' hB' g' hg'

theorem tail15215Kc : Tail15215Kc :=
  tail15215Kc_of_iii tail15215KcIii_proof

end CFSG.Quasithin

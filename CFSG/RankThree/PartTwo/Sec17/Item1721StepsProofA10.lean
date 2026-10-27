module

public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofSW

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

@[expose] def KS1721Frame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsE27 A →
    (Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) →
    ∀ Ω : Set (Subgroup G), Ω.ncard = 3 → (∀ F ∈ Ω, F ≤ A ∧ Nat.card F = 3) →
      (∀ g ∈ Subgroup.normalizer (A : Set G), ∀ F ∈ Ω, F.map (MulAut.conj g).toMonoidHom ∈ Ω) →
      ∀ c : G, Subgroup.zpowers c ∈ Ω →
        (∀ F ∈ Ω, ∃ g ∈ Subgroup.normalizer (A : Set G),
          F = (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom) →
        ∃ g ∈ Subgroup.normalizer (A : Set G), g * c * g⁻¹ = c⁻¹

theorem claim1721SA10_of (h1715 : Item1715) (hK : KS1721Frame) : Claim1721SA10 := by
  intro G _ _ A c L Y₀ Y₁ S p P h _ _ hΩ
  have hs := h.toSec17Std
  rcases h1715 G A c L Y₀ hs with ⟨hΩ', -⟩ | ⟨-, -, -, hW, hT⟩
  · exact absurd hΩ' hΩ
  · refine hK G A hs.isE27 hW (omegaA A) hT.1 (fun F hF => ⟨hF.1, hF.2.1⟩)
      (fun g hg F hF => (map_conj_mem_omegaA_iff hg).mpr hF) c hs.zpowers_mem_omegaA hT.2

end CFSG.RankThree.PartTwo.Sec17

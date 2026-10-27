module

public import CFSG.LocalAnalysis.WeakClosure81.W18Four

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Blueprint (LieModel)

@[expose] def Asch5_4Dynkin : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (H T : Subgroup Q),
    CFSG.Open.IsKGroup ↥H → IsSylowIn 2 T H → T < H → ¬ HasCompFactor H IsCalL0 →
    H ≠ lGen IsCalL0 H T →
    (∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (perfectCore H) ≤ 3 ∨ CFSG.Open.pRank p (lGen IsCalL0 H T) ≤ 1) →
    ∀ L : Subgroup Q, IsComponentModN (OInf H) H L → L ⊔ T = H →
      HasQuotShape L (OInf H : Set Q) (fun X _ => IsAlt X 6 ∨ IsL3 X 1) →
        ∃ t ∈ T, ActsOnDynkinMod (OInf H) L t

@[expose] def Asch2_2One : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (G : Subgroup Q) (p : ℕ), p.Prime → 3 < p →
    CFSG.Open.IsKGroup ↥G → CFSG.Open.pRank p G ≤ 3 →
    ∀ (M N : Subgroup Q) [(N.subgroupOf M).Normal], N ≤ M → M ≤ G →
      CFSG.layer (↥M ⧸ N.subgroupOf M) = ⊤ →
        CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ N.subgroupOf M)) ≤ 3

namespace MinCex183

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem exists_dynkin_182 (hD : Asch5_4Dynkin) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) {L : Subgroup G} (hL : IsComponentModN (OInf H) H L)
    (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (OInf H : Set G) (fun X _ => IsAlt X 6 ∨ IsL3 X 1)) :
    ∃ t ∈ D.T, ActsOnDynkinMod (OInf H) L t := by
  obtain ⟨hK, hT, hTlt, hno, hne, hp⟩ := c.hyps_5_11 h2
  exact hD G H D.T hK hT hTlt hno hne
    (fun p hpp hp2 => (hp p hpp hp2).imp_left fun h3 =>
      (CFSG.SectionRank.pRank_mono hpp.one_lt (perfectCore_le H)).trans h3) L hL hLT hX

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end

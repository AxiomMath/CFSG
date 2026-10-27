module

public import CFSG.Assembly.Defs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoKGroup
public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Piece

variable {G : Type} [Group G]

@[expose] def GGRCSKGPiece (C₀ E J : Subgroup G) : Prop :=
  J ≤ C₀ ∧ IsSubnormal J C₀ ∧ ⁅J, J⁆ = J ∧
    pCoreOf 2 C₀ ≤ J ⊔ (pCoreOf 2 C₀ ⊓ Subgroup.centralizer (pCoreOf 2 C₀ : Set G)) ∧
    pCoreOf 2 C₀ ≤
      ⁅J, pCoreOf 2 C₀⁆ ⊔ (pCoreOf 2 C₀ ⊓ Subgroup.centralizer (pCoreOf 2 C₀ : Set G)) ∧
    E ≤ Subgroup.normalizer (J : Set G) ∧
    ∀ [((pCoreOf 2 C₀).subgroupOf J).Normal],
      CFSG.Assembly.IsQuasisimple (↥J ⧸ (pCoreOf 2 C₀).subgroupOf J) ∧
      LargeEvenMarking (↥J ⧸ (pCoreOf 2 C₀).subgroupOf J) (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ ε ∈ E, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => ∃ s s' : ↥J,
          QuotientGroup.mk s = l ∧ QuotientGroup.mk s' = l' ∧ (s' : G) = ε⁻¹ * s * ε) φ)

end Piece

section Tags

@[expose] def GGRootCentKGStructTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p n f : ℕ) (ψ : (ggU t n f).K →* G),
    p.Prime → p ≠ 2 → StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → commutator ↥ψ.range = ⊤ →
    LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) t n 2 f →
    Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    GGTwoLocalRankFour p (Subgroup.normalizer (ψ.range : Set G)) →
    (∃ Bs : Subgroup G, IsElemAbelian p Bs ∧ p ^ 4 ≤ Nat.card Bs ∧
      Bs ≤ Subgroup.normalizer (ψ.range : Set G) ∧ ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) →
    ∀ r : G, GGRootInvolution (ggU t n f).D t ψ r →
      ¬ Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer {r}) →
    ∀ E : Subgroup G, E ≤ Subgroup.normalizer (ψ.range : Set G) →
      E ≤ Subgroup.centralizer {r} → IsPGroup p E →
      (∀ e ∈ E, GGPsiInnerDiag (ggU t n f).D ψ e) →
      ∃ 𝒥 : Set (Subgroup G),
        (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer {r} → ⁅P, P⁆ = P → P ≤ sSup 𝒥) ∧
        ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer {r}) E J

@[expose] def GGRootCentOTwoTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → commutator ↥ψ.range = ⊤ →
    LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) t n 2 f →
    Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    (∃ (p : ℕ) (Bs : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p Bs ∧ p ^ 4 ≤ Nat.card Bs ∧
      Bs ≤ Subgroup.normalizer (ψ.range : Set G) ∧ ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) →
    ∀ r : G, GGRootInvolution (ggU t n f).D t ψ r →
      ¬ Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer {r}) →
      pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer {r}) ≤ ψ.range

theorem ggRootCentKGStructTag_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGRootCentKGStructTag t := by
  intro G _ _ p n f ψ _ _ _ hrk
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggRootCentOTwoTag_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGRootCentOTwoTag t := by
  intro G _ _ n f ψ _ hrk
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggRootCentKGStructTag_POmegaOdd : GGRootCentKGStructTag .POmegaOdd :=
  fun _ _ _ _ _ _ _ _ _ hadm => absurd rfl hadm.2.2.2

theorem ggRootCentOTwoTag_POmegaOdd : GGRootCentOTwoTag .POmegaOdd :=
  fun _ _ _ _ _ _ hadm => absurd rfl hadm.2.2.2

theorem ggRootCentKGStructTag_forall (hPSL : GGRootCentKGStructTag .PSL)
    (hPSU : GGRootCentKGStructTag .PSU) (hPSp : GGRootCentKGStructTag .PSp)
    (hOp : GGRootCentKGStructTag .POmegaPlus) (hOm : GGRootCentKGStructTag .POmegaMinus)
    (hF4 : GGRootCentKGStructTag .F4) (hE6 : GGRootCentKGStructTag .E6)
    (hE7 : GGRootCentKGStructTag .E7) (hE8 : GGRootCentKGStructTag .E8)
    (h2E6 : GGRootCentKGStructTag .twistedE6) : ∀ t, GGRootCentKGStructTag t := by
  intro t
  cases t with
  | PSL => exact hPSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaOdd => exact ggRootCentKGStructTag_POmegaOdd
  | POmegaPlus => exact hOp
  | POmegaMinus => exact hOm
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact h2E6
  | G2 => exact ggRootCentKGStructTag_of_placeholder _ (Or.inl rfl)
  | trialityD4 => exact ggRootCentKGStructTag_of_placeholder _ (Or.inr (Or.inl rfl))
  | twistedB2 =>
    exact ggRootCentKGStructTag_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 =>
    exact ggRootCentKGStructTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 =>
    exact ggRootCentKGStructTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits =>
    exact ggRootCentKGStructTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem ggRootCentOTwoTag_forall (hPSL : GGRootCentOTwoTag .PSL)
    (hPSU : GGRootCentOTwoTag .PSU) (hPSp : GGRootCentOTwoTag .PSp)
    (hOp : GGRootCentOTwoTag .POmegaPlus) (hOm : GGRootCentOTwoTag .POmegaMinus)
    (hF4 : GGRootCentOTwoTag .F4) (hE6 : GGRootCentOTwoTag .E6)
    (hE7 : GGRootCentOTwoTag .E7) (hE8 : GGRootCentOTwoTag .E8)
    (h2E6 : GGRootCentOTwoTag .twistedE6) : ∀ t, GGRootCentOTwoTag t := by
  intro t
  cases t with
  | PSL => exact hPSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaOdd => exact ggRootCentOTwoTag_POmegaOdd
  | POmegaPlus => exact hOp
  | POmegaMinus => exact hOm
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact h2E6
  | G2 => exact ggRootCentOTwoTag_of_placeholder _ (Or.inl rfl)
  | trialityD4 => exact ggRootCentOTwoTag_of_placeholder _ (Or.inr (Or.inl rfl))
  | twistedB2 => exact ggRootCentOTwoTag_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 =>
    exact ggRootCentOTwoTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 =>
    exact ggRootCentOTwoTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits =>
    exact ggRootCentOTwoTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end Tags

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBLift
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrPRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRowFrame (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A

@[expose] def GGRowPRankLeTwo (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
        Nat.card E < p ^ 3

theorem ggRow_absurd_of_frame (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hF : GGRowFrame S) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel S p Bs K) : False := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  obtain ⟨y, hnb⟩ := hK.1
  have hInnK : GGInnerDiagOn Bs K := hcfg.1.2.2.1.2 y K hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  obtain ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, h4⟩ :=
    ggNbr_exists_frame_pair hRig hcfg.1.1 hnb hInnK hΛ hhas (hF p hp hodd lab hΛ hS)
  have hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    hK.2
  have hC₁ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc₁) hr₁
  have hC₂ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc₂) hr₂
  rcases ggCoxRefl_mul_orderOf_le_three hpres.1 hle3 hC₁ hC₂ with h | h
  · have h42 : 4 ∣ 2 := h4.trans (orderOf_dvd_of_pow_eq_one h)
    omega
  · have h43 : 4 ∣ 3 := h4.trans (orderOf_dvd_of_pow_eq_one h)
    omega

theorem ggRow_absurd_of_pRank {S : ℕ → LargeEvenLabel → Prop} (hP : GGRowPRankLeTwo S)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {K : Subgroup G}
    (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K) (hrow : GGInnerDiagOnLabel S p Bs K) : False := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  exact not_largeEvenMarking_of_labelAll_card_lt (S := S p)
    (fun lab hlab hS => hP p hp hodd lab hlab hS) (ggNbr_inndiag_pRank_ge_three hcfg hK hrow)

theorem ggRow_absurd_of_cells (hRig : GGLabelRigidInput) {S Sf Sp : ℕ → LargeEvenLabel → Prop}
    (hcov : ∀ p lab, S p lab → Sf p lab ∨ Sp p lab) (hF : GGRowFrame Sf)
    (hP : GGRowPRankLeTwo Sp) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel S p Bs K) : False := by
  have hor : GGInnerDiagOnLabel (fun p lab => Sf p lab ∨ Sp p lab) p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hQ => ⟨hcov _ _ hQ.1, hQ.2⟩) hrow
  rcases hor.elim_or with h | h
  · exact ggRow_absurd_of_frame hRig hF hcfg hpres hle3 hK h
  · exact ggRow_absurd_of_pRank hP hcfg hK h

end CFSG.StandardType

end

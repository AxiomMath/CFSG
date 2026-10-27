module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRowsNarrow
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRowR3Glue
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyR3Rank
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin


private theorem nsq4_two_le_n_of_ggLabelIso {p : ℕ} {lab labJ labK : LargeEvenLabel}
    (hrow : GGTablePRow p labJ labK) (hiso : GGLabelIso lab labJ) (h2 : 2 ≤ lab.n) :
    2 ≤ labJ.n := by
  rcases hiso with rfl | ⟨-, -, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h2
  · omega
  all_goals first
    | (rw [h]; exact h2)
    | (rw [h]; dsimp only; omega)
    | (exfalso; rw [h] at hrow; simp [GGTablePRow] at hrow)

theorem nsNbr_fieldRow_narrow (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hTP : GGNbrTablePNbrInputOn GGRegimeFieldTwo) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQFour p Bs L) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hK : ¬ GGInnerDiagOnLabel GGLabNbrOk p Bs K) :
    (p = 3 ∧ GGHasLabel ⟨.twE6, 0, 1⟩ (K ⧸ Subgroup.center K)) ∨
      (p = 7 ∧ GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K)) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨labK, hKΛ, hhasK, -⟩ := largeEvenMarking_exists_hasLabel (hInn.2 y K hnb)
  obtain ⟨labL, labJ, -, hq4, -, hJΛ, hdvd, hhasJ⟩ :=
    ggNbr_label_J_of_tcj_onLabel hTCJ hcfg hq hnb
  have hJ2 : 2 ≤ labJ.n := le_trans hq4 (Nat.le_of_dvd (by have := hJΛ.1; omega) hdvd)
  have hnokK : ¬ GGLabNbrOk p labK := fun hok => hK (largeEvenMarking_mono
    (fun _ _ _ _ _ _ ⟨he, hP⟩ => ⟨he ▸ hok, hP⟩)
    (ggInnerDiagOn_relabel hRig (hInn.2 y K hnb) hKΛ hhasK))
  have hK1 : labK.n = 1 := by
    have h := hnokK
    simp only [GGLabNbrOk, not_or, not_le] at h
    have h1 := hKΛ.1
    omega
  have hKnA : ¬ (labK.tag = .A ∧ p = 3 ∧ 5 ≤ labK.rank) := by
    have h := hnokK
    simp only [GGLabNbrOk, not_or, not_le] at h
    rintro ⟨ht, hp3, hr⟩
    exact h.2 ⟨ht, hK1, hp3, hr⟩
  have hreg : GGRegimeFieldTwo p (Nat.card Bs) labJ labK := ⟨hJ2, hK1, hKnA⟩
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ :=
    hTP G p B Bs x L D J y K hcfg hInn.1 (hInn.2 y K hnb) hnb labJ labK hJΛ hKΛ hreg hhasJ hhasK
  have hj2 : 2 ≤ jlab.n :=
    nsq4_two_le_n_of_ggLabelIso hrow (hRig labJ jlab _ hJΛ hjΛ hhasJ hhasJ1) hJ2
  have hnok : ¬ GGLabNbrOk p klab := fun hok => hK (largeEvenMarking_mono
    (fun _ _ _ _ _ _ ⟨he, hP⟩ => ⟨he ▸ hok, hP⟩)
    (ggInnerDiagOn_relabel hRig (hInn.2 y K hnb) hkΛ hhasK1))
  rcases ggTablePRow_fieldTwo hp hrow hkΛ hj2 hnok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, hhasK1⟩
  · exact Or.inr ⟨rfl, hhasK1⟩

theorem nsNbr_twE6_absurd (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hBig : GGTwE6BigLabelsKnown) (hRank : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hInn : GGInnerDiagAll 3 B Bs x L D J)
    (hq : GGInnerDiagOnLabel GGLabQFour 3 Bs L) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K)
    (hlabK : GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K)) : False := by
  obtain ⟨hNK, hInnK⟩ := ggRowR3_innerDiagOnLab hRig (hInn.2 y K hnb) hlabK
  have h5 : 3 ^ 5 ≤ Nat.card (ggGamma K hNK).range :=
    hRank G 3 B Bs x L D J hcfg rfl y K hnb (hInnK.mono fun _ _ h => h.1) hNK
      (ggTorusSelfCent_ggGamma hNK hcfg.2.1.2.2.2)
  obtain ⟨labL, labJ, _, hq4, _, hJΛ, hdvd, hhasJ⟩ := ggNbr_label_J_of_tcj_onLabel hTCJ hcfg hq hnb
  have hJ2 : 2 ≤ labJ.n := le_trans hq4 (Nat.le_of_dvd (by have := hJΛ.1; omega) hdvd)
  obtain ⟨hK0, lab, hlab, hraw⟩ := hInnK
  obtain ⟨_, _, _, _, _, _, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hn1 : lab.n = 1 := by
    have h1 := hlab.1
    have h2 := hP₀.1.2
    simp only [GGLabQTwo] at h2
    omega
  have hAll := hBig lab hlab hP₀.1.1.1 hn1
  obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, hP⟩, hAll'⟩⟩ := largeEvenRawDatum_exists (hAll _ hraw)
  obtain ⟨hJK, hset⟩ := ggTwE6BigSetting_of_nbr hL hPJ hcfg hnb hNK h5 θ hP.2.2.2
  have hM := hAll' hs hna K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hK0
    (ggGamma K hNK).range (ggGamma K hNK ⟨x, hcfg.tableB_facts.2.2.1⟩) (J.subgroupOf K) hset
  exact ggRowR3_false_of_marking hRig hJK hM hJΛ hJ2 hhasJ

@[expose] def NSNbrLinearInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 → ¬ GGSplitLie 3 L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
          GGInnerDiagOnLabel GGLabQFour 3 Bs L →
            ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K → ∀ ℓ : ℕ, 5 ≤ ℓ →
              ¬ GGHasLabel ⟨.A, ℓ, 1⟩ (↥K ⧸ Subgroup.center ↥K)

theorem nsNbrQFourInputOf_of_parts {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hTP : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (hBig : GGTwE6BigLabelsKnown)
    (hRank : GGTwE6ThreeNbrRankInput) (hLin : NSNbrLinearInput) (hBase : NSQFourInputOf T) :
    NSNbrQFourInputOf T := by
  intro G _ _ B Bs x L D J 𝒦 hreg y K hnb
  by_contra hK
  obtain ⟨hcfgR, hns, ι, M, e, hpres, hTM, hbig⟩ := hreg
  have hcfg : GGConfig 3 B Bs x L D J := hcfgR.1.1
  have hInn : GGInnerDiagAll 3 B Bs x L D J := hcfgR.1.2.2.1
  have hq : GGInnerDiagOnLabel GGLabQFour 3 Bs L :=
    hBase G 3 B Bs x L D J 𝒦 ⟨hcfgR, hns, ι, M, e, hpres, hTM, hbig⟩
  by_cases hok : GGInnerDiagOnLabel GGLabNbrOk 3 Bs K
  · obtain ⟨labA, hAΛ, hhasA, R, _, I, F, θ, hPA⟩ := largeEvenMarking_exists_hasLabel hok
    rcases hPA.1 with h2 | ⟨htag, hn1, -, hrk⟩
    · exact hK (largeEvenMarking_mono (fun lab' _ _ _ _ _ ⟨he, hP⟩ => ⟨by
        unfold GGLabQFour; rw [he]; exact h2, hP⟩)
        (ggInnerDiagOn_relabel hRig (hInn.2 y K hnb) hAΛ hhasA))
    · obtain ⟨t, r, n⟩ := labA
      simp only at htag hn1 hrk
      subst htag
      subst hn1
      exact hLin G B Bs x L D J 𝒦 hcfgR hns ι M e hpres (hT hTM) hq y K hnb r hrk hhasA
  · rcases nsNbr_fieldRow_narrow hRig hTCJ hTP hcfg hInn hq hnb hok with ⟨-, hlab⟩ | ⟨h7, -⟩
    · exact nsNbr_twE6_absurd hRig hTCJ hL hPJ hBig hRank hcfg hInn hq hnb hlab
    · omega

end NSJoin

end CFSG.StandardType

end

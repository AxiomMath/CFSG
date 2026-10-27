module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16Split
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixFooteMain

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.OddStandard.HigherRank.YamadaG23 (StrothSigma6 FooteMainL6)
open CFSG.ComponentClassification.StandardRecognition (ClassicalInvolutionTheoremModels)
open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE)

@[expose] def Q16Residual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (C : Cfg G M X 6),
    Nat.card ↥(Rc X) ≤ 2 → Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16 → Function.Surjective C.θ →
      (¬ ∃ ψ : Equiv.Perm (Fin 6) →* ↥M, ∀ σ, C.θ (ψ σ) = σ) → 2 ^ 9 ∣ Nat.card G →
        CFSG.Assembly.InCatalog G

theorem q16Residual_of_stroth
    (hStroth : StrothSigma6) (hFM : FooteMainL6) (hCIT : ClassicalInvolutionTheoremModels) :
    Q16Residual := by
  intro G _ _ M X C hR hQ hsurj _ _
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQdef
  have hWQ : blockU X = Q := Subgroup.eq_of_le_of_card_ge C.S.W_le_Q (by
    have := C.S.card_blockU_ge
    norm_num at this
    omega)
  have hE : IsE 4 ↥Q := by
    refine ⟨⟨IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext ?_), fun x _ => ?_⟩,
      by rw [hQ]; norm_num⟩
    · exact C.Q_comm hR _ (a : ↥Q).2 _ (b : ↥Q).2
    · have hx : (x : G) ∈ blockU X := by
        rw [hWQ]
        exact x.2
      have h2 := C.S.elemU.2 _ hx
      exact Subtype.ext (by simpa using h2)
  have hSyl := isSylowIn_of_centralizer_eq (CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' M)
    (C.centralizer_Q_eq hR)
  exact inCatalog_of_strothSigma6_footeMain hStroth hFM hCIT C.S.simple hE
    (C.isQuotIso_sym hR hsurj) hSyl

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

theorem inCatalog_of_card_Q_of_residual (hRes : Q16Residual) (C : Cfg G M X 6)
    (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) :
    CFSG.Assembly.InCatalog G := by
  obtain ⟨D⟩ := C.exists_piData (by norm_num) (by decide)
  rcases C.theta_alt_or_surjective with halt | hsurj
  · exact (D.q16_false_alt hR hQ halt).elim
  · by_cases hsplit : ∃ ψ : Equiv.Perm (Fin 6) →* ↥M, ∀ σ, C.θ (ψ σ) = σ
    · exact (D.q16_false_split hR hQ hsurj hsplit).elim
    · by_cases h9 : 2 ^ 9 ∣ Nat.card G
      · exact hRes G M X C hR hQ hsurj hsplit h9
      · exact (D.q16_false_of_not_dvd hR hQ hsurj h9).elim

end Cfg

end CFSG.RankThree.PartTwo.Sec19.SolEven

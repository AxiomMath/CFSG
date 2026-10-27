module

public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourDefs
public import CFSG.LocalAnalysis.StandardType.GGBstarLemmaCNoTwoSub
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Marking

variable {G : Type} [Group G] [Finite G]

theorem ggTwE6ThreeBstarRank_of_marking {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hL : commutator L = ⊤)
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift 3 4 R) (hOD : GGOutdiagOdd 3 R I) (hcov : GGTwE6CoverRank R)
    (hKG : GGTwE6SCFourNotTwoLocal R I) :
    3 ^ 5 ≤ Nat.card (ggGamma L hN).range := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hBeq, hm, hA4⟩ := hcfg.eq_bstar_of_card_range_lt hL θ hN hlift hlt
  subst hBeq
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨E, hE, hEL, hE6⟩ := hcfg.exists_elemAbelian_three_six hL θ hcov
  have hY : ∀ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer (L : Set G) →
      T₀ ≤ Subgroup.centralizer ({x} : Set G) → IsPGroup 2 T₀ → T₀ = ⊥ :=
    fun T₀ hTL hTx hT2 => twoSub_centralizer_eq_bot_of_rank hp hE hEL (by rw [hm]; exact hE6)
      hTL hTx hT2
  have hnc := UnitTB.exists_noncyclic_of_torusLift hp (by norm_num) hL θ hlift
  obtain ⟨V, hV1, hV2, hVB⟩ := hcfg.beta_twoLocal_of_noTwoSub hnc hL θ hN h3 hOD hY
  obtain ⟨hAE, hAI, hASC⟩ := ggGamma_range_hypsKG hcfg θ hN h3
  refine hKG L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
    (ggGamma L hN).range hAE hAI hA4 hASC ⟨V, hV1, hV2, ?_⟩
  rintro _ ⟨b, rfl⟩ l hl
  rw [← ggBeta_ggQuotHom L hN θ b l]
  exact hVB _ ⟨b, rfl⟩ _ hl

end Marking

section Certs


theorem ggTwE6CoverRank_recipe {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ∣ 2 ^ n + 1) :
    GGTwE6CoverRank (TwE6Delta.RecipeR K n) := fun L' _ _ ψ hs hk hc =>
  have h := ggTwE6ThreeCoverRankInput_holds K n hn hK hd L' ψ hs hk hc
  ⟨h.1, fun h3 => h.2 (Or.inr h3)⟩

theorem ggTwE6ThreeBstarRankInput_of_known (hKG : GGTwE6ThreeSCFourNotTwoLocalInput) :
    GGTwE6ThreeBstarRankInput := by
  intro G _ _ p B Bs x L D J hcfg hMB hN
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ GGOutdiagOdd 3 R I ∧ GGTwE6CoverRank R ∧
      GGTwE6SCFourNotTwoLocal R I)
    (fun lab hlab hs => largeEvenLabelAll_twE6Three_of hlab hs
      (P := fun R _ I => GGOutdiagOdd 3 R I ∧ GGTwE6CoverRank R ∧ GGTwE6SCFourNotTwoLocal R I)
      (fun K _ _ n hn hK hd => ⟨TwE6Delta.ggOutdiagOdd_twE6 hn hK 3,
        ggTwE6CoverRank_recipe hn hK hd, hKG K n hn hK hd⟩))
    (fun _ _ _ _ _ _ hP => hP.1) hMB
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, rfl, -⟩, -, hBsN, h3⟩, hlift, hOD, hcov, hKG'⟩ :=
    largeEvenRawDatum_exists hraw
  exact ggTwE6ThreeBstarRank_of_marking hcfg hL θ hBsN h3 hlift hOD hcov hKG'

end Certs

end CFSG.StandardType

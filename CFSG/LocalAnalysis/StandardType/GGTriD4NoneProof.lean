module

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Core

variable {G : Type} [Group G] [Finite G]

theorem ggTriD4_core (hsub : GGNbrSubcomponentInput) (hL : GGTriD4StdSubInput)
    (hE6 : GGTwE6LocalRankInput) {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G} {y : G}
    {K : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (h43 : GGL43 Bs x X)
    (hnbr : GGNbr 3 B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hKperf : commutator K = ⊤) {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : K ⧸ Subgroup.center K ≃* R) (hInn : GGTriD4InnDiag R I) (hSchur : GGTriD4Schur R)
    (hRank : GGTriD4AutRank R) (hComp : GGTriD4Components R)
    (hB1 : ∀ (b : G) (hb : b ∈ Bs ⊓ Subgroup.centralizer (X : Set G)),
      ggLAut K θ ⟨b, hN hb.1⟩ ∈ I)
    (hout : ∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∉ I) : False := by
  obtain ⟨hI, hBstar, hDJ⟩ := hcfg
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hBBs : B ≤ Bs := hBstar.1
  have hxBs : x ∈ Bs := hBBs hxB
  have hx3 : x ^ 3 = 1 := hBstar.2.1.2 x hxBs
  have hZ : Subgroup.center K = ⊥ := hSchur K hKperf θ
  have hσ3 : ggLAut K θ ⟨x, hN hxBs⟩ ^ 3 = 1 := ggLAut_pow_eq_one_of_pow K θ (hN hxBs) hx3
  have hIS : ∀ φ : MulAut R, φ ∈ I ↔ φ ∈ (MulAut.conj : R →* MulAut R).range := by
    intro φ
    rw [hInn, MonoidHom.mem_range]
    rfl
  have hσout : ggLAut K θ ⟨x, hN hxBs⟩ ∉ (MulAut.conj : R →* MulAut R).range := by
    intro hσS
    obtain ⟨b, hb, hbout⟩ := hout
    exact hbout ((hIS _).2 (ggLAut_mem_of_split K θ _ hN h43.2 inf_le_left hxBs
      (fun b hb => (hIS _).1 (hB1 b hb)) hσS b hb))
  have hJK : J ≤ K := hsub G 3 B x L D J hI hDJ y K hnbr
  have hJc := isComponentOf_inf_centralizer_of_ggNbr hS hDJ hnbr hJK
  obtain ⟨Q, e, hQ⟩ := exists_component_fixed_of_centerless θ hZ (hN hxBs) hJc
  obtain ⟨hQZ, hQm⟩ := hComp _ hσ3 hσout Q hQ
  have hJZ : Subgroup.center J = ⊥ := center_eq_bot_of_mulEquiv e hQZ
  have hJm := hQm.imp (largeEvenMarking_of_mulEquiv e) (largeEvenMarking_of_mulEquiv e)
  have hrank : LargeEvenTwoLocalRank 3 G ≤ 4 :=
    twoLocalRank_le_of_sHat hp hnbr.1 hKperf θ (hBBs.trans hN) (c := 3) hRank
  have hA2 := hJm.resolve_left (hL.1 G B x L D J hI hDJ)
  have hLm := hL.2 G B x L D J hI hDJ hrank hA2 hJZ
  have h5 := five_le_twoLocalRank_of_twE6 hE6 hLx hx1 hx3 hLm
  omega

end Core

theorem ggL44iiiTriD4NoneInput_of_known (hsub : GGNbrSubcomponentInput) (hKG : GGTriD4KnownInput)
    (hL : GGTriD4StdSubInput) (hE6 : GGTwE6LocalRankInput) : GGL44iiiTriD4NoneInput := by
  intro G _ _ p B Bs x L D J X B₂ hFC hM h43 h44 h44ii d hd hd1 y K hnbr hyd hN P hP
  have hKperf : commutator K = ⊤ := hP.1
  have hM1 := largeEvenMarking_and_labelAll_simple_imp (S := fun lab => lab.tag = .triD4)
    (P' := fun R _ I _ => GGTriD4InnDiag R I ∧ GGTriD4Schur R ∧ GGTriD4AutRank R ∧
      GGTriD4Components R)
    (fun lab hlab ht => largeEvenLabelAll_triD4_known hKG hlab ht) hP
  refine largeEvenMarking_mono ?_ hM1
  rintro lab R _ I F θ ⟨hPθ, hfacts⟩
  refine ⟨hPθ, ?_⟩
  rintro ⟨htag, hp3⟩ - hB1 hout
  subst hp3
  obtain ⟨hInn, hSchur, hRank, hComp⟩ := hfacts htag
  exact ggTriD4_core hsub hL hE6 hFC.1 h43 hnbr hN hKperf θ hInn hSchur hRank hComp hB1 hout

end CFSG.StandardType

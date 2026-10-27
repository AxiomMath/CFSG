module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoEndsL
public import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private theorem ggQ2_twD4_aut48_labelAll :
    LargeEvenLabelAll (⟨.twD, 4, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      GGTorusAutCardSC 3 R I 3 48 := by
  have h48 : (2 : ℕ) ^ 3 * Nat.factorial 3 = 48 := by norm_num
  have h : LargeEvenLabelAll (⟨.twD, 4, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      GGTorusAutCardSC 3 R I 3 (2 ^ 3 * Nat.factorial 3) :=
    ggTwOm_label (r := 3) (f := 1) (by norm_num) (by norm_num)
      (Or.inr ⟨by decide, by norm_num⟩)
  simpa only [h48] using h

private theorem ggQ2_twD4_scRank_labelAll :
    LargeEvenLabelAll (⟨.twD, 4, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      GGCenterPrime 3 R ∧ GGTorusSCRank 3 3 R I := by
  refine ggTwOm_label_of_rec (r := 3) (f := 1) (by norm_num)
    (P := fun R _ I => GGCenterPrime 3 R ∧ GGTorusSCRank 3 3 R I) ?_
  intro K _ _ _ hK b c hbc
  have h3 : 3 ∣ 2 ^ 1 - 1 ∨ (Odd 3 ∧ 3 ∣ 2 ^ 1 + 1) := Or.inr ⟨by decide, by norm_num⟩
  obtain ⟨hZ, -, hcp⟩ :=
    ggTwOm_facts_rec (K := K) (n := 1) (m := 3) (r := 3) hK hbc (by norm_num) rfl h3
  refine ⟨hcp, ?_⟩
  exact ggTorusSCRank_of_selfCentRankGE Nat.prime_three hZ (fun φ hφ _ => hφ) hcp
    (ggTwOm_scRank_rec (K := K) (n := 1) (m := 3) (r := 3) hK hbc (by norm_num) rfl h3)

private theorem ggQ2_twD4_inner_subset_labelAll :
    LargeEvenLabelAll (⟨.twD, 4, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  refine ggTwOm_label_of_rec (r := 3) (f := 1) (by norm_num)
    (P := fun R _ I => I ⊆ Set.range (MulAut.conj : R →* MulAut R)) ?_
  intro K _ _ _ hK b c hbc φ hφ
  exact hφ

private theorem ggQ2_twD4_all_labelAll :
    LargeEvenLabelAll (⟨.twD, 4, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      (GGTorusAutCardSC 3 R I 3 48 ∧ GGCenterPrime 3 R ∧ GGTorusSCRank 3 3 R I) ∧
        I ⊆ Set.range (MulAut.conj : R →* MulAut R) :=
  largeEvenLabelAll_and
    (largeEvenLabelAll_and ggQ2_twD4_aut48_labelAll ggQ2_twD4_scRank_labelAll)
    ggQ2_twD4_inner_subset_labelAll

private theorem ggQ2_twD4_innSet_subset_labelAll :
    LargeEvenLabelAll (⟨.twD, 4, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      LargeEvenInnSet R ⊆ I :=
  fun _ hQ => largeEvenRawDatum_inn_all hQ

private theorem ggQ2_twD4_strengthen_labelAll :
    LargeEvenLabelAll (⟨.twD, 4, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      ((GGTorusAutCardSC 3 R I 3 48 ∧ GGCenterPrime 3 R ∧ GGTorusSCRank 3 3 R I) ∧
        I ⊆ Set.range (MulAut.conj : R →* MulAut R)) ∧ LargeEvenInnSet R ⊆ I :=
  largeEvenLabelAll_and ggQ2_twD4_all_labelAll ggQ2_twD4_innSet_subset_labelAll

private theorem ggQ2_twD4_innerOn {G : Type} [Group G] {L Bs : Subgroup G} {R : Type}
    [Group R] {I : Set (MulAut R)} {θ : ↥L ⧸ Subgroup.center ↥L ≃* R}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hperf : commutator ↥L = ⊤)
    (hind : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * (l : G) * b) φ)
    (hInner : ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R)) :
    ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ := by
  intro b hb
  have hb' : b⁻¹ ∈ Bs := Bs.inv_mem hb
  obtain ⟨φ, hφI, hφ⟩ := hind b⁻¹ hb'
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center ↥L := by
    have hker_eq : ψ.ker = Subgroup.center ↥L := by
      dsimp [ψ]
      rw [← MonoidHom.comap_ker]
      rw [MonoidHom.ker_eq_bot (θ : ↥L ⧸ Subgroup.center ↥L →* R) (MulEquiv.injective θ)]
      rw [MonoidHom.comap_bot]
      exact QuotientGroup.ker_mk' _
    rw [hker_eq]
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hN hb
  let a : MulAut ↥L := L.normalizerMonoidHom ⟨b, hbN⟩
  have hcoe : ∀ l : ↥L, ((a l : ↥L) : G) = b * (l : G) * b⁻¹ := by
    intro l
    change ((L.normalizerMonoidHom ⟨b, hbN⟩ l : ↥L) : G) = b * (l : G) * b⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hind' : ∀ l : ↥L, φ (ψ l) = ψ (a l) := by
    intro l
    exact hφ l (a l) (by simpa using hcoe l)
  obtain ⟨k, hk⟩ := isInner_of_induces hψ hker hperf a (hInner φ hφI) hind'
  refine ⟨(k : G), k.2, fun l hl => ?_⟩
  have h := congrArg (fun f : MulAut ↥L => (((f ⟨l, hl⟩ : ↥L) : G))) hk
  simpa [hcoe, MulAut.conj_apply] using h

theorem ggQ2_twD4_automizer_ge48
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hlab : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hcard : Nat.card ↥Bs = 3 ^ 4)
    (hmk : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    48 ≤ Nat.card ↥(ggAutomizer L Bs) := by
  have hInnOn : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hlab
  obtain ⟨lab₁, hlab₁, hP₁, hhas₁⟩ := FrameRoute.ggFrameQTwo_exists_hasLabel hmk
  have hlab₁_eq : lab₁ = ⟨.twD, 4, 1⟩ := by
    obtain ⟨t, r, n⟩ := lab₁
    obtain ⟨h1, h2, h3⟩ := hP₁
    subst h1
    subst h2
    subst h3
    rfl
  have hhas : GGHasLabel (⟨.twD, 4, 1⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) :=
    hlab₁_eq ▸ hhas₁
  have hlabTwD : LargeEvenInLambda2 (⟨.twD, 4, 1⟩ : LargeEvenLabel) := by
    norm_num [LargeEvenInLambda2]
  have hLperf : commutator ↥L = ⊤ := hmk.1
  have hRelabel := ggInnerDiagOn_relabel ggLabelRigidInput_holds hInnOn hlabTwD hhas
  have hStrengthened := largeEvenMarking_and_labelAll
    (S := fun lab => lab = ⟨.twD, 4, 1⟩)
    (fun _ _ hlab => by cases hlab; exact ggQ2_twD4_strengthen_labelAll)
    (fun _ _ _ _ _ _ hP => hP.1)
    hRelabel
  obtain ⟨_, _, _, R, instR, I, F, θ, hPP'⟩ := largeEvenMarking_exists_hasLabel hStrengthened
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hPP'.1.2.1
  have hInd : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * (l : G) * b) φ := hPP'.1.2.2
  have hAut : GGTorusAutCardSC 3 R I 3 48 := hPP'.2.1.1.1
  have hcp : GGCenterPrime 3 R := hPP'.2.1.1.2.1
  have hRank : GGTorusSCRank 3 3 R I := hPP'.2.1.1.2.2
  have hInnerSub : I ⊆ Set.range (MulAut.conj : R →* MulAut R) := hPP'.2.1.2
  have hInnI : LargeEvenInnSet R ⊆ I := hPP'.2.2
  have hInn : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ :=
    ggQ2_twD4_innerOn hN hLperf hInd hInnerSub
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hsurj : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center ↥L := by
    have hker_eq : ψ.ker = Subgroup.center ↥L := by
      dsimp [ψ]
      rw [← MonoidHom.comap_ker]
      rw [MonoidHom.ker_eq_bot (θ : ↥L ⧸ Subgroup.center ↥L →* R) (MulEquiv.injective θ)]
      rw [MonoidHom.comap_bot]
      exact QuotientGroup.ker_mk' _
    rw [hker_eq]
  have hnotdvd : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L) := hcp ↥L ψ hsurj hker hLperf
  have hZ : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) := by
    intro g hg
    rw [Nat.prime_three.coprime_iff_not_dvd]
    intro h3
    exact hnotdvd (h3.trans (Subgroup.orderOf_dvd_natCard _ hg))
  have hcardAut := ggAutomizer_card_eq_of_torusSCRank (J := L) (N := 48) θ hInnI hRank hAut
    hcfg.2.1.2.1 hcfg.2.1.2.2.2 hLperf hZ hInn
  exact hcardAut.ge

end CFSG.StandardType

end

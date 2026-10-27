module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegPCyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbr_hyperplane_not_centralizing {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K) {B₀ : Subgroup G} (hB₀ : B₀ ≤ Bs)
    (hcard : Nat.card B₀ * p = Nat.card Bs) :
    ∃ b ∈ B₀, ∃ k ∈ K, b * k * b⁻¹ ≠ k := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hβ : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  obtain ⟨hBmax, hyB, -, -, -, hker⟩ := hK.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hBmax.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  by_contra hcon
  push Not at hcon
  have hle : B₀ ⊓ B ≤ Subgroup.zpowers y := by
    intro b hb
    have hcent : b ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      calc k * b = b * k * b⁻¹ * b := by rw [hcon b hb.1 k hk]
        _ = b * k := by group
    refine (hker b).1 ⟨hb.2, Subgroup.centralizer_le_normalizer _ hcent, ?_⟩
    refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    have h2 : g₂ ∈ Subgroup.centralizer (K : Set G) := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
      exact Subgroup.zpow_mem _ hcent n
    rw [commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 h2 g₁ hg₁)]
    exact Subgroup.one_mem _
  have hyp : Nat.card (Subgroup.zpowers y) ≤ p := by
    have hy : y ^ p = 1 := hBmax.1.2 y hyB
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hy)
  have hcard1 : Nat.card (B₀ ⊓ B : Subgroup G) ≤ p := (Subgroup.card_le_of_le hle).trans hyp
  have h1 : B₀.relIndex B * Nat.card (B₀ ⊓ B : Subgroup G) = Nat.card B :=
    Subgroup.relIndex_mul_card B₀ B
  have h2 : B₀.relIndex Bs * Nat.card (B₀ ⊓ Bs : Subgroup G) = Nat.card Bs :=
    Subgroup.relIndex_mul_card B₀ Bs
  rw [inf_eq_left.2 hB₀] at h2
  have hB₀pos : 0 < Nat.card B₀ := Nat.card_pos
  have hrel : B₀.relIndex Bs = p := by
    apply Nat.eq_of_mul_eq_mul_left hB₀pos
    calc Nat.card B₀ * B₀.relIndex Bs = B₀.relIndex Bs * Nat.card B₀ := mul_comm _ _
      _ = Nat.card Bs := h2
      _ = Nat.card B₀ * p := hcard.symm
  have hrelB : B₀.relIndex B ≤ p := by
    have := Subgroup.relIndex_le_of_le_right (H := B₀) hBBs (by rw [hrel]; exact hp.ne_zero)
    rwa [hrel] at this
  have hpow : p ^ 4 ≤ Nat.card B := by
    rw [hBcard]
    exact Nat.pow_le_pow_right hp.pos hβ
  have hBle : Nat.card B ≤ p * p := by
    rw [← h1]
    exact Nat.mul_le_mul hrelB hcard1
  have hp2 : 2 ≤ p := hp.two_le
  have h3 : p ^ 4 ≤ p * p := hpow.trans hBle
  have h4 : 4 ≤ p * p := by nlinarith [hp2]
  have h5 : p ^ 4 = p * p * (p * p) := by ring
  nlinarith [h3, h4, h5]

@[expose] def KGLangTorusNTCont (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
    ∀ A : Subgroup (MulAut K), IsElemAbelian p A →
      (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
      (∃ α ∈ A, α ≠ 1 ∧ kgInducedAut θ α ∈ I) →
      ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I → KGLangTorusConcl p θ I A α₀

@[expose] def KGLangTorusNTOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab (KGLangTorusNTCont p)

theorem kgLangTorusNTCont_of_cont {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (h : KGLangTorusCont p R I F) : KGLangTorusNTCont p R I F :=
  fun K _ _ θ hK A hA hAI _ α₀ hα₀ hα₀I => h K θ hK A hA hAI α₀ hα₀ hα₀I

theorem kgLangTorusNTOn_of_on {S : ℕ → LargeEvenLabel → Prop} (h : KGLangTorusOn S) :
    KGLangTorusNTOn S :=
  fun p lab hp hp2 hlab hS Q hQ =>
    largeEvenRawDatum_mono (fun _ _ _ _ h' => ⟨h'.1, kgLangTorusNTCont_of_cont h'.2⟩)
      (h p lab hp hp2 hlab hS Q hQ)

theorem KGLangTorusNTOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S' p lab → S p lab) (h : KGLangTorusNTOn S) : KGLangTorusNTOn S' :=
  fun p lab hp hp2 hlab hS' => h p lab hp hp2 hlab (hS p lab hS')

theorem KGLangTorusNTOn.or {S S' : ℕ → LargeEvenLabel → Prop} (h : KGLangTorusNTOn S)
    (h' : KGLangTorusNTOn S') : KGLangTorusNTOn fun p lab => S p lab ∨ S' p lab := by
  rintro p lab hp hp2 hlab (hS | hS)
  · exact h p lab hp hp2 hlab hS
  · exact h' p lab hp hp2 hlab hS

theorem ggMarkingAll_kgLangTorusNT {S : ℕ → LargeEvenLabel → Prop} (h : KGLangTorusNTOn S)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (K : Type*) [Group K] :
    GGMarkingAll (K := K) fun lab R _ I F _ => S p lab → KGLangTorusNTCont p R I F :=
  ggRegKG_markingAll_guard (fun lab hlab hs => h p lab hp hp2 hlab hs) K

theorem ggNbrLangRegCore_of_hyperplane_nt {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hK : commutator ↥K = ⊤)
    {R : Type} [Group R] {I F : Set (MulAut R)} (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hinn : ∀ r : R, MulAut.conj r ∈ I) (hLT : KGLangTorusNTCont p R I F)
    (hall : ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
      ggLAut K θ ⟨b, hN hb⟩ = u * f)
    (b₀ : G) (hb₀ : b₀ ∈ Bs) (hb₀I : ggLAut K θ ⟨b₀, hN hb₀⟩ ∉ I)
    {B₀ : Subgroup G} (hB₀ : B₀ ≤ Bs)
    (hmem : ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hnc : ∃ b ∈ B₀, ∃ k ∈ K, b * k * b⁻¹ ≠ k) :
    ∃ T : Subgroup G, T ≤ Subgroup.centralizer (B₀ : Set G) ∧
      (∀ a ∈ T, ∀ c ∈ T, a * c = c * a) ∧
      b₀ ∈ Subgroup.normalizer (T : Set G) ∧
      (∀ t ∈ T, b₀ * t * b₀⁻¹ = t → ∃ s ∈ T,
        t = ((List.range p).map fun i => b₀ ^ i * s * (b₀ ^ i)⁻¹).prod) ∧
      ∃ e ∈ B₀ ⊓ T, e ≠ 1 := by
  obtain ⟨b, hb, k, hk, hbk⟩ := hnc
  have hbBs : b ∈ Bs := hB₀ hb
  refine ggNbrLangRegCore_of_data hSC hN θ hinn b₀ hb₀ hB₀ hmem
    (hLT ↥K θ hK (ggBsAut hN).range (ggBsAut_range_isElemAbelian hBs hN)
      (by rintro _ ⟨b, rfl⟩; exact hall b b.2) ?_ (ggBsAut hN ⟨b₀, hb₀⟩) ⟨_, rfl⟩ hb₀I)
  refine ⟨ggBsAut hN ⟨b, hbBs⟩, ⟨_, rfl⟩, fun h1 => hbk ?_, (hmem b hbBs).1 hb⟩
  exact congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : G)) h1

theorem ggNbrLangTorusAxisOn_of_split_nt_of_inputs (hraw : GGRawInnFieldInput)
    (hnorm : GGInndiagNormalInput) {S S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → S₁ p lab ∨ S₂ p lab) (hpc : GGRawPCyclicOn S₁)
    (hcyc : KGRawFieldCyclicOn S₂) (hLT : KGLangTorusNTOn S) : GGNbrLangTorusAxisOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBstar : GGBstar p B Bs := hcfg.2.1
  refine NbrLangTypeA.ggMarkingAll_mono ?_
    (ggRegKG_markingAll_and (ggRegKG_markingAll_and (ggRegKG_markingAll_and
      (ggRegKG_markingAll_and (ggRegKG_markingAll_and (ggRegKG_markingAll_perfect_simple ↥K)
        (ggRegKG_markingAll_of_labelAll fun lab hlab => hraw p hp hp2 lab hlab))
      (ggRegKG_markingAll_of_labelAll_simple (P' := fun R _ I _ => GGInndiagNormal R I) hnorm))
      (ggRegKG_markingAll_guard (S := S₁) (P := GGRawPCyclic p) (p := p)
        (fun lab hlab hs => hpc p hp hp2 lab hlab hs) ↥K))
      (ggMarkingAll_kgRawFieldCyclic (S := S₂) hcyc hp hp2 ↥K))
      (ggMarkingAll_kgLangTorusNT hLT hp hp2 ↥K))
  rintro lab R _ I F θ ⟨⟨⟨⟨⟨⟨hX, hs, hna⟩, hrawθ⟩, hnormθ⟩, hpcθ⟩, hcycθ⟩, hLTθ⟩ hSl hall b₀ hb₀ hb₀I
  rcases hS p lab hSl with h₁ | h₂
  · obtain ⟨B₀, hB₀, hcard, hb₀', hmem⟩ := exists_index_prime_of_raw_pcyclic hp hBstar.2.1 hs hna
      (hpcθ h₁) ((ggLAut K θ).comp (Subgroup.inclusion hN)) hb₀ hb₀I
    exact ⟨B₀, hB₀, hcard, hb₀', fun b hb h => (hmem b hb).2 h,
      ggNbrLangRegCore_of_hyperplane_nt hBstar.2.1 hBstar.2.2.2 hN hX θ (hrawθ hs hna).2.2.1
        (hLTθ hSl) hall b₀ hb₀ hb₀I hB₀ hmem
        (ggNbr_hyperplane_not_centralizing hcfg hK hB₀ hcard)⟩
  · obtain ⟨B₀, hB₀, hcard, hb₀', hmem⟩ := exists_index_prime_of_raw_aut hp hBstar.2.1 hs hna
      hrawθ hnormθ (hcycθ h₂) ((ggLAut K θ).comp (Subgroup.inclusion hN)) (fun b => hall b b.2)
      hb₀ hb₀I
    exact ⟨B₀, hB₀, hcard, hb₀', fun b hb h => (hmem b hb).2 h,
      ggNbrLangRegCore_of_hyperplane_nt hBstar.2.1 hBstar.2.2.2 hN hX θ (hrawθ hs hna).2.2.1
        (hLTθ hSl) hall b₀ hb₀ hb₀I hB₀ hmem
        (ggNbr_hyperplane_not_centralizing hcfg hK hB₀ hcard)⟩

theorem ggNbrLangTorusAxisOn_of_kgNT_of_inputs (hraw : GGRawInnFieldInput)
    (hnorm : GGInndiagNormalInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    {S : ℕ → LargeEvenLabel → Prop} (hLT : KGLangTorusNTOn S) : GGNbrLangTorusAxisOn S :=
  ggNbrLangTorusAxisOn_of_split_nt_of_inputs hraw hnorm (S₁ := GGNotD4Three)
    (S₂ := fun p lab => ¬ GGNotD4Three p lab) (fun _ _ _ => em _) hpc kgRawFieldCyclicOn_D4Three
    hLT

@[expose] def GGNbrLangRest12RegSplit : Prop :=
  KGLangTorusNTOn GGNbrLangRegLabel ∧ GGNbrLangAxisOn GGNbrLangRest12NonRegLabel

theorem ggNbrLangAxisOn_rest12NonReg_of_rest12 (h : GGNbrLangAxisOn GGNbrLangRest12Label) :
    GGNbrLangAxisOn GGNbrLangRest12NonRegLabel :=
  GGNbrLangAxisOn.mono (fun _ _ hl => hl.1) h

section Certified


theorem ggNbrLangTorusAxisOn_of_kgNT (hpc : GGRawPCyclicOn GGNotD4Three)
    {S : ℕ → LargeEvenLabel → Prop} (hLT : KGLangTorusNTOn S) : GGNbrLangTorusAxisOn S :=
  ggNbrLangTorusAxisOn_of_kgNT_of_inputs ggRawInnFieldInput_holds ggInndiagNormalInput_holds hpc
    hLT

theorem ggNbrLangAxisOn_rest12_of_regNT (hpc : GGRawPCyclicOn GGNotD4Three)
    (hLT : KGLangTorusNTOn GGNbrLangRegLabel)
    (hrest : GGNbrLangAxisOn GGNbrLangRest12NonRegLabel) :
    GGNbrLangAxisOn GGNbrLangRest12Label := by
  refine ((ggNbrLangAxisOn_of_torusOn (ggNbrLangTorusAxisOn_of_kgNT hpc hLT)).or hrest).mono ?_
  intro p lab hS
  by_cases h : GGNbrLangRegLabel p lab
  · exact Or.inl h
  · exact Or.inr ⟨hS, h⟩

end Certified

end CFSG.StandardType

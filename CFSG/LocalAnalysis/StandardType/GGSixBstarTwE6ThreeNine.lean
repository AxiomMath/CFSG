module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAut
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAutTwoLocal
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAutInduces
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProof
public import CFSG.LocalAnalysis.StandardType.GGSixBstarModelFrameTransfer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderNine
public import CFSG.SignalizerFunctorTheorem.Solvable.Bender.Basic
public import CFSG.SignalizerFunctorTheorem.Assembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffTwE6Three

open CFSG.Open in
theorem le_of_centralizer_le {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D M T : Subgroup G} (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2)
    (hC : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ M)
    (hT : IsPGroup 2 T) (hDT : D ≤ Subgroup.normalizer (T : Set G)) : T ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime p (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hle : p ≤ Nat.card D := by
    rw [hDc]
    exact Nat.le_self_pow two_ne_zero p
  rw [← CFSG.SignalizerFunctorTheorem.Solvable.Bender.iSup_hyperplanes_inf_centralizer hp hD hle
    hDT hcop]
  refine iSup₂_le fun B hB => ?_
  have hBc : Nat.card B = p := by
    have h := hB.2
    rw [hDc, pow_two] at h
    exact (Nat.eq_of_mul_eq_mul_left hp.pos h).symm
  obtain ⟨d, hdB, hd1⟩ : ∃ d ∈ B, d ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr h
    rw [hbot, Subgroup.card_bot] at hBc
    exact hp.one_lt.ne hBc
  intro t ht
  refine hC d (hB.1 hdB) hd1 ?_
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdB) ht.2

section Frame

theorem ggSixTwE6ThreeBRankFour (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (hP : GGExcTwE6ThreeLabel t n f p)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) : 3 ^ 4 ≤ Nat.card B := by
  obtain ⟨rfl, rfl, -⟩ := hP
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hctx.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hctx.beta.2.2.2
  rw [hBc]
  exact Nat.pow_le_pow_right (by norm_num) h4

@[expose] def GGSixBstarE6ThreeFrameNineOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ →
    (∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J) →
    GGBstarModelFrame (TableBExc.E6Three.adPerm .E6 3) p (ggM p B x L D J) Bs ∨
      GGBstarModelFrame NoOffRest.hypPerm p (ggM p B x L D J) Bs

theorem ggSixBstarNoOffenderNineOn_of_e6ThreeFrameNineOn {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixBstarE6ThreeFrameNineOn P) (hP3 : ∀ t n f p, P t n f p → p = 3) :
    GGSixBstarNoOffenderNineOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC h9
  obtain rfl := hP3 t n f p hP
  rcases h G 3 B Bs x L D J t n f ψ hP hctx hC h9 with hF | hF
  · exact hF.noOffender (NoOffRest.adPerm_injective (by norm_num))
      NoOffRest.actNoOffender_adPerm_E6
  · exact hF.noOffender NoOffRest.hypPerm_injective NoOffRest.actNoOffender_hypPerm_E6

end Frame

section Inputs

@[expose] def GGTwE6ThreeToralCentInput : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → 3 ∣ 2 ^ f + 1 →
    ∀ {X : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))}, IsElemAbelian 3 X → X ≤ LayerSixE.twInndiagAut f → Nat.card X = 3 ^ 4 →
      (∃ U : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))), U ≠ ⊥ ∧ IsPGroup 2 U ∧ X ≤ Subgroup.normalizer (U : Set _)) →
      ∃ g ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f)) →*
          MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range,
        g ^ 3 = 1 ∧ g ∉ X ∧ ∀ y ∈ X, g * y = y * g

@[expose] def GGTwE6ThreeSCShapeInput : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → 3 ∣ 2 ^ f + 1 →
    ∀ {M' S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))}, S ≤ M' →
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range
          ≤ M' →
      IsElemAbelian 3 S → S ≤ LayerSixE.twInndiagAut f → 3 ^ 5 ≤ Nat.card S →
      (∀ g ∈ M', (∀ s ∈ S, g * s = s * g) → g ^ 3 = 1 → g ∈ S) →
      GGBstarModelFrame (TableBExc.E6Three.adPerm .E6 3) 3 M' S ∨
        GGBstarModelFrame NoOffRest.hypPerm 3 M' S

@[expose] def GGSixTwE6ThreeBstarRankNineInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), GGExcTwE6ThreeLabel t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ →
    (∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J) → 3 ^ 5 ≤ Nat.card Bs

theorem ggSixTwE6ThreeBstarRankNineInput_of_toralCent (hKG : GGTwE6ThreeToralCentInput) :
    GGSixTwE6ThreeBstarRankNineInput := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC h9iii
  by_contra hlt
  push Not at hlt
  have h4B : 3 ^ 4 ≤ Nat.card B := ggSixTwE6ThreeBRankFour G p B Bs x L D J t n f ψ hP hctx
  obtain ⟨rfl, rfl, h3f⟩ := hP
  have hBsle : B ≤ Bs := hctx.2.1.1
  have hBs : IsElemAbelian 3 Bs := hctx.2.1.2.1
  have hBsEq : Bs = B := by
    obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hBs).exists_card_eq
    have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have hBB : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBsle
    have hk5 : k < 5 := by
      have : 3 ^ k < 3 ^ 5 := hk ▸ hlt
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    have hr4 : 4 ≤ LargeEvenTwoLocalRank 3 G := by
      have : 3 ^ 4 ≤ 3 ^ LargeEvenTwoLocalRank 3 G := hBc ▸ h4B
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    have hrk : LargeEvenTwoLocalRank 3 G ≤ k := by
      have : 3 ^ LargeEvenTwoLocalRank 3 G ≤ 3 ^ k := by rw [← hBc, ← hk]; exact hBB
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    have hk4 : k = LargeEvenTwoLocalRank 3 G := by omega
    exact (Subgroup.eq_of_le_of_card_ge hBsle (by rw [hBc, hk, hk4])).symm
  have hcardBs : Nat.card Bs = 3 ^ 4 := by
    have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have hr4 : LargeEvenTwoLocalRank 3 G = 4 := by
      have h1 : 3 ^ 4 ≤ 3 ^ LargeEvenTwoLocalRank 3 G := hBc ▸ h4B
      have h2 : 3 ^ LargeEvenTwoLocalRank 3 G < 3 ^ 5 := hBc ▸ (hBsEq ▸ hlt)
      have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
      omega
    rw [hBsEq, hBc, hr4]
  obtain ⟨T, hT1, hT2, hBT⟩ := hctx.1.2.2.2.2.2.2.1.1.2.2
  obtain ⟨hDB, hDel, hDcard, -⟩ := hctx.2.2.1.1
  have hTM : T ≤ ggM 3 B x L D J :=
    le_of_centralizer_le Nat.prime_three (by norm_num) hDel hDcard h9iii hT2 (hDB.trans hBT)
  have hBsT : Bs ≤ Subgroup.normalizer (T : Set G) := hBsEq ▸ hBT
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  obtain ⟨π, hπ, hπker, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ.ker ≤ π.ker := hπker ▸ hker
  have hkerEq : ψ.ker = π.ker := by
    refine le_antisymm hkπ ?_
    rw [hπker]
    intro z hz
    rw [MonoidHom.mem_ker]
    have h : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subgroup.mem_center_iff.mp hz y)
    rw [hCψ, Subgroup.mem_bot] at h
    exact h
  obtain ⟨χ, hχinj, hχrange, hval⟩ :=
    NormalizerAut.exists_injective_factor_of_surjective hπ hkerEq
  have hχG0 : χ.range = ggG0 3 B x L D J := hχrange.trans hrange
  have hCχ : Subgroup.centralizer (χ.range : Set G) = ⊥ := by rw [hχrange]; exact hCψ
  have hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := hctx.2.2.2.2.2.2.1.1
  have hBsM : Bs ≤ ggM 3 B x L D J := hBsN
  have hBsdiag : ∀ b ∈ Bs, GGPsiInnerDiag (ggU .twistedE6 n f).D ψ b := hctx.2.2.2.2.2.2.1.2
  have hMeq : (χ.range : Set G) = (ggG0 3 B x L D J : Set G) := by rw [hχG0]
  have hM : ggM 3 B x L D J ≤ Subgroup.normalizer (χ.range : Set G) := by rw [hMeq]
  have hχM : χ.range ≤ ggM 3 B x L D J := by
    rw [hχG0]
    exact Subgroup.le_normalizer
  set Φ := NormalizerAut.normAutOn χ hχinj hM with hΦ
  have hΦinj : Function.Injective Φ := NormalizerAut.normAutOn_injective χ hχinj hM hCχ
  set S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))) := (Bs.subgroupOf (ggM 3 B x L D J)).map Φ with hS
  have hcardS : Nat.card S = Nat.card Bs := by
    rw [hS, Subgroup.card_map_of_injective (K := Bs.subgroupOf (ggM 3 B x L D J)) hΦinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsM).toEquiv
  have hSI : S ≤ LayerSixE.twInndiagAut f := by
    rintro _ ⟨⟨b, hbM⟩, hb, rfl⟩
    have hbBs : b ∈ Bs := hb
    have hbN : b ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hBsN hbBs
    obtain ⟨α, hαD, hα⟩ :=
      LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hbN (hBsdiag b hbBs)
    have hind := NormalizerAut.ggInduces_normAutOn (π := π) (ψ := ψ) χ hχinj hval hM ⟨b, hbM⟩
    have huniq := LayerSixE.GGInduces.unique hπ hbN hind hα
    rw [huniq]
    exact hαD
  set U : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))) := (T.subgroupOf (ggM 3 B x L D J)).map Φ with hU
  have hU1 : U ≠ ⊥ := by
    obtain ⟨⟨t0, ht0⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT1
    rw [Ne, Subgroup.eq_bot_iff_forall]
    push Not
    refine ⟨Φ ⟨t0, hTM ht0⟩, ⟨⟨t0, hTM ht0⟩, ht0, rfl⟩, ?_⟩
    intro h
    apply ht1
    have h3 : t0 = 1 := congrArg Subtype.val (hΦinj (h.trans (map_one Φ).symm))
    exact Subtype.ext h3
  have hU2 : IsPGroup 2 U := by
    have : IsPGroup 2 (T.subgroupOf (ggM 3 B x L D J)) :=
      hT2.comap_of_injective _ (Subgroup.subtype_injective _)
    exact this.map Φ
  have key : ∀ (m : ggM 3 B x L D J), (m : G) ∈ Bs →
      ∀ t : ggM 3 B x L D J, t ∈ T.subgroupOf (ggM 3 B x L D J) ↔
        m * t * m⁻¹ ∈ T.subgroupOf (ggM 3 B x L D J) := by
    intro m hm t
    simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp (hBsT hm) (t : G)
  have hSU : S ≤ Subgroup.normalizer (U : Set _) := by
    rintro _ ⟨m, hm, rfl⟩
    have hmBs : (m : G) ∈ Bs := hm
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨_, (key m hmBs τ).mp hτ, ?_⟩
      simp [map_mul, map_inv]
    · rintro ⟨τ', hτ', hτ'u⟩
      refine ⟨m⁻¹ * τ' * m, ?_, ?_⟩
      · apply (key m hmBs (m⁻¹ * τ' * m)).mpr
        have e : m * (m⁻¹ * τ' * m) * m⁻¹ = τ' := by group
        rw [e]
        exact hτ'
      · have h2 : Φ m * u * (Φ m)⁻¹ = Φ τ' := hτ'u.symm
        simp only [map_mul, map_inv]
        rw [← h2]
        group
  have hSel : IsElemAbelian 3 S :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hBs _) Φ
  obtain ⟨g, hg, hg3, hgS, hgc⟩ := hKG hf h3f hSel hSI (hcardS.trans hcardBs) ⟨U, hU1, hU2, hSU⟩
  obtain ⟨m, rfl⟩ := NormalizerAut.conj_range_le_range_normAutOn χ hχinj hM hχM hg
  apply hgS
  have hm3 : m ^ 3 = 1 := hΦinj (by rw [map_pow, hg3, map_one])
  have hmc : (m : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := hgc (Φ ⟨h, hBsM hh⟩) ⟨⟨h, hBsM hh⟩, hh, rfl⟩
    have h2 : (⟨h, hBsM hh⟩ : ggM 3 B x L D J) * m = m * ⟨h, hBsM hh⟩ :=
      hΦinj (by rw [map_mul, map_mul]; exact h1.symm)
    exact congrArg Subtype.val h2
  have hm3' : (m : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hm3
    simpa using this
  have hmBs : (m : G) ∈ Bs := hctx.2.1.2.2.2 _ hmc hm3'
  exact ⟨m, hmBs, rfl⟩

theorem ggSixBstarE6ThreeFrameNineOn_twE6 (hrank : GGSixTwE6ThreeBstarRankNineInput)
    (hshape : GGTwE6ThreeSCShapeInput) : GGSixBstarE6ThreeFrameNineOn GGExcTwE6ThreeLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC h9iii
  have h5Bs : 3 ^ 5 ≤ Nat.card Bs := hrank G p B Bs x L D J t n f ψ hP hctx hC h9iii
  obtain ⟨rfl, rfl, h3f⟩ := hP
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  obtain ⟨π, hπ, hπker, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ.ker ≤ π.ker := hπker ▸ hker
  have hkerEq : ψ.ker = π.ker := by
    refine le_antisymm hkπ ?_
    rw [hπker]
    intro z hz
    rw [MonoidHom.mem_ker]
    have h : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subgroup.mem_center_iff.mp hz y)
    rw [hCψ, Subgroup.mem_bot] at h
    exact h
  obtain ⟨χ, hχinj, hχrange, hval⟩ :=
    NormalizerAut.exists_injective_factor_of_surjective hπ hkerEq
  have hχG0 : χ.range = ggG0 3 B x L D J := hχrange.trans hrange
  have hCχ : Subgroup.centralizer (χ.range : Set G) = ⊥ := by rw [hχrange]; exact hCψ
  have hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := hctx.2.2.2.2.2.2.1.1
  have hBsM : Bs ≤ ggM 3 B x L D J := hBsN
  have hBsdiag : ∀ b ∈ Bs, GGPsiInnerDiag (ggU .twistedE6 n f).D ψ b := hctx.2.2.2.2.2.2.1.2
  have hBs : IsElemAbelian 3 Bs := hctx.2.1.2.1
  have hMeq : (χ.range : Set G) = (ggG0 3 B x L D J : Set G) := by rw [hχG0]
  have hM : ggM 3 B x L D J ≤ Subgroup.normalizer (χ.range : Set G) := by rw [hMeq]
  have hχM : χ.range ≤ ggM 3 B x L D J := by
    rw [hχG0]
    exact Subgroup.le_normalizer
  set Φ := NormalizerAut.normAutOn χ hχinj hM with hΦ
  have hΦinj : Function.Injective Φ := NormalizerAut.normAutOn_injective χ hχinj hM hCχ
  set S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))) := (Bs.subgroupOf (ggM 3 B x L D J)).map Φ with hS
  have hcardS : Nat.card S = Nat.card Bs := by
    rw [hS, Subgroup.card_map_of_injective (K := Bs.subgroupOf (ggM 3 B x L D J)) hΦinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsM).toEquiv
  have hSI : S ≤ LayerSixE.twInndiagAut f := by
    rintro _ ⟨⟨b, hbM⟩, hb, rfl⟩
    have hbBs : b ∈ Bs := hb
    have hbN : b ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hBsN hbBs
    obtain ⟨α, hαD, hα⟩ :=
      LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hbN (hBsdiag b hbBs)
    have hind := NormalizerAut.ggInduces_normAutOn (π := π) (ψ := ψ) χ hχinj hval hM ⟨b, hbM⟩
    have huniq := LayerSixE.GGInduces.unique hπ hbN hind hα
    rw [huniq]
    exact hαD
  have hSC : ∀ g ∈ Φ.range, (∀ s ∈ S, g * s = s * g) → g ^ 3 = 1 → g ∈ S := by
    rintro _ ⟨m, rfl⟩ hgc hg3
    have hm3 : m ^ 3 = 1 := hΦinj (by rw [map_pow, hg3, map_one])
    have hmc : (m : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h1 := hgc (Φ ⟨h, hBsM hh⟩) ⟨⟨h, hBsM hh⟩, hh, rfl⟩
      have h2 : (⟨h, hBsM hh⟩ : ggM 3 B x L D J) * m = m * ⟨h, hBsM hh⟩ :=
        hΦinj (by rw [map_mul, map_mul]; exact h1.symm)
      exact congrArg Subtype.val h2
    have hm3' : (m : G) ^ 3 = 1 := by
      have := congrArg Subtype.val hm3
      simpa using this
    exact ⟨m, hctx.2.1.2.2.2 _ hmc hm3', rfl⟩
  have hF := hshape hf h3f (M' := Φ.range) (S := S) (Subgroup.map_le_range Φ _)
    (NormalizerAut.conj_range_le_range_normAutOn χ hχinj hM hχM)
    (CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hBs _) Φ) hSI
    (hcardS ▸ h5Bs) hSC
  rcases hF with hF | hF
  · exact Or.inl (GGBstarModelFrame.of_injective_hom hBsM Φ hΦinj hF)
  · exact Or.inr (GGBstarModelFrame.of_injective_hom hBsM Φ hΦinj hF)

theorem ggSixBstarNoOffenderNineOn_twE6 (hKG : GGTwE6ThreeToralCentInput)
    (hshape : GGTwE6ThreeSCShapeInput) : GGSixBstarNoOffenderNineOn GGExcTwE6ThreeLabel :=
  ggSixBstarNoOffenderNineOn_of_e6ThreeFrameNineOn
    (ggSixBstarE6ThreeFrameNineOn_twE6 (ggSixTwE6ThreeBstarRankNineInput_of_toralCent hKG) hshape)
    fun _ _ _ _ h => h.2.1

end Inputs

end NoOffTwE6Three

end CFSG.StandardType

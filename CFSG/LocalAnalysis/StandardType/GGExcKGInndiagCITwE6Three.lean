module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLangTorus
public import CFSG.LocalAnalysis.StandardType.GGExcKGInndiagCIE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesIsogenyTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAutInduces
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeToral
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (IsElemAbelian)
open TableBExc.E6Three

private theorem e6tw_fixCard_one {p : ℕ} (hp : p.Prime) (R : ℕ) :
    GGFixCard p (1 : Equiv.Perm (Fin R)) = p ^ R := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  unfold GGFixCard
  have h : Nat.card {z : Fin R → ZMod p // ∀ i, z ((1 : Equiv.Perm (Fin R)) i) = z i} =
      Nat.card (Fin R → ZMod p) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun z i => rfl)
  rw [h, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem e6tw_three_dvd_card {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) :
    3 ∣ Nat.card (GaloisField 2 (2 * f)) - 1 := by
  have hcard : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    generalize 2 ^ f = m at h1 ⊢
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
    omega
  rw [hcard, h]
  exact Dvd.dvd.mul_right h3 _

private theorem e6tw_mem_normalizer {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (c : G) : c ∈ Subgroup.normalizer (N : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hN.conj_mem h hh c, fun hh => ?_⟩
  have := hN.conj_mem _ hh c⁻¹
  simpa [mul_assoc] using this

private theorem e6tw_bridge
    {n f : ℕ} (hadm : GGKnownAdm .twistedE6 n f) :
    ∃ Φ : GGAutU .twistedE6 n f →* MulAut ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f)),
      Function.Injective Φ ∧
      (∀ b, GGInnDiagU .twistedE6 n f b → Φ b ∈ LayerSixE.twInndiagAut f) ∧
      (∀ c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
        ∃ κ ∈ (ggPsiU .twistedE6 n f).range, Φ κ = MulAut.conj c) := by
  have hf : 1 ≤ f := hadm.1.2.1
  haveI : Finite (ggU .twistedE6 n f).K :=
    ggU_finite_exc (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hadm
  haveI : Finite (GGAutU .twistedE6 n f) := GGSFCore.finite_ggAutU
  haveI hN : ((ggPsiU .twistedE6 n f).range).Normal :=
    GGSFCore.normal_range_ggPsiU .twistedE6 n f
  obtain ⟨-, hker, -, hcent⟩ := ggKnownSetting_autU hadm
  obtain ⟨π, hπ, hkerπ, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : (ggPsiU .twistedE6 n f).ker ≤ π.ker := hker.trans hkerπ.ge
  have hkerEq : (ggPsiU .twistedE6 n f).ker = π.ker := by
    refine le_antisymm hkπ ?_
    rw [hkerπ]
    intro z hz
    have hz' : z ∈ Subgroup.center (ggU .twistedE6 n f).K := hz
    rw [MonoidHom.mem_ker]
    have h : (ggPsiU .twistedE6 n f) z ∈
        Subgroup.centralizer ((ggPsiU .twistedE6 n f).range : Set (GGAutU .twistedE6 n f)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz' y]
    rw [hcent, Subgroup.mem_bot] at h
    exact h
  obtain ⟨χ, hχinj, hχrange, hval⟩ :=
    NormalizerAut.exists_injective_factor_of_surjective hπ hkerEq
  replace hχrange : χ.range = (ggPsiU .twistedE6 n f).range := hχrange
  have hM : (⊤ : Subgroup (GGAutU .twistedE6 n f)) ≤
      Subgroup.normalizer (χ.range : Set (GGAutU .twistedE6 n f)) := by
    rw [hχrange]
    intro g _
    exact e6tw_mem_normalizer hN g
  have hCχ : Subgroup.centralizer (χ.range : Set (GGAutU .twistedE6 n f)) = ⊥ := by
    rw [hχrange]
    exact hcent
  let Φ : GGAutU .twistedE6 n f →* MulAut ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    (NormalizerAut.normAutOn χ hχinj hM).comp
      (Subgroup.topEquiv (G := GGAutU .twistedE6 n f)).symm.toMonoidHom
  have hΦ : ∀ b, Φ b = NormalizerAut.normAutOn χ hχinj hM ⟨b, Subgroup.mem_top b⟩ :=
    fun b => rfl
  refine ⟨Φ, ?_, ?_, ?_⟩
  · exact (NormalizerAut.normAutOn_injective χ hχinj hM hCχ).comp
      (Subgroup.topEquiv (G := GGAutU .twistedE6 n f)).symm.injective
  · intro b hb
    have hbN : b ∈ Subgroup.normalizer ((ggPsiU .twistedE6 n f).range :
        Set (GGAutU .twistedE6 n f)) :=
      e6tw_mem_normalizer hN b
    obtain ⟨α, hαD, hα⟩ :=
      LayerSixE.exists_induces_twistedE6 hf hπval (ggPsiU .twistedE6 n f) hker hkπ hbN hb
    have hind := NormalizerAut.ggInduces_normAutOn (π := π)
      (ψ := ggPsiU .twistedE6 n f) χ hχinj hval hM ⟨b, Subgroup.mem_top b⟩
    have huniq := LayerSixE.GGInduces.unique hπ hbN hind hα
    rw [hΦ, huniq]
    exact hαD
  · intro c
    refine ⟨χ c, ?_, ?_⟩
    · rw [← hχrange]
      exact ⟨c, rfl⟩
    · rw [hΦ]
      exact NormalizerAut.normAutOn_chi χ hχinj hM c (Subgroup.mem_top _)

theorem ggKGInndiagCIa_twistedE6_three
    (n f : ℕ) (hadm : GGKnownAdm .twistedE6 n f)
    {π : Equiv.Perm (Fin (ggU (absTag .twistedE6) 6 f).D.rank)} (hπ : π = 1)
    (h3 : 3 ∣ 2 ^ f + 1)
    {E : Subgroup (GGAutU .twistedE6 n f)} (hE : IsElemAbelian 3 E)
    (hdiag : ∀ b ∈ E, GGInnDiagU .twistedE6 n f b) : Nat.card E ≤ GGFixCard 3 π := by
  subst hπ
  obtain ⟨Φ, hΦinj, hΦdiag, -⟩ := e6tw_bridge hadm
  have hf : 1 ≤ f := hadm.1.2.1
  have hS : E.map Φ ≤ LayerSixE.twInndiagAut f := by
    rintro _ ⟨b, hb, rfl⟩
    exact hΦdiag b (hdiag b hb)
  have hX := NoOffTwE6Three.isElemAbelian_twLift hf hS (IsElemAbelian.map hE Φ)
  have hcard := NoOffTwE6Three.card_twLift hf hS
  have hXI := NoOffTwE6Three.twLift_le_hatAut_range hf (E.map Φ)
  have hbound :=
    (card_le_and_normalizes_of_le_hatAut (e6tw_three_dvd_card hf h3) hX hXI).1
  rw [hcard, Subgroup.card_map_of_injective hΦinj] at hbound
  rw [e6tw_fixCard_one Nat.prime_three]
  exact hbound

section OuterCommuting

open CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three

theorem twE6CI_exists_outer_commuting_of_card
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1)
    {Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hY : IsElemAbelian 3 Y) (hYI : Y ≤ (RecipeExcLang.twConj K σ).range)
    (hYc : Nat.card Y = 3 ^ 6) :
    ∃ z ∈ (RecipeExcLang.twConj K σ).range,
      z ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range ∧
      ∀ y ∈ Y, z * y = y * z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := inferInstance
  set Ω := AlgebraicClosure K
  set Fr : Ω →+* Ω := iterateFrobenius Ω 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨g, hg, hgn, rfl⟩ := TwE6DD2.exists_eq_langCube hn hK σ hσ h3 Fr hFr hY hYI hYc
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := Ω)
    (three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3)
  have hL : E6ThreeModel.IsLang Fr g := ⟨hg, hgn⟩
  obtain ⟨D, hD⟩ := E6ThreeModel.exists_tFrame hn hK σ hσ Fr hFr h3 hL hζ hζo
  have hnot := E6ThreeModel.langTorus_not_le_cgrp hn hK σ hσ Fr hFr h3 hL hζ hζo hD
  push Not at hnot
  obtain ⟨x, hx, hxC⟩ := hnot
  obtain ⟨b, hb, rfl⟩ := TwistedDiag.mem_thetaTorus.1 hx
  have hxR : g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
    refine (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn _).1 ?_
    rw [TwistedDiag.mem_thetaFixed]
    exact ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup b),
      (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr b).2 hb⟩
  refine ⟨rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hxR⟩, ?_, ?_, ?_⟩
  · rw [← rgrpConjAut_range hn hK σ hσ Fr hFr]
    exact ⟨_, rfl⟩
  · rintro ⟨c, hc⟩
    have h1 : rgrpConjAut hn hK σ hσ Fr hFr (twInndiagEquivRgrp hn hK σ hσ Fr hFr
        ⟨c, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.2⟩) =
        rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hxR⟩ :=
      (rgrpConjAut_apply_baseChange hn hK σ hσ Fr hFr _).trans
        ((RecipeExcLang.twConj_of_mem_C0 σ c).trans hc)
    have h2 : baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) =
        g * rootDiagUnit Tag.E6 b * g⁻¹ :=
      congrArg Subtype.val (rgrpConjAut_injective hn hK σ hσ Fr hFr h1)
    exact hxC ⟨c.1, c.2, h2⟩
  · intro y hy
    obtain ⟨c, hc, hcR, rfl⟩ := (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr).1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    change g * rootDiagUnit Tag.E6 b * g⁻¹ * (g * rootDiagUnit Tag.E6 c * g⁻¹) =
      g * rootDiagUnit Tag.E6 c * g⁻¹ * (g * rootDiagUnit Tag.E6 b * g⁻¹)
    rw [show g * rootDiagUnit Tag.E6 b * g⁻¹ * (g * rootDiagUnit Tag.E6 c * g⁻¹) =
        g * (rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 c) * g⁻¹ by group,
      show g * rootDiagUnit Tag.E6 c * g⁻¹ * (g * rootDiagUnit Tag.E6 b * g⁻¹) =
        g * (rootDiagUnit Tag.E6 c * rootDiagUnit Tag.E6 b) * g⁻¹ by group,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm b c]

end OuterCommuting

private theorem e6tw_map_conj_of_commute {A : Type*} [Group A] {S S' : Subgroup A} {w i : A}
    (hw : ∀ y ∈ S', w * y = y * w) (h : S.map (MulAut.conj (w * i)).toMonoidHom = S') :
    S.map (MulAut.conj i).toMonoidHom = S' := by
  have key : ∀ x ∈ S, MulAut.conj i x = MulAut.conj (w * i) x := by
    intro x hx
    have hy : MulAut.conj (w * i) x ∈ S' := h ▸ Subgroup.mem_map_of_mem _ hx
    have hc := hw _ hy
    simp only [MulAut.conj_apply, mul_inv_rev] at hc ⊢
    have h1 : w * (i * x * i⁻¹) * w⁻¹ = i * x * i⁻¹ := by
      refine mul_left_cancel (a := w) ?_
      calc w * (w * (i * x * i⁻¹) * w⁻¹) = w * (w * i * x * (i⁻¹ * w⁻¹)) := by group
        _ = w * i * x * (i⁻¹ * w⁻¹) * w := hc
        _ = w * (i * x * i⁻¹) := by group
    rw [← h1]
    group
  rw [← h]
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (key x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, key x hx⟩

theorem ggKGInndiagCId_twistedE6_three
    (n f : ℕ) (hadm : GGKnownAdm .twistedE6 n f)
    {π : Equiv.Perm (Fin (ggU (absTag .twistedE6) 6 f).D.rank)} (hπ : π = 1)
    (h3 : 3 ∣ 2 ^ f + 1)
    {E E' : Subgroup (GGAutU .twistedE6 n f)} (hE : IsElemAbelian 3 E) (hE' : IsElemAbelian 3 E')
    (hdiag : ∀ b ∈ E, GGInnDiagU .twistedE6 n f b) (hdiag' : ∀ b ∈ E', GGInnDiagU .twistedE6 n f b)
    (hcE : Nat.card E = GGFixCard 3 π) (hcE' : Nat.card E' = GGFixCard 3 π) :
    ∃ κ : GGAutU .twistedE6 n f, GGInnDiagU .twistedE6 n f κ ∧
      E.map (MulAut.conj κ).toMonoidHom = E' := by
  subst hπ
  obtain ⟨Φ, hΦinj, hΦdiag, hΦinn⟩ := e6tw_bridge hadm
  have hf : 1 ≤ f := hadm.1.2.1
  rw [e6tw_fixCard_one Nat.prime_three] at hcE hcE'
  have hcard : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hrange := twInndiagAut_eq_range_twConj hf
  have hS : ∀ F : Subgroup (GGAutU .twistedE6 n f), (∀ b ∈ F, GGInnDiagU .twistedE6 n f b) →
      F.map Φ ≤ (RecipeExcLang.twConj _ (frobQEquiv hf)).range := by
    intro F hF
    rintro _ ⟨b, hb, rfl⟩
    rw [← hrange]
    exact hΦdiag b (hF b hb)
  have hc6 : ∀ F : Subgroup (GGAutU .twistedE6 n f), Nat.card F = 3 ^ 6 →
      Nat.card (F.map Φ) = 3 ^ 6 := fun F h => by
    rw [Subgroup.card_map_of_injective hΦinj, h]
  obtain ⟨β, hβ, hβS⟩ := TwE6DD2.exists_conj_of_card hf hcard (frobQEquiv hf) (frobQ_apply 2 f) h3
    (hE.map Φ) (hS E hdiag) (hc6 E hcE) (hE'.map Φ) (hS E' hdiag') (hc6 E' hcE')
  obtain ⟨z, hz, hzn, hzc⟩ := twE6CI_exists_outer_commuting_of_card hf hcard (frobQEquiv hf)
    (frobQ_apply 2 f) h3 (hE'.map Φ) (hS E' hdiag') (hc6 E' hcE')
  haveI : (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range.Normal :=
    RootCentExc.normal_range_mulAutConj
  have hle := NoOffTwE6Three.twInndiagAut_le_sup_zpowers hf (hrange ▸ hz) hzn
  rw [sup_comm] at hle
  obtain ⟨w, hw, i, hi, hwi⟩ :=
    Subgroup.mem_sup_of_normal_right.1 (hle (hrange ▸ hβ))
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  obtain ⟨c, rfl⟩ := hi
  have hconj : (E.map Φ).map (MulAut.conj (MulAut.conj c)).toMonoidHom = E'.map Φ := by
    refine e6tw_map_conj_of_commute (w := z ^ k) (fun y hy => ?_) (hwi ▸ hβS)
    exact (Commute.zpow_left (hzc y hy) k).eq
  obtain ⟨κ, hκr, hκ⟩ := hΦinn c
  refine ⟨κ, GGSFCore.ggInnDiagU_of_mem_range hκr, ?_⟩
  apply Subgroup.map_injective hΦinj
  have h1 : (E.map (MulAut.conj κ).toMonoidHom).map Φ =
      (E.map Φ).map (MulAut.conj (Φ κ)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  rw [h1, hκ]
  exact hconj

end CFSG.StandardType

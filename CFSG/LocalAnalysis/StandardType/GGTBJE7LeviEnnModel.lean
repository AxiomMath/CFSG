module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnModel
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJModel
public import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggE7_model
    {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    {Bs X : Subgroup G} {n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.E7, 0, n⟩)
    (hinn : GGInnerDiagOn Bs X) (hlab : GGHasLabel ⟨.E7, 0, n⟩ (↥X ⧸ Subgroup.center ↥X)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ _ : ↥X ≃* adjointGroup .E7 K, Subgroup.center ↥X = ⊥ ∧
        Bs ≤ Subgroup.normalizer (X : Set G) ∧
        ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ := by
  classical
  obtain ⟨hperf, lab', _hlab', hraw'⟩ := ggInnerDiagOn_relabel hRig hinn hΛ hlab
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨_, _, hrest₀⟩ := hQ₀
  obtain ⟨_, hP₀⟩ := hrest₀
  obtain ⟨hlabeq, _, _⟩ := hP₀
  subst hlabeq
  have hInnAll : LargeEvenLabelAll ⟨.E7, 0, n⟩
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) :=
    largeEvenLabelAll_subset_inn hΛ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨R, _instR, I, F, hQR, hguard⟩ := largeEvenRawDatum_exists (hInnAll _ hraw')
  obtain ⟨hsR, hnaR, hrest⟩ := hQR
  obtain ⟨θ, hP'⟩ := hrest
  obtain ⟨_, hBsN, hind⟩ := hP'
  have hI : I ⊆ LargeEvenInnSet R := hguard hsR hnaR
  have hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ :=
    F4AutRefl.exists_conj_of_inn hperf θ hI hBsN hind
  obtain ⟨K, _instK, _finK, hKcard, hQK⟩ := hraw'
  obtain ⟨_, _, hrestK⟩ := hQK
  obtain ⟨θ_K, _hPK⟩ := hrestK
  obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv K .E7
  let eAd : ↥X ⧸ Subgroup.center ↥X ≃* Blueprint.AdjointQuotient .E7 K := θ_K.trans eQ
  have hRq : IsQuasisimple R := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnaR).1
  have hf : Function.Surjective ((θ.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center ↥X))) :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ((θ.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center ↥X))).ker ≤
      Subgroup.center ↥X := by
    rw [MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  have hperfX : Group.IsPerfect ↥X := Group.isPerfect_def.mpr hperf
  have hXq : IsQuasisimple ↥X :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperfX _ hf hker).mpr hRq
  have hZ : Subgroup.center ↥X = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7 hXq hΛ.1 hKcard eAd
  let eX : ↥X ⧸ Subgroup.center ↥X ≃* ↥X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let eA : Blueprint.AdjointQuotient .E7 K ≃* adjointGroup .E7 K :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .E7) (K := K))).trans
      QuotientGroup.quotientBot
  exact ⟨K, _instK, _finK, charP_two_of_card hKcard, hKcard, eX.symm.trans (eAd.trans eA),
    hZ, hBsN, hinner⟩

theorem ggE7Enn_model_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E7, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n + 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ (e : ↥L ≃* adjointGroup .E7 Fq) (E : Subgroup (adjointGroup .E7 Fq)),
        IsElemAbelian p E ∧ p ^ 6 ≤ Nat.card E ∧
        (∀ g : adjointGroup .E7 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E7 Fq →* MulAut (adjointGroup .E7 Fq)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hn : 1 ≤ n := hΛ.1
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ']
    rw [hpow] at hpn
    omega
  have hml : LargeEvenMarking ↥L (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    hH.2.2.1.1
  obtain ⟨hLperf, _lab', R, _instR, _I, _F, θ, _hlab', hmark⟩ :=
    largeEvenMarking_exists' hml
  obtain ⟨hNmark, _hind⟩ := hmark
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, ⟨⟨θ₀⟩, hlift₀⟩⟩ :=
    (largeEvenLabelAll_torusLift_excPlus (p := p) (lab := (⟨.E7, 0, n⟩ : LargeEvenLabel))
      hp hp2 ⟨Or.inl rfl, hpn⟩) _ hL
  have hlift : GGTorusLift p 6 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 6 ≤ Nat.card (ggGamma L hNmark).range :=
    (card_range_ggGamma_bstar_ge hH.1 hLperf θ hNmark hlift).1
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggE7_model hRig hΛ hH.2.2.1.1 hL
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e7Levi_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, e, E,
    hEel, hEcard, hEsc, hArange⟩

theorem ggE7Enn_model_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E7, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n + 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ (e : ↥K ≃* adjointGroup .E7 Fq) (E : Subgroup (adjointGroup .E7 Fq)),
        IsElemAbelian p E ∧ p ^ 6 ≤ Nat.card E ∧
        (∀ g : adjointGroup .E7 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E7 Fq →* MulAut (adjointGroup .E7 Fq)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hn : 1 ≤ n := hΛ.1
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ']
    rw [hpow] at hpn
    omega
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmk : LargeEvenMarking ↥K (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    hH.2.2.1.2 y K hnb
  obtain ⟨hKperf, _lab', R, _instR, _I, _F, θ, _hlab', hmark⟩ :=
    largeEvenMarking_exists' hmk
  obtain ⟨hNmark, _hind⟩ := hmark
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, ⟨⟨θ₀⟩, hlift₀⟩⟩ :=
    (largeEvenLabelAll_torusLift_excPlus (p := p) (lab := (⟨.E7, 0, n⟩ : LargeEvenLabel))
      hp hp2 ⟨Or.inl rfl, hpn⟩) _ hK
  have hlift : GGTorusLift p 6 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 6 ≤ Nat.card (ggGamma K hNmark).range :=
    pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hKperf θ hNmark hlift
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggE7_model hRig hΛ (hH.2.2.1.2 y K hnb) hK
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e7Levi_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, e, E,
    hEel, hEcard, hEsc, hArange⟩

end CFSG.StandardType

end

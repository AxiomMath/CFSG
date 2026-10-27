module

public import CFSG.LocalAnalysis.StandardType.GGSixD4SmallVacuousLin
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmNsRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

namespace D4Vac

open Module CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData NoOffOm SevOm

theorem polar_map_of_mem {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (u w : V) : QuadraticMap.polar Q (g u) (g w) = QuadraticMap.polar Q u w := by
  have hQ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hQ, hQ, hQ]

theorem exists_two_subgroup {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U}
    {t : StatedLieTag} {n f : ℕ} {ψ : U →* G} (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hBG₀ : B ≤ ggG0 p B x L D J) :
    ∃ T : Subgroup G, T ≤ ggG0 p B x L D J ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨T, -, hT2, hBT, hTB⟩ := hctx.1.2.2.2.2.2.2.2.2.1
  have hDB : D ≤ B := hctx.2.2.1.1.1
  have hcop : Nat.Coprime p (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hTM : T ≤ ggM p B x L D J := s1.2.2.1 T (hDB.trans hBT) hcop
  have hcomm : ⁅T, B⁆ ≤ T ⊓ ggG0 p B x L D J := by
    rw [Subgroup.commutator_le]
    intro c hc b hb
    have h1 : b * c⁻¹ * b⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hBT hb) c⁻¹).mp (T.inv_mem hc)
    have h2 : c * b * c⁻¹ ∈ ggG0 p B x L D J :=
      (Subgroup.mem_normalizer_iff.mp (hTM hc) b).mp (hBG₀ hb)
    rw [commutatorElement_def]
    refine ⟨?_, (ggG0 p B x L D J).mul_mem h2 ((ggG0 p B x L D J).inv_mem (hBG₀ hb))⟩
    have e : c * b * c⁻¹ * b⁻¹ = c * (b * c⁻¹ * b⁻¹) := by group
    rw [e]
    exact T.mul_mem hc h1
  refine ⟨T ⊓ ggG0 p B x L D J, inf_le_right, fun h => hTB (le_bot_iff.mp (h ▸ hcomm)),
    hT2.to_le inf_le_left, fun b hb => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · rintro ⟨hc, hc'⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hBT hb) c).mp hc,
      (ggG0 p B x L D J).mul_mem ((ggG0 p B x L D J).mul_mem (hBG₀ hb) hc')
        ((ggG0 p B x L D J).inv_mem (hBG₀ hb))⟩
  · rintro ⟨hc, hc'⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hBT hb) c).mpr hc, ?_⟩
    have e : c = b⁻¹ * (b * c * b⁻¹) * b := by group
    rw [e]
    exact (ggG0 p B x L D J).mul_mem ((ggG0 p B x L D J).mul_mem
      ((ggG0 p B x L D J).inv_mem (hBG₀ hb)) hc') (hBG₀ hb)

theorem false_of_plusFour {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    {ψ : spinGroup (quadPlus 4 K) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (plusDatum 4 K (by norm_num)) .POmegaPlus 4 f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpK : ¬ p ∣ Nat.card K - 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn3]
    exact hker
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ :=
      PsiDiag.SpinP.exists_mem_centralizer hn3 ψ hker (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hC, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  have hBs := hctx.2.1
  have hBG₀ : B ≤ ggG0 p B x L D J := hBs.1.trans (hBψ.trans hrange.le)
  obtain ⟨T, hTG₀, hT1, hT2, hBT⟩ := exists_two_subgroup hctx s1 hBG₀
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadPlus 4 K hn3
  set Q := coordinateQuadPlus 4 K with hQ
  set πe := MulEquiv.ofBijective (AutOm.spinModelPlus (K := K) hn3)
    ⟨AutOm.spinModelPlus_injective hn3, AutOm.spinModelPlus_surjective hn3⟩ with hπe
  set φ : matrixDerived Q →* G := ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψinj.comp πe.symm.injective
  have hφrange : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨πe u, by simp [hφ]⟩
  have hBφ : Bs ≤ φ.range := hφrange ▸ hBψ
  have hG₀ : φ.range = ggG0 p B x L D J := hφrange.trans hrange
  set m : matrixDerived Q →* ((Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) :=
    (matrixLinearIso (d := 2 * 4) (K := K)).toMonoidHom.comp (matrixDerived Q).subtype with hm
  have hminj : Function.Injective m := by
    intro Y Y' h
    have h1 : matrixLinearIso (d := 2 * 4) (K := K) (Y : GL (Fin (2 * 4)) K) =
        matrixLinearIso (Y' : GL (Fin (2 * 4)) K) := h
    exact Subtype.ext (matrixLinearIso.injective h1)
  have hmap : ∀ H : Subgroup (matrixDerived Q),
      (H.map (matrixDerived Q).subtype).map (matrixLinearIso (d := 2 * 4) (K := K)).toMonoidHom =
        H.map m := fun H => by rw [Subgroup.map_map]
  have hA := genMax_of_orth hnd hT3 hp hp2 hBs.2.1 hBs.2.2.2 φ hφinj hBφ
  obtain ⟨r, ⟨F⟩⟩ := exists_frame_of_genMax hA
  rw [hmap] at F
  have hV : finrank K (Fin (2 * 4) → K) ≤ 8 := by rw [Module.finrank_fin_fun]
  have hr4 := r_le_four F hV
  have hcA : Nat.card ((Bs.comap φ).map m) = p ^ r := by
    rw [← F.range, Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hcBs : Nat.card ((Bs.comap φ).map m) = Nat.card Bs := by
    rw [Subgroup.card_map_of_injective hminj]
    have e := (Bs.comap φ).equivMapOfInjective φ hφinj
    rw [Nat.card_congr e.toEquiv, Subgroup.map_comap_eq_self hBφ]
  have hpB : p ^ 4 ≤ Nat.card B := by
    rw [hctx.1.2.2.2.2.2.2.1.1.2.1]
    exact Nat.pow_le_pow_right hp.pos hctx.1.2.2.2.2.2.1.2.2.2
  have hBeq : B = Bs := by
    refine Subgroup.eq_of_le_of_card_ge hBs.1 ?_
    calc Nat.card Bs = p ^ r := hcBs.symm.trans hcA
      _ ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos hr4
      _ ≤ Nat.card B := hpB
  have hr : 4 ≤ r := by
    have h1 : p ^ 4 ≤ p ^ r :=
      calc p ^ 4 ≤ Nat.card B := hpB
        _ ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
        _ = p ^ r := hcBs.symm.trans hcA
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  set T' := (T.comap φ).map m with hT'def
  have hT'2 : IsPGroup 2 T' := (hT2.comap_of_injective φ hφinj).map m
  have hT'Q : ∀ t ∈ T', ∀ u w : Fin (2 * 4) → K,
      QuadraticMap.polar Q (t u) (t w) = QuadraticMap.polar Q u w := by
    rintro _ ⟨Y, -, rfl⟩ u w
    exact polar_map_of_mem (matrixDerived_le_isometries Q Y.2) u w
  have hAT : ∀ a ∈ (Bs.comap φ).map m, ∀ t ∈ T', a⁻¹ * t * a ∈ T' := by
    rintro _ ⟨Ya, hYa, rfl⟩ _ ⟨Yt, hYt, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap] at hYa hYt
    have hb : φ Ya ∈ B := hBeq ▸ hYa
    rw [← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map_of_mem m ?_
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hBT (B.inv_mem hb)) (φ Yt)).mp hYt
    rwa [inv_inv] at h1
  have hT'ne : T' ≠ ⊥ := by
    intro hbot
    apply hT1
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨Y, rfl⟩ : g ∈ φ.range := hG₀ ▸ hTG₀ hg
    have hmem : m Y ∈ T' := Subgroup.mem_map_of_mem m hg
    rw [hbot, Subgroup.mem_bot, ← map_one m] at hmem
    rw [hminj hmem, map_one]
    exact Subgroup.one_mem _
  exact hT'ne (eq_bot_of_frame hV hp hp2 hpK F hr hT'2 hT'Q hAT)

end D4Vac

section Inputs

theorem ggSix_false_of_plusFour {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {f : ℕ} {ψ : (ggU .POmegaPlus 4 f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : ¬ p ∣ 2 ^ f - 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hpK : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hpq
  revert ψ
  rw [ggU_POmegaPlus_eq (by norm_num : 3 ≤ 4)]
  intro ψ hctx
  exact D4Vac.false_of_plusFour hctx s1 hpK

theorem ggSixRootFusionWitnessOn_POmegaPlusFourNonsplit :
    GGSixRootFusionWitnessOn fun t n f p => t = .POmegaPlus ∧ n = 4 ∧ ¬ p ∣ 2 ^ f - 1 := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1
  obtain ⟨rfl, rfl, hpq⟩ := hP
  exact (ggSix_false_of_plusFour hctx s1 hpq).elim

theorem ggSixRootFusionWitOmPlusQ1D4Small_holds : GGSixRootFusionWitOmPlusQ1D4Small :=
  ggSixRootFusionWitnessOn_POmegaPlusFourNonsplit.mono fun _ _ f p ht => ⟨ht.1, ht.2.1, by
    rcases ht.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num⟩

theorem ggSixRootFusionWitOmPlusQ1_holds : GGSixRootFusionWitOmPlusQ1 :=
  ggSixRootFusionWitOmPlusQ1_of_small ggSixRootFusionWitOmPlusQ1D4Small_holds

end Inputs

end CFSG.StandardType

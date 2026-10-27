module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkModel
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmRest
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlk
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartTwo.Sec21

namespace WitOmBlk

theorem witnessAlt_of_model {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {U : Type} [Group U] {Δ : UniversalRootDatum U} {t : StatedLieTag}
    {n f : ℕ} {ψ : U →* G} (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (φ : matrixDerived Q →* G) (hφ : Function.Injective φ) (hφr : φ.range = ggG0 p B x L D J)
    (hBφ : Bs ≤ φ.range) (hpq : ¬ p ∣ 2 ^ f - 1) (hpq' : ¬ p ∣ 2 ^ f + 1) (E : Subgroup G) (r : G)
    {s : G} (hs : s ∈ ggG0 p B x L D J) (hs2 : orderOf s = 2) :
    GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) t f r s := by
  have hcard : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
    have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
    have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hctx.prime.pos hr4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBBs
  rw [← hφr] at hs
  obtain ⟨u, rfl⟩ := hs
  have hu : u * u = 1 := by
    have h2 := pow_orderOf_eq_one (φ u)
    rw [hs2, pow_two, ← map_mul] at h2
    exact hφ (by rw [h2, map_one])
  obtain ⟨g, a, hga, hwit⟩ := exists_conj_witness_of_model hnd hT hctx.prime hctx.ne_two
    (by rw [hK]; exact hpq) (by rw [hK]; exact hpq') hctx.bstar.2.1 hctx.bstar.2.2.2 hcard φ hφ
    hBφ t f hu
  refine Or.inr (Or.inl ⟨φ (g⁻¹ * a * g), ?_, φ g, Subgroup.le_normalizer (hφr ▸ ⟨g, rfl⟩), ?_⟩)
  · rw [← map_mul, ← map_mul]
    congr 1
    calc g⁻¹ * a * g * u = g⁻¹ * (a * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * u * g⁻¹ * a) * g := by rw [hga]
      _ = u * (g⁻¹ * a * g) := by group
  · have hconj : φ g * φ (g⁻¹ * a * g) * (φ g)⁻¹ = φ a := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    rw [hconj, ← hφr]
    exact hwit.fusionWitness

theorem witnessAlt_plus_rest {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} (hn : 3 ≤ n)
    {ψ : spinGroup (quadPlus n (GaloisField 2 f)) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (plusDatum n (GaloisField 2 f) hn) .POmegaPlus n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : ¬ p ∣ 2 ^ f - 1) (hpq' : ¬ p ∣ 2 ^ f + 1)
    (E : Subgroup G) (r : G) {s : G} (hs : s ∈ ggG0 p B x L D J) (hs2 : orderOf s = 2) :
    GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .POmegaPlus f r s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  have hin : ∀ c, GGPsiInnerDiag (plusDatum n (GaloisField 2 f) hn) ψ c → c ∈ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus n (GaloisField 2 f) hn
  set πe := MulEquiv.ofBijective (AutOm.spinModelPlus (K := GaloisField 2 f) hn)
    ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ with hπe
  set φ : matrixDerived (coordinateQuadPlus n (GaloisField 2 f)) →* G :=
    ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφr : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨πe v, by simp [hφ]⟩
  exact witnessAlt_of_model hctx (GaloisField.card 2 f (by omega)) hnd hT φ hφinj
    (hφr.trans hrange) (fun b hb => by rw [hφr]; exact hin b (hctx.2.2.2.2.2.2.1.2 b hb)) hpq
    hpq' E r hs hs2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem witnessAlt_minus_rest {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2 ^ f) {ψ : spinGroup (quadMinus n K b c) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (minusDatum n hirr) .POmegaMinus n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : ¬ p ∣ 2 ^ f - 1) (hpq' : ¬ p ∣ 2 ^ f + 1)
    (E : Subgroup G) (r : G) {s : G} (hs : s ∈ ggG0 p B x L D J) (hs2 : orderOf s = 2) :
    GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .POmegaMinus f r s := by
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hn : 4 ≤ n := hctx.2.2.2.1.1.2.2
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  have hin : ∀ c₀, GGPsiInnerDiag (minusDatum n hirr) ψ c₀ → c₀ ∈ ψ.range := by
    intro c₀ hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  set πe := MulEquiv.ofBijective (AutOm.spinModelMinus hn hirr)
    ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩ with hπe
  set φ : matrixDerived (coordinateQuadMinus n K (by omega) b c) →* G :=
    ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφr : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨πe v, by simp [hφ]⟩
  exact witnessAlt_of_model hctx hK hnd hT φ hφinj (hφr.trans hrange)
    (fun b' hb => by rw [hφr]; exact hin b' (hctx.2.2.2.2.2.2.1.2 b' hb)) hpq hpq' E r hs hs2

end WitOmBlk

section Inputs

theorem ggSixRootFusionWitOmPlusRest_holds : GGSixRootFusionWitOmPlusRest := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, hpq, hpq'⟩ := hP
  by_cases hn : 3 ≤ n
  · revert ψ
    rw [ggU_POmegaPlus_eq hn]
    intro ψ hctx s1 _ E r _ _ _ s hs hs2
    exact WitOmBlk.witnessAlt_plus_rest hn hctx s1 hpq hpq' E r hs hs2
  · intro hctx
    exact absurd hctx.2.2.2.1.1.2.2 (by omega)

theorem ggSixRootFusionWitOmMinusRest_holds : GGSixRootFusionWitOmMinusRest := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 _ E r _ _ _ s hs hs2
  obtain ⟨rfl, hpq, hpq'⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact WitOmBlk.witnessAlt_minus_rest (K := GaloisField 2 f) (minusCoeffs_irr 2 f)
    (GaloisField.card 2 f (by have := hctx.2.2.2.1.1.2.1; omega)) hctx s1 hpq hpq' E r hs hs2

theorem ggSixRootFusionWitnessOn_POmegaPlus_of_q1 (h : GGSixRootFusionWitOmPlusQ1) :
    GGSixRootFusionWitnessOn fun t _ _ _ => t = .POmegaPlus :=
  ggSixRootFusionWitnessOn_POmegaPlus_of_parts h ggSixRootFusionWitOmPlusRest_holds

theorem ggSixRootFusionWitnessOn_POmegaMinus_of_q1 (h : GGSixRootFusionWitOmMinusQ1) :
    GGSixRootFusionWitnessOn fun t _ _ _ => t = .POmegaMinus :=
  ggSixRootFusionWitnessOn_POmegaMinus_of_parts h ggSixRootFusionWitOmMinusRest_holds

theorem ggSixRootFusionWitnessInputFor_otherClassical_of_q1 (hPl : GGSixRootFusionWitOmPlusQ1)
    (hMi : GGSixRootFusionWitOmMinusQ1) : GGSixRootFusionWitnessInputFor GGOtherClassicalTag :=
  ggSixRootFusionWitnessInputFor_otherClassical_of_omega
    (ggSixRootFusionWitnessOn_POmegaPlus_of_q1 hPl) (ggSixRootFusionWitnessOn_POmegaMinus_of_q1 hMi)

end Inputs

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURich
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSUFrameSL

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace UFusion

theorem exists_zeta {f p : ℕ} (hf : 1 ≤ f) (hpp : p.Prime) (hp : p ∣ 2 ^ f + 1) :
    ∃ ζ : (GaloisField 2 (2 * f))ˣ, ζ ≠ 1 ∧ ζ ^ p = 1 ∧
      unitaryInvolution (GaloisField 2 (2 * f)) 2 f (ζ : GaloisField 2 (2 * f)) * ζ = 1 := by
  have := Fact.mk hpp
  have hdvd : p ∣ Nat.card (GaloisField 2 (2 * f))ˣ := by
    rw [Nat.card_units, card_galoisField_two_mul 2 f hf]
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have := Nat.mul_self_sub_mul_self_eq (2 ^ f) 1
      simpa [sq] using this
    rw [h1]
    exact Dvd.dvd.mul_right hp _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨ζ, ?_, ?_, ?_⟩
  · rintro rfl
    rw [orderOf_one] at hζ
    exact hpp.one_lt.ne hζ
  · rw [← hζ]
    exact pow_orderOf_eq_one ζ
  · have h1 : ζ ^ (2 ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (hζ ▸ hp)
    rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, h1, Units.val_one]

end UFusion

@[expose] def GGUnitarySemisimpleComponentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m f : ℕ), 1 ≤ f →
    ∀ ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G,
    ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)) →
    ∀ Q : GL (Fin (m + 1)) (GaloisField 2 (2 * f)),
      UFusion.IsUFrame (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) Q →
      ∀ S : Set G, S ⊆ UFusion.uFrameTorus ψ Q →
        ∀ L₁ : Subgroup G, IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer S) →
          ∃ I : Finset (Fin (m + 1)), L₁ ≤ UFusion.uFrameBlock ψ Q I ∧
            ∀ g ∈ S, ∃ e : Fin (m + 1) → (GaloisField 2 (2 * f))ˣ,
              (g, LinFusion.ggFrameDiag Q e) ∈ UFusion.suInducedPairs ψ ∧
                ∀ i ∈ I, ∀ j ∈ I, e i = e j

@[expose] def GGUnitaryBstarFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (hf : 1 ≤ f)
    (ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G),
    GGSixCtxV2 p B Bs x L D J (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) .PSU
      (m + 1) f ψ →
    GGSixStepOne p B Bs x L D J → p ∣ 2 ^ f + 1 →
      ∃ Q : GL (Fin (m + 1)) (GaloisField 2 (2 * f)),
        UFusion.IsUFrame (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) Q ∧
          Bs ≤ UFusion.uFrameTorus ψ Q

theorem ggStepTwoUnitaryFusion_of_frame (hT : GGUnitaryBstarFrameInput)
    (hCmp : GGUnitarySemisimpleComponentInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ} (hf : 1 ≤ f)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1))
      .PSU (m + 1) f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p ∣ 2 ^ f + 1)
    (hDJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) {b : G} {L₁ : Subgroup G}
    (hpair : GGStepTwoPair p B Bs x L D J b L₁) :
    ∃ w ∈ Subgroup.normalizer (Bs : Set G), w ∈ ggG0 p B x L D J ∧ w⁻¹ * b * w ∈ D := by
  obtain ⟨Q, hQ, hBT⟩ := hT G p B Bs x L D J m f hf ψ hctx s1 hp
  have hpp : p.Prime := hctx.1.2.2.2.2.2.1.1
  obtain ⟨⟨-, hBel, -, hSC⟩, ⟨⟨-, -, hDcard, -⟩, -⟩, -, ⟨hrange, hker⟩, -⟩ := hctx.2
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact s1.1
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hrange]
    exact hctx.j_isComponentOf_inf
  obtain ⟨I₀, hJI, hDI⟩ := hCmp G m f hf ψ hker Q hQ D (fun g hg => hBT (hctx.d_le_bstar hg)) J hJ
  have hD : Bs ⊓ Subgroup.centralizer (UFusion.uFrameBlock ψ Q I₀ : Set G) = D := by
    refine le_antisymm (fun g hg => hDJ ⟨hg.1, Subgroup.centralizer_le hJI hg.2⟩) fun g hg => ?_
    obtain ⟨e, he, heI⟩ := hDI g hg
    exact ⟨hctx.d_le_bstar hg, UFusion.mem_centralizer_uFrameBlock he heI⟩
  obtain ⟨hbB, -, hcomp₁, hcard₁⟩ := hpair
  have hcomp₂ : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [hrange]
    exact hcomp₁
  obtain ⟨I, hLI, hbI⟩ := hCmp G m f hf ψ hker Q hQ {b}
    (Set.singleton_subset_iff.mpr (hBT hbB)) L₁ hcomp₂
  obtain ⟨d, hd, hdI⟩ := hbI b (Set.mem_singleton b)
  have hcardI : Nat.card (Bs ⊓ Subgroup.centralizer (UFusion.uFrameBlock ψ Q I : Set G) :
      Subgroup G) ≤ p ^ 2 :=
    le_trans (Subgroup.card_le_of_le (inf_le_inf_left _ (Subgroup.centralizer_le hLI))) hcard₁
  obtain ⟨w, hwN, hwR, hw⟩ := UFusion.exists_conj_mem_of_uFrameEq hker hC hQ hpp
    (UFusion.exists_zeta hf hpp hp) hBT (fun b hb => hBel.2 b hb) hSC hD hDcard hbB hd hdI hcardI
  exact ⟨w, hwN, hrange ▸ hwR, hw⟩

section Inputs

@[expose] def GGStepTwoUnitaryFusionEqInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n f).D .PSU n f ψ → GGSixStepOne p B Bs x L D J →
    p ∣ 2 ^ f + 1 → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        ∃ m ∈ Subgroup.normalizer (Bs : Set G), m⁻¹ * b * m ∈ D

theorem ggStepTwoUnitaryFusionEqInput_of_frame (hT : GGUnitaryBstarFrameInput)
    (hCmp : GGUnitarySemisimpleComponentInput) : GGStepTwoUnitaryFusionEqInput := by
  intro G _ _ p B Bs x L D J n f
  by_cases hf : 1 ≤ f
  · have e : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e]
    intro ψ hctx s1 hp hDJ b L₁ hpair
    obtain ⟨-, -, hn, -⟩ := hctx.2.2.2.1.1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨w, hwN, -, hw⟩ := ggStepTwoUnitaryFusion_of_frame hT hCmp hf hctx s1 hp hDJ hpair
    exact ⟨w, hwN, hw⟩
  · intro ψ hctx
    exact absurd hctx.2.2.2.1.1.2.1 hf

@[expose] def GGStepTwoLinearFusionEqInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    GGStepTwoLinearType p t f → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        ∃ m ∈ Subgroup.normalizer (Bs : Set G), m⁻¹ * b * m ∈ D

theorem ggStepTwoLinearFusionEqInput_of_frame (hT : GGUnitaryBstarFrameInput)
    (hCmp : GGUnitarySemisimpleComponentInput) : GGStepTwoLinearFusionEqInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin hDJ b L₁ hpair
  rcases hlin with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
  · obtain ⟨-, -, hn, -⟩ := hctx.2.2.2.1.1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨w, hwN, -, hw⟩ := ggStepTwoLinearFusion_PSL_of_frameEq
      ggLinearSemisimpleComponentInput_holds ggLinearFrameEqInput_holds hctx s1 hp hpair
    exact ⟨w, hwN, hw⟩
  · exact ggStepTwoUnitaryFusionEqInput_of_frame hT hCmp G p B Bs x L D J n f ψ hctx s1 hp hDJ b
      L₁ hpair

@[expose] def GGUnitaryBstarCentralizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n f).D .PSU n f ψ → GGSixStepOne p B Bs x L D J →
    p ∣ 2 ^ f + 1 → 2 ≤ f → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D

@[expose] def GGStepTwoUnitaryFusionLargeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n f).D .PSU n f ψ → GGSixStepOne p B Bs x L D J →
    p ∣ 2 ^ f + 1 → 2 ≤ f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        ∃ m ∈ Subgroup.normalizer (Bs : Set G), m⁻¹ * b * m ∈ D

theorem ggStepTwoUnitaryFusionLargeInput_of_frame (hT : GGUnitaryBstarFrameInput)
    (hCmp : GGUnitarySemisimpleComponentInput) (hI1 : GGUnitaryBstarCentralizerInput) :
    GGStepTwoUnitaryFusionLargeInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hp hf b L₁ hpair
  exact ggStepTwoUnitaryFusionEqInput_of_frame hT hCmp G p B Bs x L D J n f ψ hctx s1 hp
    (hI1 G p B Bs x L D J n f ψ hctx s1 hp hf) b L₁ hpair

end Inputs

end CFSG.StandardType

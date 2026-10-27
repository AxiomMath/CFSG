module

public import CFSG.LocalAnalysis.StandardType.GGActualFrobReversal
public import CFSG.LocalAnalysis.StandardType.GGFinModelExists
public import CFSG.LocalAnalysis.StandardType.GGLangFixedFamilies
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Rot
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallUnitary
public import CFSG.RankThree.PartOne.D4RC.RxIso

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.ClassicalInvolution.Phan
open CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3

@[expose] noncomputable def actualQuadraticSubfield (f : ℕ) : Subfield GGL :=
  RingHom.eqLocusField (iterateFrobenius GGL 2 (2 * f)) (RingHom.id GGL)

theorem mem_actualQuadraticSubfield_iff (f : ℕ) (c : GGL) :
    c ∈ actualQuadraticSubfield f ↔ c ^ (2 ^ f) ^ 2 = c := by
  simpa [actualQuadraticSubfield] using mem_fixedField_iff (Ω := GGL) (ℓ := 2) (f := f) c

theorem card_actualQuadraticSubfield {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (actualQuadraticSubfield f) = (2 ^ f) ^ 2 := by
  simpa [actualQuadraticSubfield] using natCard_fixedField (Ω := GGL) (ℓ := 2) (f := f) hf

theorem finite_actualQuadraticSubfield {f : ℕ} (hf : 1 ≤ f) :
    Finite (actualQuadraticSubfield f) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_actualQuadraticSubfield hf]
  exact ne_of_gt (by positivity)

instance actualQuadraticSubfield_charP (f : ℕ) : CharP (actualQuadraticSubfield f) 2 :=
  Subfield.charP (actualQuadraticSubfield f) 2

instance actualQuadraticSubfield_finite (f : ℕ) [NeZero f] :
    Finite (actualQuadraticSubfield f) :=
  finite_actualQuadraticSubfield (Nat.pos_of_ne_zero (NeZero.ne f))

theorem coe_actualQuadraticSubfield_eq_range {f : ℕ} (hf : 1 ≤ f) :
    (actualQuadraticSubfield f : Set GGL) = Set.range (ggRatEmb (2 * f)) := by
  ext c
  change c ∈ actualQuadraticSubfield f ↔ c ∈ Set.range (ggRatEmb (2 * f))
  rw [mem_actualQuadraticSubfield_iff, ggRatEmb_range (f := 2 * f) (by omega)]
  have hpow : (2 : ℕ) ^ (2 * f) = (2 ^ f) ^ 2 := by
    calc
      (2 : ℕ) ^ (2 * f) = 2 ^ (f * 2) := by rw [mul_comm]
      _ = (2 ^ f) ^ 2 := by rw [pow_mul]
  simp [hpow]

end CFSG.StandardType.GGFinModel

namespace CFSG.StandardType.ResidualA2Pair

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.StandardType.CompactA2Pair
open scoped MatrixGroups

theorem pair_of_matched_frame_original_member_actualField
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) {n : ℕ} [NeZero f]
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (ρF : Equiv.Perm (Fin (langTag t).rank → ℤ)) (hFrob : FrobRootMap M.D ρF)
    (j : Matrix.SpecialLinearGroup (Fin 3) GGL →* ModGL (langTag t) GGL)
    (σ : Fin 3 → Fin 3 → Fin (langTag t).rank → ℤ)
    (hpair : CFSG.RankThree.PartOne.KF4.IsA2Frame j σ)
    (hrev : ∀ i k : Fin 3, i ≠ k → ρF (σ i k) = σ k i)
    {I₀ I₁ : Type*} [Finite I₀] [Finite I₁]
    (a₀ : I₀ → Fin (langTag t).rank → GGLˣ)
    (a₁ : I₁ → Fin (langTag t).rank → GGLˣ)
    (ha₀ : ∀ i, ∃ k : ℕ, a₀ i ^ (p ^ k) = 1)
    (ha₁ : ∀ i, ∃ k : ℕ, a₁ i ^ (p ^ k) = 1)
    (hk₀ : famKernel (Set.range a₀) = {σ 0 1, -σ 0 1})
    (hk₁ : famKernel (Set.range a₁) = {σ 1 2, -σ 1 2})
    (ψ : ↥M.D.Γ →* G) (hψinj : Function.Injective ψ) (hX : ψ.range = X)
    (β : ↥Bs →* ModGL (langTag t) GGL)
    (hpres : ∀ (b : ↥Bs) (y : ↥M.D.Γ), β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹ ∈ M.D.Γ)
    (hcompat : ∀ (b : ↥Bs) (y : ↥M.D.Γ),
      ψ ⟨β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹, hpres b y⟩ =
        (b : G) * ψ y * (b : G)⁻¹)
    (r s : MulAut ↥Bs)
    (hH₀ : ∀ z : ModGL (langTag t) GGL,
      z ∈ Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₀ i)) ↔
        ∃ b : ↥Bs, r b = b ∧ β b = z)
    (hH₁ : ∀ z : ModGL (langTag t) GGL,
      z ∈ Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)) ↔
        ∃ b : ↥Bs, s b = b ∧ β b = z) :
    ∃ θG : Su (actualQuadraticSubfield f) 2 f 3 →* G,
      Function.Injective θG ∧ θG.range ≤ X ∧
      (B12 (actualQuadraticSubfield f) 2 f).map θG = ggRankOneIn X Bs r ∧
      (B23 (actualQuadraticSubfield f) 2 f).map θG = ggRankOneIn X Bs s ∧
      UnitaryBlockStandardPair (actualQuadraticSubfield f) 2 f θG.range
        (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  have hf : 1 ≤ f := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne f))
  exact pair_of_matched_frame_original_member M (n := n) hf hp hp2 hreg
    ρF hFrob j σ hpair hrev (actualQuadraticSubfield f)
    (mem_actualQuadraticSubfield_iff f) (card_actualQuadraticSubfield hf)
    a₀ a₁ ha₀ ha₁ hk₀ hk₁ ψ hψinj hX β hpres hcompat r s hH₀ hH₁

theorem pair_of_matched_frame_original_member_toral_actualField
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) {n : ℕ} [NeZero f]
    (hp : p.Prime) (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1)
    (j : Matrix.SpecialLinearGroup (Fin 3) GGL →* ModGL (langTag t) GGL)
    (σ : Fin 3 → Fin 3 → Fin (langTag t).rank → ℤ)
    (hpair : CFSG.RankThree.PartOne.KF4.IsA2Frame j σ)
    {I₀ I₁ : Type*} [Finite I₀] [Finite I₁]
    (a₀ : I₀ → Fin (langTag t).rank → GGLˣ)
    (a₁ : I₁ → Fin (langTag t).rank → GGLˣ)
    (htor₀ : ∀ i, rootDiagUnit (langTag t) (a₀ i) ∈ M.D.torus)
    (htor₁ : ∀ i, rootDiagUnit (langTag t) (a₁ i) ∈ M.D.torus)
    (ha₀ : ∀ i, ∃ k : ℕ, a₀ i ^ (p ^ k) = 1)
    (ha₁ : ∀ i, ∃ k : ℕ, a₁ i ^ (p ^ k) = 1)
    (hk₀ : famKernel (Set.range a₀) = {σ 0 1, -σ 0 1})
    (hk₁ : famKernel (Set.range a₁) = {σ 1 2, -σ 1 2})
    (ψ : ↥M.D.Γ →* G) (hψinj : Function.Injective ψ) (hX : ψ.range = X)
    (β : ↥Bs →* ModGL (langTag t) GGL)
    (hpres : ∀ (b : ↥Bs) (y : ↥M.D.Γ), β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹ ∈ M.D.Γ)
    (hcompat : ∀ (b : ↥Bs) (y : ↥M.D.Γ),
      ψ ⟨β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹, hpres b y⟩ =
        (b : G) * ψ y * (b : G)⁻¹)
    (r s : MulAut ↥Bs)
    (hH₀ : ∀ z : ModGL (langTag t) GGL,
      z ∈ Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₀ i)) ↔
        ∃ b : ↥Bs, r b = b ∧ β b = z)
    (hH₁ : ∀ z : ModGL (langTag t) GGL,
      z ∈ Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)) ↔
        ∃ b : ↥Bs, s b = b ∧ β b = z) :
    ∃ θG : Su (actualQuadraticSubfield f) 2 f 3 →* G,
      Function.Injective θG ∧ θG.range ≤ X ∧
      (B12 (actualQuadraticSubfield f) 2 f).map θG = ggRankOneIn X Bs r ∧
      (B23 (actualQuadraticSubfield f) 2 f).map θG = ggRankOneIn X Bs s ∧
      UnitaryBlockStandardPair (actualQuadraticSubfield f) 2 f θG.range
        (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  obtain ⟨ρ, hρ⟩ := CFSG.StandardType.GGFinModel.exists_frobRootMap_model M
  have hrev := CFSG.StandardType.GGFinModel.reversal_frame_of_toral_kernels
    M hρ hp hp2 hplus hpair (Set.range a₀) (Set.range a₁)
    (fun a ha => by obtain ⟨i, rfl⟩ := ha; exact htor₀ i)
    (fun a ha => by obtain ⟨i, rfl⟩ := ha; exact htor₁ i) hk₀ hk₁
  exact pair_of_matched_frame_original_member_actualField M (n := n)
    hp hp2 (Or.inr hplus) ρ hρ j σ hpair hrev a₀ a₁ ha₀ ha₁ hk₀ hk₁
    ψ hψinj hX β hpres hcompat r s hH₀ hH₁

end CFSG.StandardType.ResidualA2Pair

end

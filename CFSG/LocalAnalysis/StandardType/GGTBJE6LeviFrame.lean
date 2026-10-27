module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviCore
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnola
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviSplitModel
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeylPTorsion
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralExcAdj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

@[expose] def GGE6LeviFrame (p : ℕ)
    [NeZero p] {R : Type} [Group R] (E : Subgroup R) : Prop :=
  ∃ (Lf : Type) (_ : Field Lf) (ζ : Lfˣ) (hζ : ζ ^ p = 1)
    (ι₀ : Multiplicative (Fin Tag.E6.rank → ZMod p) →* R)
    (nk : Fin Tag.E6.rank → R) (m : ℕ)
    (wt : GGTorusTorWit m 6 R (E.map (MulAut.conj : R →* MulAut R))),
    orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = E ∧
    (∀ k s, nk k * ι₀ (Multiplicative.ofAdd s) * (nk k)⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p (simple .E6 k) s))) ∧
    (∀ k, wt.n k = nk k) ∧ wt.Holds CartanMatrix.E₆ CoxeterMatrix.E₆ ∧
    ∀ t : Fin Tag.E6.rank → ZMod p, ι₀ (Multiplicative.ofAdd t) ≠ 1 →
      ∀ Y : Subgroup R, IsComponentOf Y
        (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set R)) →
      ∃ i : KernelComponent
          (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E6 p t))),
        (∀ s : Fin Tag.E6.rank → ZMod p,
          (∀ γ ∈ componentRoots
              (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E6 p t))) i,
            ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .E6 p s j = 0) →
          ι₀ (Multiplicative.ofAdd s) ∈ Subgroup.centralizer (Y : Set R)) ∧
        ∀ c ∈ componentRoots
            (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E6 p t))) i,
          ∃ y ∈ Y, ∀ s, y * ι₀ (Multiplicative.ofAdd s) * y⁻¹ =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p (rootReflection c) s))

theorem e6Split_frame
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hq : p ∣ Nat.card K - 1) :
    ∃ (ζ : Kˣ) (hζ : ζ ^ p = 1)
      (ι₀ : Multiplicative (Fin Tag.E6.rank → ZMod p) →* adjointGroup .E6 K),
      orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = TableBExc.torusPow .E6 K p ∧
      (∀ s, (ι₀ (Multiplicative.ofAdd s) : ModGL .E6 K) = ExcFrames.frameDiag ζ hζ s) ∧
      (∀ k s, weylElement .E6 K k * ι₀ (Multiplicative.ofAdd s) * (weylElement .E6 K k)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p (simple .E6 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer ((TableBExc.torusPow .E6 K p) : Set (adjointGroup .E6 K)),
        ∃ v : WeylGroup .E6, ∀ s,
          g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p v s))) := by
  classical
  have hp : p.Prime := Fact.out
  have hpk : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hfullp : ∀ a : Fin Tag.E6.rank → Kˣ, (∀ i, a i ^ p = 1) →
      rootDiagUnit .E6 a ∈ torusGroup .E6 K :=
    TableBExc.fullp_E6 hp.one_lt
      ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
  let ι := ExcFrames.frameHomP hfullp ζ hζ (1 : adjointGroup .E6 K)
  have hιcoe : ∀ s : Fin Tag.E6.rank → ZMod p,
      (ι (Multiplicative.ofAdd s) : ModGL .E6 K) = ExcFrames.frameDiag ζ hζ s := by
    intro s
    simp [ι, ExcFrames.frameHomP]
  have hdet : IsUnit ((Tag.E6.symmetrizedCartan.det : ℤ) : ZMod p) :=
    StepTwoToralExc.isUnit_det_symmetrizedCartan_E6 hp3
  have hι : Function.Injective ι := by
    intro s t h
    have hco := congrArg Subtype.val h
    rw [← ofAdd_toAdd s, ← ofAdd_toAdd t, hιcoe, hιcoe] at hco
    exact Multiplicative.toAdd.injective (ExcFrames.frameDiag_injective hζo hζ hdet hco)
  have hrange : ι.range = TableBExc.torusPow .E6 K p := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      apply ExcFrames.mem_torusPow_iff_coe.mpr
      rw [← ofAdd_toAdd s, hιcoe]
      exact ExcFrames.frameDiag_mem_of_fullp hfullp ζ hζ _
    · intro hg
      obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_of_mem hζo hζ hdet
        (ExcFrames.mem_torusPow_iff_coe.mp hg)
      exact ⟨Multiplicative.ofAdd s, Subtype.ext ((hιcoe s).trans hs)⟩
  have hsimple : ∀ k s, weylElement .E6 K k * ι (Multiplicative.ofAdd s) *
      (weylElement .E6 K k)⁻¹ =
      ι (Multiplicative.ofAdd (TableBExc.torusAct .E6 p (simple .E6 k) s)) := by
    intro k s
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe, weylElement]
    rw [← canonicalRep_simple (coxeterSystem .E6) K k]
    exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ (simple .E6 k) s
  have hnorm : ∀ g ∈ Subgroup.normalizer
      ((TableBExc.torusPow .E6 K p) : Set (adjointGroup .E6 K)),
      ∃ v : WeylGroup .E6, ∀ s, g * ι (Multiplicative.ofAdd s) * g⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E6 p v s)) := by
    intro g hg
    obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes
      (Subgroup.mem_normalizer_iff.mp hg)
    refine ⟨w, fun s => ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe]
    rw [hw _ (ExcFrames.frameDiag_mem_of_fullp hfullp ζ hζ s)]
    exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ w s
  exact ⟨ζ, hζ, ι, hζo, hι, hrange, hιcoe, hsimple, hnorm⟩

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
import CFSG.LieType.ChevTwo.OppCl.AutLiftsUnitary
import CFSG.RankThree.PartOne.SEITZ2.SU3Pair
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1UCore
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTorus
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartOne.CTP.SeitzFineU5
import CFSG.RankThree.PartOne.CTP.StdSub
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.KF.U4Model
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

private theorem p9uFU_le_normalizer_of_actsDiagonally
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (hrange : ψ.range = X)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs) :
    Bs ≤ Subgroup.normalizer (X : Set G) := by
  intro b hb
  obtain ⟨g, -, hunit⟩ := hd b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← hrange] at hx
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', -, hy'⟩ := hunit.2 x'
    rw [← hrange]
    show b * ψ x' * b⁻¹ ∈ ψ.range
    exact ⟨y', hy'.symm⟩
  · let f : G →* G := MulAut.conj b
    have hf : Function.Injective f := (MulAut.conj b).injective
    have hcard : Nat.card ↥(Subgroup.map f X) = Nat.card ↥X :=
      Subgroup.card_map_of_injective (K := X) (f := f) hf
    exact le_of_eq hcard.symm

theorem qtwoDL1_unitAut_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ) (hrange : ψ.range = X)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    (hfull : Nat.card ↥Bs = 3 ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))
    (φ : ↥Bs →* MulAut ↥X)
    (hφ : ∀ (b : ↥Bs) (x : ↥X), ((φ b x : ↥X) : G) = (b : G) * (x : G) * (b : G)⁻¹)
    (α : MulAut ↥X) (hα : ∀ b : ↥Bs, α * φ b = φ b * α) (hα2 : α ^ 2 = 1) :
    α = 1 := by
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := by simpa using h.dvd
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp hdvd
  have hα' : ∀ (t : Su K 2 1 n) (d : Fin n → K),
      ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d →
        (∀ l, d l ^ 3 = 1) → (∀ a ∈ (∅ : Finset (Fin n)), ∀ b ∈ (∅ : Finset (Fin n)), d a = d b) →
          ∀ z : ↥X, (z : G) = ψ t → ∀ y : ↥X, α (z * y * z⁻¹) = z * α y * z⁻¹ := by
    intro t d htd hd3 _ z hz y
    have hBs : ψ t ∈ Bs := ggNSDiag_torus_le h hd t ⟨d, htd, by rw [hp3]; exact hd3⟩
    have hφz : ∀ w : ↥X, φ ⟨ψ t, hBs⟩ w = z * w * z⁻¹ := fun w => by
      apply Subtype.ext
      rw [hφ]
      simp [hz]
    have hc := congrArg (fun f : MulAut ↥X => f y) (hα ⟨ψ t, hBs⟩)
    simp only [MulAut.mul_apply] at hc
    rw [hφz, hφz] at hc
    exact hc
  obtain ⟨s, hs, -, hsact⟩ := qtwoDL1_unitChart_fixTorus hK h hrange
    (J := (∅ : Finset (Fin n))) (Or.inl rfl) α hα' (k := 1) (by simpa using hα2)
  have hs1 : s = 1 := by
    have hmat := (mem_coordBlockSU_iff.mp hs)
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [hmat i j (Or.inl (Finset.notMem_empty i))]
    simp [Matrix.one_apply]
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  have hy : (y : G) ∈ ψ.range := by rw [hrange]; exact y.2
  obtain ⟨u, hu⟩ := hy
  rw [hsact u y hu.symm, hs1, one_mul, inv_one, mul_one, hu]
  rfl

theorem qtwoDL1_invFix_unit {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ) (hrange : ψ.range = X)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    (hfull : Nat.card ↥Bs = 3 ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))
    {t : G} (htC : t ∈ Subgroup.centralizer (Bs : Set G))
    (htN : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t ^ 2 = 1) :
    t ∈ Subgroup.centralizer (X : Set G) := by
  have hBN : Bs ≤ Subgroup.normalizer (X : Set G) :=
    p9uFU_le_normalizer_of_actsDiagonally hrange hd
  let φ : ↥Bs →* MulAut ↥X :=
    (Subgroup.normalizerMonoidHom X).comp (Subgroup.inclusion hBN)
  have hφ : ∀ (b : ↥Bs) (x : ↥X),
      ((φ b x : ↥X) : G) = (b : G) * (x : G) * (b : G)⁻¹ := by
    intro b x
    exact Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨(b : G), hBN b.2⟩ x
  let α : MulAut ↥X := Subgroup.normalizerMonoidHom X ⟨t, htN⟩
  have hαval : ∀ x : ↥X, ((α x : ↥X) : G) = t * (x : G) * t⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨t, htN⟩ x
  have hα2 : α ^ 2 = 1 := by
    have h2 : (⟨t, htN⟩ : Subgroup.normalizer (X : Set G)) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ht2]
    change (Subgroup.normalizerMonoidHom X ⟨t, htN⟩) ^ 2 = 1
    rw [← map_pow, h2, map_one]
  have hα : ∀ b : ↥Bs, α * φ b = φ b * α := by
    intro b
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [MulAut.mul_apply, MulAut.mul_apply, hαval, hφ, hφ, hαval]
    have hb : (b : G) * t = t * (b : G) :=
      Subgroup.mem_centralizer_iff.mp htC (b : G) b.2
    have hb' : t * (b : G) = (b : G) * t := hb.symm
    have hb'' : (b : G)⁻¹ * t⁻¹ = t⁻¹ * (b : G)⁻¹ := by
      rw [← mul_inv_rev, hb', mul_inv_rev]
    calc t * ((b : G) * (x : G) * (b : G)⁻¹) * t⁻¹
        = (t * (b : G)) * (x : G) * ((b : G)⁻¹ * t⁻¹) := by group
      _ = ((b : G) * t) * (x : G) * (t⁻¹ * (b : G)⁻¹) := by rw [hb', hb'']
      _ = (b : G) * (t * (x : G) * t⁻¹) * (b : G)⁻¹ := by group
  have hα1 : α = 1 := qtwoDL1_unitAut_centralizer hK h hrange hd hfull φ hφ α hα hα2
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxα : α ⟨x, hx⟩ = (⟨x, hx⟩ : ↥X) := by rw [hα1, MulAut.one_apply]
  have hval : ((α ⟨x, hx⟩ : ↥X) : G) = t * x * t⁻¹ := hαval ⟨x, hx⟩
  have h2 : t * x * t⁻¹ = x := by rw [← hval, hxα]
  have h3 : t * x = x * t := by
    have := congrArg (· * t) h2
    simpa [mul_assoc] using this
  exact h3.symm

end CFSG.StandardType.QTwo

end

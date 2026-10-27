module

public import CFSG.RankThree.PartOne.KE.E6TwFourData
public import CFSG.RankThree.PartOne.KE.E6TwFourFinal
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3TwActor
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Basic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitComponentEmbed
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.GH74.Statements
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.S8.Statements

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open CFSG.RankThree.E6 (e6Index e6Rho)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

namespace TwE6Nonsplit


theorem e6_tw_four_components_dvd (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ x, weylQuotientHom .E6 L ⟨n, hnm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x) :
    ∀ x : twistedE6RootGroup K σ, orderOf x = p →
      ∀ X : Subgroup (twistedE6RootGroup K σ),
        IsComponentOf X (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))) →
          p ∣ Nat.card X := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ :=
    e6_tw_four_frame K hf hK σ hσ hp hp3 hpq L n hnm hnW
  intro x hx X hX
  set A : Subgroup (twistedE6RootGroup K σ) :=
    Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)) with hAdef
  have hXA : IsComponentOf X A := hX
  have hxA : x ∈ A := by
    rw [hAdef]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let xA : ↥A := ⟨x, hxA⟩
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ψ, hψinj, hψ, hψb⟩ := e6_tw_four_perx K hf hK σ hσ hp hp3 hordq hΦ L n hnm hnW
    g0 hg0C hg0 hperf hT hx c hh
  set h : ModGL Tag.E6 L := g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0 with hhdef
  have hhT : h ∈ twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)) := hh
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hhT).1
  rcases (rootCharKernel b).eq_empty_or_nonempty with hker | hne
  ·
    have hFr : ∀ z, iterateFrobenius L ℓ f z = z ^ (ℓ ^ f) :=
      fun z => iterateFrobenius_def ℓ f z
    have hordh : orderOf h = p := by
      have e1 : orderOf h = orderOf (twE6Emb K σ L (c * x * c⁻¹)) := by
        rw [hhdef]
        have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
          (twE6Emb K σ L (c * x * c⁻¹))
        simpa [MulAut.conj_apply] using this
      have e2 : orderOf (twE6Emb K σ L (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
        orderOf_injective (twE6Emb K σ L) (twE6Emb_injective) _
      have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
        simpa [MulAut.conj_apply] using this
      rw [e1, e2, e3, hx]
    have hbp : orderOf (rootDiagUnit Tag.E6 b) = p := by rw [← hb]; exact hordh
    have hap : ∀ i, b i ^ p = 1 := pow_eq_one_of_orderOf_rootDiagUnit hbp
    have hb1 : b ≠ 1 := ne_one_of_orderOf_rootDiagUnit hp hbp
    have hbT : b ∈ fixedCharTuples (e6SM (-1)) (iterateFrobenius L ℓ f) := by
      have hh' : h ∈ (fixedCharTuples (e6SM (-1)) (iterateFrobenius L ℓ f)).map
          (rootDiagUnitHom Tag.E6 L) := by
        rw [← hT]
        exact hhT
      obtain ⟨b', hb', hb'e⟩ := Subgroup.mem_map.1 hh'
      have hb'b : b' = b := rootDiagUnit_injective (hb'e.trans hb)
      rwa [hb'b] at hb'
    have hstab := e6TwFour_stab_of_fixed (iterateFrobenius L ℓ f) hFr hp hp3 hordq hΦ hbT hap hb1
    have htoral : toralCentralizer Tag.E6 L b = torusGroup Tag.E6 L := by
      rw [toralCentralizer_eq_sup (τ := Tag.E6) (K := L) b hstab, hker]
      simp [rootSpan]
    have hmem : ∀ y : ↥A, ψ y ∈ torusGroup Tag.E6 L := by
      intro y
      have hψy : ψ y = g0⁻¹ * twE6Emb K σ L (c * (y : twistedE6RootGroup K σ) * c⁻¹) * g0 :=
        hψ y
      have hadj : ψ y ∈ adjointGroup Tag.E6 L := by
        rw [hψy]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg0C) (twE6Emb_mem _))
          hg0C
      have hcen : ψ y ∈ Subgroup.centralizer ({rootDiagUnit Tag.E6 b} : Set (ModGL Tag.E6 L)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        have hψx : ψ xA = rootDiagUnit Tag.E6 b := (hψ xA).trans hb
        have hyx : y * xA = xA * y :=
          Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
        calc rootDiagUnit Tag.E6 b * ψ y = ψ xA * ψ y := by rw [hψx]
          _ = ψ (xA * y) := by rw [← map_mul]
          _ = ψ (y * xA) := by rw [hyx]
          _ = ψ y * ψ xA := by rw [← map_mul]
          _ = ψ y * rootDiagUnit Tag.E6 b := by rw [hψx]
      exact htoral ▸ Subgroup.mem_inf.2 ⟨hadj, hcen⟩
    have hcomm : ∀ a a' : ↥A, a * a' = a' * a := by
      intro a a'
      apply hψinj
      rw [map_mul, map_mul]
      obtain ⟨u, hu⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hmem a)
      obtain ⟨v, hv⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hmem a')
      rw [hu, hv, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    haveI : Group.IsSolvable ↥A := Group.isSolvable_of_comm hcomm
    exact (CFSG.StandardType.ExcNonsplit.not_isComponentOf_of_isSolvable hXA).elim
  ·
    obtain ⟨hq, hnc⟩ := e6_tw_four_derived K hf hK σ hσ hp hp3 hordq hΦ L n hnm hnW g0 hg0C
      hg0 hperf hT hx c hh hb.symm hne
    have hpd : p ∣ Nat.card ↥⁅A, A⁆ := (hp.dvd_iff_not_coprime).2 hnc
    exact F4Nonsplit.dvd_card_of_isComponentOf_of_quasisimple hq hpd hXA

theorem dvd_card_of_isComponentOf_twE6_of_phiFour {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 4).eval ((2 ^ f : ℕ) : ℤ))
    {a : twistedE6RootGroup K σ} (ha : orderOf a = p)
    {X : Subgroup (twistedE6RootGroup K σ)}
    (hX : IsComponentOf X (Subgroup.centralizer ({a} : Set (twistedE6RootGroup K σ)))) :
    p ∣ Nat.card X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hpq : (p : ℤ) ∣ (((2 ^ f : ℕ) : ℤ) ^ 2 + 1) := by
    simpa [exhaustionPhi] using hpf
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hcm := canonicalRep_mem_monomialSubgroup (AlgebraicClosure K) (e6F4U * e6NegRho)
  have hπ : weylQuotientHom Tag.E6 (AlgebraicClosure K)
      ⟨canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) (e6F4U * e6NegRho), hcm⟩ =
        e6F4U * e6NegRho :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep (e6F4U * e6NegRho))
  have hnW : ∀ x, weylQuotientHom Tag.E6 (AlgebraicClosure K)
      ⟨canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) (e6F4U * e6NegRho), hcm⟩ • x =
        e6SM (-1) *ᵥ permLattice e6Rho x := fun x => by
    rw [hπ]
    exact e6TwFour_weylImage x
  exact e6_tw_four_components_dvd (ℓ := 2) K hf hK σ hσ hp hp3 hpq (AlgebraicClosure K) _ hcm
    hnW a ha X hX

end TwE6Nonsplit

end CFSG.StandardType

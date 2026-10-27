module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Walter.Defs
public import Certificates.Certificate10027
public import Certificates.Certificate10095
public import Certificates.Certificate10095Base
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10104
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate1016Base
public import Certificates.Certificate2051
public import Certificates.Certificate2053
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2130
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate3085Base
public import Certificates.Certificate9201

public section

namespace CFSG.StandardType.TwE6MaxEleven

open CFSG.Assembly.LowTwoRank CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3

@[expose] def twE6Ord : ℕ := 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19

@[expose] def twE6Primes : List (ℕ × ℕ) :=
  [(2, 36), (3, 9), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1)]

@[expose] def filterCheckE (t : StatedLieTag) (n p f o : ℕ) : Bool :=
  decide (11 ∣ o → o < twE6Ord → ¬ 3 ^ 6 ∣ o ∨ o = 9196830720 ∨ o = 25015379558400)

@[expose] def sporadicCheckE (s : TauCeti.SporadicName) : Bool :=
  decide (s ≠ .Th → s ≠ .M → sporadicCard s ∣ twE6Ord → 11 ∣ sporadicCard s →
    ¬ 3 ^ 6 ∣ sporadicCard s ∨ sporadicCard s = 9196830720 ∨
      sporadicCard s = 25015379558400 ∨ s = .Suz ∨ s = .Fi22)

theorem primes_twE6Ord : ∀ p : ℕ, p.Prime → p ∣ twE6Ord →
    ∃ e, (p, e) ∈ twE6Primes ∧ ¬ p ^ (e + 1) ∣ twE6Ord := by
  refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
  simp only [twE6Primes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  norm_num

theorem lieSearch_twE6 : lieSearchV twE6Primes twE6Ord filterCheckE = true := by
  decide +kernel

theorem filterE_alt {n : ℕ} (hn : 5 ≤ n) (hord : n.factorial / 2 ∣ twE6Ord) :
    ¬ 3 ^ 6 ∣ n.factorial / 2 := by
  have h5 : ¬ 5 ^ 3 ∣ twE6Ord := by decide +kernel
  have hn14 : n ≤ 14 := by
    by_contra hle
    push Not at hle
    have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h125 : 5 ^ 3 ∣ n.factorial :=
      (by decide +kernel : 5 ^ 3 ∣ Nat.factorial 15).trans (Nat.factorial_dvd_factorial hle)
    have hnfact : n.factorial = 2 * (n.factorial / 2) := (Nat.mul_div_cancel' h2).symm
    have h125' : 5 ^ 3 ∣ 2 * (n.factorial / 2) := hnfact ▸ h125
    exact h5 ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h125').trans hord)
  interval_cases n <;> decide +kernel

theorem sporadicCheckE_true : ∀ s : TauCeti.SporadicName, sporadicCheckE s = true := by
  decide +kernel

theorem not_two_pow_sixtySeven_dvd : ¬ 2 ^ 67 ∣ twE6Ord := by decide +kernel

theorem not_thirtySeven_dvd : ¬ 37 ∣ twE6Ord := by decide +kernel

theorem not_fortyOne_dvd : ¬ 41 ∣ twE6Ord := by decide +kernel

theorem not_twentyNine_dvd : ¬ 29 ∣ twE6Ord := by decide +kernel

theorem not_card_Th_dvd : ¬ 90745943887872000 ∣ twE6Ord := by decide +kernel

theorem not_eleven_dvd_tits : ¬ 11 ∣ 35942400 := by decide +kernel

end CFSG.StandardType.TwE6MaxEleven

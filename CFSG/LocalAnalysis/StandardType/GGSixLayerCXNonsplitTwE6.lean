module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitCentralMarking
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Arith
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Cover
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Cyclic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6FourDvd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Label
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6SixDvd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Tag
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Ten
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6ThreeDvd
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 LayerSixE


namespace TwE6Nonsplit

private noncomputable abbrev TwE6Ad (f : ℕ) : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
  graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)

private theorem ggNonsplitDvdAt_twE6_ad_of_row {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpC : p ∣ Nat.card ↥(TwE6Ad f)) {m : ℕ}
    (hm : m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 12 ∨ m = 18)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi m).eval ((2 ^ f : ℕ) : ℤ)) :
    ExcNonsplit.GGNonsplitDvdAt ↥(TwE6Ad f) p := by
  haveI : Finite (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := finite_modGL
  obtain ⟨hKcard, hσapply, hring, -⟩ := twistedE6RootGroup_bridge f hf
  intro a ha X hX
  by_cases ha1 : a = 1
  · subst ha1
    rw [ExcNonsplit.centralizer_one_eq_top] at hX
    obtain rfl := ExcNonsplit.eq_top_of_isComponentOf_top
      (isQuasisimple_graphFixedRootGroup f hf) hX
    rwa [Subgroup.card_top]
  · have : Fact p.Prime := ⟨hp⟩
    have hao : orderOf a = p := orderOf_eq_prime ha ha1
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · have hrow : ∀ (a : ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          orderOf a = p → ∀ (X : Subgroup ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(twistedE6RootGroup
            (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)))) →
          p ∣ Nat.card X :=
        fun a ha X hX => dvd_card_of_isComponentOf_twE6_of_phiThree
          (K := GaloisField 2 (2 * f)) hf hKcard
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp3 hpf ha hX
      unfold twistedE6RootGroup at hrow
      rw [hring] at hrow
      exact hrow a hao X hX
    · have hrow : ∀ (a : ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          orderOf a = p → ∀ (X : Subgroup ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(twistedE6RootGroup
            (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)))) →
          p ∣ Nat.card X :=
        fun a ha X hX => dvd_card_of_isComponentOf_twE6_of_phiFour
          (K := GaloisField 2 (2 * f)) hf hKcard
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp3 hpf ha hX
      unfold twistedE6RootGroup at hrow
      rw [hring] at hrow
      exact hrow a hao X hX
    · have hrow : ∀ (a : ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          orderOf a = p → ∀ (X : Subgroup ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(twistedE6RootGroup
            (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)))) →
          p ∣ Nat.card X :=
        fun a ha X hX => dvd_card_of_isComponentOf_twE6_of_phiSix
          (K := GaloisField 2 (2 * f)) hf hKcard
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp3 hpf ha hX
      unfold twistedE6RootGroup at hrow
      rw [hring] at hrow
      exact hrow a hao X hX
    · have hreg : ∀ (a : ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          orderOf a = p → ∀ (X : Subgroup ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          ¬ IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(twistedE6RootGroup
            (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)))) :=
        fun a ha X => not_isComponentOf_centralizer_twE6_of_dvd_phi_regular hf hKcard
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp3 (Or.inl rfl) hpf ha
      unfold twistedE6RootGroup at hreg
      rw [hring] at hreg
      exact absurd hX (hreg a hao X)
    · have hreg : ∀ (a : ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          orderOf a = p → ∀ (X : Subgroup ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          ¬ IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(twistedE6RootGroup
            (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)))) :=
        fun a ha X => not_isComponentOf_centralizer_twE6_of_dvd_phi_regular hf hKcard
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp3
          (Or.inr (Or.inl rfl)) hpf ha
      unfold twistedE6RootGroup at hreg
      rw [hring] at hreg
      exact absurd hX (hreg a hao X)
    · have hreg : ∀ (a : ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          orderOf a = p → ∀ (X : Subgroup ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
          ¬ IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(twistedE6RootGroup
            (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)))) :=
        fun a ha X => not_isComponentOf_centralizer_twE6_of_dvd_phi_regular hf hKcard
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp3
          (Or.inr (Or.inr rfl)) hpf ha
      unfold twistedE6RootGroup at hreg
      rw [hring] at hreg
      exact absurd hX (hreg a hao X)

private theorem ggNonsplitCoreAt_twE6_ad_of_ten {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 < p)
    (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 10).eval ((2 ^ f : ℕ) : ℤ))
    (hpC : p ∣ Nat.card ↥(TwE6Ad f)) :
    ExcNonsplit.GGNonsplitCoreAt ↥(TwE6Ad f) p := by
  haveI : Finite (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := finite_modGL
  obtain ⟨hKcard, hσapply, hring, hgroup⟩ := twistedE6RootGroup_bridge f hf
  unfold twistedE6RootGroup at hgroup
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  refine ExcNonsplit.ggNonsplitCoreAt_of_cyclic_components hp hp2 hp3
    (isQuasisimple_graphFixedRootGroup f hf) hpC ?_ ?_ ?_
  · have hcyc : ∀ a b : ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)),
        a ^ p = 1 → b ^ p = 1 → a * b = b * a → a ≠ 1 → b ∈ Subgroup.zpowers a :=
      fun a b ha hb hab ha1 => mem_zpowers_twE6_of_ten (K := GaloisField 2 (2 * f)) hf hKcard
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp5 hpf a b ha hb hab ha1
    unfold twistedE6RootGroup at hcyc
    rw [hgroup] at hcyc
    exact hcyc
  · intro X hX lab hlab hc hM
    exact not_halfSplit_of_isComponentOf_top_ad hf hq1 hq2 hX hlab hc hM
  · intro a ha X hX _
    have hmark : ∀ (a : ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
        orderOf a = p → ∀ (X : Subgroup ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
        IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(twistedE6RootGroup
          (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)))) →
        ¬ GGNbrClauseFiveMarking p a X :=
      fun a ha X hX => not_ggNbrClauseFiveMarking_of_isComponentOf_twE6_of_ten
        (K := GaloisField 2 (2 * f)) hf hKcard
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp5 hpf hq1 hq2 a ha X hX
    unfold twistedE6RootGroup at hmark
    rw [hgroup] at hmark
    exact hmark a ha X hX

private theorem ggNonsplitCoreAt_twE6_sc_of_ten {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 < p)
    (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 10).eval ((2 ^ f : ℕ) : ℤ))
    (hpC : p ∣ Nat.card ↥(TwE6Ad f)) :
    ExcNonsplit.GGNonsplitCoreAt (twistedE6Group 2 f) p := by
  obtain ⟨hKcard, hσapply, hring, hgroup⟩ := twistedE6RootGroup_bridge f hf
  unfold twistedE6RootGroup at hgroup
  obtain ⟨π, hπ, hker, -, -⟩ := LayerSixE.exists_model_twistedE6 hf
  haveI : Finite ↥(e6Data_valid.minGroup (GaloisField 2 (2 * f))) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hkerc : π.ker ≤ Subgroup.center (twistedE6Group 2 f) := hker.le
  have hker3 : ∀ z ∈ π.ker, z ^ 3 = 1 := fun z hz => ker_pow_three hf hker hz
  have hcop : Nat.gcd 3 p = 1 := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  have hker1 : ∀ z : twistedE6Group 2 f, π z = 1 → z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have h3 := hker3 z hz
    have h := pow_gcd_eq_one.mpr ⟨h3, hzp⟩
    rwa [hcop, pow_one] at h
  refine ExcNonsplit.ggNonsplitCoreAt_of_cyclic_components hp hp2 hp3
    (CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 (p := 2) (f := f) hf)
    (hpC.trans (Subgroup.card_dvd_of_surjective hπ)) ?_ ?_ ?_
  · have hcyc : ∀ a b : ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)),
        a ^ p = 1 → b ^ p = 1 → a * b = b * a → a ≠ 1 → b ∈ Subgroup.zpowers a :=
      fun a b ha hb hab ha1 => mem_zpowers_twE6_of_ten (K := GaloisField 2 (2 * f)) hf hKcard
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp5 hpf a b ha hb hab ha1
    unfold twistedE6RootGroup at hcyc
    rw [hgroup] at hcyc
    exact fun a b ha hb hab ha1 =>
      ExcNonsplit.mem_zpowers_of_central_cover π hp hp3 hker3 hcyc ha hb hab ha1
  · intro X hX lab hlab hc hM
    exact not_halfSplit_of_isComponentOf_top_sc hf hq1 hq2 hX hlab hc hM
  · intro a ha X hX _ hmark
    have hmarkC : ∀ (a : ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
        orderOf a = p → ∀ (X : Subgroup ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))),
        IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(twistedE6RootGroup
          (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)))) →
        ¬ GGNbrClauseFiveMarking p a X :=
      fun a ha X hX => not_ggNbrClauseFiveMarking_of_isComponentOf_twE6_of_ten
        (K := GaloisField 2 (2 * f)) hf hKcard
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp5 hpf hq1 hq2 a ha X hX
    unfold twistedE6RootGroup at hmarkC
    rw [hgroup] at hmarkC
    have hπa1 : π a ≠ 1 := by
      intro h1
      have ha1 : a = 1 := hker1 a h1 (by rw [← ha]; exact pow_orderOf_eq_one a)
      rw [ha1, orderOf_one] at ha
      exact hp.one_lt.ne ha
    have hπo : orderOf (π a) = p :=
      orderOf_eq_prime (by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]) hπa1
    have hX' := E6Nonsplit.isComponentOf_map_centralizer_of_central_cover π hπ hkerc a hX
    have hnorm : ∀ j ∈ X, a⁻¹ * j * a ∈ X := by
      intro j hj
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hX.1 hj)
      rwa [mul_assoc, hc, inv_mul_cancel_left]
    exact hmarkC (π a) hπo (X.map π) hX'
      (ExcNonsplit.ggNbrClauseFiveMarking_map_of_central π hkerc hnorm hmark)

end TwE6Nonsplit

theorem ggTwE6NonsplitCoreInput_holds : GGTwE6NonsplitCoreInput := by
  intro f p hf hp hp2 hq1 hq2
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hp3' : 3 < p := by
    have h2 := hp.two_le
    omega
  haveI : Finite (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := finite_modGL
  haveI : Finite ↥(e6Data_valid.minGroup (GaloisField 2 (2 * f))) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
  obtain ⟨hKcard, hσapply, hring, hgroup⟩ := TwE6Nonsplit.twistedE6RootGroup_bridge f hf
  unfold twistedE6RootGroup at hgroup
  by_cases hpC : p ∣ Nat.card ↥(TwE6Nonsplit.TwE6Ad f)
  · obtain ⟨m, hm, hpf⟩ := TwE6Nonsplit.exists_dvd_phi_of_dvd_card_twE6
      (K := GaloisField 2 (2 * f)) hf hKcard
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσapply hp hp2 (by
        unfold twistedE6RootGroup
        rw [hring]
        exact hpC)
    have hrow : ∀ {m : ℕ}, (m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 12 ∨ m = 18) →
        (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi m).eval ((2 ^ f : ℕ) : ℤ) →
        ExcNonsplit.GGNonsplitCoreAt (twistedE6Group 2 f) p ∧
          ExcNonsplit.GGNonsplitCoreAt ↥(TwE6Nonsplit.TwE6Ad f) p := by
      intro m hm hpf
      have hd := TwE6Nonsplit.ggNonsplitDvdAt_twE6_ad_of_row hf hp hp3' hpC hm hpf
      exact ⟨ExcNonsplit.ggNonsplitCoreAt_of_dvd
          (TwE6Nonsplit.ggNonsplitDvdAt_twE6_sc_of_ad (f := f) (p := p) hf hd),
        ExcNonsplit.ggNonsplitCoreAt_of_dvd hd⟩
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (E6Nonsplit.dvd_sub_one_of_dvd_phiOne (Nat.one_le_two_pow) hpf) hq1
    · exact absurd (E6Nonsplit.dvd_add_one_of_dvd_phiTwo hpf) hq2
    · exact hrow (Or.inl rfl) hpf
    · exact hrow (Or.inr (Or.inl rfl)) hpf
    · exact hrow (Or.inr (Or.inr (Or.inl rfl))) hpf
    · exact hrow (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hpf
    · have hp5 : 5 < p :=
        TwE6Nonsplit.five_lt_of_dvd_phiTen hp hp2 hp3 Nat.one_le_two_pow hq2 hpf
      exact ⟨TwE6Nonsplit.ggNonsplitCoreAt_twE6_sc_of_ten hf hp hp5 hq1 hq2 hpf hpC,
        TwE6Nonsplit.ggNonsplitCoreAt_twE6_ad_of_ten hf hp hp5 hq1 hq2 hpf hpC⟩
    · exact hrow (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hpf
    · exact hrow (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hpf
  · have hsc : ExcNonsplit.GGNonsplitCoreAt (twistedE6Group 2 f) p :=
      ExcNonsplit.ggNonsplitCoreAt_of_not_dvd hp hp2 hp3
        (TwE6Nonsplit.not_dvd_card_twE6_sc_of_ad hf hp hp3 hpC)
        (fun X hX lab hlab hc hM =>
          TwE6Nonsplit.not_halfSplit_of_isComponentOf_top_sc hf hq1 hq2 hX hlab hc hM)
    have had : ExcNonsplit.GGNonsplitCoreAt ↥(TwE6Nonsplit.TwE6Ad f) p :=
      ExcNonsplit.ggNonsplitCoreAt_of_not_dvd hp hp2 hp3 hpC
        (fun X hX lab hlab hc hM =>
          TwE6Nonsplit.not_halfSplit_of_isComponentOf_top_ad hf hq1 hq2 hX hlab hc hM)
    exact ⟨hsc, had⟩

theorem ggNonsplitTag_twistedE6 : GGNonsplitTag .twistedE6 :=
  ggNonsplitTag_twistedE6_of_core ggTwE6NonsplitCoreInput_holds

end CFSG.StandardType

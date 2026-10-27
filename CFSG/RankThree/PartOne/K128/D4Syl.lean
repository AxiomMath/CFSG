module

public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.RankThree.PartOne.K128.TorusCoord
public import CFSG.RankThree.PartOne.K128.ShapeEmbed
public import CFSG.RankThree.PartOne.K128.TorusShape
public import CFSG.RankThree.PartOne.K128.D4Arith
public import CFSG.RankThree.PartOne.KE.CTTwistedArith
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveTorus
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.PartOne.KE.FamilyArith
public import CFSG.RankThree.PartOne.KF.F128Syl
public import CFSG.RankThree.PartOne.KF.ClsExcE
public import CFSG.RankThree.PartOne.K128.FixCenter
public import CFSG.RankThree.PartOne.S11d.PSLRank
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KE.Statements
public import CFSG.RankThree.PartOne.KF.F128Cyclic
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.K1214
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne
open CFSG.Assembly (evenRank)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def conjEmb {C : Type*} [Group C] {M : Type*} [Group M] (ι : C →* M) (g0 : M) (c : C) :
    C →* M :=
  (MulAut.conj g0⁻¹).toMonoidHom.comp (ι.comp (MulAut.conj c).toMonoidHom)

theorem conjEmb_apply {C : Type*} [Group C] {M : Type*} [Group M] (ι : C →* M) (g0 : M) (c y : C) :
    conjEmb ι g0 c y = g0⁻¹ * ι (c * y * c⁻¹) * g0 := by
  simp [conjEmb, MulAut.conj_apply]

theorem conjEmb_injective {C : Type*} [Group C] {M : Type*} [Group M] {ι : C →* M}
    (hι : Function.Injective ι) (g0 : M) (c : C) : Function.Injective (conjEmb ι g0 c) := by
  intro a b hab
  rw [conjEmb_apply, conjEmb_apply] at hab
  have h1 := mul_left_cancel (mul_right_cancel hab)
  have h2 := hι h1
  have := congrArg (fun z => c⁻¹ * z * c) h2
  simpa [mul_assoc] using this

theorem ordProj_triality_split {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (h : p ∣ q - 1) :
    p ^ (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)).factorization p =
      p ^ ((q - 1) * (q - 1)).factorization p := by
  have hq1 : 1 ≤ q := by omega
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn₀ : (q - 1) * (q - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h' : (p : ℤ) ∣ (q : ℤ) - 1 := by
    have := Int.natCast_dvd_natCast.2 h
    rwa [Nat.cast_sub hq1, Nat.cast_one] at this
  have hsmall : ∀ m : ℤ, m = 1 ∨ m = 2 ∨ m = 3 → ¬ (p : ℤ) ∣ m := by
    intro m hm hd
    rcases hm with rfl | rfl | rfl
    · exact hpz.not_dvd_one hd
    · have : p ∣ 2 := by exact_mod_cast hd
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have : p ∣ 3 := by exact_mod_cast hd
      have := Nat.le_of_dvd (by norm_num) this
      omega
  have hq0 : ¬ (p : ℤ) ∣ q := by
    intro hd
    refine hsmall 1 (Or.inl rfl) ?_
    have e : (1 : ℤ) = q - ((q : ℤ) - 1) := by ring
    rw [e]
    exact dvd_sub hd h'
  have h1 : ¬ (p : ℤ) ∣ (q : ℤ) + 1 := by
    intro hd
    refine hsmall 2 (Or.inr (Or.inl rfl)) ?_
    have e : (2 : ℤ) = ((q : ℤ) + 1) - ((q : ℤ) - 1) := by ring
    rw [e]
    exact dvd_sub hd h'
  have h2 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 + q + 1 := by
    intro hd
    refine hsmall 3 (Or.inr (Or.inr rfl)) ?_
    have e : (3 : ℤ) = ((q : ℤ) ^ 2 + q + 1) - ((q : ℤ) - 1) * (q + 2) := by ring
    rw [e]
    exact dvd_sub hd (dvd_mul_of_dvd_left h' _)
  have h3 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 - q + 1 := by
    intro hd
    refine hsmall 1 (Or.inl rfl) ?_
    have e : (1 : ℤ) = ((q : ℤ) ^ 2 - q + 1) - ((q : ℤ) - 1) * q := by ring
    rw [e]
    exact dvd_sub hd (dvd_mul_of_dvd_left h' _)
  have h4 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := by
    intro hd
    refine hsmall 1 (Or.inl rfl) ?_
    have e : (1 : ℤ) = ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) - ((q : ℤ) - 1) * ((q + 1) * q ^ 2) := by
      ring
    rw [e]
    exact dvd_sub hd (dvd_mul_of_dvd_left h' _)
  refine CTTw.ordProj_eq_of_int_cofactor hn₀
    (R := (q : ℤ) ^ 12 * ((q : ℤ) + 1) ^ 2 * ((q : ℤ) ^ 2 + q + 1) ^ 2 *
      ((q : ℤ) ^ 2 - q + 1) ^ 2 * ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1)) ?_ ?_
  · simp only [Nat.cast_mul, CTTw.cast_pow_sub_one hq1, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
      Nat.cast_sub hq1]
    ring
  · intro hR
    rcases hpz.dvd_or_dvd hR with hR | hR
    · rcases hpz.dvd_or_dvd hR with hR | hR
      · rcases hpz.dvd_or_dvd hR with hR | hR
        · rcases hpz.dvd_or_dvd hR with hR | hR
          · exact hq0 (hpz.dvd_of_dvd_pow hR)
          · exact h1 (hpz.dvd_of_dvd_pow hR)
        · exact h2 (hpz.dvd_of_dvd_pow hR)
      · exact h3 (hpz.dvd_of_dvd_pow hR)
    · exact h4 hR

theorem d4T36d_one_eq {q : ℕ} (hq : 1 ≤ q) : d4T36d 1 q = q ^ 2 + q + 1 := by
  have h := d4T36d_cast (ε := 1) (Or.inl rfl) hq
  zify
  linarith

theorem d4T36d_neg_eq {q : ℕ} (hq : 1 ≤ q) : d4T36d (-1) q = q ^ 2 - q + 1 := by
  have h := d4T36d_cast (ε := -1) (Or.inr rfl) hq
  have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  zify [hle]
  linarith

theorem dvd_phiNat_of_dvd_cycloVal {p ℓ f m : ℕ} (hq : 1 ≤ ℓ ^ f)
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6) (h : (p : ℤ) ∣ cycloVal m ℓ f) :
    p ∣ phiNat m (ℓ ^ f) := by
  have hle : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  rcases hm with rfl | rfl | rfl | rfl
  · rw [cycloVal_one] at h
    simp only [phiNat]
    have h1 : (p : ℤ) ∣ ((ℓ ^ f - 1 : ℕ) : ℤ) := by rw [Nat.cast_sub hq]; exact h
    exact_mod_cast h1
  · rw [cycloVal_two] at h
    simp only [phiNat]
    exact_mod_cast h
  · rw [cycloVal_three] at h
    simp only [phiNat]
    exact_mod_cast h
  · rw [cycloVal_six] at h
    simp only [phiNat]
    have h1 : (p : ℤ) ∣ (((ℓ ^ f) ^ 2 - ℓ ^ f + 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hle]
      exact h
    exact_mod_cast h1

set_option linter.unusedSectionVars false

theorem sylowShape_D4_36 {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    SylowShape p 2 ((d4T36d ε (ℓ ^ f)).factorization p)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega : 1 ≤ f * 3)
    (by rw [hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨n, hn, w, hnW, hw, g0, -, -, -, hconj⟩ := d4T36_frame hf K hK σ hσ hε hp hp3 hpd L
  have hT := twistedTorus_D4_eq_map_of_weylImage (iterateFrobenius L ℓ f) hn w hnW (d4T36M ε) hw
  have hCcard := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl)
    σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
  have hd0 : d4T36d ε (ℓ ^ f) ≠ 0 := ((d4T36d_odd hε (by omega)).pos).ne'
  have hord : (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
      2 * (d4T36d ε (ℓ ^ f)).factorization p := by
    have h := d4T36_ordProj hε hp hp3 hq2 hpd
    rw [← hCcard] at h
    have h2 := Nat.pow_right_injective hp.two_le h
    rw [h2, Nat.factorization_mul hd0 hd0, Finsupp.add_apply]
    ring
  have hexp : ∀ x : Lˣ, x ^ (((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1) = 1 ↔
      x ^ (d4T36d ε (ℓ ^ f)) = 1 := fun x => by
    rw [← d4T36d_cast hε (by omega), zpow_natCast]
  refine sylowShape_of_embeds (L := L) (m₁ := d4T36d ε (ℓ ^ f)) (m₂ := d4T36d ε (ℓ ^ f)) hp hord
    (Nat.pow_succ_factorization_not_dvd hd0 hp) (Nat.pow_succ_factorization_not_dvd hd0 hp) ?_
  intro Q hQ
  obtain ⟨c, hc⟩ := hconj Q hQ
  have hθ := conjEmb_injective (triEmb_injective (K := K) (σ := σ) (L := L)) g0 c
  obtain ⟨Φ, hΦ, hΦy⟩ := exists_coord_embedding ((conjEmb (triEmb K σ L) g0 c).comp Q.subtype)
    (hθ.comp (Subgroup.subtype_injective Q))
    (fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f))
    (fun y => by
      rw [← hT]
      have := hc y y.2
      rwa [← conjEmb_apply] at this) 0 2
    (fun a ha b hb h0 h2 => eq_of_d4QCoord_eq_d4T36 hε (fun c => iterateFrobenius_def ℓ f c) ha hb
      (by
        rw [d4QCoord_apply, d4QCoord_apply]
        funext k
        fin_cases k
        · exact h0
        · exact h2))
  refine ⟨Φ, hΦ, fun y => ?_⟩
  obtain ⟨a, ha, -, h1, h2⟩ := hΦy y
  have := (mem_fixedCharTuples_d4T36 hε (fun c => iterateFrobenius_def ℓ f c) a).1 ha
  rw [h1, h2]
  exact ⟨(hexp _).1 this.2.2.2, (hexp _).1 this.2.2.1⟩

theorem sylowShape_D4_qplus {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) :
    SylowShape p 2 ((ℓ ^ f + 1).factorization p)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1 := by exact_mod_cast hpq
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega : 1 ≤ f * 3)
    (by rw [hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨g0, -, -, -, hconj⟩ := d4Q_frame hf K hK σ hσ hp (by omega) hpq' L
  have hT := d4Q_twistedTorus (L := L) (iterateFrobenius L ℓ f)
  have hCcard := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl)
    σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
  have hd1 : ℓ ^ f + 1 ≠ 0 := by omega
  have hd3 : (ℓ ^ f) ^ 3 + 1 ≠ 0 := by positivity
  have hv3 := factorization_cube_add_one hp5 hq2 hpq
  have hord : (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
      2 * (ℓ ^ f + 1).factorization p := by
    have h := d4Q_ordProj hp (by omega) hq2 hpq'
    rw [← hCcard] at h
    have h2 := Nat.pow_right_injective hp.two_le h
    rw [h2, Nat.factorization_mul hd1 hd3, Finsupp.add_apply, hv3]
    ring
  refine sylowShape_of_embeds (L := L) (m₁ := (ℓ ^ f) ^ 3 + 1) (m₂ := ℓ ^ f + 1) hp hord ?_
    (Nat.pow_succ_factorization_not_dvd hd1 hp) ?_
  · rw [← hv3]
    exact Nat.pow_succ_factorization_not_dvd hd3 hp
  intro Q hQ
  obtain ⟨c, hc⟩ := hconj Q hQ
  have hθ := conjEmb_injective (triEmb_injective (K := K) (σ := σ) (L := L)) g0 c
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨Φ, hΦ, hΦy⟩ := exists_coord_embedding ((conjEmb (triEmb K σ L) g0 c).comp Q.subtype)
    (hθ.comp (Subgroup.subtype_injective Q))
    (fixedCharTuples d4QM (iterateFrobenius L ℓ f))
    (fun y => by
      rw [← hT]
      have := hc y y.2
      rwa [← conjEmb_apply] at this) 0 2
    (fun a ha b hb h0 h2 => eq_of_d4QCoord_eq hFr ha hb
      (by
        rw [d4QCoord_apply, d4QCoord_apply]
        funext k
        fin_cases k
        · exact h0
        · exact h2))
  refine ⟨Φ, hΦ, fun y => ?_⟩
  obtain ⟨a, ha, -, h1, h2⟩ := hΦy y
  rw [h1, h2]
  exact ⟨d4Q_pow0 hFr ha, d4Q_pow2 hFr ha⟩

theorem sylowShape_D4_split {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f - 1) :
    SylowShape p 2 ((ℓ ^ f - 1).factorization p)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hCcard := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl)
    σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
  have hq1 : ℓ ^ f - 1 ≠ 0 := by omega
  have hord : (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
      2 * (ℓ ^ f - 1).factorization p := by
    have h := ordProj_triality_split hp hp5 hq2 hpq
    rw [← hCcard] at h
    have h2 := Nat.pow_right_injective hp.two_le h
    rw [h2, Nat.factorization_mul hq1 hq1, Finsupp.add_apply]
    ring
  have hq3 : ∀ c : K, c ^ ((ℓ ^ f) ^ 3) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ (σ (σ c)) = c
    simp only [hσ]
    rw [← pow_mul, ← pow_mul, show ℓ ^ f * (ℓ ^ f * ℓ ^ f) = (ℓ ^ f) ^ 3 by ring, hq3]
  obtain ⟨-, ⟨eT, -⟩, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have hcardL := card_orbitField_D4_orientation hℓ hf hK (r := 1) (Or.inl rfl)
    (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσ c)
  have hk : Nat.card (trialityFixedField K σ.toRingHom) = ℓ ^ f := by
    rw [← hL2, hcardL ⟨1, by decide⟩, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide,
      pow_one]
  have hpe : p ^ (ℓ ^ f - 1).factorization p ∣ ℓ ^ f - 1 := Nat.ordProj_dvd _ _
  have hdK : p ^ (ℓ ^ f - 1).factorization p ∣ Nat.card K - 1 := by
    rw [hK]
    refine hpe.trans ?_
    simpa using Nat.sub_dvd_pow_sub_pow (ℓ ^ f) 1 3
  have hdk : p ^ (ℓ ^ f - 1).factorization p ∣
      Nat.card (trialityFixedField K σ.toRingHom) - 1 := by
    rw [hk]
    exact hpe
  obtain ⟨ι₁, hι₁⟩ := exists_injective_units (K := K) hdK
  obtain ⟨ι₂, hι₂⟩ := exists_injective_units (K := trialityFixedField K σ.toRingHom) hdk
  let Ψ₀ : (Fin 2 → Multiplicative (ZMod (p ^ (ℓ ^ f - 1).factorization p))) →*
      Kˣ × (trialityFixedField K σ.toRingHom)ˣ :=
    (ι₁.comp (Pi.evalMonoidHom (fun _ : Fin 2 =>
      Multiplicative (ZMod (p ^ (ℓ ^ f - 1).factorization p))) 0)).prod
    (ι₂.comp (Pi.evalMonoidHom (fun _ : Fin 2 =>
      Multiplicative (ZMod (p ^ (ℓ ^ f - 1).factorization p))) 1))
  have hΨ₀ : Function.Injective Ψ₀ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : ι₁ (v 0) = 1 := congrArg Prod.fst hv
    have h2 : ι₂ (v 1) = 1 := congrArg Prod.snd hv
    funext i
    fin_cases i
    · exact (injective_iff_map_eq_one _).1 hι₁ _ h1
    · exact (injective_iff_map_eq_one _).1 hι₂ _ h2
  have hle := graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom
  refine sylowShape_of_injective hp ((Subgroup.inclusion hle).comp (eT.toMonoidHom.comp Ψ₀)) ?_
    hord
  exact (Subgroup.inclusion_injective hle).comp (eT.injective.comp hΨ₀)

theorem sylowShape_D4 {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {m : ℕ}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpd : p ∣ phiNat m (ℓ ^ f)) :
    SylowShape p 2 ((phiNat m (ℓ ^ f)).factorization p)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hℓ : ℓ.Prime := Fact.out
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  rcases hm with rfl | rfl | rfl | rfl
  · exact sylowShape_D4_split hf K hK σ hσ hp hp5 hpd
  · exact sylowShape_D4_qplus hf K hK σ hσ hp hp5 hpd
  · have hpd' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
      have : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1 := hpd
      have h' : (p : ℤ) ∣ (((ℓ ^ f) ^ 2 + ℓ ^ f + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 this
      push_cast at h'
      rw [one_mul]
      exact h'
    have h := sylowShape_D4_36 hf K hK σ hσ (ε := 1) (Or.inl rfl) hp (by omega) hpd'
    rwa [d4T36d_one_eq hq1] at h
  · have hle : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hpd' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
      have : p ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := hpd
      have h2 : (((ℓ ^ f) ^ 2 - ℓ ^ f + 1 : ℕ) : ℤ) =
          ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
        push_cast [Nat.cast_sub hle]
        ring
      rw [← h2]
      exact_mod_cast this
    have h := sylowShape_D4_36 hf K hK σ hσ (ε := -1) (Or.inr rfl) hp (by omega) hpd'
    rwa [d4T36d_neg_eq hq1] at h

theorem pRank_le_one_D4_twelve {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ∣ (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1) :
    CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ 1 := by
  obtain ⟨T₀, -, -, h⟩ := triality_cyclotomic_twelve_torus_and_prime_centralizers hℓ hf K hK σ hσ
  exact pRank_le_one_of_cyclic_pSubgroups hp (h p hp (by omega) hpd).2.1

theorem kf128SylTag_trialityD4 : KF128SylTag .trialityD4 := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 hZ hLR2 n f₀ hf₀ hM α hαp hinn hLRA hFix hF hrk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm := statedLieAdmissible_of_lieModel hM
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hm1 : 1 ≤ p * f₀ := hadm.2.1
  have hp2 : p ≠ 2 := by omega
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hM
  obtain ⟨K, hKf, hKfin, σ, hK, hσ, ⟨eT⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hm1 hch.2
  have hK3 : Nat.card K = (2 ^ (p * f₀)) ^ 3 := hK
  have hmodN : LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .trialityD4 0 2 f₀ := by
    rcases hFix with h | ⟨ht, -⟩
    · exact h
    · exact absurd ht (by decide)
  have hch' := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodN
  obtain ⟨K', hK'f, hK'fin, σ', hK', hσ', ⟨e'⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf₀ hch'.2
  have hK'3 : Nat.card K' = (2 ^ f₀) ^ 3 := hK'
  have eN : ↥(fixRes α) ≃* graphFixedRootGroup TwistTag.D4 K' σ'.toRingHom :=
    (fixResEquivQuotient hF).trans e'
  have hpT : p ∣ Nat.card T := dvd_card_of_pRank_pos hp (by omega)
  obtain ⟨m, hmem, hdvd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp
    (by omega) (by omega : 2 ≠ p) hch).1 hpT).2.2.2.2 rfl
  have hd : (p : ℤ) ∣ cycloVal m 2 (p * f₀) := hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hq1 : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_pow _ _ (by norm_num)
  have hq1' : 1 ≤ 2 ^ f₀ := Nat.one_le_pow _ _ (by norm_num)
  have hq2' : 2 ≤ 2 ^ f₀ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  have hpq' : ¬ p ∣ 2 ^ f₀ := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  have hQ : 2 ^ (p * f₀) = (2 ^ f₀) ^ p := by rw [← pow_mul, mul_comm]
  by_cases h12 : m = 12
  ·
    exfalso
    subst h12
    rw [cycloVal_twelve] at hd
    have hpd : p ∣ (2 ^ (p * f₀)) ^ 4 - (2 ^ (p * f₀)) ^ 2 + 1 := by
      have h24 : (2 ^ (p * f₀)) ^ 2 ≤ (2 ^ (p * f₀)) ^ 4 :=
        Nat.pow_le_pow_right hq1 (by omega)
      have h1 : (p : ℤ) ∣ (((2 ^ (p * f₀)) ^ 4 - (2 ^ (p * f₀)) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        exact hd
      exact_mod_cast h1
    have h1 := pRank_le_one_D4_twelve Nat.prime_two hm1 K hK3 σ hσ hp hp5 hpd
    have h2 := pRank_eq_of_mulEquiv_of_one_lt hp.one_lt eT
    omega
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
  have hpdQ : p ∣ phiNat m (2 ^ (p * f₀)) := dvd_phiNat_of_dvd_cycloVal hq1 hm' hd
  have hpdq : p ∣ phiNat m (2 ^ f₀) := by
    refine dvd_phiNat_of_dvd_pow hp hq1' hm' ?_
    rw [← hQ]
    exact hpdQ
  have hshT := sylowShape_D4 hm1 K hK3 σ hσ hm' hp hp5 hpdQ
  have hshN := sylowShape_D4 hf₀ K' hK'3 σ' hσ' hm' hp hp5 hpdq
  have hlte := factorization_phiNat_pow hp hp5 hq2' hpq' hm' hpdq
  rw [← hQ] at hlte
  have hne : phiNat m (2 ^ f₀) ≠ 0 := by
    rcases hm' with rfl | rfl | rfl | rfl <;> simp only [phiNat] <;> omega
  have hone : 1 ≤ (phiNat m (2 ^ f₀)).factorization p :=
    (hp.dvd_iff_one_le_factorization hne).1 hpdq
  refine ⟨(phiNat m (2 ^ (p * f₀))).factorization p, by omega, SylowShape.of_mulEquiv eT hshT, ?_⟩
  have he1 : (phiNat m (2 ^ (p * f₀))).factorization p - 1 =
      (phiNat m (2 ^ f₀)).factorization p := by omega
  rw [he1]
  exact SylowShape.of_mulEquiv eN hshN

end CFSG.RankThree.PartOne.K128

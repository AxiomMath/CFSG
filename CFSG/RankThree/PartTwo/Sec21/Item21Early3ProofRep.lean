module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Quasisimple
import CFSG.Foundations.HigherElementaryThompson
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofCenter
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofQuasi
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.OrderReductions.FrattiniAutomorphisms
open CFSG.Assembly.RankThreeEven (localRank projSL)
open Sec4.Census
open scoped IsMulCommutative Matrix

namespace Item21Early3Proof

theorem exists_rep_of_critical {X : Type} [Group X] [Finite X] (hX : SectionFourHyp X)
    [hperf : Group.IsPerfect X] (h3 : CFSG.Open.pRank 2 (⊤ : Subgroup X) = 3) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {D : Subgroup X} (hD : CriticalAt p D)
    (hodd : Odd (Nat.card (Subgroup.centralizer (D : Set X)))) :
    5 ≤ p ∧ ∃ ρ : X →* GL (Fin 4) (ZMod p), (∀ y, ρ y = 1 → y ∈ oddCore X) ∧
      ∀ y, (ρ y : Matrix (Fin 4) (Fin 4) (ZMod p)).det = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    have : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  have hDp : IsPGroup p D := pCore_isPGroup.to_le hD.le
  have : D.Normal := hD.normal
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) (⊤ : Subgroup X)
  rw [h3] at hEcard
  obtain ⟨eE⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := E)
    (fun a b => hE.1.is_comm.comm a b) (fun a => Subtype.ext (hE.2 a a.2)) hEcard
  set ι : Multiplicative (Fin 3 → ZMod 2) →* X := E.subtype.comp eE.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp eE.symm.injective
  have hA2 : ∀ a : Multiplicative (Fin 3 → ZMod 2), a ^ 2 = 1 := by
    intro a
    obtain ⟨e, rfl⟩ := eE.surjective a
    rw [← map_pow, show e ^ 2 = 1 from Subtype.ext (hE.2 e e.2), map_one]
  have hA8 : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by
    rw [← Nat.card_congr eE.toEquiv, hEcard]
    norm_num
  set ρA : Multiplicative (Fin 3 → ZMod 2) →* MulAut D := hD.conjD.comp ι with hρAdef
  have hρA : ∀ a (d : D), ((ρA a d : D) : X) = ι a * d * (ι a)⁻¹ := fun a d =>
    hD.conjD_apply (ι a) d
  have hfaith : Function.Injective ρA := by
    intro a₁ a₂ h
    apply hι
    set c := (ι a₁)⁻¹ * ι a₂ with hc
    have hcD : c ∈ Subgroup.centralizer (D : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : X)) h
      simp only [hρA] at h1
      calc d * c = (ι a₁)⁻¹ * (ι a₁ * d * (ι a₁)⁻¹) * ι a₂ := by rw [hc]; group
        _ = (ι a₁)⁻¹ * (ι a₂ * d * (ι a₂)⁻¹) * ι a₂ := by rw [h1]
        _ = c * d := by rw [hc]; group
    have hc2 : c ^ 2 = 1 := by
      rw [hc, ← map_inv, ← map_mul, ← map_pow, hA2, map_one]
    have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
    have h2 : orderOf c ∣ Nat.card (Subgroup.centralizer (D : Set X)) := by
      rw [← Subgroup.orderOf_mk c hcD]
      exact orderOf_dvd_natCard _
    have h3 : orderOf c = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left).mpr hodd) h1 h2
    rw [orderOf_eq_one_iff, hc, inv_mul_eq_one] at h3
    exact h3
  have hfix : ∀ a : Multiplicative (Fin 3 → ZMod 2), a ≠ 1 →
      CFSG.pRank p (fixedSubgroupOf (ρA a)) ≤ 2 := by
    intro a ha
    set C := fixedSubgroupOf (ρA a) with hC
    have ht : orderOf (ι a) = 2 := orderOf_eq_prime (by rw [← map_pow, hA2, map_one])
      (fun h => ha (hι (by rw [h, map_one])))
    have hCt : ∀ c ∈ C.map D.subtype, c * ι a = ι a * c := by
      rintro _ ⟨c, hc, rfl⟩
      have h1 := congrArg Subtype.val ((mem_fixedSubgroupOf (ρA a) c).mp hc)
      rw [hρA] at h1
      change (c : X) * ι a = ι a * c
      calc (c : X) * ι a = ι a * c * (ι a)⁻¹ * ι a := by rw [h1]
        _ = ι a * c := by group
    have h1 := pRank_le_localRank_of_centralizes hp hp2 ht hCt
    have h2 := hX.localRank_lt p hp hp3
    rw [← pRank_congr_mulEquiv hp.one_lt (C.equivMapOfInjective D.subtype D.subtype_injective)]
      at h1
    omega
  obtain ⟨hd, ⟨a₀, ⟨ha₀1, ha₀⟩, -⟩, -⟩ := class_two_eight_action_inverting_quotient hp2 hDp
    (fun x => Subtype.ext (by simpa using hD.exp x x.2)) hD.commutator_le_center hA2 hA8 ρA
    hfaith hfix
  obtain ⟨-, -, -, hVelem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  have := hVelem
  have : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  set R := frattiniLin hD with hRdef
  have hR := frattiniLin_apply hD
  have hdet : ∀ y, LinearMap.det (R y) = 1 := by
    intro y
    have := map_eq_one_of_isPerfect_comm ((Units.map LinearMap.det).comp R.toHomUnits) y
    exact congrArg Units.val this
  have hneg : R (ι a₀) = -1 := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hwx : w = Additive.ofMul (x : D ⧸ frattini D) := by rw [hx]; rfl
    rw [hwx, hR, LinearMap.neg_apply, Module.End.one_apply, ← ofMul_inv]
    exact congrArg Additive.ofMul (ha₀ x)
  have hfin4 : Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) = 4 := by
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive (D ⧸ frattini D))
    rw [Nat.card_zmod] at hpow
    have hrank := pRank_eq_of_card_eq_pow hp.one_lt (A := D ⧸ frattini D) hpow
    have h1 := hdet (ι a₀)
    rw [hneg, ← LinearMap.det_toMatrix (Module.finBasis (ZMod p) (Additive (D ⧸ frattini D))),
      map_neg, LinearMap.toMatrix_one, Matrix.det_neg, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
    have hne : (-1 : ZMod p) ≠ 1 := by
      intro h
      have h2 : (2 : ZMod p) = 0 := by
        calc (2 : ZMod p) = 1 - (-1) := by ring
          _ = 0 := by rw [h, sub_self]
      exact two_ne_zero_zmod hp hp2 h2
    rcases hd with h | h
    · rw [hrank] at h
      rw [h, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, neg_one_sq, one_mul] at h1
      exact absurd h1 hne
    · rwa [hrank] at h
  set b := Module.finBasisOfFinrankEq (ZMod p) (Additive (D ⧸ frattini D)) hfin4
  exact ⟨hp5, frattiniMat hD b, fun y hy => mem_oddCore_of_frattiniLin_eq_one hD hp2 hodd
    ((frattiniMat_eq_one_iff hD b y).mp hy), det_frattiniMat_eq_one hD b⟩

theorem false_of_critical_L34 (hL34 : FourL34NotSLFourOdd) {X : Type} [Group X] [Finite X]
    (hX : SectionFourHyp X) [Group.IsPerfect X] (h3 : CFSG.Open.pRank 2 (⊤ : Subgroup X) = 3)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {D : Subgroup X} (hD : CriticalAt p D)
    (hodd : Odd (Nat.card (Subgroup.centralizer (D : Set X))))
    (hq : IsQuasisimple (X ⧸ oddCore X)) (hcyc : IsCyclic (Subgroup.center (X ⧸ oddCore X)))
    (hZ : Nat.card (Subgroup.center (X ⧸ oddCore X)) = 4)
    (e : (X ⧸ oddCore X) ⧸ Subgroup.center (X ⧸ oddCore X) ≃* projSL 3 (GaloisField 2 2)) :
    False := by
  obtain ⟨hp5, ρ, hρ, hdet⟩ := exists_rep_of_critical hX h3 hp hp3 hD hodd
  have : Fact p.Prime := ⟨hp⟩
  have hker : ρ.ker ≤ oddCore X := fun y hy => hρ y hy
  exact (hL34 p hp5 X (glToSL ρ hdet) (oddCore X) (CFSG.ABGDGroups.odd_card_oddCore X)
    (by rw [ker_glToSL]; exact hker) hq hcyc hZ).false e

open Item21EarlyProof Item21Early2Proof

variable {G : Type} [Group G] [Finite G]

theorem exists_critical_of_sec21 (hOrd : KS213Order)
    (hNine : KS213Nine) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hO2 : CFSG.pCore 2 L = ⊥) (hq : ¬ IsQuasisimple L) (hX : IsBar211 (lBar L)) :
    SectionFourHyp L ∧ ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ D : Subgroup L, CriticalAt p D ∧
      Odd (Nat.card (Subgroup.centralizer (D : Set L))) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hc1 : c ≠ 1 := hpairs.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hLq : IsQuasisimple (lBar L) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  obtain ⟨hTs, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  set K₀ := centerPre T with hK₀
  have hK₀s : Group.IsSolvable K₀ := isSolvable_centerPre T hTs
  have : IsSimpleGroup (lBar L ⧸ Subgroup.center (lBar L)) := hLq.2.1
  have : IsSimpleGroup (L ⧸ K₀) := (centerPreEquiv T).isSimpleGroup
  have hbig : 5616 < Nat.card (L ⧸ K₀) := by
    rw [Nat.card_congr (centerPreEquiv T).toEquiv]
    exact hOrd _ hX
  have hL4 : SectionFourHyp L := by
    have hLtop : L ≠ ⊤ := fun hLt =>
      Sec6.centralizer_ne_top_of_ne_one hpair.standing.toTheoremFourHyp hc1
        (top_le_iff.mp (hLt ▸ Sec6.le_centralizer_of_mem_thetaComponentsAt hLc))
    exact hpair.standing.toTheoremFourHyp.sectionFourHyp hLtop
  refine ⟨hL4, ?_⟩
  have hK₀top : K₀ ≠ ⊤ := QuotientGroup.nontrivial_iff.mp inferInstance
  have hctop : ∀ N : Subgroup L, N ≤ Subgroup.center L →
      ¬ Subgroup.centralizer (N : Set L) ≤ K₀ := by
    intro N hN hle
    rw [centralizer_eq_top_of_le_center hN, top_le_iff] at hle
    exact hK₀top hle
  obtain ⟨p₀, hp₀, hS₀⟩ := Sec4.Census.exists_centralizer_pCore_le hK₀s hq
  have hSp : ∀ p : ℕ, p.Prime → Subgroup.centralizer (CFSG.pCore p L : Set L) ≤ K₀ →
      3 < p ∧ CFSG.pCore p L ≠ ⊥ := by
    intro p hp hpS
    have : Fact p.Prime := ⟨hp⟩
    have hne : CFSG.pCore p L ≠ ⊥ := by
      intro h
      rw [h] at hpS
      exact hctop ⊥ bot_le hpS
    refine ⟨?_, hne⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hne hO2
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hctop _ (pCore_three_le_center T hT3) hpS
    have := hp.two_le
    omega
  by_contra hO
  push Not at hO
  have hlin : ∀ p : ℕ, p.Prime → Subgroup.centralizer (CFSG.pCore p L : Set L) ≤ K₀ →
      ∃ (N : Subgroup L) (_ : N.Normal), Sec4.Census.LinearOutcome L p N := by
    intro p hp hpS
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hp3, hne⟩ := hSp p hp hpS
    obtain ⟨D, hD⟩ := Sec4.Census.exists_criticalAt (by omega) hne
    have heven := hO p hp hp3 D hD
    rw [Nat.not_odd_iff_even] at heven
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer (D : Set L)) 2
      (even_iff_two_dvd.mp heven)
    have ht' : orderOf (t : L) = 2 := by rwa [Subgroup.orderOf_coe]
    have hr := Sec4.Census.pRank_le_localRank_of_centralizes hp (by omega) ht'
      (fun h hh => Subgroup.mem_centralizer_iff.mp t.2 h hh)
    have := hL4.localRank_lt p hp hp3
    exact Sec4.Census.linearOutcome_of_criticalAt hK₀s hp3 hpS hD (by omega)
  rcases Sec4.Census.linear_endgame hK₀s hO2 hp₀ hS₀ hlin with ⟨⟨e⟩⟩ | ⟨p, hp, hp3, ⟨e⟩⟩ |
      ⟨⟨e⟩⟩
  ·
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
      rw [Sec4.Census.card_SL2]
      norm_num
    exact Sec13.false_of_surjective_of_card_lt hK₀s (e.toMonoidHom.comp (QuotientGroup.mk' _))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega) (by omega)
  ·
    have : Fact p.Prime := ⟨hp⟩
    have e' : L ⧸ Sec4.oTwoP p L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      (QuotientGroup.quotientMulEquivOfEq (Sec4.Census.oTwoP_eq_of_pCore_two_eq_bot p hO2)).trans
        e
    obtain ⟨E', hE'3, hE'9⟩ := hNine _ hX
    obtain ⟨E₀, hE3, hE9⟩ := exists_nine_quotient T hE'3 hE'9
    exact Sec13.false_of_oTwoP_equiv_SL2 hp hp3 e' hE3 hE9
  ·
    have hc := Sec4.Census.card_SL3_three
    exact Sec13.false_of_surjective_of_card_lt hK₀s (e.toMonoidHom.comp (QuotientGroup.mk' _))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega) (by omega)

end Item21Early3Proof

end CFSG.RankThree.PartTwo.Sec21

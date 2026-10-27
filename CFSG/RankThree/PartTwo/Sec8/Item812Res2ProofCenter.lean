module

public import CFSG.RankThree.PartTwo.Sec8.Item812Proof810
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofXNormal
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.Assembly.RankThreeEven (localRank projSp)

namespace Item812Res2

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section KFact

variable {M : Type*} [Group M]

theorem zpow_apply_eq_self {τ : MulAut M} {y : M} (h : τ y = y) (k : ℤ) : (τ ^ k) y = y := by
  have hmem : τ ∈ MulAction.stabilizer (MulAut M) y := h
  exact Subgroup.zpow_mem _ hmem k

theorem mulAutConj_injective (hM : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : x ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun τ : MulAut M => τ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rw [hM, Subgroup.mem_bot] at hmem
  exact hmem

variable {F : Type} [Field F] [CharP F 2]

theorem center_statedProj_eq_bot : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := by
  set e : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
    MulEquiv.ofBijective (proj 2 F) ⟨KFacts.proj_injective_of_charTwo, proj_surjective⟩
  rw [eq_bot_iff]
  intro y hy
  have hy' : e.symm y ∈ Subgroup.center (StatedSp 2 F) := by
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy (e g)
  rw [KFacts.center_statedSp_eq_bot, Subgroup.mem_bot] at hy'
  rw [Subgroup.mem_bot]
  have := congrArg e hy'
  rwa [MulEquiv.apply_symm_apply, map_one] at this

theorem exists_involution_commute_of_pow_three [Finite F] {x : StatedSp 2 F} (hx : x ^ 3 = 1) :
    ∃ j : StatedSp 2 F, j ^ 2 = 1 ∧ j ≠ 1 ∧ x * j = j * x := by
  by_cases hx1 : x = 1
  · exact ⟨sp4J F, sp4J_sq F, sp4J_ne_one F, by rw [hx1, one_mul, mul_one]⟩
  · obtain ⟨φ, rfl⟩ := KFacts.exists_mulAut_apply_sp4T_eq hx hx1
    refine ⟨φ (sp4J F), ?_, ?_, ?_⟩
    · rw [← map_pow, sp4J_sq, map_one]
    · rw [Ne, map_eq_one_iff _ φ.injective]
      exact sp4J_ne_one F
    · rw [← map_mul, ← map_mul, sp4T_mul_sp4J]

theorem outer_image_eq_zpowers [Finite F] {m : ℕ} (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ m)
    (Ab : Subgroup (MulAut (StatedProj (StatedSp 2 F)))) (h3 : ∀ β ∈ Ab, β ^ 3 = 1)
    {α : MulAut (StatedProj (StatedSp 2 F))} (hα : α ∈ Ab) (hout : ¬ KFacts.IsInnerAut α) :
    (∀ β ∈ Ab, ∃ k : ℤ, KFacts.IsInnerAut (β * (α ^ k)⁻¹)) ∧
      Nat.card ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp 2 F)))).comp Ab.subtype).ker * 3 = Nat.card Ab := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := StatedProj (StatedSp 2 F) with hP
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hm hF
  obtain ⟨-, -, -, -, hcyc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure hm hFr hord
      hzp
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner P with hI
  set π := QuotientGroup.mk' I with hπ
  have hπI : ∀ τ : MulAut P, π τ = 1 ↔ KFacts.IsInnerAut τ := fun τ => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hα3 : α ^ 3 = 1 := h3 α hα
  have hπα : orderOf (π α) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hα3, map_one]) (fun h => hout ((hπI α).mp h))
  set S := Ab.map π with hS
  have hSα : π α ∈ S := ⟨α, hα, rfl⟩
  have hS3 : ∀ s ∈ S, s ^ 3 = 1 := by
    rintro _ ⟨β, hβ, rfl⟩
    rw [← map_pow, h3 β hβ, map_one]
  have hScard : Nat.card S = 3 := by
    have := hcyc
    obtain ⟨s₀, hs₀⟩ := IsCyclic.exists_generator (α := S)
    have hcardS : orderOf s₀ = Nat.card S := orderOf_eq_card_of_forall_mem_zpowers hs₀
    have hs₀3 : s₀ ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hS3 _ s₀.2)
    have hdvd : Nat.card S ∣ 3 := hcardS ▸ orderOf_dvd_of_pow_eq_one hs₀3
    have hle : 3 ≤ Nat.card S := by
      have h1 := Subgroup.card_le_of_le ((Subgroup.zpowers_le (H := S)).mpr hSα)
      rwa [Nat.card_zpowers, hπα] at h1
    have h3pos := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hSeq : Subgroup.zpowers (π α) = S :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le (H := S)).mpr hSα)
      (by rw [hScard, Nat.card_zpowers, hπα])
  refine ⟨fun β hβ => ?_, ?_⟩
  · have hmem : π β ∈ Subgroup.zpowers (π α) := hSeq ▸ ⟨β, hβ, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨k, (hπI _).mp ?_⟩
    rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
  · have hρrange : Nat.card (π.comp Ab.subtype).range = 3 := by
      have : (π.comp Ab.subtype).range = S := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [this, hScard]
    have h1 := Subgroup.card_mul_index (π.comp Ab.subtype).ker
    rw [Subgroup.index_ker, hρrange] at h1
    exact h1

theorem exists_fixed_involution_of_card_le_nine [Finite F] {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ m) (Ab : Subgroup (MulAut (StatedProj (StatedSp 2 F))))
    (hcomm : ∀ β ∈ Ab, ∀ γ ∈ Ab, β * γ = γ * β) (h3 : ∀ β ∈ Ab, β ^ 3 = 1)
    (hcard : Nat.card Ab ≤ 9) {α : MulAut (StatedProj (StatedSp 2 F))} (hα : α ∈ Ab)
    (hout : ¬ KFacts.IsInnerAut α) :
    ∃ J : StatedProj (StatedSp 2 F), orderOf J = 2 ∧ ∀ β ∈ Ab, β J = J := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := StatedProj (StatedSp 2 F) with hP
  have hZ : Subgroup.center P = ⊥ := center_statedProj_eq_bot
  have hconjinj := mulAutConj_injective hZ
  have hα3 : α ^ 3 = 1 := h3 α hα
  obtain ⟨hcoset, hkercard⟩ := outer_image_eq_zpowers hm hF Ab h3 hα hout
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner P with hI
  set π := QuotientGroup.mk' I with hπ
  have hπI : ∀ τ : MulAut P, π τ = 1 ↔ KFacts.IsInnerAut τ := fun τ => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  set ρ : Ab →* CFSG.ComponentClassification.OuterAutomorphisms.Outer P :=
    π.comp Ab.subtype with hρ
  have hker : Nat.card ρ.ker ≤ 3 := by omega
  have hι : ∃ ι₀ ∈ Ab, KFacts.IsInnerAut ι₀ ∧
      ∀ β ∈ Ab, KFacts.IsInnerAut β → β ∈ Subgroup.zpowers ι₀ := by
    by_cases hex : ∃ β ∈ Ab, KFacts.IsInnerAut β ∧ β ≠ 1
    · obtain ⟨ι, hιA, hιI, hι1⟩ := hex
      refine ⟨ι, hιA, hιI, fun β hβ hβI => ?_⟩
      have hιker : (⟨ι, hιA⟩ : Ab) ∈ ρ.ker := (hπI ι).mpr hιI
      have hord3 : orderOf (⟨ι, hιA⟩ : Ab) = 3 :=
        orderOf_eq_prime (Subtype.ext (by simpa using h3 ι hιA))
          (fun h => hι1 (congrArg Subtype.val h))
      have heq : Subgroup.zpowers (⟨ι, hιA⟩ : Ab) = ρ.ker :=
        Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le (H := ρ.ker)).mpr hιker)
          (by rw [Nat.card_zpowers, hord3]; exact hker)
      have hβker : (⟨β, hβ⟩ : Ab) ∈ ρ.ker := (hπI β).mpr hβI
      rw [← heq] at hβker
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hβker
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · push Not at hex
      refine ⟨1, Ab.one_mem, ⟨1, map_one _⟩, fun β hβ hβI => ?_⟩
      rw [hex β hβ hβI]
      exact Subgroup.one_mem _
  obtain ⟨ι₀, hι₀A, ⟨B, hB⟩, hι₀gen⟩ := hι
  have hnotin : α ∉ (conjAut 2 F).range := by
    rintro ⟨A', rfl⟩
    exact hout (KFacts.conjAut_mem_inner_of_charTwo A')
  obtain ⟨σ, -, H, hαH⟩ := KFacts.sp4_even_order_three_field_descent α hα3 hnotin
  set γ : MulAut P := conjAut 2 F H with hγ
  set f : MulAut P := fieldAut 2 F σ with hf
  set B' : P := γ⁻¹ B with hB'
  have hcB' : γ⁻¹ * ι₀ * γ = MulAut.conj B' := by
    have h := KFacts.mul_mulAutConj_mul_inv γ⁻¹ B
    rwa [inv_inv, hB] at h
  have hcomm₀ : ι₀ * α = α * ι₀ := hcomm ι₀ hι₀A α hα
  have hfB : f B' = B' := by
    have h1 : MulAut.conj B' * f = f * MulAut.conj B' := by
      rw [← hcB']
      have hαf : f = γ⁻¹ * α * γ := by rw [hαH]; group
      rw [hαf]
      calc γ⁻¹ * ι₀ * γ * (γ⁻¹ * α * γ) = γ⁻¹ * (ι₀ * α) * γ := by group
        _ = γ⁻¹ * (α * ι₀) * γ := by rw [hcomm₀]
        _ = γ⁻¹ * α * γ * (γ⁻¹ * ι₀ * γ) := by group
    have h2 : f * MulAut.conj B' * f⁻¹ = MulAut.conj B' := by
      rw [← h1]
      group
    rw [KFacts.mul_mulAutConj_mul_inv] at h2
    exact hconjinj h2
  have hB'3 : B' ^ 3 = 1 := by
    apply hconjinj
    rw [map_pow, ← hcB', map_one]
    have : (γ⁻¹ * ι₀ * γ) ^ 3 = γ⁻¹ * ι₀ ^ 3 * γ := by
      have h := conj_pow (a := γ⁻¹) (b := ι₀) (i := 3)
      rwa [inv_inv] at h
    rw [this, h3 ι₀ hι₀A]
    group
  obtain ⟨B₀, hB₀⟩ := (KFacts.mem_range_proj_spIncl_iff σ B').mpr hfB
  set incl := (proj 2 F).comp (KFacts.spIncl σ) with hincl
  have hinj : Function.Injective incl := KFacts.proj_spIncl_injective σ
  have hB₀3 : B₀ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hB₀, hB'3, map_one]
  obtain ⟨J₀, hJ₀2, hJ₀1, hJ₀B⟩ := exists_involution_commute_of_pow_three hB₀3
  set J' : P := incl J₀ with hJ'
  have hfJ' : f J' = J' := (KFacts.mem_range_proj_spIncl_iff σ J').mp ⟨J₀, rfl⟩
  have hBJ' : B' * J' = J' * B' := by
    rw [← hB₀, hJ', ← map_mul, ← map_mul, hJ₀B]
  refine ⟨γ J', ?_, fun β hβ => ?_⟩
  · rw [MulEquiv.orderOf_eq γ, hJ', orderOf_injective incl hinj]
    exact orderOf_eq_prime hJ₀2 hJ₀1
  · have hαJ : α (γ J') = γ J' := by
      rw [hαH]
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, hfJ']
    have hιJ : ι₀ (γ J') = γ J' := by
      have hι₀ : ι₀ = γ * MulAut.conj B' * γ⁻¹ := by rw [← hcB']; group
      rw [hι₀]
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, MulAut.conj_apply, hBJ',
        mul_inv_cancel_right]
    obtain ⟨k, hk⟩ := hcoset β hβ
    have hkA : β * (α ^ k)⁻¹ ∈ Ab := Ab.mul_mem hβ (Ab.inv_mem (Ab.zpow_mem hα k))
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hι₀gen _ hkA hk)
    have hβeq : β = ι₀ ^ l * α ^ k := by rw [hl]; group
    rw [hβeq, MulAut.mul_apply, zpow_apply_eq_self hαJ, zpow_apply_eq_self hιJ]

end KFact

theorem four_le_localRank_of_fixed_involution {G : Type} [Group G] [Finite G] {A X : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (X : Set G)) {j : X ⧸ aschbacherSolvableCore 3 X}
    (hj : orderOf j = 2)
    (hfix : ∀ (a : G) (ha : a ∈ A), thetaQuotMulAut X (compAction X ⟨a, hAN ha⟩) j = j) :
    4 ≤ localRank 3 G := by
  classical
  obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  set D₀ := (Subgroup.zpowers j).comap (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) with hD₀
  set D := D₀.map X.subtype with hD
  have hD₀card : Nat.card D₀ =
      Nat.card (aschbacherSolvableCore 3 X) * Nat.card (Subgroup.zpowers j) :=
    QuotientGroup.card_preimage_mk (aschbacherSolvableCore 3 X)
      ((Subgroup.zpowers j : Subgroup (X ⧸ aschbacherSolvableCore 3 X)) :
        Set (X ⧸ aschbacherSolvableCore 3 X))
  have hDcard : Nat.card D = Nat.card (aschbacherSolvableCore 3 X) * 2 := by
    rw [hD, Subgroup.card_map_of_injective X.subtype_injective, hD₀card, Nat.card_zpowers, hj]
  have hconj : ∀ a ∈ A, ∀ d ∈ D, a * d * a⁻¹ ∈ D := by
    intro a ha d hd
    obtain ⟨x, hx, rfl⟩ := hd
    have hτx : ((compAction X ⟨a, hAN ha⟩ x : X) : G) = a * x * a⁻¹ :=
      normalizerMonoidHom_apply_coe (hAN ha) x
    refine ⟨compAction X ⟨a, hAN ha⟩ x, ?_, hτx⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (show QuotientGroup.mk' (aschbacherSolvableCore 3 X) x ∈ Subgroup.zpowers j from hx)
    change QuotientGroup.mk' (aschbacherSolvableCore 3 X) (compAction X ⟨a, hAN ha⟩ x) ∈
      Subgroup.zpowers j
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 X) (compAction X ⟨a, hAN ha⟩ x) =
        thetaQuotMulAut X (compAction X ⟨a, hAN ha⟩)
          (QuotientGroup.mk' (aschbacherSolvableCore 3 X) x) := rfl
    rw [h1, ← hk, map_zpow, hfix a ha]
    exact Subgroup.zpow_mem_zpowers j k
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨hconj a ha d, fun hd => ?_⟩
    have := hconj a⁻¹ (A.inv_mem ha) _ hd
    simpa [mul_assoc] using this
  refine CFSG.RankThree.Classical2.le_localRank_of_normalizes Nat.prime_three hAD hA
    (by rw [hA81]; norm_num) ?_ (by rw [hDcard]; exact Dvd.intro_left _ rfl)
  rw [hDcard]
  refine Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3) ?_
  norm_num

theorem inf_thetaQuotCentralizer_le_zpowers_of_projSp {G : Type} [Group G] [Finite G]
    (h3' : localRank 3 G ≤ 3) {A : Subgroup G} (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (hA81 : Nat.card A = 81) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) {X : Subgroup G}
    (hXb : X ∈ thetaComponentsAt 3 b)
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3))) {x : G}
    (hxA : x ∈ A) (hxout : InducesOuterTheta x X) :
    A ⊓ thetaQuotCentralizer X ≤ Subgroup.zpowers b := by
  classical
  by_contra hne
  obtain ⟨w, ⟨hwA, hwC⟩, hwb⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  have hAN := le_normalizer_of_projSp h3' hAab hbA hb1 hXb hX
  set F := GaloisField 2 3 with hFdef
  set e : X ⧸ aschbacherSolvableCore 3 X ≃* StatedProj (StatedSp 2 F) :=
    hX.some.trans (projSpEquivStatedProj 2 F) with he
  set ρ : A →* MulAut (StatedProj (StatedSp 2 F)) :=
    (KFacts.inducedAutHom X e).comp (Subgroup.inclusion hAN) with hρ
  have hρapply : ∀ y : A, ρ y =
      MulAut.congr e (thetaQuotMulAut X (compAction X ⟨y, hAN y.2⟩)) := fun y => rfl
  have hbker : ρ ⟨b, hbA⟩ = 1 := by
    rw [hρapply]
    have h1 : compAction X ⟨b, hAN hbA⟩ = 1 := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      change b * (x : G) * b⁻¹ = (x : G)
      have hxb : (x : G) * b = b * x :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (le_centralizer_of_mem_thetaComponentsAt_three hXb x.2)
      rw [← hxb, mul_inv_cancel_right]
    rw [h1, map_one, map_one]
  have hwker : ρ ⟨w, hwA⟩ = 1 := by
    rw [hρapply]
    obtain ⟨z, hz, hzw⟩ := hwC
    have hz' : (⟨w, hAN hwA⟩ : Subgroup.normalizer (X : Set G)) = z := Subtype.ext hzw.symm
    have h1 : thetaQuotMulAut X (compAction X ⟨w, hAN hwA⟩) = 1 := by
      rw [hz']
      exact hz
    rw [h1, map_one]
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hbord : orderOf (⟨b, hbA⟩ : A) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hb3))
      (fun h1 => hb1 (by simpa using congrArg Subtype.val h1))
  have hkercard : 9 ≤ Nat.card ρ.ker := by
    have hdvd : Nat.card ρ.ker ∣ 3 ^ 4 := by
      rw [show (3 : ℕ) ^ 4 = Nat.card A by rw [hA81]; norm_num]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hgt : 3 < Nat.card ρ.ker := by
      by_contra hle
      push Not at hle
      have heq : Subgroup.zpowers (⟨b, hbA⟩ : A) = ρ.ker :=
        Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le (H := ρ.ker)).mpr hbker)
          (by rw [Nat.card_zpowers, hbord]; exact hle)
      have hwmem : (⟨w, hwA⟩ : A) ∈ Subgroup.zpowers (⟨b, hbA⟩ : A) := heq ▸ hwker
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwmem
      exact hwb ⟨k, by simpa using congrArg Subtype.val hk⟩
    rw [hieq] at hgt ⊢
    interval_cases i <;> simp_all
  have hrangecard : Nat.card ρ.range ≤ 9 := by
    have h1 := Subgroup.card_mul_index ρ.ker
    rw [Subgroup.index_ker, hA81] at h1
    have h2 : 9 * Nat.card ρ.range ≤ 81 := h1 ▸ Nat.mul_le_mul_right _ hkercard
    omega
  have hρx : ¬ KFacts.IsInnerAut (ρ ⟨x, hxA⟩) :=
    (KFacts.not_isInnerAut_inducedAutHom_iff X e (hAN hxA)).mpr hxout
  have hcomm : ∀ β ∈ ρ.range, ∀ γ ∈ ρ.range, β * γ = γ * β := by
    rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
    rw [← map_mul, ← map_mul, hAab.1.is_comm.comm y y']
  have h3 : ∀ β ∈ ρ.range, β ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (by simpa using hAab.2 y y.2), map_one]
  obtain ⟨J, hJ2, hJfix⟩ := exists_fixed_involution_of_card_le_nine (m := 3)
    (by norm_num) (GaloisField.card 2 3 (by norm_num)) ρ.range hcomm h3 hrangecard
    ⟨⟨x, hxA⟩, rfl⟩ hρx
  have hjfix : ∀ (a' : G) (ha' : a' ∈ A),
      thetaQuotMulAut X (compAction X ⟨a', hAN ha'⟩) (e.symm J) = e.symm J := by
    intro a' ha'
    have h1 : e (thetaQuotMulAut X (compAction X ⟨a', hAN ha'⟩) (e.symm J)) = J :=
      hJfix _ ⟨⟨a', ha'⟩, rfl⟩
    apply e.injective
    rw [h1, MulEquiv.apply_symm_apply]
  have hj2 : orderOf (e.symm J) = 2 := by rw [MulEquiv.orderOf_eq, hJ2]
  have h4 := four_le_localRank_of_fixed_involution hAab hA81 hAN hj2 hjfix
  omega


end Item812Res2

section Final


theorem pair810Center : Pair810Center := by
  intro G _ _ A c L a b X n h hX
  obtain ⟨x, hxA, hxk⟩ := h.mem_pairOmega.2.2.2.1
  have hxout : InducesOuterTheta x X := by
    rcases hxk with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
  exact Item812Res2.inf_thetaQuotCentralizer_le_zpowers_of_projSp
    h.toTheoremFourHyp.localRank_three.le h.mem_partTwoF.1 h.card_eq h.mem_pairOmega.1
    h.mem_pairOmega.2.1 h.mem_pairOmega.2.2.1 hX hxA hxout

theorem item810_of' (h87 : Item87) (h89 : Item89) : Item810 :=
  item810_of h87 h89 pair810Center

end Final

end CFSG.RankThree.PartTwo.Sec8

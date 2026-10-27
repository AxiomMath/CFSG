module

import CFSG.RankThree.PartTwo.Sec8.Item84PairProofGammaU
import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofTools
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2Minus
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofKFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.AutG2OrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.RankThree.PartTwo.Sec21.Item229Pre
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof CFSG.RankThree.PartTwo.Sec8.Item86ResProof
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut inducedAutHom)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

section Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_residual {X : Subgroup G} {M₀ : Type*} [Group M₀]
    (E : X ⧸ aschbacherSolvableCore 3 X ≃* M₀) (hZ : Subgroup.center M₀ = ⊥) {c : G}
    (hcN : c ∈ Subgroup.normalizer (X : Set G)) (hc3 : c ^ 3 = 1)
    (hin : IsInnerAut (inducedAutHom X E ⟨c, hcN⟩))
    (hne : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨c, hcN⟩) ≠ 1) :
    ∃ w : M₀, MulAut.conj w = inducedAutHom X E ⟨c, hcN⟩ ∧ w ^ 3 = 1 ∧ w ≠ 1 ∧
      Nonempty (imageModTheta X
          (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G))) ≃*
        inSubgroup perfectResidual (Subgroup.centralizer ({w} : Set M₀))) := by
  obtain ⟨w, hw⟩ := hin
  have hinj := Item812Res7.conj_injective_of_center_trivial hZ
  have hw3 : w ^ 3 = 1 := by
    apply hinj
    rw [map_pow MulAut.conj w 3, hw, map_one]
    exact KFacts.inducedAutHom_pow_eq_one X E hcN hc3
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hne
    apply (MulAut.congr E).injective
    rw [map_one, ← KFacts.inducedAutHom_apply, ← hw, map_one]
  refine ⟨w, hw, hw3, hw1, ?_⟩
  refine KFacts.nonempty_imageModTheta_perfectResidual_mulEquiv hcN
    ⟨1, by rw [pow_one]; exact hc3⟩ E _ fun z => ?_
  rw [← hw, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  · intro h
    calc z * w = w * z * w⁻¹ * w := by rw [h]
      _ = w * z := by group

theorem false_of_central_three {X K : Subgroup G} (hKX : K ≤ X)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥) {x : imageModTheta X K}
    (hxc : ∀ y, x * y = y * x) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) : False := by
  obtain ⟨-, -, hθ3, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set ρ := Item87Proof.modThetaOnto hKX with hρ
  have hρs : Function.Surjective ρ := Item87Proof.modThetaOnto_surjective hKX
  have hkθ : ρ.ker ≤ aschbacherSolvableCore 3 K :=
    hθmax _ (MonoidHom.normal_ker ρ) (Item87Proof.isSolvable_ker_modThetaOnto hKX)
      (Item87Proof.not_three_dvd_card_ker_modThetaOnto hKX)
  obtain ⟨k, rfl⟩ := hρs x
  have hkZ : (k : K ⧸ aschbacherSolvableCore 3 K) ∈
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H k' =>
      have h1 : ρ (k⁻¹ * k'⁻¹ * k * k') = 1 := by
        have hc := hxc (ρ k')
        simp only [map_mul, map_inv]
        rw [mul_assoc _ (ρ k) (ρ k'), hc]
        group
      have h2 : k⁻¹ * k'⁻¹ * k * k' ∈ aschbacherSolvableCore 3 K := hkθ h1
      have h3 : ((k' * k : K) : K ⧸ aschbacherSolvableCore 3 K) =
          ((k * k' : K) : K ⧸ aschbacherSolvableCore 3 K) := by
        rw [QuotientGroup.eq]
        have e : (k' * k)⁻¹ * (k * k') = k⁻¹ * k'⁻¹ * k * k' := by group
        rw [e]
        exact h2
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h3]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hkZ
  have hok : orderOf (⟨k, hkZ⟩ : aschbacherSolvableCore 3 K) = orderOf k :=
    (Subgroup.orderOf_coe _).symm
  have hdvd : orderOf (ρ k) ∣ orderOf (⟨k, hkZ⟩ : aschbacherSolvableCore 3 K) := by
    rw [hok]
    exact orderOf_map_dvd ρ k
  have hdvd2 : orderOf (⟨k, hkZ⟩ : aschbacherSolvableCore 3 K) ∣
      Nat.card (aschbacherSolvableCore 3 K) := orderOf_dvd_natCard _
  have h3 : orderOf (ρ k) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
  · exact hx1 (orderOf_eq_one_iff.mp h1)
  · rw [h1] at hdvd
    exact hθ3 (hdvd.trans hdvd2)

theorem center_projSL_two_eq_bot {k : ℕ} (hk : 2 ≤ k) :
    Subgroup.center (projSL 2 (GaloisField 2 k)) = ⊥ := by
  have : IsSimpleGroup (projSL 2 (GaloisField 2 k)) := Sec21.isSimpleGroup_projSL_two hk
  apply Item84Pair.center_eq_bot_of_isSimpleGroup
  obtain ⟨-, -, u, v, huv⟩ := Item87Proof.isQuasisimple_projSL_two hk
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  exact ⟨u', v', fun h' => huv (by rw [← QuotientGroup.mk_mul, h', QuotientGroup.mk_mul])⟩

theorem inducedAutHom_trans_conj {X : Subgroup G} {M₀ : Type*} [Group M₀]
    (E : X ⧸ aschbacherSolvableCore 3 X ≃* M₀) (g : M₀) (x : Subgroup.normalizer (X : Set G)) :
    inducedAutHom X (E.trans (MulAut.conj g)) x =
      MulAut.conj g * inducedAutHom X E x * (MulAut.conj g)⁻¹ := by
  rw [KFacts.inducedAutHom_apply, KFacts.inducedAutHom_apply, KFacts.congr_trans]
  ext m
  rfl

theorem exists_conj_residual_class {X : Subgroup G} {M₀ : Type*} [Group M₀]
    (E : X ⧸ aschbacherSolvableCore 3 X ≃* M₀) (hZ : Subgroup.center M₀ = ⊥) {c : G}
    (hcN : c ∈ Subgroup.normalizer (X : Set G)) (hc3 : c ^ 3 = 1)
    (hin : IsInnerAut (inducedAutHom X E ⟨c, hcN⟩))
    (hne : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨c, hcN⟩) ≠ 1) {P : M₀ → Prop}
    (hP : ∀ w : M₀, w ^ 3 = 1 → w ≠ 1 → ∃ g : M₀, P (g * w * g⁻¹)) :
    ∃ (E' : X ⧸ aschbacherSolvableCore 3 X ≃* M₀) (w : M₀),
      MulAut.conj w = inducedAutHom X E' ⟨c, hcN⟩ ∧ w ^ 3 = 1 ∧ w ≠ 1 ∧ P w ∧
      Nonempty (imageModTheta X
          (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G))) ≃*
        inSubgroup perfectResidual (Subgroup.centralizer ({w} : Set M₀))) := by
  obtain ⟨w₀, hw₀, hw₀3, hw₀1, -⟩ := exists_conj_residual E hZ hcN hc3 hin hne
  obtain ⟨g, hg⟩ := hP w₀ hw₀3 hw₀1
  set E' := E.trans (MulAut.conj g) with hE'
  have hcE' : inducedAutHom X E' ⟨c, hcN⟩ = MulAut.conj (g * w₀ * g⁻¹) := by
    rw [hE', inducedAutHom_trans_conj, ← hw₀, KFacts.mul_mulAutConj_mul_inv, MulAut.conj_apply]
  have hin' : IsInnerAut (inducedAutHom X E' ⟨c, hcN⟩) := by
    rw [hcE']
    exact ⟨_, rfl⟩
  obtain ⟨w, hw, hw3, hw1, hiso⟩ := exists_conj_residual E' hZ hcN hc3 hin' hne
  have hww : w = g * w₀ * g⁻¹ :=
    Item812Res7.conj_injective_of_center_trivial hZ (hw.trans hcE')
  exact ⟨E', w, hw, hw3, hw1, hww ▸ hg, hiso⟩

theorem ringChar_eq_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : ringChar K = 2 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hp, k, hpr, hk⟩ := FiniteField.card' K
  have h1 : p ∣ 2 ^ f := by
    rw [← hK, Nat.card_eq_fintype_card, hk]
    exact dvd_pow_self p k.ne_zero
  have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp (hpr.dvd_of_dvd_pow h1)
  subst h2
  exact ringChar.eq K 2

theorem four_le_two_pow {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem ringEquiv_pow_three_eq_one {K : Type} [Field K] [Finite K] {q : ℕ} {σ : K ≃+* K}
    (hK : Nat.card K = q ^ 3) (hσ : ∀ c, σ c = c ^ q) : σ ^ 3 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  apply RingEquiv.ext
  intro y
  have h1 : q * (q * q) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK]
    ring
  have h3 : σ (σ (σ y)) = y := by
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, h1, FiniteField.pow_card]
  exact h3

end Generic

@[expose] def ResidualShape (Q : Type*) [Group Q] (k : ℕ) : Prop :=
  Nonempty (Q ≃* projSL 2 (GaloisField 2 k)) ∨
    (IsQuasisimple Q ∧ ∃ x : Q, (∀ y, x * y = y * x) ∧ x ≠ 1 ∧ x ^ 3 = 1) ∨ Subsingleton Q

theorem ResidualShape.of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') {k : ℕ}
    (h : ResidualShape Q' k) : ResidualShape Q k := by
  unfold ResidualShape at h ⊢
  rcases h with hφ | ⟨hq, x, hxc, hx1, hx3⟩ | hs
  · obtain ⟨φ⟩ := hφ
    exact Or.inl ⟨e.trans φ⟩
  · refine Or.inr (Or.inl ⟨LocalCores.isQuasisimple_of_mulEquiv e.symm hq, e.symm x, ?_, ?_, ?_⟩)
    · intro y
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hxc]
    · intro h1
      apply hx1
      rw [← MulEquiv.apply_symm_apply e x, h1, map_one]
    · rw [← map_pow, hx3, map_one]
  · exact Or.inr (Or.inr ⟨fun u v => e.injective (Subsingleton.elim _ _)⟩)

theorem residualShape_of_threeA {M₀ : Type*} [Group M₀] [Finite M₀] {z : M₀} {k : ℕ}
    (h : ∃ N : Subgroup M₀, N ≤ Subgroup.centralizer ({z} : Set M₀) ∧
        (∀ x ∈ Subgroup.centralizer ({z} : Set M₀), ∀ y ∈ Subgroup.centralizer ({z} : Set M₀),
          x * y * x⁻¹ * y⁻¹ ∈ N) ∧
        IsQuasisimple N ∧ ∃ x ∈ N, (∀ n ∈ N, x * n = n * x) ∧ x ≠ 1 ∧ x ^ 3 = 1) :
    ResidualShape (inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set M₀))) k := by
  obtain ⟨N, hNC, hcomm, hq, x, hxN, hxc, hx1, hx3⟩ := h
  have heq := Sec21.Item228Census3Proof.inSubgroup_perfectResidual_eq_of_commutator hNC
    (Subgroup.isPerfect_iff.mp hq.1) hcomm
  refine ResidualShape.of_mulEquiv (MulEquiv.subgroupCongr heq) (Or.inr (Or.inl ⟨hq, ⟨x, hxN⟩,
    (fun y => Subtype.ext (hxc y y.2)), (fun h1 => hx1 (congrArg Subtype.val h1)),
    Subtype.ext (by simpa using hx3)⟩))

theorem residual_projSL_of_threeB {M₀ : Type*} [Group M₀] [Finite M₀] {z : M₀}
    {S : Subgroup M₀} (hSC : S ≤ Subgroup.centralizer ({z} : Set M₀))
    (hcomm : ∀ x ∈ Subgroup.centralizer ({z} : Set M₀), ∀ y ∈ Subgroup.centralizer ({z} : Set M₀),
      x * y * x⁻¹ * y⁻¹ ∈ S)
    {F : Type} [Field F] [Finite F] {k : ℕ} (hF : Nat.card F = 2 ^ k) (hk : 2 ≤ k)
    (e : SL(2, F) ≃* S) :
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set M₀)) ≃*
      projSL 2 (GaloisField 2 k)) := by
  obtain ⟨σ⟩ := KFacts.nonempty_sl2_mulEquiv_projSL hF
  have hSq : IsQuasisimple S :=
    LocalCores.isQuasisimple_of_mulEquiv (σ.symm.trans e) (Item87Proof.isQuasisimple_projSL_two hk)
  have heq := Sec21.Item228Census3Proof.inSubgroup_perfectResidual_eq_of_commutator hSC
    (Subgroup.isPerfect_iff.mp hSq.1) hcomm
  exact ⟨(MulEquiv.subgroupCongr heq).trans (e.symm.trans σ)⟩

theorem residualShape_of_threeB {M₀ : Type*} [Group M₀] [Finite M₀] {z : M₀} {S : Subgroup M₀}
    (hSC : S ≤ Subgroup.centralizer ({z} : Set M₀))
    (hcomm : ∀ x ∈ Subgroup.centralizer ({z} : Set M₀), ∀ y ∈ Subgroup.centralizer ({z} : Set M₀),
      x * y * x⁻¹ * y⁻¹ ∈ S)
    {F : Type} [Field F] [Finite F] {k : ℕ} (hF : Nat.card F = 2 ^ k) (hk : 2 ≤ k)
    (e : SL(2, F) ≃* S) :
    ResidualShape (inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set M₀))) k :=
  Or.inl (residual_projSL_of_threeB hSC hcomm hF hk e)

theorem isQuasisimple_residual_of_le {M₀ : Type*} [Group M₀] {z : M₀} {N : Subgroup M₀}
    (hNC : N ≤ Subgroup.centralizer ({z} : Set M₀))
    (hcomm : ∀ x ∈ Subgroup.centralizer ({z} : Set M₀), ∀ y ∈ Subgroup.centralizer ({z} : Set M₀),
      x * y * x⁻¹ * y⁻¹ ∈ N) (hq : IsQuasisimple N) :
    IsQuasisimple (inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set M₀))) := by
  have heq := Sec21.Item228Census3Proof.inSubgroup_perfectResidual_eq_of_commutator hNC
    (Subgroup.isPerfect_iff.mp hq.1) hcomm
  exact LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr heq).symm hq

section Models


variable {G : Type} [Group G] [Finite G]

theorem g2_residualShape (hC : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus)
    (hA : Sec11.KS11Lie4Proof.G2ThreeACentMinus) {X : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (X : Set G)) (hc3 : c ^ 3 = 1)
    (hck : ¬ (KFacts.InducesStdKind X c .field ∨ KFacts.InducesStdKind X c .graphField))
    (hne : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨c, hcN⟩) ≠ 1) {f : ℕ} (hf : 2 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (E : X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :
    ResidualShape (imageModTheta X
      (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)))) f := by
  have hK3 : ringChar K ≠ 3 := by rw [ringChar_eq_two_of_card hK]; decide
  have hK4 : 4 ≤ Nat.card K := hK ▸ four_le_two_pow hf
  have : Finite (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := Finite.of_equiv _ E.toEquiv
  have hin : IsInnerAut (inducedAutHom X E ⟨c, hcN⟩) := by
    by_contra hnot
    have hout : Sec4.InducesOuterTheta c X :=
      (KFacts.not_isInnerAut_inducedAutHom_iff X E hcN).mp hnot
    exact hck (Or.inl (KFacts.InducesStdKind.g2 K hK3 hK4
      (KFacts.inducesKindG2_field X hK3 hK4 hc3 hout E)))
  obtain ⟨-, w, -, hw3, hw1, hP, ⟨eW⟩⟩ := exists_conj_residual_class E
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot hcN hc3 hin hne
    (P := fun w => w ∈ Sec11.KS11Lie4Proof.g2ShortSL2 K ∨ w ∈ Sec11.KS11Lie4Proof.g2LongSL2 K)
    (fun w hw3 hw1 => Sec11.KS11Lie4Proof.g2ThreeConjSL2_of_minus hC K hK3 hK4 w hw3 hw1)
  refine ResidualShape.of_mulEquiv eW ?_
  rcases hP with hS | hM
  · exact residualShape_of_threeA
      (Sec11.KS11Lie4Proof.g2ThreeACent_of_minus hA K hK3 hK4 w hS hw3 hw1)
  · obtain ⟨e⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
    exact residualShape_of_threeB (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
      (Sec11.KS11Lie4Proof.g2Short_commute_g2Long hs hM))
      (Sec11.KS11Lie4Proof.g2ThreeBCent_holds K hK3 hK4 w hM hw3 hw1).1 hK hf e

theorem d4_residualShape {X : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (X : Set G)) (hc3 : c ^ 3 = 1)
    (hck : ¬ (KFacts.InducesStdKind X c .field ∨ KFacts.InducesStdKind X c .graphField))
    (hne : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨c, hcN⟩) ≠ 1) {m : ℕ} (hm1 : 1 ≤ m)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ m)
    (E : X ⧸ aschbacherSolvableCore 3 X ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ResidualShape (imageModTheta X
      (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)))) (3 * m) := by
  have hin : IsInnerAut (inducedAutHom X E ⟨c, hcN⟩) := by
    by_contra hnot
    have hout : Sec4.InducesOuterTheta c X :=
      (KFacts.not_isInnerAut_inducedAutHom_iff X E hcN).mp hnot
    exact hck (Or.inr (KFacts.InducesStdKind.triality m hm1 K hK σ hσ
      (KFacts.inducesKindTriality_graphField hm1 hK hσ X hc3 hout E)))
  have : Finite (graphFixedRootGroup TwistTag.D4 K
    σ.toRingHom) := Finite.of_equiv _ E.toEquiv
  have hσ3 : σ ^ 3 = 1 := ringEquiv_pow_three_eq_one hK hσ
  have hq3 : ¬ 3 ∣ 2 ^ m := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  obtain ⟨-, w, -, hw3, hw1, hP, ⟨eW⟩⟩ := exists_conj_residual_class E
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
    hcN hc3 hin hne
    (P := fun w => w ∈ Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom ∨
      w ∈ Subgroup.centralizer ((Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom : Subgroup
        (graphFixedRootGroup TwistTag.D4 K
          σ.toRingHom)) : Set (graphFixedRootGroup
            TwistTag.D4 K σ.toRingHom)))
    (fun w hw3 hw1 => Sec11.KS11Lie6Proof.d4ThreeConj_holds K (2 ^ m) σ hK hσ hq3 w hw3 hw1)
  refine ResidualShape.of_mulEquiv eW ?_
  rcases hP with hS | hCS
  · rcases Sec11.KS11Lie6Proof.d4ThreeACent_holds K (2 ^ m) σ hK hσ hq3 w hS hw3 hw1 with
      hsol | hN
    · refine Or.inr (Or.inr ⟨fun u v => ?_⟩)
      have hbot := Sec11.KS11Lie4Proof.eq_bot_of_isPerfect_of_isSolvable
        (Item87Proof.isPerfect_residual _)
        (Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion (Item87Proof.residual_le
            (Subgroup.centralizer ({w} : Set (graphFixedRootGroup
              TwistTag.D4 K σ.toRingHom)))))
          (Subgroup.inclusion_injective _))
      obtain ⟨u, hu⟩ := u
      obtain ⟨v, hv⟩ := v
      rw [hbot, Subgroup.mem_bot] at hu hv
      subst hu
      subst hv
      rfl
    · exact residualShape_of_threeA hN
  · obtain ⟨e⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
    have : Finite (orbitField TwistTag.D4 K σ.toRingHom
      Sec11.KS11Lie4Proof.d4Outer) := Subtype.finite
    have hF : Nat.card (orbitField TwistTag.D4 K
        σ.toRingHom Sec11.KS11Lie4Proof.d4Outer) = 2 ^ (3 * m) := by
      rw [Sec11.KS11Lie4Proof.natCard_orbitField_d4Outer hσ3, hK, ← pow_mul, mul_comm]
    exact residualShape_of_threeB (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hCS) s hs))
      (Sec11.KS11Lie6Proof.d4ThreeBCent_holds K (2 ^ m) σ hK hσ hq3 w hCS hw3 hw1).1 hF
      (by omega) e

theorem ree_residual {X : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (X : Set G)) (hc3 : c ^ 3 = 1)
    (hck : ¬ (KFacts.InducesStdKind X c .field ∨ KFacts.InducesStdKind X c .graphField))
    (hne : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨c, hcN⟩) ≠ 1) {m : ℕ}
    (hR : IsGammaTypeRee (X ⧸ aschbacherSolvableCore 3 X) m) :
    IsoSUThree (imageModTheta X
      (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)))) (2 ^ (3 * m)) := by
  obtain ⟨k, hk, hkm, ⟨e₀⟩⟩ := hR
  obtain ⟨-, k', hk'1, hkk', K, _, _, _, hK, ⟨e₁⟩⟩ :=
    Sec4.exists_mulEquiv_reeGamma ((Sec4.Census.bridgeExceptional46).reeF4 k hk)
  set E := e₀.trans e₁ with hE
  have : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma K k') := Finite.of_equiv _ E.toEquiv
  have hin : IsInnerAut (inducedAutHom X E ⟨c, hcN⟩) := by
    by_contra hnot
    have hout : Sec4.InducesOuterTheta c X :=
      (KFacts.not_isInnerAut_inducedAutHom_iff X E hcN).mp hnot
    exact hck (Or.inl (KFacts.InducesStdKind.largeRee k' hk'1 K hK
      (KFacts.inducesKindLargeRee_field X hk'1 hK
        (CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj k' K hK) hc3 hout E)))
  obtain ⟨w, -, hw3, hw1, ⟨eW⟩⟩ := exists_conj_residual E
    (CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial k' K hK) hcN hc3 hin hne
  obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ := Sec8.ReeF4Conj2Proof.kF83ReeCentThree_holds k' K hk'1 hK w
    (orderOf_eq_prime hw3 hw1)
  have h3m : 2 * k' + 1 = 3 * m := by omega
  rw [h3m] at hF ψ
  exact ⟨F, inferInstance, inferInstance, hF, ⟨eW.trans ψ⟩⟩

@[expose] def KF84Sp4ThreeCent : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], 4 ≤ Nat.card F →
    ∀ y : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F),
      orderOf y = 3 →
        Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set
          (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F)))) ≃*
          SL(2, F))

theorem sp4_residual (hSp : KF84Sp4ThreeCent) {X : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (X : Set G)) (hc3 : c ^ 3 = 1)
    (hck : ¬ (KFacts.InducesStdKind X c .field ∨ KFacts.InducesStdKind X c .graphField))
    (hne : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨c, hcN⟩) ≠ 1) {f : ℕ} (hf : 2 ≤ f)
    (eX : X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 f)) :
    Nonempty (imageModTheta X
      (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G))) ≃*
        projSL 2 (GaloisField 2 f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f with hFdef
  have hF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  have hF4 : 4 ≤ Nat.card F := hF ▸ four_le_two_pow hf
  set e : X ⧸ aschbacherSolvableCore 3 X ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    eX.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
      (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).symm with he
  have : Finite (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :=
    Finite.of_equiv _ e.toEquiv
  have hin : IsInnerAut (inducedAutHom X e ⟨c, hcN⟩) := by
    by_contra hnot
    have hout : Sec4.InducesOuterTheta c X :=
      (KFacts.not_isInnerAut_inducedAutHom_iff X e hcN).mp hnot
    rcases KFacts.inducesKindPSp4Even_diagonal_or_field X hc3 hout e with ⟨hx, hD, hni⟩ | hfield
    · obtain ⟨A, hA⟩ := hD
      apply hni
      rw [← hA]
      exact KFacts.conjAut_mem_inner_of_charTwo A
    · exact hck (Or.inl (KFacts.InducesStdKind.psp4even F ⟨e, hfield⟩))
  obtain ⟨w₀, hw₀⟩ := hin
  have hnab : ∃ u v : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F),
      u * v ≠ v * u := by
    by_contra hall
    push Not at hall
    apply hne
    apply (MulAut.congr e).injective
    rw [map_one, ← KFacts.inducedAutHom_apply, ← hw₀]
    ext z
    rw [MulAut.conj_apply, MulAut.one_apply, hall w₀ z, mul_inv_cancel_right]
  have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr hF4))
  have hZ := Item84Pair.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨w, -, hw3, hw1, ⟨eW⟩⟩ := exists_conj_residual e hZ hcN hc3 ⟨w₀, hw₀⟩ hne
  obtain ⟨ι⟩ := hSp F hF4 w (orderOf_eq_prime hw3 hw1)
  obtain ⟨σ⟩ := KFacts.nonempty_sl2_mulEquiv_projSL hF
  exact ⟨eW.trans (ι.trans σ)⟩

end Models

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

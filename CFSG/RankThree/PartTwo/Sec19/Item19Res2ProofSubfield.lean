module

public import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJ
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSubfieldCore
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Assembly.RankThreeEven (projSL)

theorem nine_dvd_two_pow_three_mul_sub_one {e : ℕ} (he3 : 2 ^ e % 3 = 1) :
    9 ∣ 2 ^ (3 * e) - 1 := by
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ e = 3 * a + 1 := ⟨2 ^ e / 3, by omega⟩
  rw [mul_comm, pow_mul, ha]
  have h : (3 * a + 1) ^ 3 = 9 * (3 * a ^ 3 + 3 * a ^ 2 + a) + 1 := by ring
  rw [h, Nat.add_sub_cancel]
  exact dvd_mul_right 9 _

theorem exists_mul_ne_of_isPerfect {Q : Type*} [Group Q] [Nontrivial Q] [Group.IsPerfect Q] :
    ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hcomm : commutator Q = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, h a b, mul_inv_cancel_right, mul_inv_cancel, Subgroup.mem_bot]
  have htop := Group.IsPerfect.commutator_eq_top (G := Q)
  rw [hcomm] at htop
  exact bot_ne_top htop

theorem ksJParSubfield :
    KSJParSubfield := by
  intro G _ _ K L hLK c e he1 he3 hKiso hLiso hLp hcN hc3 hkind hLc P hP hcP
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψK⟩ := hKiso
  obtain ⟨ψL⟩ := hLiso
  set F := GaloisField 2 (3 * e) with hF
  set F₀ := GaloisField 2 e with hF₀
  have hFcard : Nat.card F = 2 ^ (3 * e) := GaloisField.card 2 (3 * e) (by omega)
  have hF₀card : Nat.card F₀ = 2 ^ e := GaloisField.card 2 e (by omega)
  set Ψ : K ⧸ CFSG.pCore 2 K ≃* projectiveSL 3 F :=
    ψK.trans (Sec4.projSLEquivProjectiveSL 3 F) with hΨ
  have hq3 : 2 ^ (3 * e) % 3 = 1 := by
    rw [mul_comm, pow_mul, Nat.pow_mod, he3]
  obtain ⟨hperf, -⟩ := Sec13.isPerfect_center_projSL 2 (3 * e) (by omega) hq3
  have hsimple := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field F
  have hnab := exists_mul_ne_of_isPerfect (Q := projSL 3 F)
  have hsimpleK : IsSimpleGroup (K ⧸ CFSG.pCore 2 K) := ψK.isSimpleGroup
  have hnabK : ∃ a b : K ⧸ CFSG.pCore 2 K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨ψK.symm a, ψK.symm b, fun h => hab ?_⟩
    apply ψK.symm.injective
    rw [map_mul, map_mul, h]
  obtain ⟨hqK, hcK⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnabK
  have hθ : aschbacherSolvableCore 3 K = CFSG.pCore 2 K :=
    Sec14.aschbacherSolvableCore_eq_pCore_two hqK hcK
  set Ψ' : K ⧸ aschbacherSolvableCore 3 K ≃* projectiveSL 3 F :=
    (QuotientGroup.quotientMulEquivOfEq hθ).trans Ψ with hΨ'
  set τ := Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩) with hτ
  set α := MulAut.congr Ψ' τ with hα
  have hα3 : α ^ 3 = 1 := by
    have hc3' : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hc3 ▸ pow_orderOf_eq_one c)
    rw [hα, hτ, ← map_pow, ← map_pow, ← map_pow, hc3', map_one, map_one, map_one]
  have hout : ¬ KFacts.IsInnerAut α := by
    rw [hα, KFacts.isInnerAut_congr]
    obtain ⟨hx, hnot⟩ := hkind.inducesOuterTheta K (by decide)
    exact hnot
  have hconjK : ∀ k : K, c * (k : G) * c⁻¹ ∈ K := fun k =>
    (Subgroup.mem_normalizer_iff.mp hcN k).mp k.2
  have hαk : ∀ k : K, α (Ψ (k : K ⧸ CFSG.pCore 2 K)) =
      Ψ ((⟨c * k * c⁻¹, hconjK k⟩ : K) : K ⧸ CFSG.pCore 2 K) := by
    intro k
    have h1 : Ψ'.symm (Ψ (k : K ⧸ CFSG.pCore 2 K)) = (k : K ⧸ aschbacherSolvableCore 3 K) := by
      apply Ψ'.injective
      rw [MulEquiv.apply_symm_apply]
      change Ψ _ = Ψ (QuotientGroup.quotientMulEquivOfEq hθ (k : K ⧸ aschbacherSolvableCore 3 K))
      rw [QuotientGroup.quotientMulEquivOfEq_mk]
    change Ψ' (τ (Ψ'.symm (Ψ (k : K ⧸ CFSG.pCore 2 K)))) = _
    rw [h1, hτ, Sec4.thetaQuotMulAut_mk]
    change Ψ (QuotientGroup.quotientMulEquivOfEq hθ _) = _
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  set Φ : L →* projectiveSL 3 F := Ψ.toMonoidHom.comp (Step1911EndProof.phiL hLK) with hΦ
  set Lb := Φ.range with hLb
  have hfix : ∀ y ∈ Lb, α y = y := by
    rintro _ ⟨l, rfl⟩
    change α (Ψ (Step1911EndProof.phiL hLK l)) = Ψ (Step1911EndProof.phiL hLK l)
    rw [Step1911EndProof.phiL_apply, hαk]
    have hcl : c * (l : G) * c⁻¹ = l := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2)
      rw [← this, mul_inv_cancel_right]
    congr 2
    exact Subtype.ext hcl
  set P' := P.map Ψ.toMonoidHom with hP'
  have hPα : ∀ y ∈ P', α y ∈ P' := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective p
    refine ⟨_, hcP k ⟨c * k * c⁻¹, hconjK k⟩ rfl hp, ?_⟩
    exact (hαk k).symm
  have hP'par : IsProperParabolic P' := isProperParabolic_map_equiv Ψ hP
  have hLbp : Group.IsPerfect Lb :=
    Group.IsPerfect.ofSurjective (f := Φ.rangeRestrict) Φ.rangeRestrict_surjective
  have hker2 : IsPGroup 2 Φ.ker := by
    intro x
    have h1 : Step1911EndProof.phiL hLK (x : L) = 1 := by
      apply Ψ.injective
      rw [map_one]
      exact MonoidHom.mem_ker.mp x.2
    have hx := (Step1911EndProof.phiL_eq_one_iff hLK x).mp h1
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hkerle : Φ.ker ≤ CFSG.pCore 2 L := le_sSup ⟨inferInstance, hker2⟩
  have hcardL₀ : Nat.card (L ⧸ CFSG.pCore 2 L) = Nat.card (projectiveSL 3 F₀) :=
    Nat.card_congr (ψL.trans (Sec4.projSLEquivProjectiveSL 3 F₀)).toEquiv
  have hL1 : Nat.card L = Nat.card Lb * Nat.card Φ.ker := by
    rw [hLb, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hL2 : Nat.card L = Nat.card (L ⧸ CFSG.pCore 2 L) * Nat.card (CFSG.pCore 2 L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hkerle
  have hkpos : 0 < Nat.card Φ.ker := Nat.card_pos
  have hLbt : Nat.card Lb = Nat.card (L ⧸ CFSG.pCore 2 L) * t := by
    have : Nat.card Lb * Nat.card Φ.ker = Nat.card (L ⧸ CFSG.pCore 2 L) * t * Nat.card Φ.ker := by
      rw [← hL1, hL2, ht]
      ring
    exact Nat.eq_of_mul_eq_mul_right hkpos this
  have hdvd : Nat.card (projectiveSL 3 F₀) ∣ Nat.card Lb := ⟨t, by rw [hLbt, hcardL₀]⟩
  have h9 : 9 ∣ Nat.card F - 1 := by
    rw [hFcard]
    exact nine_dvd_two_pow_three_mul_sub_one he3
  have hK₀ : Nat.card F₀ ^ 3 = Nat.card F := by
    rw [hF₀card, hFcard, ← pow_mul, mul_comm]
  obtain ⟨hcardLb, hpar⟩ := core h9 hα3 hout hLbp hfix hK₀ hdvd hP'par hPα
  have hker : Φ.ker = CFSG.pCore 2 L := by
    refine Subgroup.eq_of_le_of_card_ge hkerle ?_
    have h1 : Nat.card L = Nat.card (L ⧸ CFSG.pCore 2 L) * Nat.card Φ.ker := by
      rw [hL1, hcardLb, hcardL₀]
    have hqpos : 0 < Nat.card (L ⧸ CFSG.pCore 2 L) := Nat.card_pos
    have h2 : Nat.card (L ⧸ CFSG.pCore 2 L) * Nat.card (CFSG.pCore 2 L) =
        Nat.card (L ⧸ CFSG.pCore 2 L) * Nat.card Φ.ker := by rw [← hL2, h1]
    exact (Nat.eq_of_mul_eq_mul_left hqpos h2).le
  set Θ : L ⧸ CFSG.pCore 2 L ≃* Lb :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange Φ)
    with hΘ
  have hΘmk : ∀ l : L, ((Θ (l : L ⧸ CFSG.pCore 2 L) : Lb) : projectiveSL 3 F) = Φ l := fun l =>
    rfl
  have heq : (P.comap (Step1911EndProof.phiL hLK)).map (QuotientGroup.mk' (CFSG.pCore 2 L)) =
      ((P' ⊓ Lb).subgroupOf Lb).map Θ.symm.toMonoidHom := by
    ext z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf, hΘmk]
    constructor
    · rintro ⟨l', hl', hl'l⟩
      have hll : Φ l' = Φ l := by
        rw [QuotientGroup.mk'_apply] at hl'l
        have h1 := QuotientGroup.eq.mp hl'l
        rw [← hker] at h1
        have h2 := MonoidHom.mem_ker.mp h1
        rw [map_mul, map_inv, inv_mul_eq_one] at h2
        exact h2
      refine ⟨?_, ⟨l, rfl⟩⟩
      rw [← hll]
      exact ⟨_, hl', rfl⟩
    · rintro ⟨⟨p, hp, hpl⟩, -⟩
      refine ⟨l, ?_, rfl⟩
      have h1 : p = Step1911EndProof.phiL hLK l := Ψ.injective hpl
      rw [SetLike.mem_coe, Subgroup.mem_comap, ← h1]
      exact hp
  rw [heq]
  exact isProperParabolic_map_equiv Θ.symm hpar

end CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof

module

public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofFour
public import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofU4Inv
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport
import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace Item21Early3Proof

variable {G : Type} [Group G]

theorem center_eq_bot_of_simple_perfect {X : Type*} [Group X] [IsSimpleGroup X]
    [Group.IsPerfect X] : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative X := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative X hc

theorem three_dvd_two_pow_add_one {n : ℕ} (hno : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hno
  have h : (2 : ℕ) ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h]

end Item21Early3Proof

open Item21Early3Proof

theorem item214UnitaryOdd_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) : Item214UnitaryOdd := by
  intro G _ _ A E U c L hpair ⟨n, hn1, hno, ⟨eL⟩⟩ ⟨U', hU', hU'L⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := hpair.standing
  have hG := hst.toTheoremFourHyp
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩
  have hcomA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hEA : E ≤ A := hpair.mem_E.2
  have hcA : c ∈ A := hEA hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLstar : L ∈ lStar A := hpairs.2.2.1.2.2
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA hc1 L hLc
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have := isSimpleGroup_projSU (m := 4) (n := n) le_rfl (by omega)
  have : IsSimpleGroup L := eL.isSimpleGroup
  have hZL : Subgroup.center L = ⊥ := center_eq_bot_of_simple_perfect
  have hθ : aschbacherSolvableCore 3 L = ⊥ := by
    obtain ⟨hTs, -⟩ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 L) with h | h
    · exact h
    · exfalso
      rw [h] at hTs
      have hsol : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := L)).symm.injective
      exact Group.IsPerfect.not_isSolvable L hsol
  let eθ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 2 n :=
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot).trans eL
  have hrep : ∀ x ∈ A, ∃ y ∈ A ⊓ L, ∀ l ∈ L, x * l * x⁻¹ = y * l * y⁻¹ := by
    intro x hx
    have hout := Item223PrintProof.not_inducesOuterTheta_of_mem_thetaComponentsAt hG hc3 hc1
      hLc (by omega) eθ (hcomA x hx c hcA) (hAe.2 x hx)
    obtain ⟨y, hyL, hy⟩ :=
      Item223PrintProof.exists_conj_eq_of_not_inducesOuterTheta hθ (hAL hx) hout
    exact ⟨y, ⟨Item223PrintProof.mem_of_conj_eq hAmax hAL hZL hx hyL hy, hyL⟩, hy⟩
  have hCA : Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ≤ 3 := by
    have hcyc := h66 G hst A hpair.mem_S L hLstar
    have hle : A ⊓ Subgroup.centralizer (L : Set G) ≤ A ⊓ Sec4.thetaQuotCentralizer L := by
      rintro x ⟨hxA, hxC⟩
      refine ⟨hxA, Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAL hxA, fun l hl => ?_⟩⟩
      rw [← Subgroup.mem_centralizer_iff.mp hxC l hl, mul_inv_cancel_right, inv_mul_cancel]
      exact Subgroup.one_mem _
    have hexp : Monoid.exponent (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hAe.2 x x.2.1)
    rw [IsCyclic.exponent_eq_card] at hexp
    exact (Subgroup.card_le_of_le hle).trans (Nat.le_of_dvd (by norm_num) hexp)
  obtain ⟨hU'E, hU'ab, hU'4⟩ := mem_fourGroups_iff.mp hU'.1
  have hCE9 := Sec6.card_inf_centralizer_of_mem_fourGroupsMinus
    (Late.isE27_of_mem_partTwoE hpair.mem_E.1) hU'
  obtain ⟨f, hfE, hfL⟩ : ∃ f ∈ E ⊓ Subgroup.centralizer (U' : Set G),
      f ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hno
    push Not at hno
    have hle : E ⊓ Subgroup.centralizer (U' : Set G) ≤ A ⊓ Subgroup.centralizer (L : Set G) :=
      fun x hx => ⟨hEA hx.1, hno x hx⟩
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨e, heE, u, hu, heu⟩ : ∃ e ∈ E, ∃ u ∈ U', e * u * e⁻¹ ≠ u := by
    by_contra hno
    push Not at hno
    have hbot : ⁅U', E⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := hno x hx w hw
      calc x * w = x * w * x⁻¹ * x := by group
        _ = w * x := by rw [this]
    have h1 : U' = ⊥ := hU'.2.trans hbot
    rw [h1, Subgroup.card_bot] at hU'4
    norm_num at hU'4
  obtain ⟨yf, hyf, hf⟩ := hrep f (hEA hfE.1)
  obtain ⟨ye, hye, he⟩ := hrep e (hEA heE)
  have huL : u ∈ L := hU'L hu
  have hyf1 : yf ≠ 1 := by
    rintro rfl
    apply hfL
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hf l hl
    rw [one_mul, inv_one, mul_one] at h1
    calc l * f = f * l * f⁻¹ * f := by rw [h1]
      _ = f * l := by group
  have hyfu : yf * u = u * yf := by
    have h1 := hf u huL
    have h2 : f * u * f⁻¹ = u := by
      rw [(Subgroup.mem_centralizer_iff.mp hfE.2 u hu).symm, mul_inv_cancel_right]
    calc yf * u = yf * u * yf⁻¹ * yf := by group
      _ = u * yf := by rw [← h1, h2]
  have heuU : e * u * e⁻¹ ∈ U' := (Subgroup.mem_normalizer_iff.mp (hU'E heE) u).mp hu
  have hyeu : ye * u * ye⁻¹ = e * u * e⁻¹ := (he u huL).symm
  have hUc : ∀ w ∈ U', ∀ w' ∈ U', w * w' = w' * w := fun w hw w' hw' =>
    congrArg Subtype.val (hU'ab.1.is_comm.comm ⟨w, hw⟩ ⟨w', hw'⟩)
  have hu2 : u * u = 1 := by rw [← sq]; exact hU'ab.2 u hu
  set K := GaloisField 2 (2 * n) with hKdef
  have hK : Nat.card K = (2 ^ n) ^ 2 := U4Lines.card_galoisField_two_mul n (by omega)
  have hU : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hpq : 3 ∣ 2 ^ n + 1 := three_dvd_two_pow_add_one hno
  let e₀ : projSU 4 2 n ≃* StatedProj (StatedSU 4 (2 ^ n) K) :=
    (MulEquiv.subgroupCongr (Census.projImage_statedSU 4 2 n).symm).trans
      (Census.statedProjEquivProjImage _).symm
  let eZ : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU 4 (2 ^ n) K) :=
    (QuotientGroup.quotientMulEquivOfEq hZL).trans
      (QuotientGroup.quotientBot.trans (eL.trans e₀))
  set F : Subgroup L := (A ⊓ L).subgroupOf L with hFdef
  have hFexp : ∀ z ∈ F, z ^ 3 = 1 := by
    intro z hz
    apply Subtype.ext
    have hzA : (z : G) ∈ A := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).1
    simpa using hAe.2 _ hzA
  have hFcomm : ∀ z ∈ F, ∀ w ∈ F, z * w = w * z := by
    intro z hz w hw
    apply Subtype.ext
    exact hcomA _ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).1 _
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)).1
  obtain ⟨ψ, hψ⟩ := CFSG.RankThree.PartOne.KFU.exists_diag_iso_le (by omega) hK Nat.prime_three
    hpq hZL eZ F hFexp hFcomm
  set yf' : L := ⟨yf, hyf.2⟩ with hyf'
  set ye' : L := ⟨ye, hye.2⟩ with hye'
  set u' : L := ⟨u, huL⟩ with hu'
  have hyfF : yf' ∈ F := Subgroup.mem_subgroupOf.mpr hyf
  have hyeF : ye' ∈ F := Subgroup.mem_subgroupOf.mpr hye
  have hft : ((ψ.symm yf' : unitarySU 2 n K 4) : GL (Fin 4) K) ∈
      CFSG.RankThree.PartOne.KFU.torusSU 3 4 K :=
    hψ _ (by rw [MulEquiv.apply_symm_apply]; exact hyfF)
  have het : ((ψ.symm ye' : unitarySU 2 n K 4) : GL (Fin 4) K) ∈
      CFSG.RankThree.PartOne.KFU.torusSU 3 4 K :=
    hψ _ (by rw [MulEquiv.apply_symm_apply]; exact hyeF)
  have hf1 : ((ψ.symm yf' : unitarySU 2 n K 4) : GL (Fin 4) K) ≠ 1 := by
    intro h1
    apply hyf1
    have h2 : ψ.symm yf' = 1 := Subtype.ext h1
    have h3 : yf' = 1 := by rw [← ψ.symm.injective.eq_iff, h2, map_one]
    exact congrArg Subtype.val h3
  have hvv : ((ψ.symm u' : unitarySU 2 n K 4) : GL (Fin 4) K) *
      (ψ.symm u' : unitarySU 2 n K 4) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul,
      show u' * u' = 1 from Subtype.ext hu2, map_one, Subgroup.coe_one]
  have hfv : ((ψ.symm yf' : unitarySU 2 n K 4) : GL (Fin 4) K) *
      (ψ.symm u' : unitarySU 2 n K 4) =
      (ψ.symm u' : unitarySU 2 n K 4) * (ψ.symm yf' : unitarySU 2 n K 4) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      show yf' * u' = u' * yf' from Subtype.ext hyfu]
  have hconj : ψ.symm ye' * ψ.symm u' * (ψ.symm ye')⁻¹ =
      ψ.symm (⟨e * u * e⁻¹, hU'L heuU⟩ : L) := by
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext hyeu
  have hvw : ((ψ.symm u' : unitarySU 2 n K 4) : GL (Fin 4) K) *
      ((ψ.symm ye' : unitarySU 2 n K 4) * (ψ.symm u' : unitarySU 2 n K 4) *
        ((ψ.symm ye' : unitarySU 2 n K 4) : GL (Fin 4) K)⁻¹) =
      ((ψ.symm ye' : unitarySU 2 n K 4) * (ψ.symm u' : unitarySU 2 n K 4) *
        ((ψ.symm ye' : unitarySU 2 n K 4) : GL (Fin 4) K)⁻¹) *
        (ψ.symm u' : unitarySU 2 n K 4) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul, hconj, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (hUc u hu _ heuU)
  have hkey := conj_eq_of_torus hU hft het hf1 (ψ.symm u').2 hvv hfv hvw
  apply heu
  have h1 : ψ.symm ye' * ψ.symm u' * (ψ.symm ye')⁻¹ = ψ.symm u' := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hkey
  rw [hconj] at h1
  have h2 := congrArg Subtype.val (ψ.symm.injective h1)
  exact h2

theorem item214Unitary_of_items
    (h211 : Item211) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) :
    Item214Unitary :=
  item214Unitary_of h211 (item214UnitaryOdd_of h45 h66)

end CFSG.RankThree.PartTwo.Sec21

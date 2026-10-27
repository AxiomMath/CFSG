module

import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofKField
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec14.Ronan1422IQBUnique
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1418Off

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_thetaQuotCentralizer_of_forall {K R : Subgroup G} {b : G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hRb : ⁅R, Subgroup.zpowers b⁆ = R)
    (h : ∀ y ∈ Subgroup.zpowers b, ∃ u v : G, y = u * v ∧
      u ∈ Subgroup.normalizer (K : Set G) ∧ (∀ r ∈ R, u * r = r * u) ∧
      v ∈ thetaQuotCentralizer K) :
    R ≤ thetaQuotCentralizer K := by
  rw [← hRb, Subgroup.commutator_le]
  intro r hr y hy
  obtain ⟨u, v, rfl, huN, hur, hv⟩ := h y hy
  have hrv : r * v * r⁻¹ ∈ thetaQuotCentralizer K := conj_mem_thetaQuotCentralizer hv (hRK hr)
  have hw : r * v * r⁻¹ * v⁻¹ ∈ thetaQuotCentralizer K := mul_mem hrv (inv_mem hv)
  have hw' := conj_mem_thetaQuotCentralizer hw huN
  have hru : r * u = u * r := (hur r hr).symm
  have e : ⁅r, u * v⁆ = u * (r * v * r⁻¹ * v⁻¹) * u⁻¹ := by
    rw [commutatorElement_def]
    calc r * (u * v) * r⁻¹ * (u * v)⁻¹ = (r * u) * v * r⁻¹ * v⁻¹ * u⁻¹ := by group
      _ = (u * r) * v * r⁻¹ * v⁻¹ * u⁻¹ := by rw [hru]
      _ = u * (r * v * r⁻¹ * v⁻¹) * u⁻¹ := by group
  rw [e]
  exact hw'

theorem inf_thetaQuotCentralizer_le {A E K R : Subgroup G} {b : G}
    (hAab : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hE : IsHyperplane A E)
    (hbA : b ∈ A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hRE : R ≤ Subgroup.centralizer (E : Set G))
    (hRb : ⁅R, Subgroup.zpowers b⁆ = R) (hR : ¬ R ≤ thetaQuotCentralizer K) :
    A ⊓ thetaQuotCentralizer K ≤ E ∧ b ∉ thetaQuotCentralizer K := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hE9 : Nat.card E = 9 := by
    have h := hE.2
    rw [h27] at h
    omega
  refine ⟨fun x hx => ?_, fun hb => hR (le_thetaQuotCentralizer_of_forall hRK hRb fun y hy =>
    ⟨1, y, (one_mul y).symm, one_mem _, fun r _ => by rw [one_mul, mul_one],
      Subgroup.zpowers_le.mpr hb hy⟩)⟩
  by_contra hxE
  apply hR
  refine le_thetaQuotCentralizer_of_forall hRK hRb fun y hy => ?_
  have hyA : y ∈ A := Subgroup.zpowers_le.mpr hbA hy
  have hsup : E ⊔ Subgroup.zpowers x = A :=
    Sec12.eq_of_card_nine_lt h27 (sup_le hE.1 (Subgroup.zpowers_le.mpr hx.1)) le_sup_left hE9
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) hxE
  have hc : ∀ u ∈ E, ∀ v ∈ Subgroup.zpowers x, u * v = v * u := fun u hu v hv =>
    hcomm u (hE.1 hu) v (Subgroup.zpowers_le.mpr hx.1 hv)
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc
  have hy' : y ∈ ((E ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [hsup]
    exact hyA
  rw [hset] at hy'
  obtain ⟨u, hu, v, hv, rfl⟩ := hy'
  exact ⟨u, v, rfl, hAK (hE.1 hu), fun r hr => Subgroup.mem_centralizer_iff.mp (hRE hr) u hu,
    Subgroup.zpowers_le.mpr hx.2 hv⟩

theorem inf_thetaQuotCentralizer_eq {A E K R : Subgroup G} {b e : G}
    (hAab : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hE : IsHyperplane A E)
    (hbA : b ∈ A) (heE : e ∈ E) (he1 : e ≠ 1) (hK : K ∈ thetaComponentsAt 3 e)
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hRE : R ≤ Subgroup.centralizer (E : Set G))
    (hRb : ⁅R, Subgroup.zpowers b⁆ = R) (hR : ¬ R ≤ thetaQuotCentralizer K) :
    A ⊓ thetaQuotCentralizer K = Subgroup.zpowers e ∨ A ⊓ thetaQuotCentralizer K = E := by
  obtain ⟨hle, -⟩ := inf_thetaQuotCentralizer_le hAab h27 hE hbA hAK hRK hRE hRb hR
  have he3 : e ^ 3 = 1 := hAab.2 e (hE.1 heE)
  have heC : Subgroup.zpowers e ≤ A ⊓ thetaQuotCentralizer K :=
    Subgroup.zpowers_le.mpr ⟨hE.1 heE, mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hK⟩
  have hE9 : Nat.card E = 9 := by
    have h := hE.2
    rw [h27] at h
    omega
  have hdvd : Nat.card (A ⊓ thetaQuotCentralizer K : Subgroup G) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hE9]
    exact Subgroup.card_dvd_of_le hle
  have h3 : Nat.card (Subgroup.zpowers e) = 3 := Sec13.card_zpowers_of_pow_three he3 he1
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h3dvd : 3 ∣ Nat.card (A ⊓ thetaQuotCentralizer K : Subgroup G) :=
    h3 ▸ Subgroup.card_dvd_of_le heC
  interval_cases k
  · rw [hk] at h3dvd
    norm_num at h3dvd
  · left
    exact (Subgroup.eq_of_le_of_card_ge heC (by rw [hk, h3]; norm_num)).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hk, hE9]; norm_num)

theorem eq_of_le_inf {H X X' J : Subgroup G} (hX : X ∈ thetaComponentsIn H)
    (hX' : X' ∈ thetaComponentsIn H) (hJp : Group.IsPerfect J) (hJ : J ≤ X ⊓ X')
    (hJθ : ¬ J ≤ inSubgroup (aschbacherSolvableCore 3) H) : X = X' := by
  by_contra hne
  apply hJθ
  rw [← commutator_self_eq_of_isPerfect hJp, Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact Ronan1422IQB.commutator_mem_theta_of_ne_in hX hX' hne (hJ hx).1 (hJ hy).2

theorem mem_lStar_of_inf_le_zpowers {A K : Subgroup G} {e : G} (heA : e ∈ A) (he1 : e ≠ 1)
    (hA3 : ∀ x ∈ A, x ^ 3 = 1) (hK : K ∈ thetaComponentsAt 3 e)
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hC : A ⊓ thetaQuotCentralizer K ≤ Subgroup.zpowers e) : K ∈ lStar A := by
  refine ⟨mem_thetaComponentFamily_iff.mpr ⟨e, heA, he1, hK⟩, fun K' hK' hKK' => ?_⟩
  obtain ⟨e', he'A, he'1, hK'e'⟩ := mem_thetaComponentFamily_iff.mp hK'
  set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
  set J := inSubgroup perfectResidual (K ⊓ K') with hJ
  have hJle : J ≤ K ⊓ K' := Sec6.inSubgroup_perfectResidual_le _
  have hJK' : J ≤ Subgroup.centralizer ({e'} : Set G) :=
    (hJle.trans inf_le_right).trans (le_centralizer_of_mem_thetaComponentsAt hK'e')
  have he'C : e' ∈ thetaQuotCentralizer K := by
    have hJN : J ≤ Subgroup.normalizer (θK : Set G) :=
      (hJle.trans inf_le_left).trans (le_normalizer_theta K)
    have hset : ((θK ⊔ J : Subgroup G) : Set G) = (θK : Set G) * (J : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left θK J hJN
    refine mem_thetaQuotCentralizer_iff.mpr ⟨hAK he'A, fun l hl => ?_⟩
    have hl' : l ∈ ((θK ⊔ J : Subgroup G) : Set G) := by
      have hKeq : K = J ⊔ θK := hKK'
      rw [sup_comm, ← hKeq]
      exact hl
    rw [hset] at hl'
    obtain ⟨t, ht, j, hj, rfl⟩ := hl'
    have hje : e' * j = j * e' :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hJK' hj)).symm
    have hte : e' * t * e'⁻¹ ∈ θK :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_theta K (hAK he'A)) t).mp ht
    have hjK : j ∈ K := (hJle hj).1
    have h1 : t⁻¹ * (e' * t * e'⁻¹) ∈ θK := mul_mem (inv_mem ht) hte
    have h2 : j⁻¹ * (t⁻¹ * (e' * t * e'⁻¹)) * j⁻¹⁻¹ ∈ θK :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta K (inv_mem hjK)) _).mp h1
    have e : (t * j)⁻¹ * (e' * (t * j) * e'⁻¹) = j⁻¹ * (t⁻¹ * (e' * t * e'⁻¹)) * j⁻¹⁻¹ := by
      calc (t * j)⁻¹ * (e' * (t * j) * e'⁻¹) = j⁻¹ * t⁻¹ * (e' * t * e'⁻¹) * (e' * j * e'⁻¹) := by
            group
        _ = j⁻¹ * t⁻¹ * (e' * t * e'⁻¹) * j := by rw [hje, mul_inv_cancel_right]
        _ = j⁻¹ * (t⁻¹ * (e' * t * e'⁻¹)) * j⁻¹⁻¹ := by group
    rw [e]
    exact h2
  have he'e : e' ∈ Subgroup.zpowers e := hC ⟨he'A, he'C⟩
  have heq : Subgroup.zpowers e' = Subgroup.zpowers e :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he'e) (by
      rw [Sec13.card_zpowers_of_pow_three (hA3 e heA) he1,
        Sec13.card_zpowers_of_pow_three (hA3 e' he'A) he'1])
  have hcent : Subgroup.centralizer ({e'} : Set G) = Subgroup.centralizer ({e} : Set G) := by
    rw [Sec13.centralizer_singleton_eq_zpowers, Sec13.centralizer_singleton_eq_zpowers, heq]
  have hK'e : K' ∈ thetaComponentsAt 3 e := by
    unfold thetaComponentsAt at hK'e' ⊢
    rw [hcent] at hK'e'
    exact hK'e'
  have hJθ : ¬ J ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) := by
    intro hle
    have hKC : K ≤ Subgroup.centralizer ({e} : Set G) := le_centralizer_of_mem_thetaComponentsAt hK
    have hJθK : J ≤ θK :=
      le_inf hle (hJle.trans inf_le_left) |>.trans (Res611Res7.theta_inf_le_theta hKC)
    have hKθ : K ≤ θK := by
      have hKeq : K = J ⊔ θK := hKK'
      rw [hKeq]
      exact sup_le hJθK le_rfl
    exact Sec15.Proof1423.not_le_thetaQuotCentralizer_self hK
      (hKθ.trans (theta_le_thetaQuotCentralizer K))
  have hJp : Group.IsPerfect J := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hKK : K = K' := eq_of_le_inf hK hK'e hJp hJle hJθ
  subst hKK
  show K = inSubgroup perfectResidual (K ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore 3) K
  rw [inf_idem]
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  rw [show inSubgroup perfectResidual K = K from le_antisymm (Sec6.inSubgroup_perfectResidual_le K)
    (Sec6.le_inSubgroup_perfectResidual_of_isPerfect hKp le_rfl)]
  exact (sup_eq_left.mpr (theta_le K)).symm

end CFSG.RankThree.PartTwo.Sec14.Wales1418Off

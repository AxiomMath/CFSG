module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.GH74.Generic.GKFCover
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Generic.Certificates
import CFSG.GH74.Statements
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open CFSG.RankThree.PerfectCover Subgroup

theorem subsingleton_of_closure_of_pow_three_eq_top {H : Type} [Group H] [Finite H]
    [IsMulCommutative H] {S : Set H} (hS : ∀ s ∈ S, s ^ 3 = 1)
    (hgen : Subgroup.closure S = ⊤) (h3 : ¬ 3 ∣ Nat.card H) : Subsingleton H := by
  have hexp3 : ∀ y : H, y ^ 3 = 1 := by
    intro y
    have hy : y ∈ Subgroup.closure S := by rw [hgen]; exact Subgroup.mem_top y
    refine Subgroup.closure_induction (p := fun z _ => z ^ 3 = 1) ?_ ?_ ?_ ?_ hy
    · intro x hx
      exact hS x hx
    · exact one_pow 3
    · intro a b _ _ ha hb
      have hcomm : Commute a b := mul_comm' a b
      rw [hcomm.mul_pow, ha, hb, one_mul]
    · intro a _ ha
      rw [inv_pow, ha, inv_one]
  have hexp : Monoid.exponent H ∣ 3 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hexp3
  have hp3 : IsPGroup 3 H := IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hexp)
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := H)).mp hp3
  have hcard1 : Nat.card H = 1 := by
    rcases n with - | n
    · simpa using hn
    · exfalso
      exact h3 (by rw [hn]; exact dvd_pow_self 3 (Nat.succ_ne_zero n))
  exact (Nat.card_eq_one_iff_unique.mp hcard1).1

theorem commutator_eq_top_of_closure_pow_three_eq_top {X : Type} [Group X] [Finite X]
    (Z : Subgroup X) [Z.Normal] (hZ3 : ¬ 3 ∣ Nat.card Z)
    (hgen : Subgroup.closure {x : X | x ^ 3 = 1} = ⊤)
    (hperf : commutator (X ⧸ Z) = ⊤) : commutator X = ⊤ := by
  have hmap : (commutator X).map (QuotientGroup.mk' Z) = commutator (X ⧸ Z) := by
    rw [commutator_def, Subgroup.map_commutator, commutator_def]
    simp [Subgroup.map_top_of_surjective (QuotientGroup.mk' Z)
      (QuotientGroup.mk'_surjective Z)]
  have hsup : Z ⊔ commutator X = ⊤ := by
    rw [← QuotientGroup.comap_map_mk' Z (commutator X), hmap, hperf, Subgroup.comap_top]
  let φ : Z →* (X ⧸ commutator X) := (QuotientGroup.mk' (commutator X)).comp Z.subtype
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (commutator X) y
    have hx : x ∈ Z ⊔ commutator X := by rw [hsup]; exact Subgroup.mem_top x
    have hx' : x ∈ (↑(Z ⊔ commutator X) : Set X) := hx
    rw [Subgroup.mul_normal, Set.mem_mul] at hx'
    obtain ⟨z, hz, d, hd, hzd⟩ := hx'
    refine ⟨⟨z, hz⟩, ?_⟩
    have hd1 : QuotientGroup.mk' (commutator X) d = 1 :=
      (QuotientGroup.eq_one_iff d).mpr hd
    show QuotientGroup.mk' (commutator X) z = QuotientGroup.mk' (commutator X) x
    rw [← hzd, map_mul, hd1, mul_one]
  have hkerφ : φ.ker = (commutator X).subgroupOf Z := by
    ext z
    show QuotientGroup.mk' (commutator X) (z : X) = 1 ↔
      z ∈ (commutator X).subgroupOf Z
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hdvd : Nat.card (X ⧸ commutator X) ∣ Nat.card Z := by
    have e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    let e' : Z ⧸ (commutator X).subgroupOf Z ≃* X ⧸ commutator X :=
      (QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans e
    rw [← Nat.card_congr e'.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  have h3D : ¬ 3 ∣ Nat.card (X ⧸ commutator X) := fun h => hZ3 (h.trans hdvd)
  have hgen' : Subgroup.closure ((QuotientGroup.mk' (commutator X)) ''
      {x : X | x ^ 3 = 1}) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen,
      Subgroup.map_top_of_surjective (QuotientGroup.mk' (commutator X))
        (QuotientGroup.mk'_surjective (commutator X))]
  have hS : ∀ s ∈ (QuotientGroup.mk' (commutator X)) '' {x : X | x ^ 3 = 1}, s ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hx, map_one]
  have hsub : Subsingleton (X ⧸ commutator X) :=
    subsingleton_of_closure_of_pow_three_eq_top hS hgen' h3D
  refine top_unique fun x _ => ?_
  have hx : (QuotientGroup.mk x : X ⧸ commutator X) = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff x).mp hx

theorem eq_bot_of_isU3_quotient
    {X : Type} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    {f : ℕ} (hZ : Z ≤ center X) (hZ3 : ¬ 3 ∣ Nat.card Z) (hX : IsU3 (X ⧸ Z) f) (hf : 4 ≤ f)
    (heven : Even f) (hgen : closure {x : X | x ^ 3 = 1} = ⊤) : Z = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow Nat.prime_two hK
  have hf1 : 1 ≤ f := by omega
  have hq3 : (3, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ f = 2 := (Prod.mk.inj h).2
    have h4 : 2 ^ 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    rw [h2] at h4
    norm_num at h4
  obtain ⟨hcomm, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier (p := 2) (f := f) hK hf1
      (n := 3) (by norm_num) (by norm_num) hq3
  have hperfProj : Group.IsPerfect (StatedProj (StatedSU 3 (2 ^ f) K)) :=
    Group.isPerfect_def.mpr hcomm
  have hperfQuot : Group.IsPerfect (X ⧸ Z) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hXperf : commutator X = ⊤ :=
    commutator_eq_top_of_closure_pow_three_eq_top Z hZ3 hgen hperfQuot.commutator_eq_top
  have hgcd : Nat.gcd 3 (2 ^ f + 1) = 1 := by
    have hmod : 2 ^ f % 3 = 1 := CFSG.two_pow_mod_three_of_even heven
    have hnot : ¬ 3 ∣ 2 ^ f + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hmod]
      norm_num
    exact Nat.prime_three.coprime_iff_not_dvd.2 hnot
  have hMultProj : Nat.card (hopfMultiplier (StatedProj (StatedSU 3 (2 ^ f) K))) = 1 := by
    have hcard : Nat.card (CFSG.Open.griessHopfMultiplier
        (StatedProj (StatedSU 3 (2 ^ f) K))) = Nat.gcd 3 (2 ^ f + 1) := by
      rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv, hcard, hgcd]
  let q : X →* StatedProj (StatedSU 3 (2 ^ f) K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨s, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z s
    exact ⟨x, rfl⟩
  have hqker : q.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hqle : q.ker ≤ center X := by rw [hqker]; exact hZ
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier
    (Group.isPerfect_def.mpr hXperf) q hq hqle
  rw [hqker, hMultProj] at hdvd
  exact Subgroup.eq_bot_of_card_eq (H := Z) (Nat.dvd_one.mp hdvd)

theorem kU3Mult_holds :
    KU3Mult :=
  fun _ _ _ Z _ _ hZ hZ3 hX hf heven hgen => eq_bot_of_isU3_quotient Z hZ hZ3 hX hf heven hgen

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end

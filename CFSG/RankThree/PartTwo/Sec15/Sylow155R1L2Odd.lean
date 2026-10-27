module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1AutDefs
public import CFSG.Open.PGLModelDefs
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound
import CFSG.Holt.Fixed

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.GorensteinWalter
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (sl2EquivPSL2 even_SL2_full_automorphism_semilinear_model)
open scoped LinearAlgebra.Projectivization

section Aux

variable {F : Type} [Field F] [Finite F]

private theorem card_points_modEq_card_fixedBy {p : ℕ} [Fact p.Prime] {g : PSL2 F}
    (hg : orderOf g = p) :
    Nat.card (ℙ F (Fin 2 → F)) ≡ Nat.card (MulAction.fixedBy (ℙ F (Fin 2 → F)) g) [MOD p] := by
  have hP : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  simpa only [CFSG.Holt.fixSet_zpowers] using
    CFSG.Holt.card_modEq_card_fixSet (Ω := ℙ F (Fin 2 → F)) hP

private theorem card_fixedBy_le_two {g : PSL2 F} (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy (ℙ F (Fin 2 → F)) g) ≤ 2 :=
  psl2_fixedPoint_card_le_two F g hg

private theorem smul_ne_self_of_orderOf_three (h3 : 3 ∣ Nat.card F + 1) {y : PSL2 F}
    (hy : orderOf y = 3) (P : ℙ F (Fin 2 → F)) : y • P ≠ P := by
  intro hP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := card_points_modEq_card_fixedBy (F := F) hy
  rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (Module.finrank_fin_fun F)] at hmod
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    exact absurd hy (by decide)
  have hle := card_fixedBy_le_two (F := F) hy1
  have hpos : 0 < Nat.card (MulAction.fixedBy (ℙ F (Fin 2 → F)) y) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨P, MulAction.mem_fixedBy.mpr hP⟩⟩, inferInstance⟩
  have h3' : (Nat.card F + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
  unfold Nat.ModEq at hmod
  omega

private theorem eq_of_smul_eq_of_orderOf_two (h2 : Even (Nat.card F)) {t : PSL2 F}
    (ht : orderOf t = 2) {P Q : ℙ F (Fin 2 → F)} (hP : t • P = P) (hQ : t • Q = Q) : P = Q := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_points_modEq_card_fixedBy (F := F) ht
  rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (Module.finrank_fin_fun F)] at hmod
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  have hle := card_fixedBy_le_two (F := F) ht1
  have hgt : 1 < Nat.card (MulAction.fixedBy (ℙ F (Fin 2 → F)) t) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact ⟨⟨P, MulAction.mem_fixedBy.mpr hP⟩, ⟨Q, MulAction.mem_fixedBy.mpr hQ⟩,
      fun h => hne (congrArg Subtype.val h)⟩
  unfold Nat.ModEq at hmod
  obtain ⟨m, hm⟩ := h2
  omega

end Aux

private theorem mem_inner_of_isPGroup_two {G : Type} [Group G]
    (hout : Odd (Nat.card (Outer G))) {V : Subgroup (MulAut G)} (hV : IsPGroup 2 V)
    {v : MulAut G} (hv : v ∈ V) : v ∈ inner G := by
  obtain ⟨k, hk⟩ := hV ⟨v, hv⟩
  have hvk : v ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set π := QuotientGroup.mk' (inner G)
  have h1 : orderOf (π v) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hvk, map_one])
  have h2 : orderOf (π v) ∣ Nat.card (Outer G) := orderOf_dvd_natCard (π v)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Outer G)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hout)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

private theorem conj_injective_of_center_eq_bot {G : Type*} [Group G]
    (h : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : x * g * x⁻¹ = g := by
      simpa [MulAut.conj_apply] using DFunLike.congr_fun hx g
    calc g * x = (x * g * x⁻¹) * x := by rw [hg]
      _ = x * g := by group
  rwa [h, Subgroup.mem_bot] at hxc

private theorem res1AutCent_psl_two_odd {n : ℕ} (hn : Odd n) :
    Res1AutCent (PSL2 (GaloisField 2 n)) := by
  intro α V y hy3 _ _ hV _ hyV v hv
  have hn0 : n ≠ 0 := hn.pos.ne'
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have hEven : Even (Nat.card (GaloisField 2 n)) := by
    rw [hcard]
    exact (Nat.even_pow' hn0).mpr even_two
  have h3 : 3 ∣ Nat.card (GaloisField 2 n) + 1 := by
    rw [hcard]
    simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hn
  have hout : Odd (Nat.card (Outer (PSL2 (GaloisField 2 n)))) := by
    rw [← Nat.card_congr (equivalence (sl2EquivPSL2 (F := GaloisField 2 n))).toEquiv,
      (even_SL2_full_automorphism_semilinear_model (Nat.one_le_iff_ne_zero.mpr hn0)
        hcard).2.2.2.1]
    exact hn
  have hρ : Function.Injective
      (MulAut.conj : PSL2 (GaloisField 2 n) →* MulAut (PSL2 (GaloisField 2 n))) :=
    conj_injective_of_center_eq_bot (psl2_center_eq_bot _)
  let V₀ : Subgroup (PSL2 (GaloisField 2 n)) := V.comap MulAut.conj
  have hV₀ : IsPGroup 2 V₀ :=
    hV.of_injective ((MulAut.conj : PSL2 (GaloisField 2 n) →* _).subgroupComap V)
      fun a b hab => Subtype.ext (hρ (congrArg Subtype.val hab))
  have hfwd : ∀ h ∈ V₀, y * h * y⁻¹ ∈ V₀ := by
    intro h hh
    change MulAut.conj (y * h * y⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact hyV _ hh
  have hy3' : y * y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy3] at h
    simpa [pow_succ] using h
  have hynorm : y ∈ Subgroup.normalizer (V₀ : Set (PSL2 (GaloisField 2 n))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd h, fun hh => ?_⟩
    have e : y * (y * (y * h * y⁻¹) * y⁻¹) * y⁻¹ = h := by
      calc y * (y * (y * h * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * h * (y * y * y)⁻¹ := by group
        _ = h := by rw [hy3']; simp
    rw [← e]
    exact hfwd _ (hfwd _ hh)
  have hV₀1 : ∀ w ∈ V₀, w = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hwV, hw1⟩ := hcon
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hV₀ ⟨w, hwV⟩
    have hwo : orderOf w = 2 ^ k := by
      rw [← Subgroup.orderOf_mk w hwV]
      exact hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hw1 (orderOf_eq_one_iff.mp (by simpa using hwo))
    have h2dvd : 2 ∣ orderOf w := by
      rw [hwo]
      exact dvd_pow_self 2 hk0
    have ht : orderOf (w ^ (orderOf w / 2)) = 2 :=
      orderOf_pow_orderOf_div (by rw [hwo]; positivity) h2dvd
    have htV : w ^ (orderOf w / 2) ∈ V₀ := V₀.pow_mem hwV _
    have hΩodd : Odd (Nat.card (ℙ (GaloisField 2 n) (Fin 2 → GaloisField 2 n))) := by
      rw [Projectivization.card_of_finrank_two _ _ (Module.finrank_fin_fun _)]
      exact hEven.add_one
    obtain ⟨P, hP⟩ := CFSG.Holt.fixSet_nonempty_of_odd hΩodd hV₀
    have hyP := CFSG.Holt.smul_mem_fixSet_of_mem_normalizer hynorm hP
    have heq : y • P = P :=
      eq_of_smul_eq_of_orderOf_two hEven ht
        ((CFSG.Holt.mem_fixSet.mp hyP) _ htV) ((CFSG.Holt.mem_fixSet.mp hP) _ htV)
    exact smul_ne_self_of_orderOf_three h3 hy3 P heq
  obtain ⟨x, rfl⟩ := mem_inner_of_isPGroup_two hout hV hv
  rw [hV₀1 x hv, map_one]
  simp

theorem res1AutCent_projSL_two_odd {n : ℕ} (hn : Odd n) :
    Res1AutCent ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)) :=
  Res1AutCent.of_mulEquiv (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 n))
    (res1AutCent_psl_two_odd hn)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

module

import CFSG.RankThree.PartTwo.Sec21.Item22Refl
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

theorem coe_mem_normalizer_map_of_mem_thetaComponents [Finite G] {H : Subgroup G}
    {L₁ L₂ : Subgroup H} (h₁ : L₁ ∈ thetaComponents 3 H) (h₂ : L₂ ∈ thetaComponents 3 H) {x : H}
    (hx : x ∈ L₁) : (x : G) ∈ Subgroup.normalizer ((L₂.map H.subtype : Subgroup G) : Set G) := by
  have hK₁ := isComponent_map_of_mem_thetaComponents Nat.prime_three h₁
  have hK₂ := isComponent_map_of_mem_thetaComponents Nat.prime_three h₂
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := ↥H) Nat.prime_three
  have hσ := map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj x) h₂
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  have hxK : π x ∈ L₁.map π := Subgroup.mem_map_of_mem π hx
  have hnorm : ∀ y ∈ L₂.map π, π x * y * (π x)⁻¹ ∈ L₂.map π := by
    intro y hy
    rcases CFSG.LocalCores.distinct_components_commute hK₁ hK₂ with h | h
    · rw [h] at hxK
      exact mul_mem (mul_mem hxK hy) (inv_mem hxK)
    · have hc : π x * y = y * π x := by
        have := Subgroup.commutator_mem_commutator hxK hy
        rwa [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      rw [hc, mul_inv_cancel_right]
      exact hy
  have hcomp : π.comp (MulAut.conj x).toMonoidHom = (MulAut.conj (π x)).toMonoidHom.comp π := by
    ext y
    simp [MulAut.conj_apply]
  have himage : (L₂.map (MulAut.conj x).toMonoidHom).map π = L₂.map π := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hnorm y hy
    · exact (Subgroup.card_map_of_injective (MulAut.conj (π x)).injective).ge
  have heq : L₂.map (MulAut.conj x).toMonoidHom = L₂ := hbij.injOn hσ h₂ himage
  have hcomp' : (MulAut.conj (x : G)).toMonoidHom.comp H.subtype =
      H.subtype.comp (MulAut.conj x).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (L₂.map H.subtype).map (MulAut.conj (x : G)).toMonoidHom = L₂.map H.subtype
  rw [Subgroup.map_map, hcomp', ← Subgroup.map_map, heq]

theorem mem_normalizer_of_mem_thetaComponentsAt [Finite G] {c x : G} {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ thetaComponentsAt 3 c) (h₂ : L₂ ∈ thetaComponentsAt 3 c) (hx : x ∈ L₁) :
    x ∈ Subgroup.normalizer (L₂ : Set G) := by
  obtain ⟨L₁', hL₁', rfl⟩ := h₁
  obtain ⟨L₂', hL₂', rfl⟩ := h₂
  obtain ⟨x', hx', rfl⟩ := hx
  exact coe_mem_normalizer_map_of_mem_thetaComponents hL₁' hL₂' hx'

theorem mem_of_conj_eq_inv_of_mem_thetaComponentsAt [Finite G] {c t w : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) (htL : t ∈ L) (hwc : w * c = c * w) (hw3 : w ^ 3 = 1)
    (htw : t * w * t⁻¹ = w⁻¹) : w ∈ L := by
  have hwc' : (MulAut.conj w) c = c := by
    rw [MulAut.conj_apply, hwc, mul_inv_cancel_right]
  have hL' : L.map (MulAut.conj w).toMonoidHom ∈ thetaComponentsAt 3 c := by
    have h := map_mem_thetaComponentsAt (MulAut.conj w) hL
    rwa [hwc'] at h
  have htN := mem_normalizer_of_mem_thetaComponentsAt hL hL' htL
  have hw2 : w⁻¹ * w⁻¹ = w := by
    have h1 : w⁻¹ = w ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hw3)
    rw [h1, ← pow_add]
    calc w ^ (2 + 2) = w ^ 3 * w := by rw [← pow_succ]
      _ = w := by rw [hw3, one_mul]
  have hkey : w⁻¹ * t * w = w * t := by
    have h1 : t * w = w⁻¹ * t := by
      calc t * w = (t * w * t⁻¹) * t := by group
        _ = w⁻¹ * t := by rw [htw]
    calc w⁻¹ * t * w = w⁻¹ * (t * w) := by group
      _ = (w⁻¹ * w⁻¹) * t := by rw [h1, mul_assoc]
      _ = w * t := by rw [hw2]
  have hN : w * t ∈ Subgroup.normalizer (L : Set G) := by
    rw [← hkey, Subgroup.mem_normalizer_iff]
    intro h
    have e1 := (Subgroup.mem_normalizer_iff.mp htN) (w * h * w⁻¹)
    have m1 : w * h * w⁻¹ ∈ L.map (MulAut.conj w).toMonoidHom ↔ h ∈ L := by
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
        show w⁻¹ * (w * h * w⁻¹) * w = h by group]
    have m2 : t * (w * h * w⁻¹) * t⁻¹ ∈ L.map (MulAut.conj w).toMonoidHom ↔
        w⁻¹ * t * w * h * (w⁻¹ * t * w)⁻¹ ∈ L := by
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
        show w⁻¹ * (t * (w * h * w⁻¹) * t⁻¹) * w = w⁻¹ * t * w * h * (w⁻¹ * t * w)⁻¹ by group]
    exact m1.symm.trans (e1.trans m2)
  have hwN : w ∈ Subgroup.normalizer (L : Set G) := by
    have := mul_mem hN (inv_mem (Subgroup.le_normalizer htL))
    rwa [mul_inv_cancel_right] at this
  have h1 : w⁻¹ * t * w⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (inv_mem hwN) t).mp htL
  rw [inv_inv, hkey] at h1
  have := L.mul_mem h1 (L.inv_mem htL)
  rwa [mul_inv_cancel_right] at this

theorem commute_of_commute_fixed_of_commute_commOf {A : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) {φ : MulAut A} (hφ2 : orderOf φ = 2) {g : G}
    (hB : ∀ b ∈ fixedInG A φ, b * g = g * b)
    (hW : ∀ a : A, ((a⁻¹ * φ a : A) : G) * g = g * ((a⁻¹ * φ a : A) : G)) :
    ∀ a ∈ A, a * g = g * a := by
  intro a ha
  have hAc : ∀ x y : A, x * y = y * x := hAe.1.is_comm.comm
  have hA3 : ∀ x : A, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hAe.2 x x.2)
  set a' : A := ⟨a, ha⟩ with ha'
  have hb : ((a' * φ a' : A) : G) ∈ fixedInG A φ := by
    refine ⟨a' * φ a', (mem_fixedSubgroupOf φ _).mpr ?_, rfl⟩
    rw [map_mul, apply_apply_of_orderOf_eq_two hφ2]
    exact hAc _ _
  have h1 : Commute ((a' * φ a' : A) : G) g := hB _ hb
  have h2 : Commute (((φ a')⁻¹ * a' : A) : G) g := by
    have e : (φ a')⁻¹ * a' = (a'⁻¹ * φ a')⁻¹ := by group
    rw [e, Subgroup.coe_inv]
    exact (show Commute ((a'⁻¹ * φ a' : A) : G) g from hW a').inv_left
  have h3 : Commute ((((a' * φ a') * ((φ a')⁻¹ * a')) ^ 2 : A) : G) g := by
    rw [Subgroup.coe_pow, Subgroup.coe_mul _ (a' * φ a')]
    exact (h1.mul_left h2).pow_left 2
  rw [← eq_sq_of_exponent_three hA3 φ a'] at h3
  exact h3

theorem isPerfect_sSup_of_forall_isPerfect {S : Set (Subgroup G)}
    (h : ∀ M ∈ S, Group.IsPerfect M) : Group.IsPerfect (sSup S : Subgroup G) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (sSup_le fun M hM => ?_)
  · rw [commutatorElement_def]
    exact (sSup S).mul_mem ((sSup S).mul_mem ((sSup S).mul_mem ha hb) ((sSup S).inv_mem ha))
      ((sSup S).inv_mem hb)
  · calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp (h M hM)).symm
      _ ≤ ⁅sSup S, sSup S⁆ := Subgroup.commutator_mono (le_sSup hM) (le_sSup hM)

theorem mem_of_pow_eq_one_of_mem_sup_centralizer {L' T : Subgroup G}
    (hT : T ≤ Subgroup.centralizer (L' : Set G)) (hcop : ∀ v ∈ T, Nat.Coprime (orderOf v) 3)
    {y : G} (hy : y ∈ L' ⊔ T) {k : ℕ} (hyk : y ^ (3 ^ k) = 1) : y ∈ L' := by
  have hN : T ≤ Subgroup.normalizer (L' : Set G) :=
    hT.trans (Subgroup.centralizer_le_normalizer _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L' T hN] at hy
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy
  have hcomm : Commute u v := Subgroup.mem_centralizer_iff.mp (hT hv) u hu
  rw [hcomm.mul_pow] at hyk
  have hv3 : v ^ (3 ^ k) ∈ L' := by
    rw [eq_inv_of_mul_eq_one_right hyk]
    exact L'.inv_mem (L'.pow_mem hu _)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (Nat.Coprime.pow_left k (hcop v hv).symm)
  have hvL : v ∈ L' := by
    rw [← hm]
    exact L'.pow_mem hv3 m
  exact L'.mul_mem hu hvL

theorem kZero_le_of_mem_starOf [Finite G] {A L : Subgroup G} (hA : A ∈ partTwoF G) {c : G}
    (hcA : c ∈ A) (hLc : L ∈ thetaComponentsAt 3 c) {φ : MulAut A} (hφL : φ ∈ starOf A L)
    (hφ2 : orderOf φ = 2) : kZero A φ ≤ L := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hA.2.1 B hB hAB).le⟩
  obtain ⟨t, htL, htφ⟩ := hφL
  have htL' : (t : G) ∈ L := Subgroup.mem_subgroupOf.mp htL
  have hφt : ∀ a : A, ((φ a : A) : G) = (t : G) * a * (t : G)⁻¹ := fun a => by
    rw [← htφ]
    rfl
  obtain ⟨hLC, hLth⟩ :=
    (mem_thetaComponentsIn_iff (H := Subgroup.centralizer ({c} : Set G))).mp hLc
  set B := fixedInG A φ with hBdef
  set X := Subgroup.centralizer (B : Set G) with hXdef
  have hcB : c ∈ B := by
    refine ⟨⟨c, hcA⟩, (mem_fixedSubgroupOf φ _).mpr ?_, rfl⟩
    apply Subtype.ext
    rw [hφt]
    have htc : (t : G) * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp (hLC htL')
    change (t : G) * c * (t : G)⁻¹ = c
    rw [htc, mul_inv_cancel_right]
  have hXc : X ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)
  have hAX : A ≤ X := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, -, rfl⟩
    exact congrArg Subtype.val (hAc b ⟨a, ha⟩)
  set Y : Subgroup X := (L ⊓ X).subgroupOf X with hYdef
  have hY : Y.IsSubnormal := by
    have h1 := hLth.2.1.comap (Subgroup.inclusion hXc)
    convert h1 using 1
    ext x
    simp only [hYdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap,
      Subgroup.coe_inclusion]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  have hYmap : Y.map X.subtype = L ⊓ X := by
    rw [hYdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hWL : ∀ a : A, ((a⁻¹ * φ a : A) : G) ∈ L ⊓ X := by
    intro a
    refine ⟨?_, hAX (a⁻¹ * φ a).2⟩
    have hφw : φ (a⁻¹ * φ a) = (a⁻¹ * φ a)⁻¹ := by
      rw [map_mul, map_inv, apply_apply_of_orderOf_eq_two hφ2]
      group
    refine mem_of_conj_eq_inv_of_mem_thetaComponentsAt hLc htL'
      (congrArg Subtype.val (hAc (a⁻¹ * φ a) ⟨c, hcA⟩)) (hAe.2 _ (a⁻¹ * φ a).2) ?_
    rw [← hφt (a⁻¹ * φ a), hφw]
    rfl
  set S : Set (Subgroup G) :=
    {M | ∃ K : Subgroup X, IsComponent K ∧ ⁅K, Y⁆ = ⊥ ∧ K.map X.subtype = M} with hSdef
  set T : Subgroup G := sSup S with hTdef
  have hSC : ∀ M ∈ S, M ≤ Subgroup.centralizer ((L ⊓ X : Subgroup G) : Set G) := by
    rintro M ⟨K, -, hKY, rfl⟩
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← hYmap, ← Subgroup.map_commutator,
      hKY, Subgroup.map_bot]
  have hSA : ∀ M ∈ S, M ≤ Subgroup.centralizer (A : Set G) := by
    intro M hM g hg
    have hgX : g ∈ X := by
      obtain ⟨K, -, -, rfl⟩ := hM
      exact Subgroup.map_subtype_le K hg
    have hgL := hSC M hM hg
    rw [Subgroup.mem_centralizer_iff]
    exact commute_of_commute_fixed_of_commute_commOf hAe hφ2
      (fun b hb => Subgroup.mem_centralizer_iff.mp hgX b hb)
      (fun a => Subgroup.mem_centralizer_iff.mp hgL _ (hWL a))
  have hSp : ∀ M ∈ S, Group.IsPerfect M := by
    rintro M ⟨K, hK, -, rfl⟩
    exact isPerfect_map_subtype hK.1.1
  have hTC : T ≤ Subgroup.centralizer ((L ⊓ X : Subgroup G) : Set G) := sSup_le hSC
  have hTA : T ≤ Subgroup.centralizer (A : Set G) := sSup_le hSA
  have hTp : Group.IsPerfect T := isPerfect_sSup_of_forall_isPerfect hSp
  have hT3 : ¬ 3 ∣ Nat.card T := by
    intro h3
    obtain ⟨e, heT, he3, heA⟩ := Sec6.exists_pow_three_eq_one_not_mem hTp h3
      (Subgroup.le_centralizer_iff.mp hTA)
    exact heA (Sec4.mem_of_maximal_of_commute hAmax he3 fun a ha =>
      Subgroup.mem_centralizer_iff.mp (hTA heT) a ha)
  have hcop : ∀ v ∈ T, Nat.Coprime (orderOf v) 3 := by
    intro v hv
    have hdvd : orderOf v ∣ Nat.card T := by
      rw [← Subgroup.orderOf_mk v hv]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_left hdvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hT3).symm
  have hE : inSubgroup CFSG.layer X ≤ (L ⊓ X) ⊔ T := by
    rw [inSubgroup, Subgroup.map_le_iff_le_comap, CFSG.layer]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    rcases CFSG.LocalCores.component_subnormal_subgroup hK hY with hKY | hKY
    · exact (Subgroup.map_mono hKY).trans (hYmap.le.trans le_sup_left)
    · exact (le_sSup ⟨K, hK, hKY, rfl⟩ : K.map X.subtype ≤ T).trans le_sup_right
  show CFSG.GH74.GLS.oPrimeResidualOf 3 (inSubgroup CFSG.layer X) ≤ L
  rw [CFSG.GH74.GLS.oPrimeResidualOf, CFSG.GH74.GLS.oPrimeResidual, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
  have hyk : (y : G) ^ (3 ^ k) = 1 := by
    rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
  exact (mem_of_pow_eq_one_of_mem_sup_centralizer hTC hcop (hE y.2) hyk).1

theorem item222KLe :
    ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Sec21Pair G A E U c L → ∀ φ ∈ starOf A L, φ ∈ dStar A → kZero A φ ≤ L := by
  intro G _ _ A E U c L hpair φ hφL hφ
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  exact kZero_le_of_mem_starOf hpair.mem_S.1 (hpair.mem_E.2 hpairs.1.1)
    ((lZeroStarAt_subset A c) hpairs.2.2.1) hφL hφ.1.1

end CFSG.RankThree.PartTwo.Sec21

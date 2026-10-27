module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res5ProofConfig
public import CFSG.RankThree.PartTwo.Sec21.Item22Res3ProofElliptic
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec21.Item222KLeProof
import CFSG.RankThree.PartTwo.Sec21.Item22Refl
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open scoped commutatorElement

namespace Item224Res5Proof

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inv_conj (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) :
    ∃ t ∈ L, ∃ w ∈ A, w ∈ L ∧ w ≠ 1 ∧ t * w * t⁻¹ = w⁻¹ := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  obtain ⟨-, ⟨φ, hφL, hφD⟩, -⟩ := h222 G A E U c L hpair
  have hφ2 : orderOf φ = 2 := hφD.1.1
  obtain ⟨t, htL, htφ⟩ := hφL
  have htL' : (t : G) ∈ L := Subgroup.mem_subgroupOf.mp htL
  have hφt : ∀ a : A, ((φ a : A) : G) = (t : G) * a * (t : G)⁻¹ := fun a => by
    rw [← htφ]
    rfl
  obtain ⟨a, ha⟩ : ∃ a : A, φ a ≠ a := by
    by_contra h
    push Not at h
    have h1 : φ = 1 := MulEquiv.ext h
    rw [h1, orderOf_one] at hφ2
    exact absurd hφ2 (by norm_num)
  set w : A := a⁻¹ * φ a with hw
  have hw1 : (w : G) ≠ 1 := by
    intro h
    apply ha
    have h' : w = 1 := Subtype.ext h
    rw [hw, inv_mul_eq_one] at h'
    exact h'.symm
  have hφw : φ w = w⁻¹ := by
    rw [hw, map_mul, map_inv, apply_apply_of_orderOf_eq_two hφ2]
    group
  have htw : (t : G) * w * (t : G)⁻¹ = (w : G)⁻¹ := by
    rw [← hφt w, hφw]
    rfl
  have hwc : (w : G) * c = c * w := congrArg Subtype.val (hAc w ⟨c, hcA⟩)
  have hw3 : (w : G) ^ 3 = 1 := hAe.2 _ w.2
  exact ⟨t, htL', w, w.2, mem_of_conj_eq_inv_of_mem_thetaComponentsAt hLc htL' hwc hw3 htw, hw1,
    htw⟩

theorem centralizer_le_normalizer_of_sec21Pair (h222 : Item222) (h213 : Item213)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLq : IsQuasisimple L := h213 G A E U c L hpair
  obtain ⟨t, htL', w, hwA, hwL, hw1, htw⟩ := exists_mem_inv_conj h222 hpair
  have hwc : w * c = c * w := congrArg Subtype.val (hAc ⟨w, hwA⟩ ⟨c, hcA⟩)
  have hw3 : w ^ 3 = 1 := hAe.2 w hwA
  obtain ⟨hLC, hLth⟩ :=
    (mem_thetaComponentsIn_iff (H := Subgroup.centralizer ({c} : Set G))).mp hLc
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hK : IsComponent (L.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC).symm hLq,
      hLth.2.1⟩
  have hconj : ∀ s ∈ Subgroup.centralizer (A : Set G), ∀ l ∈ L, s * l * s⁻¹ ∈ L := by
    intro s hs l hl
    have hsc : s ∈ C :=
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hs c hcA).symm
    set σ : C ≃* C := MulAut.conj (⟨s, hsc⟩ : C) with hσ
    have hK' := CFSG.LocalCores.isComponent_map_mulEquiv σ hK
    rcases CFSG.LocalCores.distinct_components_commute hK hK' with heq | hcomm
    · have hmem : σ ⟨l, hLC hl⟩ ∈ (L.subgroupOf C).map σ.toMonoidHom :=
        ⟨⟨l, hLC hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      rw [← heq] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    · exfalso
      have hwC : w ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hwc
      have hws : w * s = s * w := Subgroup.mem_centralizer_iff.mp hs w hwA
      have hw' : (⟨w, hwC⟩ : C) ∈ (L.subgroupOf C).map σ.toMonoidHom := by
        refine ⟨⟨w, hwC⟩, Subgroup.mem_subgroupOf.mpr hwL, ?_⟩
        apply Subtype.ext
        change s * w * s⁻¹ = w
        rw [← hws, mul_inv_cancel_right]
      have ht' : (⟨t, hLC htL'⟩ : C) ∈ L.subgroupOf C := Subgroup.mem_subgroupOf.mpr htL'
      have h := Subgroup.commutator_mem_commutator ht' hw'
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
      have htw' : t * w = w * t := congrArg Subtype.val h
      have hinv : w⁻¹ = w := by
        rw [← htw, htw', mul_inv_cancel_right]
      apply hw1
      have h2 : w * w = 1 := by
        nth_rewrite 2 [← hinv]
        exact mul_inv_cancel _
      calc w = w ^ 3 * (w * w)⁻¹ := by group
        _ = 1 := by rw [hw3, h2, inv_one, one_mul]
  exact Item22Res3Proof.le_normalizer_of_conj_mem hconj

theorem exists_noncentral_fixed (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) :
    ∃ x : lBar L, orderOf x = 3 ∧ x ∉ Subgroup.center (lBar L) ∧
      ∀ e ∈ Sec4.autThetaQuot A L, e x = x := by
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  obtain ⟨t, htL, w, hwA, hwL, hw1, htw⟩ := exists_mem_inv_conj h222 hpair
  have hw3 : w ^ 3 = 1 := hAe.2 w hwA
  set x : lBar L := ((⟨w, hwL⟩ : L) : lBar L) with hx
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← QuotientGroup.mk_pow]
    have : (⟨w, hwL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
    rw [this, QuotientGroup.mk_one]
  have hx1 : x ≠ 1 := by
    intro h
    rw [hx, QuotientGroup.eq_one_iff] at h
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := L) Nat.prime_three
    have hdvd : orderOf (⟨⟨w, hwL⟩, h⟩ : aschbacherSolvableCore 3 L) ∣
        Nat.card (aschbacherSolvableCore 3 L) := orderOf_dvd_natCard _
    have ho : orderOf (⟨⟨w, hwL⟩, h⟩ : aschbacherSolvableCore 3 L) = 3 := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact orderOf_eq_prime hw3 hw1
    rw [ho] at hdvd
    exact hθ3 hdvd
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  refine ⟨x, hxo, fun hxZ => hx1 ?_, fun e he => ?_⟩
  ·
    have hinv : ((⟨t, htL⟩ : L) : lBar L) * x * ((⟨t, htL⟩ : L) : lBar L)⁻¹ = x⁻¹ := by
      rw [hx, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_inv]
      congr 1
      exact Subtype.ext htw
    have hc := Subgroup.mem_center_iff.mp hxZ ((⟨t, htL⟩ : L) : lBar L)
    rw [hc, mul_inv_cancel_right] at hinv
    have h2 : x * x = 1 := by
      nth_rewrite 2 [hinv]
      exact mul_inv_cancel x
    calc x = x ^ 3 * (x * x)⁻¹ := by group
      _ = 1 := by rw [hx3, h2, inv_one, one_mul]
  · obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp he
    rw [hx]
    change (((L.normalizerMonoidHom ⟨a, haN⟩) ⟨w, hwL⟩ : L) : lBar L) = _
    congr 1
    apply Subtype.ext
    change a * w * a⁻¹ = w
    rw [show a * w = w * a from congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, haA⟩ ⟨w, hwA⟩),
      mul_inv_cancel_right]

theorem isElemAbelian_autThetaQuot {p : ℕ} {A : Subgroup G} (L : Subgroup G)
    (hA : IsElemAbelian p A) : IsElemAbelian p (Sec4.autThetaQuot A L) := by
  set φ := (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
  have hAc : ∀ a b : A, a * b = b * a := hA.1.is_comm.comm
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨_, hx⟩ := x
    obtain ⟨_, hy⟩ := y
    obtain ⟨g, hgN, hgA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hx
    obtain ⟨h, hhN, hhA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hy
    apply Subtype.ext
    change φ ⟨g, hgN⟩ * φ ⟨h, hhN⟩ = φ ⟨h, hhN⟩ * φ ⟨g, hgN⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (show g * h = h * g from congrArg Subtype.val (hAc ⟨g, hgA⟩ ⟨h, hhA⟩))
  · obtain ⟨g, hgN, hgA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hx
    change φ ⟨g, hgN⟩ ^ p = 1
    rw [← map_pow]
    have h1 : (⟨g, hgN⟩ : Subgroup.normalizer (L : Set G)) ^ p = 1 :=
      Subtype.ext (by simpa using hA.2 g hgA)
    rw [h1, map_one]

theorem card_autThetaQuot_eq_nine (h66 : Sec6.Item6_6) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) : Nat.card (Sec4.autThetaQuot A L) = 9 := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hLs : L ∈ lStar A := lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1)
  set K := A ⊓ Sec4.thetaQuotCentralizer L with hK
  have hKcyc : IsCyclic K := h66 G hpair.standing A hpair.mem_S L hLs
  have hcCL : c ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _ hcCL
  have hcK : c ∈ K := by
    refine ⟨hcA, ⟨c, hcN⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      change ((⟨c * y * c⁻¹, _⟩ : L) : lBar L) = (y : lBar L)
      congr 1
      apply Subtype.ext
      change c * (y : G) * c⁻¹ = y
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hLC y.2), mul_inv_cancel_right]
  have hK3 : Nat.card K = 3 := by
    obtain ⟨g, hg⟩ := hKcyc.exists_generator
    have hcard : orderOf g = Nat.card K := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 g g.2.1)
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exfalso
      rw [h] at hcard
      have hsub : Subsingleton K := (Nat.card_eq_one_iff_unique.mp hcard.symm).1
      have : (⟨c, hcK⟩ : K) = 1 := Subsingleton.elim _ _
      exact hc1 (congrArg Subtype.val this)
    · rw [← hcard, h]
  have hmul := Sec13.card_inf_mul_card_autThetaQuot hAL
  rw [← hK, hK3, hA27] at hmul
  omega

theorem innerThreeFixed_autThetaQuot {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hLq : IsQuasisimple L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    InnerThreeFixed (lBar L) (Sec4.autThetaQuot A L) := by
  intro x hx3 hfix
  have hA := hpair.mem_S.1
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hA.1, fun B hB hAB => (hA.2.1 B hB hAB).le⟩
  have hx : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx3] at h
  obtain ⟨l, hlA, rfl, hl3⟩ := exists_lift_pow_three hLq hAL hx hfix
  have hlA' : (l : G) ∈ A := Sec4.mem_of_maximal_of_commute hAmax
    (by simpa using congrArg Subtype.val hl3)
    (fun a ha => Subgroup.mem_centralizer_iff.mp hlA a ha)
  rw [← thetaQuotMulAut_normalizerMonoidHom_of_mem l.2]
  exact Sec4.mem_autThetaQuot_iff.mpr ⟨l, _, hlA', rfl⟩

end Item224Res5Proof

open Item224Res5Proof

end CFSG.RankThree.PartTwo.Sec21

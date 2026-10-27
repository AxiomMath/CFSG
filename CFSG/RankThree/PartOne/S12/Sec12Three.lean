module

public import CFSG.RankThree.PartOne.S12.Sec13Zero
public import CFSG.RankThree.PartOne.S12.BaseNodes
public import CFSG.RankThree.PartOne.S12.Sec12Restrict
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Planes CFSG.RankThree.PartOne.Torsion37
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

namespace Sec12Three

section Setup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem L_mem_zero (h : Sec12Hyp G p A c L E) : L ∈ sectionTenZero p A :=
  (sectionTenZeroStar_subset p A).1 h.L_mem.1.1

theorem L_mem_zeroStar (h : Sec12Hyp G p A c L E) : L ∈ sectionTenZeroStar p A :=
  h.L_mem.1.1

theorem comm_c_L (h : Sec12Hyp G p A c L E) : ∀ l ∈ L, c * l = l * c := fun _ hl =>
  (Subgroup.mem_centralizer_singleton_iff.mp ((mem_thetaComponentsAt_iff.mp h.L_mem.2).1 hl)).symm

theorem pow_eq_one_of_mem_A (h : Sec12Hyp G p A c L E) {x : G} (hx : x ∈ A) : x ^ p = 1 := by
  have := h.A_elem
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem pow_eq_one_of_mem_E (h : Sec12Hyp G p A c L E) {x : G} (hx : x ∈ E) : x ^ p = 1 := by
  have := h.E_elem
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem orderOf_c (h : Sec12Hyp G p A c L E) : orderOf c = p := by
  have : Fact p.Prime := ⟨h.prime⟩
  exact orderOf_eq_prime (pow_eq_one_of_mem_A h h.c_mem) h.c_ne_one

theorem five_le (h : Sec12Hyp G p A c L E) : 5 ≤ p := by
  have hp := h.prime
  have h3 := h.three_lt
  by_contra hlt
  have : p = 4 := by omega
  exact absurd (this ▸ hp) (by decide)

theorem mul_comm_of_mem_A (h : Sec12Hyp G p A c L E) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x :=
  mul_comm_of_isElementaryAbelian h.A_elem hx hy

omit [Finite G] in
theorem dvd_card_center_of_mem {x : G} (hxL : x ∈ L) (hx : ∀ l ∈ L, x * l = l * x)
    (hord : orderOf x = p) : p ∣ Nat.card (Subgroup.center L) := by
  have hz : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hx g g.2).symm
  have h1 := orderOf_dvd_natCard (⟨⟨x, hxL⟩, hz⟩ : Subgroup.center L)
  have h2 : orderOf (⟨⟨x, hxL⟩, hz⟩ : Subgroup.center L) = p := by
    rw [← hord, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
  rwa [h2] at h1

theorem eq_one_of_central (h : Sec12Hyp G p A c L E) (hZ : ¬ p ∣ Nat.card (Subgroup.center L))
    {x : G} (hxE : x ∈ E) (hxL : x ∈ L) (hx : ∀ l ∈ L, x * l = l * x) : x = 1 := by
  by_contra hne
  have : Fact p.Prime := ⟨h.prime⟩
  exact hZ (dvd_card_center_of_mem hxL hx (orderOf_eq_prime (pow_eq_one_of_mem_E h hxE) hne))

theorem c_not_mem_L (h : Sec12Hyp G p A c L E) (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) :
    c ∉ L := fun hcL =>
  h.c_ne_one (eq_one_of_central h hZ (h.A_le_E h.c_mem) hcL (comm_c_L h))

theorem restr_of_generic (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) :
    Restr c L E (E ⊓ L) :=
  ⟨rfl, hG.E_eq, comm_c_L h⟩

theorem hCE_generic (h : Sec12Hyp G p A c L E) (hZ : ¬ p ∣ Nat.card (Subgroup.center L))
    (R : Restr c L E (E ⊓ L)) :
    ∀ f ∈ E, (∀ l ∈ L, f * l = l * f) → f ∈ Subgroup.zpowers c := by
  intro f hfE hf
  obtain ⟨f', hf', i, rfl⟩ := R.exists_mul_zpow hfE
  have hf'E := (Subgroup.mem_inf.1 hf').1
  have hf'L := (Subgroup.mem_inf.1 hf').2
  have hcomm : ∀ l ∈ L, f' * l = l * f' := by
    intro l hl
    have h1 := hf l hl
    have h2 : f' * c ^ i * l = f' * l * c ^ i := by
      rw [mul_assoc, ← R.commute_zpow hl i, ← mul_assoc]
    have h3 : l * (f' * c ^ i) = l * f' * c ^ i := by rw [mul_assoc]
    rw [h2, h3] at h1
    exact mul_right_cancel h1
  rw [eq_one_of_central h hZ hf'E hf'L hcomm, one_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i

omit [Finite G] in
theorem hCE_su5 (hS : Sec12TwoSU5 p c L E) :
    ∀ f ∈ E, (∀ l ∈ L, f * l = l * f) → f ∈ Subgroup.zpowers c := by
  intro f hf hcomm
  have hfL : f ∈ L := hS.E_le hf
  have hz : (⟨f, hfL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2).symm
  rw [← hS.center_eq]
  exact ⟨⟨f, hfL⟩, hz, rfl⟩

end Setup

section Generic

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem A_le_sup_zpowers_L (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) :
    A ≤ Subgroup.zpowers c ⊔ L := by
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]
    exact Subgroup.one_mem _
  · have : Fact p.Prime := ⟨h.prime⟩
    have hord : orderOf a = p := orderOf_eq_prime (pow_eq_one_of_mem_A h ha) ha1
    have haN : a ∈ cNormalizer c := by
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (Commute.symm (mul_comm_of_mem_A h ha h.c_mem)) j).eq
    exact hG.pElements a haN hord

theorem zpowers_comm_L (h : Sec12Hyp G p A c L E) :
    ∀ k ∈ Subgroup.zpowers c, ∀ l ∈ L, k * l = l * k := by
  intro k hk l hl
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  exact (Commute.zpow_left (comm_c_L h l hl : Commute c l) i).eq

theorem A_eq_sup (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) :
    A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  refine le_antisymm (fun a ha => ?_) (sup_le (Subgroup.zpowers_le.2 h.c_mem) inf_le_left)
  obtain ⟨z, hz, l, hl, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (zpowers_comm_L h) (A_le_sup_zpowers_L h hG ha)
  have hzA : z ∈ A := Subgroup.zpowers_le.2 h.c_mem hz
  have hlA : l ∈ A := by
    have := A.mul_mem (A.inv_mem hzA) ha
    rwa [inv_mul_cancel_left] at this
  exact Subgroup.mul_mem_sup hz (Subgroup.mem_inf.2 ⟨hlA, hl⟩)

theorem card_A_inf_L (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E)
    (hcL : c ∉ L) : Nat.card ↥(A ⊓ L) = p ^ 2 := by
  have hp := h.prime
  have hdisj : Disjoint (Subgroup.zpowers c) (A ⊓ L) :=
    Disjoint.mono_right inf_le_right
      (disjoint_iff.2 (zpowers_inf_eq_bot hp (orderOf_c h) hcL))
  have hcard := card_sup_of_commute_disjoint
    (fun k hk l hl => zpowers_comm_L h k hk l (Subgroup.mem_inf.1 hl).2) hdisj
  rw [← A_eq_sup h hG, h.A_card, Nat.card_zpowers, orderOf_c h] at hcard
  have : p * p ^ 2 = p * Nat.card ↥(A ⊓ L) := by rw [← hcard]; ring
  exact (Nat.eq_of_mul_eq_mul_left hp.pos this).symm

theorem invariant_A_inf_L (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) :
    ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      A ⊓ L ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A ⊓ L⁆ := by
  obtain ⟨-, S, hSL, hS0, hS2, hAS, hSA⟩ := L_mem_zero h
  refine ⟨S, hSL, hS0, hS2, inf_le_left.trans hAS, le_antisymm ?_ ?_⟩
  · conv_lhs => rw [hSA]
    rw [Subgroup.commutator_le]
    intro s hs a ha
    obtain ⟨z, hz, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute (zpowers_comm_L h)
      (show a ∈ Subgroup.zpowers c ⊔ L from A_le_sup_zpowers_L h hG ha)
    have hzA : z ∈ A := Subgroup.zpowers_le.2 h.c_mem hz
    have hlA : l ∈ A := by
      have := A.mul_mem (A.inv_mem hzA) ha
      rwa [inv_mul_cancel_left] at this
    have hsL : s ∈ L := hSL hs
    have hzs : z * s = s * z := zpowers_comm_L h z hz s hsL
    have hzm : z * (s * l * s⁻¹ * l⁻¹) = (s * l * s⁻¹ * l⁻¹) * z :=
      zpowers_comm_L h z hz _
        (L.mul_mem (L.mul_mem (L.mul_mem hsL hl) (L.inv_mem hsL)) (L.inv_mem hl))
    have h1 : ⁅s, z * l⁆ = ⁅s, l⁆ := by
      calc ⁅s, z * l⁆ = z * (s * l * s⁻¹ * l⁻¹) * z⁻¹ := by
            have e1 : s * (z * l) = z * (s * l) := by rw [← mul_assoc, ← hzs, mul_assoc]
            simp only [commutatorElement_def, e1]
            group
        _ = ⁅s, l⁆ := by rw [hzm]; simp [commutatorElement_def]
    rw [h1]
    exact Subgroup.commutator_mem_commutator hs (Subgroup.mem_inf.2 ⟨hlA, hl⟩)
  · conv_rhs => rw [hSA]
    exact Subgroup.commutator_mono le_rfl inf_le_left

theorem F_max_generic (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E)
    (F' : Subgroup G) (hF'L : F' ≤ L) (hF'el : IsElementaryAbelian p F')
    (hF'c : F' ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) (hFF' : E ⊓ L ≤ F') :
    F' = E ⊓ L := by
  have hcomm : ∀ k ∈ F', ∀ l ∈ Subgroup.zpowers c, k * l = l * k := fun k hk l hl =>
    (zpowers_comm_L h l hl k (hF'L hk)).symm
  have hel : IsElementaryAbelian p ↥(F' ⊔ Subgroup.zpowers c) :=
    isElementaryAbelian_sup_of_commute hF'el
      (IsElementaryAbelian.zpowers_of_pow_eq_one (pow_eq_one_of_mem_A h h.c_mem)) hcomm
  have hcent : F' ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer (A : Set G) := by
    refine sup_le (fun f hf => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨z, hz, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute (zpowers_comm_L h)
        (show a ∈ Subgroup.zpowers c ⊔ L from A_le_sup_zpowers_L h hG ha)
      have hzA : z ∈ A := Subgroup.zpowers_le.2 h.c_mem hz
      have hlA : l ∈ A := by
        have := A.mul_mem (A.inv_mem hzA) ha
        rwa [inv_mul_cancel_left] at this
      have h1 : l * f = f * l := Subgroup.mem_centralizer_iff.1 (hF'c hf) l
        (Subgroup.mem_inf.2 ⟨hlA, hl⟩)
      have h2 : z * f = f * z := zpowers_comm_L h z hz f (hF'L hf)
      calc z * l * f = z * (l * f) := by rw [mul_assoc]
        _ = z * (f * l) := by rw [h1]
        _ = (z * f) * l := by rw [mul_assoc]
        _ = (f * z) * l := by rw [h2]
        _ = f * (z * l) := by rw [mul_assoc]
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_right (mul_comm_of_mem_A h ha h.c_mem : Commute a c) i).eq
  have hEle : E ≤ F' ⊔ Subgroup.zpowers c := by
    rw [hG.E_eq]
    exact sup_le_sup_right hFF' _
  have heq := h.E_max _ hel hcent hEle
  refine le_antisymm (fun f hf => ?_) hFF'
  exact Subgroup.mem_inf.2 ⟨heq ▸ Subgroup.mem_sup_left hf, hF'L hf⟩

theorem table123Generic (h107 : InSec10Seven) (h109 : InSec10Nine) (h : Sec12Hyp G p A c L E)
    (hG : Sec12TwoGeneric p c L E) : Table123Generic p L (A ⊓ L) (E ⊓ L) where
  prime := h.prime
  five_le := five_le h
  quasisimple := hG.quasisimple
  evenLie := h107 G p A h.setup L (L_mem_zeroStar h)
  evenRank_le := (Sec9A.evenRank_subgroup_le L).trans h.evenRank_eq.le
  center_pPrime := hG.center_pPrime
  localRank_eq := hG.localRank_eq
  not_PSL_two := h109 G p A h.setup L (L_mem_zeroStar h)
  A₀_le := inf_le_right
  A₀_elem := isElementaryAbelian_of_le inf_le_left h.A_elem
  A₀_card := card_A_inf_L h hG (c_not_mem_L h hG.center_pPrime)
  A₀_invariant := invariant_A_inf_L h hG
  F_le := inf_le_right
  F_elem := isElementaryAbelian_of_le inf_le_left h.E_elem
  A₀_le_F := inf_le_inf_right L h.A_le_E
  F_le_centralizer := fun f hf a ha => by
    have hfE := (Subgroup.mem_inf.1 hf).1
    have haA := (Subgroup.mem_inf.1 ha).1
    exact (Subgroup.mem_centralizer_iff.1 (h.E_le hfE) a haA)
  F_max := fun F' hF'L hF'el hF'c hFF' => F_max_generic h hG F' hF'L hF'el hF'c hFF'

end Generic

section SUFive

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem table123SU5 (h : Sec12Hyp G p A c L E) (hS : Sec12TwoSU5 p c L E) :
    Table123SU5 p L A E where
  p_eq := hS.p_eq
  quasisimple := hS.quasisimple
  center_card := hS.center_card
  model := hS.model
  A₀_le := h.A_le_E.trans hS.E_le
  A₀_elem := h.A_elem
  A₀_card := by rw [h.A_card, hS.p_eq]
  center_le := by
    rw [hS.center_eq]
    exact Subgroup.zpowers_le.2 h.c_mem
  A₀_invariant := (L_mem_zero h).2
  F_le := hS.E_le
  F_elem := h.E_elem
  A₀_le_F := h.A_le_E
  F_le_centralizer := h.E_le
  F_max := fun F' _ hF' hc hEF => h.E_max F' hF' hc hEF

end SUFive

theorem reflectionSet_inter_eq {G : Type} [Group G] {p : ℕ} {E L : Subgroup G}
    (hL : L ∈ thetaCompZeroStarE p E) :
    reflectionSet p E ∩ (torusImage E L : Set (MulAut E)) =
      {t | t ∈ torusImage E L ∧ IsAutReflection p E t} := by
  ext t
  constructor
  · rintro ⟨⟨hr, -⟩, ht⟩
    exact ⟨ht, hr⟩
  · rintro ⟨ht, hr⟩
    exact ⟨⟨hr, L, hL, ht⟩, ht⟩

theorem two_le_rowRank {r : ℕ} (h1 : 1 ≤ r) (h12 : r ≤ 12) : 2 ≤ RowRank r := by
  interval_cases r <;> decide

end Sec12Three

theorem Sec12Hyp.table123_hyp (h107 : InSec10Seven) (h109 : InSec10Nine) (h122 : Node122)
    {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) :
    (Sec12TwoGeneric p c L E ∧ Table123Generic p L (A ⊓ L) (E ⊓ L)) ∨
      (Sec12TwoSU5 p c L E ∧ Table123SU5 p L A E) :=
  (h122 G p A c L E h).imp (fun hG => ⟨hG, Sec12Three.table123Generic h107 h109 h hG⟩)
    (fun hS => ⟨hS, Sec12Three.table123SU5 h hS⟩)

theorem Sec12Hyp.c_not_mem_of_generic {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) :
    c ∉ L :=
  Sec12Three.c_not_mem_L h hG.center_pPrime

theorem Sec12Hyp.restr_of_generic {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) :
    Sec12Three.Restr c L E (E ⊓ L) :=
  Sec12Three.restr_of_generic h hG

theorem node123_of_inputs (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h107 : InSec10Seven)
    (h109 : InSec10Nine) (h122 : Node122) (hKF : KF123) : Node123 := by
  intro G _ _ p A c L E h
  rcases Sec12Hyp.table123_hyp h107 h109 h122 h with ⟨hG, hT⟩ | ⟨hS, hT⟩
  · obtain ⟨r, hr1, hr12, hr11, hmodel, hcard, hweyl, hrefl, -, -⟩ :=
      (hKF G p L (A ⊓ L) (E ⊓ L)).1 hT
    have hZ := hG.center_pPrime
    have R := h.restr_of_generic hG
    have hcL := h.c_not_mem_of_generic hG
    have hL := Sec12Hyp.mem_thetaCompZeroStarE hSchreier hTwoAction h106 h
      (Sec12Three.hCE_generic h hZ R)
    have hEcard := R.card_E h.prime (Sec12Three.orderOf_c h) hcL
    refine ⟨?_, r, hr1, hr12, hmodel, R.rowWeylIso hweyl, fun hr8 => ?_, fun hr9 => ?_⟩
    · rw [Sec12Three.reflectionSet_inter_eq hL]
      exact R.torusImage_eq_closure_reflections p hrefl
    · have hE : Nat.card E = p ^ 3 := by
        rw [hEcard, hcard, Sec12Three.rowRank_eq_two hr1 hr8]
        ring
      exact (Subgroup.eq_of_le_of_card_ge h.A_le_E (by rw [hE, h.A_card])).symm
    · rw [hEcard, hcard, Sec12Three.rowRank_eq_three hr9 hr12 hr11]
      ring
  · have hrow := (hKF G p L A E).2 hT
    obtain ⟨hmodel, hcard, hweyl, hrefl, -, -⟩ := hrow
    have hL := Sec12Hyp.mem_thetaCompZeroStarE hSchreier hTwoAction h106 h
      (Sec12Three.hCE_su5 hS)
    refine ⟨?_, 11, by norm_num, by norm_num, hmodel, hweyl, fun hr8 => absurd hr8 (by norm_num),
      fun _ => ?_⟩
    · rw [Sec12Three.reflectionSet_inter_eq hL]
      exact hrefl
    · rw [hcard]
      rfl

theorem node124_of_inputs (h107 : InSec10Seven) (h109 : InSec10Nine) (h122 : Node122)
    (hKF : KF123) : Node124 := by
  intro G _ _ p A c L E h
  rcases Sec12Hyp.table123_hyp h107 h109 h122 h with ⟨hG, hT⟩ | ⟨hS, hT⟩
  · obtain ⟨r, hr1, hr12, hr11, hmodel, hcard, hweyl, -, hirr, -⟩ :=
      (hKF G p L (A ⊓ L) (E ⊓ L)).1 hT
    have R := h.restr_of_generic hG
    have hcL := h.c_not_mem_of_generic hG
    have hnt : torusImage (E ⊓ L) L ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).1 (Sec12Three.nontrivial_of_rowWeylIso hweyl)
    have hFcard : p ^ 2 ≤ Nat.card ↥(E ⊓ L) := by
      rw [hcard]
      exact Nat.pow_le_pow_right h.prime.pos (Sec12Three.two_le_rowRank hr1 hr12)
    obtain ⟨h1, h2⟩ := R.node124_generic h.prime (Sec12Three.orderOf_c h) hcL
      (fun x hx => Sec12Three.pow_eq_one_of_mem_E h hx) (hirr hr11) hnt hFcard
    exact ⟨h1, Or.inl h2⟩
  · obtain ⟨hmodel, -, hweyl, -, -, hlat⟩ := (hKF G p L A E).2 hT
    have hlat := hlat rfl
    have hcL := Sec12Three.comm_c_L h
    have hc5 : c ^ 5 = 1 := by
      have := Sec12Three.pow_eq_one_of_mem_A h h.c_mem
      rwa [hS.p_eq] at this
    have hnt : torusImage E L ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).1 (Sec12Three.nontrivial_of_rowWeylIso hweyl)
    refine ⟨fun B hBE hB hB0 hBne => ?_, Or.inr ⟨⟨hmodel, hweyl⟩, ?_⟩⟩
    · rcases hlat B hBE hB with h0 | hc | hE
      · exact absurd h0 hB0
      · left
        rw [hc, hS.center_eq]
      · exact absurd hE hBne
    · rcases hlat _ (Sec12Three.commutator_le_left E L) (Sec12Three.torusInvariant_commutator E L)
        with h0 | hc | hE
      · exact absurd h0 (Sec12Three.commutator_ne_bot_of_moved
          (Sec12Three.exists_moved_of_torusImage_ne_bot hnt))
      · exact absurd (hc ▸ hS.center_eq ▸ le_rfl)
          (Sec12Three.not_commutator_le_zpowers_of_perm_five hc5 hcL hweyl)
      · exact hE

end CFSG.RankThree.PartOne

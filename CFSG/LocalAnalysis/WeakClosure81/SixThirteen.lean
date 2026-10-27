module

public import CFSG.LocalAnalysis.WeakClosure81.SixTen
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveA
public import CFSG.LocalAnalysis.WeakClosure81.FourteenSix
public import CFSG.LocalAnalysis.WeakClosure81.FourteenNine
public import CFSG.Quasithin.Background.E6Nine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp6H (M V₀ V : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  normalizer_eq : normalizer (V : Set G) = M
  le : V₀ ≤ V
  le_normalizer₀ : M ≤ normalizer (V₀ : Set G)
  ne_top : V₀ ≠ ⊥ → V₀ ≠ V
  isTI : V₀ ≠ ⊥ → CFSG.CGT.Timmesfeld75.IsTI V₀
  normalizer₀ : V₀ ≠ ⊥ → normalizer (V₀ : Set G) = M
  conjGenerated : V₀ ≠ ⊥ → ConjGenerated M V₀ V

namespace Hyp6H

variable {M V₀ V : Subgroup G}

theorem le_M (h : Hyp6H M V₀ V) : V ≤ M := by
  rw [← h.normalizer_eq]
  exact Subgroup.le_normalizer

theorem hyp62 (h : Hyp6H M V₀ V) : Hyp62 M V₀ V := by
  refine ⟨h.elemAbelian, h.normalizer_eq, h.le, h.le_normalizer₀, ?_⟩
  intro X hX hXne
  by_cases hV₀ : V₀ = ⊥
  · subst hV₀
    exact absurd (le_bot_iff.1 hX) hXne
  · intro y hy
    have hTI := h.isTI hV₀ y
    have hXle : X ≤ V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup y V₀ := by
      intro x hx
      refine ⟨hX hx, ?_⟩
      exact (CFSG.CGT.Timmesfeld75.mem_conjSubgroup (g := y) (T := V₀) (x := x)).2
        (hX (by simpa using
          (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hy) x).1 hx))
    have hne : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup y V₀ ≠ ⊥ := by
      intro hbot
      exact hXne (le_bot_iff.1 (hXle.trans (le_of_eq hbot)))
    have hle : V₀ ≤ CFSG.CGT.Timmesfeld75.conjSubgroup y V₀ := by
      have h1 : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup y V₀ = V₀ :=
        hTI.resolve_left hne
      exact (le_of_eq h1.symm).trans inf_le_right
    have hcard : Nat.card (CFSG.CGT.Timmesfeld75.conjSubgroup y V₀) = Nat.card V₀ := by
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup]
      exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj y))
    have heqV : V₀ = CFSG.CGT.Timmesfeld75.conjSubgroup y V₀ :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
    have hyN : y ∈ normalizer (V₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff'']
      intro z
      rw [← CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      exact SetLike.ext_iff.1 heqV z
    rwa [h.normalizer₀ hV₀] at hyN

theorem hyp64 (h : Hyp6H M V₀ V) {n : ℕ} {g : G} (hO : InCalOStar n M V₀ V g) :
    Hyp64 n M V₀ V g :=
  ⟨h.elemAbelian, h.le, h.normalizer_eq, h.le_normalizer₀, h.isTI, h.normalizer₀, hO⟩

theorem hyp65 (h : Hyp6H M V₀ V) (hV₀ : V₀ ≠ ⊥) {n : ℕ} {g : G} (hO : InCalO1 n M V₀ V g) :
    Hyp65 n M V₀ V g :=
  ⟨h.elemAbelian, h.le, hV₀, h.normalizer_eq, h.normalizer₀ hV₀, h.isTI hV₀, hO⟩

end Hyp6H

theorem Vtil_pow_two {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (w : Vtil V₀ V hV) :
    w ^ 2 = 1 := by
  induction w using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_pow, IntMod.sq_eq_one x]
    rfl

structure Hyp613 (k p : ℕ) (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (X : Subgroup (MulAut (Vtil V₀ V hV))) : Prop where
  k_eq : k = 1 ∨ k = 2
  lt_mBar : k < mBar M V₀ V hV
  ne_bot : X ≠ ⊥
  le : X ≤ Mbar M V₀ V hV
  isPGroup : IsPGroup p X
  normal : ∀ m ∈ Mbar M V₀ V hV, ∀ x ∈ X, m * x * m⁻¹ ∈ X
  prime : p.Prime
  lt_p : k + 1 < p
  lt_min : ((k + 1 : ℕ) : ℕ∞) < min (betaN k M V) (rMV M V - (mSub V₀ : ℕ∞))

namespace Hyp613

variable {k p : ℕ} {M V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
  {X : Subgroup (MulAut (Vtil V₀ V hV))}

theorem odd_prime (h : Hyp613 k p M V₀ V hV X) : Odd p := by
  rcases h.prime.eq_two_or_odd' with h2 | hodd
  · exfalso
    have hlt := h.lt_p
    rcases h.k_eq with hk | hk
    · rw [hk] at hlt
      omega
    · rw [hk] at hlt
      omega
  · exact hodd

theorem odd_card (h : Hyp613 k p M V₀ V hV X) : Odd (Nat.card X) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).1 h.isPGroup
  rw [hn]
  exact h.odd_prime.pow

theorem lt_dParam (h : Hyp613 k p M V₀ V hV X) : k < dParam p := by
  have hp2 : p ≠ 2 := by
    intro hp2
    have hlt := h.lt_p
    rcases h.k_eq with hk | hk
    · rw [hk, hp2] at hlt
      omega
    · rw [hk, hp2] at hlt
      omega
  have hdpos : 0 < dParam p := dParam_pos h.prime hp2
  by_contra hle
  rw [not_lt] at hle
  have hdiv1 : (2 : ZMod p) = 1 → p ∣ 1 := by
    intro h2
    have h2' : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h2
    rw [ZMod.natCast_eq_natCast_iff] at h2'
    exact (Nat.modEq_iff_dvd' (show 1 ≤ 2 by norm_num)).mp h2'.symm
  have hpow : (2 : ZMod p) ^ dParam p = 1 := pow_dParam p
  rcases h.k_eq with hk | hk
  · have hd1 : dParam p = 1 := by omega
    rw [hd1, pow_one] at hpow
    exact absurd (hdiv1 hpow) h.prime.not_dvd_one
  · have hdle : dParam p = 1 ∨ dParam p = 2 := by omega
    rcases hdle with hd1 | hd2
    · rw [hd1, pow_one] at hpow
      exact absurd (hdiv1 hpow) h.prime.not_dvd_one
    · rw [hd2] at hpow
      have h4 : ((4 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        have hsq : (2 : ZMod p) ^ 2 = (4 : ZMod p) := by norm_num
        rw [hsq] at hpow
        simpa using hpow
      rw [ZMod.natCast_eq_natCast_iff] at h4
      have hp3 : p ∣ 3 := (Nat.modEq_iff_dvd' (show 1 ≤ 4 by norm_num)).mp h4.symm
      have h3p : 3 < p := by
        have hlt := h.lt_p
        rw [hk] at hlt
        exact hlt
      have := Nat.le_of_dvd (by norm_num : 0 < 3) hp3
      omega

theorem lt_rMV (h : Hyp613 k p M V₀ V hV X) : ((mSub V₀ + k : ℕ) : ℕ∞) < rMV M V := by
  have hkjr : ((k + 1 : ℕ) : ℕ∞) < rMV M V - (mSub V₀ : ℕ∞) :=
    h.lt_min.trans_le (min_le_right _ _)
  have hle : (mSub V₀ : ℕ∞) ≤ rMV M V := by
    by_contra hlt
    rw [not_le] at hlt
    have h0 : rMV M V - (mSub V₀ : ℕ∞) = 0 := tsub_eq_zero_of_le hlt.le
    have h1 : ((k + 1 : ℕ) : ℕ∞) < 0 := by simpa [h0] using hkjr
    have h2 : (0 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.zero_le _
    exact (not_lt_of_ge h2) h1
  have hstrict : ((k + 1 : ℕ) : ℕ∞) + (mSub V₀ : ℕ∞) < rMV M V := by
    have h := (ENat.add_lt_add_iff_right (ENat.natCast_ne_top (mSub V₀))).mpr hkjr
    rwa [tsub_add_cancel_of_le hle] at h
  have hcast : ((k + 1 : ℕ) : ℕ∞) + (mSub V₀ : ℕ∞) =
      (((mSub V₀ + k) + 1 : ℕ) : ℕ∞) := by
    rw [show (mSub V₀ + k) + 1 = (k + 1) + mSub V₀ by omega]
    push_cast
    ring
  rw [hcast] at hstrict
  calc ((mSub V₀ + k : ℕ) : ℕ∞) < (((mSub V₀ + k) + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.lt_succ_self _
    _ < rMV M V := hstrict

theorem hmin (h : Hyp613 k p M V₀ V hV X) :
    ((k + 2 : ℕ) : ℕ∞) ≤ min (betaN k M V) (rMV M V - (mSub V₀ : ℕ∞)) := by
  have h1 : ((k + 2 : ℕ) : ℕ∞) = ((k + 1 : ℕ) : ℕ∞) + 1 := by
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
  rw [h1]
  exact ENat.natCast_add_one_le_iff.mpr h.lt_min

end Hyp613

private theorem preCTilde_eq_inf_centralizer_of_mQuot_lt {M V₀ V : Subgroup G}
    (h : Hyp62 M V₀ V) {g : G}
    {k j : ℕ} (hj : 1 ≤ j) (hO : InCalO k M V₀ V g)
    (hmin : ((k + j : ℕ) : ℕ∞) ≤ min (betaN k M V) (rMV M V - (mSub V₀ : ℕ∞)))
    {D : Subgroup G} (hD : D ≤ conjSubgroup V g ⊓ M)
    (hDlt : E3.mQuot (conjSubgroup V g ⊓ M) D < j) :
    preCTilde V₀ V D h.isElemAbelian = V ⊓ Subgroup.centralizer (D : Set G) := by
  refine le_antisymm ?_ ?_
  · intro u hu
    have huV : u ∈ V := preCTilde_le V₀ V D h.isElemAbelian hu
    have huD : ∀ d ∈ D, ⁅u, d⁆ ∈ V₀ :=
      (mem_preCTilde_iff h.isElemAbelian (h.le_stabTil hD) huV).1 hu
    exact ⟨huV, (six_ten h hj hO hmin).2.2 D hD hDlt u huV huD⟩
  · intro u hu
    exact (mem_preCTilde_iff h.isElemAbelian (h.le_stabTil hD) hu.1).2 fun d hd => by
      have h1 : ⁅u, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_iff.1 hu.2 d hd).symm
      rw [h1]
      exact V₀.one_mem

theorem six_ten_calABar_of_ne_bot {M V₀ V : Subgroup G} (h : Hyp62 M V₀ V) {g : G} {k j : ℕ}
    (hj : 1 ≤ j) (hO : InCalO k M V₀ V g)
    (hmin : ((k + j : ℕ) : ℕ∞) ≤ min (betaN k M V) (rMV M V - (mSub V₀ : ℕ∞)))
    (hB : barSub V₀ V h.isElemAbelian (conjSubgroup V g ⊓ M) ≠ ⊥) :
    barSub V₀ V h.isElemAbelian (conjSubgroup V g ⊓ M) ∈
      calABar j M V₀ V h.isElemAbelian := by
  let B : Subgroup G := conjSubgroup V g ⊓ M
  change barSub V₀ V h.isElemAbelian B ∈ calABar j M V₀ V h.isElemAbelian
  have hten := six_ten h hj hO hmin
  have hBstab : B ≤ stabTil V₀ V := h.le_stabTil le_rfl
  have hBne : barSub V₀ V h.isElemAbelian B ≠ ⊥ := hB
  have hBleVg : B ≤ conjSubgroup V g := inf_le_left
  have hBBlt : E3.mQuot B B < j := by
    have h0 : E3.mQuot B B = 0 := by rw [E3.mQuot, Subgroup.relIndex_self]; simp
    rw [h0]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · show barSub V₀ V h.isElemAbelian B ≤ barSub V₀ V h.isElemAbelian M
    exact barSub_mono V₀ V h.isElemAbelian (show B ≤ M from inf_le_right)
  · exact hBne
  · refine ⟨?_, ?_⟩
    · intro a ha b hb
      obtain ⟨ga, hga, rfl⟩ := (mem_barSub V₀ V h.isElemAbelian B a).1 ha
      obtain ⟨gb, hgb, rfl⟩ := (mem_barSub V₀ V h.isElemAbelian B b).1 hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (B2F.isElemAbelian_comm
        (E3.isElemAbelian_conjSubgroup h.isElemAbelian g) (hBleVg hga) (hBleVg hgb))
    · intro a ha
      obtain ⟨ga, hga, rfl⟩ := (mem_barSub V₀ V h.isElemAbelian B a).1 ha
      rw [← map_pow]
      have hga2 : ga ^ 2 = 1 := Subtype.ext (by
        simpa using (E3.isElemAbelian_conjSubgroup h.isElemAbelian g).2 (ga : G) (hBleVg hga))
      rw [hga2, map_one]
  · intro C hC hlt
    let D : Subgroup G := preBarSub B V₀ V h.isElemAbelian C
    have hDB : D ≤ B := inf_le_left
    have hbarD : barSub V₀ V h.isElemAbelian D = C := by
      change barSub V₀ V h.isElemAbelian (preBarSub B V₀ V h.isElemAbelian C) = C
      rw [barSub_preBarSub]
      exact inf_eq_left.2 hC
    have hmq : E3.mQuot B D = E3.mQuot (barSub V₀ V h.isElemAbelian B) C :=
      (mQuot_barSub_preBarSub_gen h.isElemAbelian hBstab hC).symm
    have hDlt : E3.mQuot B D < j := by rw [hmq]; exact hlt
    have hCV := hten.1 D hDB hDlt
    have hDchar := preCTilde_eq_inf_centralizer_of_mQuot_lt h hj hO hmin hDB hDlt
    have hBchar := preCTilde_eq_inf_centralizer_of_mQuot_lt h hj hO hmin (le_rfl : B ≤ B) hBBlt
    have he : preCTilde V₀ V D h.isElemAbelian = preCTilde V₀ V B h.isElemAbelian := by
      rw [hDchar, hBchar, hCV]
    have hpre : preTil V₀ V h.isElemAbelian (fixV (barSub V₀ V h.isElemAbelian D)) =
        preTil V₀ V h.isElemAbelian (fixV (barSub V₀ V h.isElemAbelian B)) := by
      simpa only [preCTilde] using he
    have hfinj := preTil_injective V₀ V h.isElemAbelian hpre
    rw [hbarD] at hfinj
    exact hfinj

theorem commutator_eq_bot_of_mem_calABar_two {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {B : Subgroup (MulAut (Vtil V₀ V hV))} (hB : B ∈ calABar 2 M V₀ V hV)
    {X : Subgroup (MulAut (Vtil V₀ V hV))} (hX : X ≤ Mbar M V₀ V hV)
    (hXodd : Odd (Nat.card X))
    (hXnorm : ∀ m ∈ Mbar M V₀ V hV, ∀ x ∈ X, m * x * m⁻¹ ∈ X) :
    ⁅X, B⁆ = ⊥ := by
  have hnorm : Mbar M V₀ V hV ≤ Subgroup.normalizer (X : Set (MulAut (Vtil V₀ V hV))) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hXnorm m hm x hx
    · intro hx
      have h1 : m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x := by group
      have h2 := hXnorm m⁻¹ ((Mbar M V₀ V hV).inv_mem hm) (m * x * m⁻¹) hx
      rwa [h1] at h2
  have hXo : X ≤ CFSG.QuasithinUnique.oddCoreIn (Mbar M V₀ V hV) :=
    E6.le_oddCoreIn_of_odd hX hnorm hXodd
  have hcent : B ≤ Subgroup.centralizer
      (CFSG.QuasithinUnique.oddCoreIn (Mbar M V₀ V hV) : Set (MulAut (Vtil V₀ V hV))) :=
    E3.e3_40 (Vtil_pow_two hV) hB
  have hXcent : X ≤ Subgroup.centralizer (B : Set (MulAut (Vtil V₀ V hV))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (hcent hb) x (hXo hx)).symm
  refine le_bot_iff.1 ?_
  rw [Subgroup.commutator_le]
  intro x hx b hb
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2
    (Subgroup.mem_centralizer_iff.1 (hXcent hx) b hb).symm

end CFSG.LocalAnalysis.WeakClosure81

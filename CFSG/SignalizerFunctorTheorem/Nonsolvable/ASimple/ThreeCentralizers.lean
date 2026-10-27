module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Simple
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Basic
import CFSG.RankThree.PartOne.MB3.FixedPoint
import CFSG.Timmesfeld.RankOne.Basic

public section

namespace CFSG.SignalizerFunctorTheorem.Nonsolvable

open scoped commutatorElement

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral
open CFSG.Timmesfeld.RankOne

variable {Γ : Type} [Group Γ] [Finite Γ] {A K K₀ : Subgroup Γ}

private structure Setting (A K K₀ : Subgroup Γ) (z : Γ) : Prop where
  hK : IsASimple A K
  h3 : ¬ 3 ∣ Nat.card K
  hzA : z ∈ A
  hz : orderOf z = 3
  hA : ⁅A, A⁆ = A
  hgen : ∀ B : Subgroup Γ, B ≤ A → A ≤ Subgroup.normalizer (B : Set Γ) → z ∈ B → B = A
  hOut : ∀ T ∈ simpleComponents K,
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥T)
  hK₀ : K₀ ≤ K
  hK₀A : A ≤ Subgroup.normalizer (K₀ : Set Γ)
  hfix : ∀ a ∈ A, K ⊓ Subgroup.centralizer ({a * z * a⁻¹} : Set Γ) ≤ K₀

private lemma commute_of_mem_components {z : Γ} (h : Setting A K K₀ z) {T T' : Subgroup Γ}
    (hT : T ∈ simpleComponents K) (hT' : T' ∈ simpleComponents K) (hne : T ≠ T')
    {x y : Γ} (hx : x ∈ T) (hy : y ∈ T') : Commute x y := by
  have hc := (h.hK.components_commute hT hT' hne).1
  exact (Subgroup.mem_centralizer_iff.mp (hc hx) y hy).symm

private lemma conj_mul_three_of_commute {c x y z : Γ} (hxy : Commute x y)
    (hxz : Commute x z) (hyz : Commute y z) (hx : c * x * c⁻¹ = y)
    (hy : c * y * c⁻¹ = z) (hz : c * z * c⁻¹ = x) :
    c * (x * (y * z)) * c⁻¹ = x * (y * z) := by
  calc c * (x * (y * z)) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) * (c * z * c⁻¹) := by
        group
    _ = y * z * x := by rw [hx, hy, hz]
    _ = x * (y * z) := by
          have h : Commute x (y * z) := hxy.mul_right hxz
          rw [← h.eq]

private lemma centralizes_of_normalizes {z : Γ} (h : Setting A K K₀ z)
    (hnorm : ∀ a ∈ A, ∀ T ∈ simpleComponents K,
      T.map (MulAut.conj a).toMonoidHom = T) :
    ∀ T ∈ simpleComponents K, T ≤ Subgroup.centralizer ({z} : Set Γ) := by
  intro T hT
  letI : IsSimpleGroup ↥T := hT.2.2.1
  have hAN : A ≤ Subgroup.normalizer (T : Set Γ) := fun a ha =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hnorm a ha T hT)
  let ρ : ↥A →* MulAut ↥T := T.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  have hρ : ∀ (a : ↥A) (x : ↥T), ((ρ a) x : Γ) = (a : Γ) * x * (a : Γ)⁻¹ := fun a x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe T (Subgroup.inclusion hAN a) x
  have hzpow : (⟨z, h.hzA⟩ : ↥A) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa [h.hz] using pow_orderOf_eq_one z
  have hρ3 : (ρ ⟨z, h.hzA⟩) ^ 3 = 1 := by
    rw [← map_pow, hzpow, map_one]
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr h.hA
  haveI : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥T) :=
    h.hOut T hT
  obtain ⟨t, ht⟩ :=
    CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner ρ ⟨z, h.hzA⟩
  have ht3conj : MulAut.conj (t ^ 3) = 1 := by
    rw [map_pow (MulAut.conj : ↥T →* MulAut ↥T) t 3, ← ht, hρ3]
  have hcenter : t ^ 3 ∈ Subgroup.center ↥T := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := DFunLike.congr_fun ht3conj x
    rw [MulAut.conj_apply, MulAut.one_apply] at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hnc : ∃ x y : ↥T, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hT.2.2.2
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun e => hxy (congrArg Subtype.val e)⟩
  have ht3 : t ^ 3 = 1 := by
    have hc := CFSG.SignalizerFunctorTheorem.Diagonal.center_eq_bot (T := ↥T) hnc
    have hmem : t ^ 3 ∈ (⊥ : Subgroup ↥T) := hc ▸ hcenter
    simpa using hmem
  have hcarddvd : Nat.card ↥T ∣ Nat.card K := by
    have h1 : Nat.card ↥T = Nat.card ↥(T.subgroupOf K) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv).symm
    rw [h1]
    exact Subgroup.card_subgroup_dvd_card (T.subgroupOf K)
  have h3T : ¬ 3 ∣ Nat.card ↥T := fun h3 => h.h3 (h3.trans hcarddvd)
  have ht1 : t = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one ht3) with h1 | h3
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h3 ▸ orderOf_dvd_natCard t) h3T
  have hρz : ρ ⟨z, h.hzA⟩ = 1 := by rw [ht, ht1, map_one]
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hx' : ((ρ ⟨z, h.hzA⟩) ⟨x, hx⟩ : Γ) = x := by
    have := congrArg (fun e : MulAut ↥T => (((e ⟨x, hx⟩ : ↥T)) : Γ)) hρz
    simpa using this
  have hzxz : z * x * z⁻¹ = x := by
    rw [← hρ ⟨z, h.hzA⟩ ⟨x, hx⟩]
    exact hx'
  exact (mul_inv_eq_iff_eq_mul.mp hzxz).symm

private lemma exists_moved_component {z : Γ} (h : Setting A K K₀ z) (hne : K₀ ≠ K) :
    ∃ T₀ ∈ simpleComponents K, T₀.map (MulAut.conj z).toMonoidHom ≠ T₀ := by
  classical
  by_contra hcon
  push Not at hcon
  let B : Subgroup Γ :=
    { carrier := {b | b ∈ A ∧
        ∀ T ∈ simpleComponents K, T.map (MulAut.conj b).toMonoidHom = T}
      one_mem' := ⟨A.one_mem, fun T _ => CFSG.Timmesfeld.RankOne.map_conj_one T⟩
      mul_mem' := by
        rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
        refine ⟨A.mul_mem haA hbA, fun T hT => ?_⟩
        rw [map_conj_mul T a b, hb T hT, ha T hT]
      inv_mem' := by
        rintro a ⟨haA, ha⟩
        refine ⟨A.inv_mem haA, fun T hT => ?_⟩
        have hTa : T.map (MulAut.conj a).toMonoidHom = T := ha T hT
        have h := congrArg (fun H => H.map (MulAut.conj a⁻¹).toMonoidHom) hTa
        rw [map_conj_inv_map_conj] at h
        exact h.symm }
  have hBA : B ≤ A := fun b hb => hb.1
  have hzB : z ∈ B := ⟨h.hzA, hcon⟩
  have hconjB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    refine ⟨A.mul_mem (A.mul_mem ha hb.1) (A.inv_mem ha), fun T hT => ?_⟩
    have hTa : T.map (MulAut.conj a⁻¹).toMonoidHom ∈ simpleComponents K :=
      map_conj_mem_simpleComponents (h.hK.1 (A.inv_mem ha)) hT
    have hbT : (T.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj b).toMonoidHom =
        T.map (MulAut.conj a⁻¹).toMonoidHom := hb.2 _ hTa
    calc T.map (MulAut.conj (a * b * a⁻¹)).toMonoidHom
        = (T.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj (a * b)).toMonoidHom :=
          map_conj_mul T (a * b) a⁻¹
      _ = ((T.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj b).toMonoidHom).map
            (MulAut.conj a).toMonoidHom :=
          map_conj_mul (T.map (MulAut.conj a⁻¹).toMonoidHom) a b
      _ = (T.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
          rw [hbT]
      _ = T := by
          rw [← map_conj_mul T a a⁻¹, mul_inv_cancel,
            CFSG.Timmesfeld.RankOne.map_conj_one]
  have hNB : A ≤ Subgroup.normalizer (B : Set Γ) :=
    le_normalizer_of_conj_mem hconjB
  have hBeq : B = A := h.hgen B hBA hNB hzB
  have hnorm : ∀ a ∈ A, ∀ T ∈ simpleComponents K,
      T.map (MulAut.conj a).toMonoidHom = T := by
    intro a ha
    have haB : a ∈ B := hBeq.symm ▸ ha
    exact haB.2
  have hcentral := centralizes_of_normalizes h hnorm
  have hKc : K ≤ Subgroup.centralizer ({z} : Set Γ) := by
    rw [← h.hK.iSup_components]
    exact iSup₂_le hcentral
  have hclean : K ⊓ Subgroup.centralizer ({z} : Set Γ) = K :=
    le_antisymm inf_le_left fun x hx => Subgroup.mem_inf.mpr ⟨hx, hKc hx⟩
  have hfixz : K ⊓ Subgroup.centralizer ({z} : Set Γ) ≤ K₀ := by
    simpa using h.hfix (1 : Γ) A.one_mem
  have hKle : K ≤ K₀ := by
    rw [← hclean]
    exact hfixz
  exact hne (le_antisymm h.hK₀ hKle)


private def away (c t : Γ) : Γ := (c * t * c⁻¹) * (c ^ 2 * t * (c ^ 2)⁻¹)

private def diag (c t : Γ) : Γ := t * away c t

private lemma conj_z_pow_three {z : Γ} (h : Setting A K K₀ z) (a : Γ) :
    (a * z * a⁻¹) ^ 3 = 1 := by
  have hz3 : z ^ 3 = 1 := by simpa [h.hz] using pow_orderOf_eq_one z
  have h : (a * z * a⁻¹) ^ 3 = a * z ^ 3 * a⁻¹ := by
    rw [show z ^ 3 = z * z * z by rw [pow_succ, pow_succ, pow_one],
      pow_succ, pow_succ, pow_one]
    group
  rw [h, hz3]
  group

private lemma sq_mul_self {c : Γ} (hc : c ^ 3 = 1) : c ^ 2 * c = 1 := by
  rw [← pow_succ]
  exact hc

private lemma self_mul_sq {c : Γ} (hc : c ^ 3 = 1) : c * c ^ 2 = 1 := by
  rw [← pow_succ']
  exact hc

private lemma sq_mul_sq {c : Γ} (hc : c ^ 3 = 1) : c ^ 2 * c ^ 2 = c := by
  have h : c ^ 2 * c ^ 2 = c ^ (2 + 2) := (pow_add c 2 2).symm
  rw [h, show 2 + 2 = 4 by norm_num, show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hc, one_mul]

private lemma map_conj_sq_ne_of_ne {J : Subgroup Γ} {c : Γ} (hc3 : c ^ 3 = 1)
    (hne : J.map (MulAut.conj c).toMonoidHom ≠ J) :
    J.map (MulAut.conj (c ^ 2)).toMonoidHom ≠ J := by
  intro h2
  apply hne
  have h1 : (J.map (MulAut.conj (c ^ 2)).toMonoidHom).map
      (MulAut.conj c).toMonoidHom = J := by
    rw [← map_conj_mul, self_mul_sq hc3,
      CFSG.Timmesfeld.RankOne.map_conj_one]
  rw [h2] at h1
  exact h1

private lemma map_conj_ne_sq {J : Subgroup Γ} {c : Γ} (hc3 : c ^ 3 = 1)
    (hne : J.map (MulAut.conj c).toMonoidHom ≠ J)
    (hne2 : J.map (MulAut.conj (c ^ 2)).toMonoidHom ≠ J) :
    J.map (MulAut.conj c).toMonoidHom ≠
      J.map (MulAut.conj (c ^ 2)).toMonoidHom := by
  intro h
  apply hne2
  have h1 : (J.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      (J.map (MulAut.conj (c ^ 2)).toMonoidHom).map (MulAut.conj c).toMonoidHom := by rw [h]
  rw [← map_conj_mul, ← map_conj_mul,
    show c * c = c ^ 2 by rw [pow_two], self_mul_sq hc3,
    CFSG.Timmesfeld.RankOne.map_conj_one] at h1
  exact h1

private lemma away_mem_K {z : Γ} (h : Setting A K K₀ z) {J : Subgroup Γ}
    (hJ : J ∈ simpleComponents K) {t : Γ} (ht : t ∈ J) {c : Γ} (hcA : c ∈ A) :
    away c t ∈ K := by
  have hJc : J.map (MulAut.conj c).toMonoidHom ∈ simpleComponents K :=
    map_conj_mem_simpleComponents (h.hK.1 hcA) hJ
  have hJc2 : J.map (MulAut.conj (c ^ 2)).toMonoidHom ∈ simpleComponents K :=
    map_conj_mem_simpleComponents (h.hK.1 (Subgroup.pow_mem A hcA 2)) hJ
  have ht2 : c * t * c⁻¹ ∈ J.map (MulAut.conj c).toMonoidHom :=
    conj_mem_map_conj c ht
  have ht3 : c ^ 2 * t * (c ^ 2)⁻¹ ∈ J.map (MulAut.conj (c ^ 2)).toMonoidHom :=
    conj_mem_map_conj (c ^ 2) ht
  simpa [away] using K.mul_mem (hJc.1 ht2) (hJc2.1 ht3)

private lemma away_commute {z : Γ} (h : Setting A K K₀ z) {J : Subgroup Γ}
    (hJ : J ∈ simpleComponents K) {t : Γ} (ht : t ∈ J) {c : Γ} (hcA : c ∈ A)
    (hc3 : c ^ 3 = 1) (hne : J.map (MulAut.conj c).toMonoidHom ≠ J) {x : Γ}
    (hx : x ∈ J) : Commute (away c t) x := by
  have hne2 := map_conj_sq_ne_of_ne hc3 hne
  have hJc : J.map (MulAut.conj c).toMonoidHom ∈ simpleComponents K :=
    map_conj_mem_simpleComponents (h.hK.1 hcA) hJ
  have hJc2 : J.map (MulAut.conj (c ^ 2)).toMonoidHom ∈ simpleComponents K :=
    map_conj_mem_simpleComponents (h.hK.1 (Subgroup.pow_mem A hcA 2)) hJ
  have ht2 : c * t * c⁻¹ ∈ J.map (MulAut.conj c).toMonoidHom :=
    conj_mem_map_conj c ht
  have ht3 : c ^ 2 * t * (c ^ 2)⁻¹ ∈ J.map (MulAut.conj (c ^ 2)).toMonoidHom :=
    conj_mem_map_conj (c ^ 2) ht
  have h2 : Commute (c * t * c⁻¹) x :=
    commute_of_mem_components h hJc hJ hne ht2 hx
  have h3 : Commute (c ^ 2 * t * (c ^ 2)⁻¹) x :=
    commute_of_mem_components h hJc2 hJ hne2 ht3 hx
  simpa [away] using h2.mul_left h3

private lemma diag_fixed {z : Γ} (h : Setting A K K₀ z) {J : Subgroup Γ}
    (hJ : J ∈ simpleComponents K) {t : Γ} (ht : t ∈ J) {c : Γ} (hcA : c ∈ A)
    (hc3 : c ^ 3 = 1) (hne : J.map (MulAut.conj c).toMonoidHom ≠ J) :
    c * diag c t * c⁻¹ = diag c t := by
  have hne2 := map_conj_sq_ne_of_ne hc3 hne
  have hnecc2 := map_conj_ne_sq hc3 hne hne2
  have hJc : J.map (MulAut.conj c).toMonoidHom ∈ simpleComponents K :=
    map_conj_mem_simpleComponents (h.hK.1 hcA) hJ
  have hJc2 : J.map (MulAut.conj (c ^ 2)).toMonoidHom ∈ simpleComponents K :=
    map_conj_mem_simpleComponents (h.hK.1 (Subgroup.pow_mem A hcA 2)) hJ
  have ht2 : c * t * c⁻¹ ∈ J.map (MulAut.conj c).toMonoidHom :=
    conj_mem_map_conj c ht
  have ht3 : c ^ 2 * t * (c ^ 2)⁻¹ ∈ J.map (MulAut.conj (c ^ 2)).toMonoidHom :=
    conj_mem_map_conj (c ^ 2) ht
  have hxy : Commute t (c * t * c⁻¹) :=
    commute_of_mem_components h hJ hJc (Ne.symm hne) ht ht2
  have hxz : Commute t (c ^ 2 * t * (c ^ 2)⁻¹) :=
    commute_of_mem_components h hJ hJc2 (Ne.symm hne2) ht ht3
  have hyz : Commute (c * t * c⁻¹) (c ^ 2 * t * (c ^ 2)⁻¹) :=
    commute_of_mem_components h hJc hJc2 hnecc2 ht2 ht3
  have hy : c * (c * t * c⁻¹) * c⁻¹ = c ^ 2 * t * (c ^ 2)⁻¹ := by
    rw [pow_two, mul_inv_rev]
    group
  have hz : c * (c ^ 2 * t * (c ^ 2)⁻¹) * c⁻¹ = t := by
    have h2 : c ^ 2 = c * c := pow_two c
    have h3 : c ^ 3 = c * c * c := by rw [pow_succ, h2]
    have h1 : c * (c ^ 2 * t * (c ^ 2)⁻¹) * c⁻¹ = c ^ 3 * t * (c ^ 3)⁻¹ := by
      rw [h2, h3, mul_inv_rev, mul_inv_rev]
      group
    rw [h1, hc3]
    group
  have hmain := conj_mul_three_of_commute hxy hxz hyz rfl hy hz
  simpa [diag, away] using hmain

private lemma diag_mem_K {z : Γ} (h : Setting A K K₀ z) {J : Subgroup Γ}
    (hJ : J ∈ simpleComponents K) {t : Γ} (ht : t ∈ J) {c : Γ} (hcA : c ∈ A) :
    diag c t ∈ K := by
  have h1 : t ∈ K := hJ.1 ht
  have h2 : away c t ∈ K := away_mem_K h hJ ht hcA
  simpa [diag] using K.mul_mem h1 h2

private lemma diag_mem_K₀ {z : Γ} (h : Setting A K K₀ z) {a : Γ} (ha : a ∈ A)
    {J : Subgroup Γ} (hJ : J ∈ simpleComponents K) {t : Γ} (ht : t ∈ J) {c : Γ}
    (hc : c = a * z * a⁻¹) (hne : J.map (MulAut.conj c).toMonoidHom ≠ J) :
    diag c t ∈ K₀ := by
  have hcA : c ∈ A := by
    rw [hc]
    exact A.mul_mem (A.mul_mem ha h.hzA) (A.inv_mem ha)
  have hc3 : c ^ 3 = 1 := by
    rw [hc]
    exact conj_z_pow_three h a
  have hfixed := diag_fixed h hJ ht hcA hc3 hne
  have hcent : diag c t ∈ Subgroup.centralizer ({c} : Set Γ) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfixed).symm
  have hmem : diag c t ∈ K ⊓ Subgroup.centralizer ({c} : Set Γ) :=
    Subgroup.mem_inf.mpr ⟨diag_mem_K h hJ ht hcA, hcent⟩
  have hle : K ⊓ Subgroup.centralizer ({c} : Set Γ) ≤ K₀ := by
    rw [hc]
    exact h.hfix a ha
  exact hle hmem

private lemma exists_conj_moves {z : Γ} (h : Setting A K K₀ z) (hne : K₀ ≠ K) :
    ∀ J ∈ simpleComponents K, ∃ a ∈ A,
      J.map (MulAut.conj (a * z * a⁻¹)).toMonoidHom ≠ J := by
  obtain ⟨T₀, hT₀, hmove⟩ := exists_moved_component h hne
  intro J hJ
  obtain ⟨a, ha, hJa⟩ := h.hK.components_transitive hT₀ hJ
  refine ⟨a, ha, ?_⟩
  intro hfixJ
  apply hmove
  have h1 : (T₀.map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj (a * z * a⁻¹)).toMonoidHom = T₀.map (MulAut.conj a).toMonoidHom := by
    rw [← hJa]
    exact hfixJ
  have h2 : (T₀.map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj (a * z * a⁻¹)).toMonoidHom =
      (T₀.map (MulAut.conj z).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    rw [← map_conj_mul, show (a * z * a⁻¹) * a = a * z by group,
      map_conj_mul]
  have h3 : (T₀.map (MulAut.conj z).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      T₀.map (MulAut.conj a).toMonoidHom := by
    rw [← h2]
    exact h1
  exact (map_conj_inj).mp h3

private lemma inf_component_eq_bot {z : Γ} (h : Setting A K K₀ z) (hne : K₀ ≠ K)
    (hmove : ∀ J ∈ simpleComponents K, ∃ a ∈ A,
      J.map (MulAut.conj (a * z * a⁻¹)).toMonoidHom ≠ J) :
    ∀ J ∈ simpleComponents K, K₀ ⊓ J = ⊥ := by
  intro J hJ
  letI : IsSimpleGroup ↥J := hJ.2.2.1
  by_contra hbot
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ K₀ ⊓ J, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot (Subgroup.eq_bot_iff_forall _ |>.mpr fun y hy => hcon y hy)
  have hxJ : x ∈ J := (Subgroup.mem_inf.mp hx).2
  obtain ⟨a, ha, hmoveJ⟩ := hmove J hJ
  let c : Γ := a * z * a⁻¹
  have hcA : c ∈ A := A.mul_mem (A.mul_mem ha h.hzA) (A.inv_mem ha)
  have hc3 : c ^ 3 = 1 := conj_z_pow_three h a
  have hnormal : ((K₀ ⊓ J).subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro y j hy hj
    have hyK₀ : y ∈ K₀ := (Subgroup.mem_inf.mp hy).1
    have hyJ : y ∈ J := (Subgroup.mem_inf.mp hy).2
    have hfixj : diag c j ∈ K₀ := diag_mem_K₀ h ha hJ hj rfl hmoveJ
    have hcomm : Commute (away c j) y :=
      away_commute h hJ hj hcA hc3 hmoveJ hyJ
    have hconj : diag c j * y * (diag c j)⁻¹ = j * y * j⁻¹ := by
      calc diag c j * y * (diag c j)⁻¹
          = j * (away c j * y * (away c j)⁻¹) * j⁻¹ := by
              simp only [diag]
              group
        _ = j * y * j⁻¹ := by rw [hcomm.eq]; group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hconj]
      exact K₀.mul_mem (K₀.mul_mem hfixj hyK₀) (K₀.inv_mem hfixj)
    · exact J.mul_mem (J.mul_mem hj hyJ) (J.inv_mem hj)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K₀ ⊓ J).subgroupOf J) with hbotJ | htopJ
  · have hxmem : (⟨x, hxJ⟩ : ↥J) ∈ (K₀ ⊓ J).subgroupOf J := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [hbotJ, Subgroup.mem_bot] at hxmem
    exact hx1 (by simpa using congrArg Subtype.val hxmem)
  · have hJle : J ≤ K₀ := fun y hy => by
      have hmem : (⟨y, hy⟩ : ↥J) ∈ (K₀ ⊓ J).subgroupOf J := by
        rw [htopJ]
        trivial
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).1
    have hAll : ∀ T ∈ simpleComponents K, T ≤ K₀ := by
      intro T hT
      obtain ⟨b, hb, hTb⟩ := h.hK.components_transitive hJ hT
      rw [hTb]
      intro y hy
      obtain ⟨t, ht, rfl⟩ := hy
      exact (Subgroup.mem_normalizer_iff.mp (h.hK₀A hb) t).mp (hJle ht)
    have hKle : K ≤ K₀ := by
      rw [← h.hK.iSup_components]
      exact iSup₂_le hAll
    exact hne (le_antisymm h.hK₀ hKle)

private lemma not_normalizes_of_conj {z : Γ} (h : Setting A K K₀ z)
    (hinf : ∀ J ∈ simpleComponents K, K₀ ⊓ J = ⊥)
    {a : Γ} (ha : a ∈ A) {J : Subgroup Γ} (hJ : J ∈ simpleComponents K) :
    J.map (MulAut.conj (a * z * a⁻¹)).toMonoidHom ≠ J := by
  intro hNJ
  letI : IsSimpleGroup ↥J := hJ.2.2.1
  let c : Γ := a * z * a⁻¹
  have hcA : c ∈ A := A.mul_mem (A.mul_mem ha h.hzA) (A.inv_mem ha)
  have hc3 : c ^ 3 = 1 := conj_z_pow_three h a
  have hcN : c ∈ Subgroup.normalizer (J : Set Γ) := by
    rw [show c = a * z * a⁻¹ from rfl]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hNJ
  let α : MulAut ↥J := J.normalizerMonoidHom ⟨c, hcN⟩
  have hsub3 : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (J : Set Γ))) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hc3
  have hα3 : α ^ 3 = 1 := by
    change (J.normalizerMonoidHom ⟨c, hcN⟩) ^ 3 = 1
    rw [← map_pow, hsub3, map_one]
  have hfixcent : K ⊓ Subgroup.centralizer ({c} : Set Γ) ≤ K₀ := by
    simpa [c] using h.hfix a ha
  by_cases hα1 : α = 1
  · have hJleC : J ≤ Subgroup.centralizer ({c} : Set Γ) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hαy : α ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hα1, MulAut.one_apply]
      have hcy : c * y * c⁻¹ = y := by
        have h := congrArg Subtype.val hαy
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
        exact h
      exact (mul_inv_eq_iff_eq_mul.mp hcy).symm
    have hJle : J ≤ K₀ := fun y hy =>
      hfixcent (Subgroup.mem_inf.mpr ⟨hJ.1 hy, hJleC hy⟩)
    have hJbot : J = ⊥ := by
      have hle : J ≤ K₀ ⊓ J := fun y hy => Subgroup.mem_inf.mpr ⟨hJle hy, hy⟩
      rw [hinf J hJ] at hle
      exact eq_bot_iff.mpr hle
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥J)
    apply hy
    apply Subtype.ext
    have hym : (y : Γ) ∈ (⊥ : Subgroup Γ) := hJbot ▸ y.2
    simpa using hym
  · have hαord : orderOf α = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hα3 hα1
    by_cases hcent : J ⊓ Subgroup.centralizer ({c} : Set Γ) = ⊥
    · have hfix : ∀ y : ↥J, α y = y → y = 1 := by
        intro y hy
        have hcy : c * (y : Γ) * c⁻¹ = (y : Γ) := by
          have h := congrArg Subtype.val hy
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
          exact h
        have hycent : (y : Γ) ∈ Subgroup.centralizer ({c} : Set Γ) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (mul_inv_eq_iff_eq_mul.mp hcy).symm
        have hyin : (y : Γ) ∈ J ⊓ Subgroup.centralizer ({c} : Set Γ) :=
          Subgroup.mem_inf.mpr ⟨y.2, hycent⟩
        rw [hcent, Subgroup.mem_bot] at hyin
        exact Subtype.ext hyin
      haveI : Group.IsPerfect ↥J :=
        Subgroup.isPerfect_iff.mpr
          (commutator_self_eq_of_isSimpleGroup
            hJ.2.2.2)
      have hnil := CFSG.RankThree.PartOne.MB3.isNilpotent_of_fixedPointFree_prime α
        (by rw [hαord]; exact Nat.prime_three) hfix
      exact Group.IsPerfect.not_isNilpotent ↥J hnil
    · obtain ⟨y, hy, hy1⟩ : ∃ y ∈ J ⊓ Subgroup.centralizer ({c} : Set Γ), y ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hcent (Subgroup.eq_bot_iff_forall _ |>.mpr fun z hz => hcon z hz)
      have hyJ : y ∈ J := (Subgroup.mem_inf.mp hy).1
      have hyC : y ∈ Subgroup.centralizer ({c} : Set Γ) := (Subgroup.mem_inf.mp hy).2
      have hyK : y ∈ K := hJ.1 hyJ
      have hyK₀ : y ∈ K₀ := hfixcent (Subgroup.mem_inf.mpr ⟨hyK, hyC⟩)
      have hybot : y ∈ K₀ ⊓ J := Subgroup.mem_inf.mpr ⟨hyK₀, hyJ⟩
      rw [hinf J hJ, Subgroup.mem_bot] at hybot
      exact hy1 hybot

private lemma orbit_step {J : Subgroup Γ} {c : Γ} :
    (J.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      J.map (MulAut.conj (c ^ 2)).toMonoidHom := by
  rw [← map_conj_mul, show c * c = c ^ 2 by rw [pow_two]]

private lemma orbit_step' {J : Subgroup Γ} {c : Γ} (hc3 : c ^ 3 = 1) :
    (J.map (MulAut.conj (c ^ 2)).toMonoidHom).map (MulAut.conj c).toMonoidHom = J := by
  rw [← map_conj_mul, self_mul_sq hc3, CFSG.Timmesfeld.RankOne.map_conj_one]

private lemma orbit_step_inv {J : Subgroup Γ} {c : Γ} (hc3 : c ^ 3 = 1) :
    (J.map (MulAut.conj c).toMonoidHom).map (MulAut.conj (c ^ 2)).toMonoidHom = J := by
  rw [← map_conj_mul, sq_mul_self hc3, CFSG.Timmesfeld.RankOne.map_conj_one]

private lemma orbit_step_inv' {J : Subgroup Γ} {c : Γ} (hc3 : c ^ 3 = 1) :
    (J.map (MulAut.conj (c ^ 2)).toMonoidHom).map (MulAut.conj (c ^ 2)).toMonoidHom =
      J.map (MulAut.conj c).toMonoidHom := by
  rw [← map_conj_mul, sq_mul_sq hc3]

private lemma step5_meet {z : Γ} (h : Setting A K K₀ z)
    (hinf : ∀ J ∈ simpleComponents K, K₀ ⊓ J = ⊥)
    {a b : Γ} (ha : a ∈ A) (hb : b ∈ A) {J : Subgroup Γ} (hJ : J ∈ simpleComponents K) :
    J.map (MulAut.conj (a * z * a⁻¹)).toMonoidHom =
        J.map (MulAut.conj (b * z * b⁻¹)).toMonoidHom ∨
      J.map (MulAut.conj (a * z * a⁻¹)).toMonoidHom =
        J.map (MulAut.conj ((b * z * b⁻¹) ^ 2)).toMonoidHom ∨
      J.map (MulAut.conj ((a * z * a⁻¹) ^ 2)).toMonoidHom =
        J.map (MulAut.conj (b * z * b⁻¹)).toMonoidHom ∨
      J.map (MulAut.conj ((a * z * a⁻¹) ^ 2)).toMonoidHom =
        J.map (MulAut.conj ((b * z * b⁻¹) ^ 2)).toMonoidHom := by
  let c : Γ := a * z * a⁻¹
  let c' : Γ := b * z * b⁻¹
  change J.map (MulAut.conj c).toMonoidHom = J.map (MulAut.conj c').toMonoidHom ∨
    J.map (MulAut.conj c).toMonoidHom = J.map (MulAut.conj (c' ^ 2)).toMonoidHom ∨
    J.map (MulAut.conj (c ^ 2)).toMonoidHom = J.map (MulAut.conj c').toMonoidHom ∨
    J.map (MulAut.conj (c ^ 2)).toMonoidHom = J.map (MulAut.conj (c' ^ 2)).toMonoidHom
  by_contra hcon
  push Not at hcon
  have hc3 : c ^ 3 = 1 := conj_z_pow_three h a
  have hc'3 : c' ^ 3 = 1 := conj_z_pow_three h b
  have hcA : c ∈ A := A.mul_mem (A.mul_mem ha h.hzA) (A.inv_mem ha)
  have hc'A : c' ∈ A := A.mul_mem (A.mul_mem hb h.hzA) (A.inv_mem hb)
  have hne_c : J.map (MulAut.conj c).toMonoidHom ≠ J := by
    simpa [c] using not_normalizes_of_conj h hinf ha hJ
  have hne_c' : J.map (MulAut.conj c').toMonoidHom ≠ J := by
    simpa [c'] using not_normalizes_of_conj h hinf hb hJ
  obtain ⟨t, ht, s, hs, hts⟩ := hJ.2.2.2
  have ht2 : c * t * c⁻¹ ∈ J.map (MulAut.conj c).toMonoidHom :=
    conj_mem_map_conj c ht
  have ht3 : c ^ 2 * t * (c ^ 2)⁻¹ ∈ J.map (MulAut.conj (c ^ 2)).toMonoidHom :=
    conj_mem_map_conj (c ^ 2) ht
  have hs2 : c' * s * c'⁻¹ ∈ J.map (MulAut.conj c').toMonoidHom :=
    conj_mem_map_conj c' hs
  have hs3 : c' ^ 2 * s * (c' ^ 2)⁻¹ ∈ J.map (MulAut.conj (c' ^ 2)).toMonoidHom :=
    conj_mem_map_conj (c' ^ 2) hs
  have hJc : J.map (MulAut.conj c).toMonoidHom ∈ simpleComponents K :=
    map_conj_mem_simpleComponents (h.hK.1 hcA) hJ
  have hJc2 : J.map (MulAut.conj (c ^ 2)).toMonoidHom ∈ simpleComponents K :=
    map_conj_mem_simpleComponents (h.hK.1 (Subgroup.pow_mem A hcA 2)) hJ
  have hJc' : J.map (MulAut.conj c').toMonoidHom ∈ simpleComponents K :=
    map_conj_mem_simpleComponents (h.hK.1 hc'A) hJ
  have hJc'2 : J.map (MulAut.conj (c' ^ 2)).toMonoidHom ∈ simpleComponents K :=
    map_conj_mem_simpleComponents (h.hK.1 (Subgroup.pow_mem A hc'A 2)) hJ
  have hu_t : Commute (away c t) t := away_commute h hJ ht hcA hc3 hne_c ht
  have hu_s : Commute (away c t) s := away_commute h hJ ht hcA hc3 hne_c hs
  have hv_t : Commute (away c' s) t := away_commute h hJ hs hc'A hc'3 hne_c' ht
  have hv_s : Commute (away c' s) s := away_commute h hJ hs hc'A hc'3 hne_c' hs
  have hu_v : Commute (away c t) (away c' s) := by
    have h1 : Commute (c * t * c⁻¹) (c' * s * c'⁻¹) :=
      commute_of_mem_components h hJc hJc' hcon.1 ht2 hs2
    have h2 : Commute (c * t * c⁻¹) (c' ^ 2 * s * (c' ^ 2)⁻¹) :=
      commute_of_mem_components h hJc hJc'2 hcon.2.1 ht2 hs3
    have h3 : Commute (c ^ 2 * t * (c ^ 2)⁻¹) (c' * s * c'⁻¹) :=
      commute_of_mem_components h hJc2 hJc' hcon.2.2.1 ht3 hs2
    have h4 : Commute (c ^ 2 * t * (c ^ 2)⁻¹) (c' ^ 2 * s * (c' ^ 2)⁻¹) :=
      commute_of_mem_components h hJc2 hJc'2 hcon.2.2.2 ht3 hs3
    simpa [away] using (h1.mul_right h2).mul_left (h3.mul_right h4)
  have hd : diag c t ∈ K₀ := diag_mem_K₀ h ha hJ ht (c := c) rfl hne_c
  have hd' : diag c' s ∈ K₀ := diag_mem_K₀ h hb hJ hs (c := c') rfl hne_c'
  have hmain := commutatorElement_mul_mul
    hu_t hu_s hv_t hv_s hu_v
  have hdt : diag c t = away c t * t := by rw [diag, ← hu_t.eq]
  have hds : diag c' s = away c' s * s := by rw [diag, ← hv_s.eq]
  have heq : ⁅diag c t, diag c' s⁆ = ⁅t, s⁆ := by
    rw [hdt, hds]
    exact hmain
  have hcommK : ⁅diag c t, diag c' s⁆ ∈ K₀ := by
    rw [commutatorElement_def]
    exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem hd hd') (K₀.inv_mem hd)) (K₀.inv_mem hd')
  have hcommJ : ⁅t, s⁆ ∈ J := by
    rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem ht hs) (J.inv_mem ht)) (J.inv_mem hs)
  have hmem : ⁅t, s⁆ ∈ K₀ ⊓ J := Subgroup.mem_inf.mpr ⟨heq ▸ hcommK, hcommJ⟩
  rw [hinf J hJ, Subgroup.mem_bot] at hmem
  exact hts (commutatorElement_eq_one_iff_commute.mp hmem).eq

private lemma step5_orbit {z : Γ} (h : Setting A K K₀ z)
    (hinf : ∀ J ∈ simpleComponents K, K₀ ⊓ J = ⊥)
    {a b : Γ} (ha : a ∈ A) (hb : b ∈ A) {J : Subgroup Γ} (hJ : J ∈ simpleComponents K) :
    J.map (MulAut.conj (b * z * b⁻¹)).toMonoidHom = J ∨
      J.map (MulAut.conj (b * z * b⁻¹)).toMonoidHom =
        J.map (MulAut.conj (a * z * a⁻¹)).toMonoidHom ∨
      J.map (MulAut.conj (b * z * b⁻¹)).toMonoidHom =
        J.map (MulAut.conj ((a * z * a⁻¹) ^ 2)).toMonoidHom := by
  let c : Γ := a * z * a⁻¹
  let c' : Γ := b * z * b⁻¹
  change J.map (MulAut.conj c').toMonoidHom = J ∨
    J.map (MulAut.conj c').toMonoidHom = J.map (MulAut.conj c).toMonoidHom ∨
    J.map (MulAut.conj c').toMonoidHom = J.map (MulAut.conj (c ^ 2)).toMonoidHom
  by_contra hcon
  push Not at hcon
  have hc3 : c ^ 3 = 1 := conj_z_pow_three h a
  have hc'3 : c' ^ 3 = 1 := conj_z_pow_three h b
  have hc'A : c' ∈ A := A.mul_mem (A.mul_mem hb h.hzA) (A.inv_mem hb)
  have hmeet := step5_meet h hinf ha hb hJ
  have hmeet' : J.map (MulAut.conj c).toMonoidHom = J.map (MulAut.conj c').toMonoidHom ∨
      J.map (MulAut.conj c).toMonoidHom = J.map (MulAut.conj (c' ^ 2)).toMonoidHom ∨
      J.map (MulAut.conj (c ^ 2)).toMonoidHom = J.map (MulAut.conj c').toMonoidHom ∨
      J.map (MulAut.conj (c ^ 2)).toMonoidHom =
        J.map (MulAut.conj (c' ^ 2)).toMonoidHom := by
    simpa [c, c'] using hmeet
  have hc'2mem : J.map (MulAut.conj (c' ^ 2)).toMonoidHom =
      J.map (MulAut.conj c).toMonoidHom ∨
      J.map (MulAut.conj (c' ^ 2)).toMonoidHom =
        J.map (MulAut.conj (c ^ 2)).toMonoidHom := by
    rcases hmeet' with h | h | h | h
    · exact absurd h.symm hcon.2.1
    · exact Or.inl h.symm
    · exact absurd h.symm hcon.2.2
    · exact Or.inr h.symm
  let Y : Subgroup Γ := J.map (MulAut.conj c').toMonoidHom
  have hY : Y ∈ simpleComponents K := by
    change J.map (MulAut.conj c').toMonoidHom ∈ simpleComponents K
    exact map_conj_mem_simpleComponents (h.hK.1 hc'A) hJ
  have hYc' : Y.map (MulAut.conj c').toMonoidHom =
      J.map (MulAut.conj (c' ^ 2)).toMonoidHom := by
    simp only [Y]
    rw [← map_conj_mul, show c' * c' = c' ^ 2 by rw [pow_two]]
  have hYc'2 : Y.map (MulAut.conj (c' ^ 2)).toMonoidHom = J := by
    simp only [Y]
    rw [← map_conj_mul, sq_mul_self hc'3, CFSG.Timmesfeld.RankOne.map_conj_one]
  have hYc_not : ¬ (Y.map (MulAut.conj c).toMonoidHom = J ∨
      Y.map (MulAut.conj c).toMonoidHom = J.map (MulAut.conj c).toMonoidHom ∨
      Y.map (MulAut.conj c).toMonoidHom = J.map (MulAut.conj (c ^ 2)).toMonoidHom) := by
    rintro (h | h | h)
    · have e1 := congrArg (fun K => K.map (MulAut.conj (c ^ 2)).toMonoidHom) h
      rw [orbit_step_inv hc3,
        show Y = J.map (MulAut.conj c').toMonoidHom from rfl] at e1
      exact hcon.2.2 e1
    · have e1 := congrArg (fun K => K.map (MulAut.conj (c ^ 2)).toMonoidHom) h
      rw [orbit_step_inv hc3, orbit_step_inv hc3,
        show Y = J.map (MulAut.conj c').toMonoidHom from rfl] at e1
      exact hcon.1 e1
    · have e1 := congrArg (fun K => K.map (MulAut.conj (c ^ 2)).toMonoidHom) h
      rw [orbit_step_inv hc3, orbit_step_inv' hc3,
        show Y = J.map (MulAut.conj c').toMonoidHom from rfl] at e1
      exact hcon.2.1 e1
  have hYc2_not : ¬ (Y.map (MulAut.conj (c ^ 2)).toMonoidHom = J ∨
      Y.map (MulAut.conj (c ^ 2)).toMonoidHom = J.map (MulAut.conj c).toMonoidHom ∨
      Y.map (MulAut.conj (c ^ 2)).toMonoidHom =
        J.map (MulAut.conj (c ^ 2)).toMonoidHom) := by
    rintro (h | h | h)
    · have e1 := congrArg (fun K => K.map (MulAut.conj c).toMonoidHom) h
      rw [orbit_step' hc3, show Y = J.map (MulAut.conj c').toMonoidHom from rfl] at e1
      exact hcon.2.1 e1
    · have e1 := congrArg (fun K => K.map (MulAut.conj c).toMonoidHom) h
      rw [orbit_step' hc3, orbit_step,
        show Y = J.map (MulAut.conj c').toMonoidHom from rfl] at e1
      exact hcon.2.2 e1
    · have e1 := congrArg (fun K => K.map (MulAut.conj c).toMonoidHom) h
      rw [orbit_step' hc3, orbit_step' hc3,
        show Y = J.map (MulAut.conj c').toMonoidHom from rfl] at e1
      exact hcon.1 e1
  have hmeetY := step5_meet h hinf ha hb hY
  have hmeetY' : Y.map (MulAut.conj c).toMonoidHom = Y.map (MulAut.conj c').toMonoidHom ∨
      Y.map (MulAut.conj c).toMonoidHom = Y.map (MulAut.conj (c' ^ 2)).toMonoidHom ∨
      Y.map (MulAut.conj (c ^ 2)).toMonoidHom = Y.map (MulAut.conj c').toMonoidHom ∨
      Y.map (MulAut.conj (c ^ 2)).toMonoidHom =
        Y.map (MulAut.conj (c' ^ 2)).toMonoidHom := by
    simpa [c, c'] using hmeetY
  rcases hmeetY' with h' | h' | h' | h'
  · rcases hc'2mem with h2 | h2
    · exact hYc_not (Or.inr (Or.inl (h'.trans (hYc'.trans h2))))
    · exact hYc_not (Or.inr (Or.inr (h'.trans (hYc'.trans h2))))
  · exact hYc_not (Or.inl (h'.trans hYc'2))
  · rcases hc'2mem with h2 | h2
    · exact hYc2_not (Or.inr (Or.inl (h'.trans (hYc'.trans h2))))
    · exact hYc2_not (Or.inr (Or.inr (h'.trans (hYc'.trans h2))))
  · exact hYc2_not (Or.inl (h'.trans hYc'2))

private lemma eq_of_setting {z : Γ} (h : Setting A K K₀ z) : K₀ = K := by
  classical
  by_contra hne
  obtain ⟨T₀, hT₀, hmove⟩ := exists_moved_component h hne
  have hmoveAll := exists_conj_moves h hne
  have hinf := inf_component_eq_bot h hne hmoveAll
  have hz3 : z ^ 3 = 1 := by simpa [h.hz] using pow_orderOf_eq_one z
  let Gen : Set Γ := {c | ∃ a ∈ A, c = a * z * a⁻¹}
  let B : Subgroup Γ := Subgroup.closure Gen
  have hBA : B ≤ A := by
    change Subgroup.closure Gen ≤ A
    rw [Subgroup.closure_le]
    rintro c ⟨a, ha, rfl⟩
    exact A.mul_mem (A.mul_mem ha h.hzA) (A.inv_mem ha)
  have hzB : z ∈ B := by
    change z ∈ Subgroup.closure Gen
    have hm : (1 : Γ) * z * 1⁻¹ ∈ Gen := ⟨1, A.one_mem, rfl⟩
    simpa using Subgroup.subset_closure hm
  have hconjGen : ∀ a ∈ A, ∀ c ∈ Gen, a * c * a⁻¹ ∈ Gen := by
    rintro a ha c ⟨b, hb, rfl⟩
    exact ⟨a * b, A.mul_mem ha hb, by group⟩
  have hconjB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    change a * b * a⁻¹ ∈ Subgroup.closure Gen
    refine Subgroup.closure_induction (p := fun b _ => a * b * a⁻¹ ∈ Subgroup.closure Gen)
      (fun x hx => Subgroup.subset_closure (hconjGen a ha x hx)) ?_ ?_ ?_ hb
    · simpa using Subgroup.one_mem (Subgroup.closure Gen)
    · intro x y hx hy hpx hpy
      simpa [mul_assoc] using (Subgroup.closure Gen).mul_mem hpx hpy
    · intro x hx hpx
      simpa [mul_assoc] using (Subgroup.closure Gen).inv_mem hpx
  have hNB : A ≤ Subgroup.normalizer (B : Set Γ) :=
    le_normalizer_of_conj_mem hconjB
  have hBeq : B = A := h.hgen B hBA hNB hzB
  let β : Set (Subgroup Γ) := insert T₀
    (insert (T₀.map (MulAut.conj z).toMonoidHom)
      {T₀.map (MulAut.conj (z ^ 2)).toMonoidHom})
  have hT₀β : T₀ ∈ β := by
    simp [β]
  have hTz2_ne : T₀.map (MulAut.conj (z ^ 2)).toMonoidHom ≠ T₀ := by
    intro h2
    have e := congrArg (fun K => K.map (MulAut.conj z).toMonoidHom) h2
    rw [orbit_step' hz3] at e
    exact hmove e.symm
  have hTzTz2_ne : T₀.map (MulAut.conj z).toMonoidHom ≠
      T₀.map (MulAut.conj (z ^ 2)).toMonoidHom := by
    intro h2
    apply hTz2_ne
    have e := congrArg (fun K => K.map (MulAut.conj z).toMonoidHom) h2
    rw [orbit_step, orbit_step' hz3] at e
    exact e
  have hβ_stable : ∀ J ∈ β, J.map (MulAut.conj z).toMonoidHom ∈ β := by
    intro J hJ
    simp only [β, Set.mem_insert_iff, Set.mem_singleton_iff] at hJ ⊢
    rcases hJ with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · rw [orbit_step]
      exact Or.inr (Or.inr rfl)
    · rw [orbit_step' hz3]
      exact Or.inl rfl
  have hβ_stable2 : ∀ J ∈ β, J.map (MulAut.conj (z ^ 2)).toMonoidHom ∈ β := by
    intro J hJ
    simp only [β, Set.mem_insert_iff, Set.mem_singleton_iff] at hJ ⊢
    rcases hJ with rfl | rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · rw [orbit_step_inv hz3]
      exact Or.inl rfl
    · rw [orbit_step_inv' hz3]
      exact Or.inr (Or.inl rfl)
  have hβ_subset : β ⊆ simpleComponents K := by
    intro J hJ
    simp only [β, Set.mem_insert_iff, Set.mem_singleton_iff] at hJ
    rcases hJ with rfl | rfl | rfl
    · exact hT₀
    · exact map_conj_mem_simpleComponents (h.hK.1 h.hzA) hT₀
    · exact map_conj_mem_simpleComponents (h.hK.1 (Subgroup.pow_mem A h.hzA 2)) hT₀
  let S : Subgroup Γ :=
    { carrier := {g | ∀ J ∈ β, J.map (MulAut.conj g).toMonoidHom ∈ β}
      one_mem' := by
        intro J hJ
        rw [CFSG.Timmesfeld.RankOne.map_conj_one]
        exact hJ
      mul_mem' := by
        intro a b ha hb J hJ
        rw [map_conj_mul]
        exact ha _ (hb J hJ)
      inv_mem' := by
        intro a ha J hJ
        let f : ↥β → ↥β := fun K =>
          ⟨K.1.map (MulAut.conj a).toMonoidHom, ha K.1 K.2⟩
        have hf : Function.Injective f := by
          intro K L hKL
          apply Subtype.ext
          exact (map_conj_inj).mp (congrArg Subtype.val hKL)
        have hsurj := Finite.injective_iff_surjective.mp hf
        obtain ⟨K, hK⟩ := hsurj ⟨J, hJ⟩
        have hval : K.1.map (MulAut.conj a).toMonoidHom = J := congrArg Subtype.val hK
        rw [← hval, ← map_conj_mul]
        rw [show a⁻¹ * a = 1 by group, CFSG.Timmesfeld.RankOne.map_conj_one]
        exact K.2 }
  have hgenS : Gen ⊆ S := by
    rintro c ⟨a, ha, rfl⟩ J hJ
    have hJΩ : J ∈ simpleComponents K := hβ_subset hJ
    have hstep := step5_orbit h hinf A.one_mem ha (a := 1) (b := a) hJΩ
    simp only [one_mul, mul_one, inv_one] at hstep
    rcases hstep with hstep | hstep | hstep
    · rw [hstep]
      exact hJ
    · rw [hstep]
      exact hβ_stable J hJ
    · rw [hstep]
      exact hβ_stable2 J hJ
  have hBS : B ≤ S := by
    change Subgroup.closure Gen ≤ S
    exact (Subgroup.closure_le S).mpr hgenS
  have hAS : A ≤ S := by
    rw [← hBeq]
    exact hBS
  have hβinv : ∀ a : ↥A, ∀ J ∈ β, J.map (MulAut.conj (a : Γ)).toMonoidHom ∈ β :=
    fun a J hJ => hAS a.2 J hJ
  let σ : ↥A →* Equiv.Perm β :=
    { toFun := fun a =>
        { toFun := fun J => ⟨J.1.map (MulAut.conj (a : Γ)).toMonoidHom, hβinv a J.1 J.2⟩
          invFun := fun J =>
            ⟨J.1.map (MulAut.conj ((a : Γ)⁻¹)).toMonoidHom,
              by simpa using hβinv a⁻¹ J.1 J.2⟩
          left_inv := fun J => by
            apply Subtype.ext
            exact map_conj_inv_map_conj J.1 (a : Γ)
          right_inv := fun J => by
            apply Subtype.ext
            exact map_conj_map_conj_inv J.1 (a : Γ) }
      map_one' := by
        apply Equiv.ext
        intro J
        apply Subtype.ext
        simpa using CFSG.Timmesfeld.RankOne.map_conj_one J.1
      map_mul' := by
        intro a b
        apply Equiv.ext
        intro J
        apply Subtype.ext
        change J.1.map (MulAut.conj (↑(a * b))).toMonoidHom =
          (J.1.map (MulAut.conj (↑b)).toMonoidHom).map (MulAut.conj (↑a)).toMonoidHom
        rw [Subgroup.coe_mul, map_conj_mul] }
  have hβncard : β.ncard = 3 := by
    have h1 : T₀ ∉ (insert (T₀.map (MulAut.conj z).toMonoidHom)
        {T₀.map (MulAut.conj (z ^ 2)).toMonoidHom} : Set (Subgroup Γ)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h1 | h1)
      · exact hmove h1.symm
      · exact hTz2_ne h1.symm
    have h2 : T₀.map (MulAut.conj z).toMonoidHom ∉
        ({T₀.map (MulAut.conj (z ^ 2)).toMonoidHom} : Set (Subgroup Γ)) := by
      simp only [Set.mem_singleton_iff]
      exact hTzTz2_ne
    change β.ncard = 3
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]
  have hβcard : Nat.card β ≤ 4 := by
    rw [Nat.card_coe_set_eq, hβncard]
    norm_num
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr h.hA
  haveI : Group.IsSolvable (Equiv.Perm β) := Equiv.Perm.isSolvable hβcard
  have hσ1 : σ = 1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one σ
  have hσ1z : σ ⟨z, h.hzA⟩ = (1 : Equiv.Perm β) := by
    simpa using congrArg (fun f : ↥A →* Equiv.Perm β => f ⟨z, h.hzA⟩) hσ1
  have hzfix := congrArg (fun e : Equiv.Perm β => e (⟨T₀, hT₀β⟩ : β)) hσ1z
  apply hmove
  exact congrArg Subtype.val hzfix

theorem IsASimple.eq_of_centralizers_le (hK : IsASimple A K) (h3 : ¬ 3 ∣ Nat.card K) {z : Γ}
    (hzA : z ∈ A) (hz : orderOf z = 3) (hA : ⁅A, A⁆ = A)
    (hgen : ∀ B : Subgroup Γ, B ≤ A → A ≤ Subgroup.normalizer (B : Set Γ) → z ∈ B → B = A)
    (hOut : ∀ T ∈ simpleComponents K,
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥T))
    (hK₀ : K₀ ≤ K) (hK₀A : A ≤ Subgroup.normalizer (K₀ : Set Γ))
    (hfix : ∀ a ∈ A, K ⊓ Subgroup.centralizer ({a * z * a⁻¹} : Set Γ) ≤ K₀) : K₀ = K := by
  let h : Setting A K K₀ z :=
    { hK := hK
      h3 := h3
      hzA := hzA
      hz := hz
      hA := hA
      hgen := hgen
      hOut := hOut
      hK₀ := hK₀
      hK₀A := hK₀A
      hfix := hfix }
  exact eq_of_setting h

end CFSG.SignalizerFunctorTheorem.Nonsolvable

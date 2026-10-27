module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon
public import CFSG.LocalAnalysis.WeakClosure81.SixTen
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c1_subgroupOf_pCoreOf (K : Subgroup G) :
    (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K :=
  Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

private theorem s16c1_mk_eq_one_iff {K : Subgroup G} (k : ↥K) :
    (k : Bar2 K) = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  rw [QuotientGroup.eq_one_iff, ← s16c1_subgroupOf_pCoreOf K, Subgroup.mem_subgroupOf]

theorem s16c1_orders_of_cases {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V) (hz : z ∈ V)
    (hcases : ∀ h ∈ centralizer ({z} : Set G), ∀ w ∈ V,
      w ∉ pCoreOf 2 (centralizer ({z} : Set G)) →
        ⁅w, h⁻¹ * w * h⁆ ∈ pCoreOf 2 (centralizer ({z} : Set G)) ∨
          ∃ d ∈ ({3, 5, 17} : Set ℕ),
            (w * (h⁻¹ * w * h)) ^ d ∈ pCoreOf 2 (centralizer ({z} : Set G))) :
    ∀ v ∈ starImg (centralizer ({z} : Set G)) V, v ≠ 1 →
      ∀ a b : Bar2 (centralizer ({z} : Set G)),
        orderOf (a * v * a⁻¹ * (b * v * b⁻¹)) ∈ ({1, 2, 3, 5, 17} : Set ℕ) := by
  intro v hv hv1 a b
  let H : Subgroup G := centralizer ({z} : Set G)
  let π : ↥H →* Bar2 H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  obtain ⟨w', hw'sub, hw'v⟩ := Subgroup.mem_map.mp (show v ∈ starImg H V from hv)
  have hwV : (w' : G) ∈ V := Subgroup.mem_subgroupOf.mp hw'sub
  have hwQ : (w' : G) ∉ pCoreOf 2 H := by
    intro hmem
    have h1 : (w' : Bar2 H) = 1 := (s16c1_mk_eq_one_iff w').mpr hmem
    exact hv1 (by rw [← hw'v]; exact h1)
  obtain ⟨α, hα⟩ := QuotientGroup.mk'_surjective (N := CFSG.pCore 2 ↥H) a
  obtain ⟨β, hβ⟩ := QuotientGroup.mk'_surjective (N := CFSG.pCore 2 ↥H) b
  let c' : ↥H := β⁻¹ * α
  let x' : ↥H := c'⁻¹ * w' * c'
  have hx'val : (x' : G) = (c' : G)⁻¹ * (w' : G) * (c' : G) := by simp [x']
  have hπc' : π c' = b⁻¹ * a := by
    change QuotientGroup.mk' (CFSG.pCore 2 ↥H) (β⁻¹ * α) = b⁻¹ * a
    rw [map_mul, map_inv, hα, hβ]
  have hπx' : π x' = a⁻¹ * (b * v * b⁻¹) * a := by
    rw [show x' = c'⁻¹ * w' * c' from rfl, map_mul, map_mul, map_inv, hπc', hw'v]
    group
  have hae : a * v * a⁻¹ * (b * v * b⁻¹) = a * (v * π x') * a⁻¹ := by
    rw [hπx']; group
  have hord : orderOf (a * v * a⁻¹ * (b * v * b⁻¹)) = orderOf (v * π x') := by
    rw [hae]
    exact (SemiconjBy.orderOf_eq (x := v * π x') (y := a * (v * π x') * a⁻¹) a
      (show a * (v * π x') = (a * (v * π x') * a⁻¹) * a from by group)).symm
  have hw'2 : w' ^ 2 = 1 := by
    apply H.subtype_injective
    rw [map_pow, map_one]
    exact hV.2 (w' : G) hwV
  have hx'2 : x' ^ 2 = 1 := by
    have hx'eq : x' = MulAut.conj c'⁻¹ w' := by
      show c'⁻¹ * w' * c' = MulAut.conj c'⁻¹ w'
      rw [MulAut.conj_apply, inv_inv]
    rw [hx'eq, ← map_pow, hw'2, map_one]
  have hv2 : v ^ 2 = 1 := by
    rw [← hw'v, ← map_pow, hw'2, map_one]
  have hπx'2 : (π x') ^ 2 = 1 := by
    rw [← map_pow, hx'2, map_one]
  rw [hord]
  rcases hcases (c' : G) c'.2 (w' : G) hwV hwQ with hcomm | ⟨d, hd, hdmem⟩
  ·
    rw [← hx'val] at hcomm
    have hmem : ((⁅w', x'⁆ : ↥H) : G) ∈ pCoreOf 2 H := by
      have h1 : ((⁅w', x'⁆ : ↥H) : G) = ⁅(w' : G), (x' : G)⁆ :=
        map_commutatorElement (Subgroup.subtype H) w' x'
      rw [h1]
      exact hcomm
    have hcomm1 : ⁅v, π x'⁆ = 1 := by
      have h2 : π ⁅w', x'⁆ = 1 := (s16c1_mk_eq_one_iff (⁅w', x'⁆)).mpr hmem
      rw [map_commutatorElement π w' x', hw'v] at h2
      exact h2
    have hcommute : Commute v (π x') := commutatorElement_eq_one_iff_mul_comm.mp hcomm1
    have hsq : (v * π x') ^ 2 = 1 := by
      rw [hcommute.mul_pow, hv2, hπx'2, mul_one]
    have hdvd : orderOf (v * π x') ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h <;> rw [h] <;> simp
  ·
    rw [← hx'val] at hdmem
    have hd' : d = 3 ∨ d = 5 ∨ d = 17 := by simpa using hd
    have hmem : (((w' * x') ^ d : ↥H) : G) ∈ pCoreOf 2 H := by
      simpa only [Subgroup.coe_pow, Subgroup.coe_mul] using hdmem
    have h2 : (v * π x') ^ d = 1 := by
      have h3 : π ((w' * x') ^ d) = 1 := (s16c1_mk_eq_one_iff _).mpr hmem
      rw [map_pow, map_mul, hw'v] at h3
      exact h3
    have hdvd : orderOf (v * π x') ∣ d := orderOf_dvd_of_pow_eq_one h2
    rcases hd' with rfl | rfl | rfl
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h <;>
        rw [h] <;> simp
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h <;>
        rw [h] <;> simp
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 17)).mp hdvd with h | h <;>
        rw [h] <;> simp

private theorem s16c1_mQuot_uOne_eq_one {V : Subgroup G} (hV : IsElemAbelian 2 V) {z : G}
    (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V z)) :
    E3.mQuot V (uOne V z) = 1 := by
  have hV2 : IsPGroup 2 V := fun y => ⟨1, Subtype.ext (by simpa using hV.2 y y.2)⟩
  have hcard' : Nat.card ↥V = 2 ^ E3.mQuot V (uOne V z) * Nat.card ↥(uOne V z) :=
    E3.card_eq_two_pow_mul (U := uOne V z) hV2 (inf_le_left : uOne V z ≤ V)
  have hmul : 2 ^ E3.mQuot V (uOne V z) * Nat.card ↥(uOne V z) =
      2 * Nat.card ↥(uOne V z) := by
    rw [← hcard']; exact hcard
  have h2 : 2 ^ E3.mQuot V (uOne V z) = 2 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  exact Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using h2)

theorem s16c1_inCalO_one' {D : Data G} {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {z h : G}
    (hQM : pCoreOf 2 (centralizer ({z} : Set G)) ≤ D.M)
    (hh : h ∈ centralizer ({z} : Set G))
    (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V z))
    (hVM : ¬ conjSubgroup V h ≤ D.M) (hMV : ¬ V ≤ conjSubgroup D.M h)
    (h1 : V₀ ≠ ⊥ → V₀ ⊓ conjSubgroup D.M h ≠ ⊥) (h2 : V₀ ≠ ⊥ → conjSubgroup V₀ h ⊓ D.M ≠ ⊥) :
    InCalO 1 D.M V₀ V h := by
  have hone : E3.mQuot V (uOne V z) = 1 := s16c1_mQuot_uOne_eq_one hV hcard
  have hUconj : uOne V z ≤ conjSubgroup D.M h := by
    have hstep : uOne V z ≤ conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) h :=
      (show uOne V z ≤ pCoreOf 2 (centralizer ({z} : Set G)) from inf_le_right).trans
        (le_of_eq (s16c1_conjSubgroup_pCoreOf_self (centralizer ({z} : Set G)) hh).symm)
    exact hstep.trans (E3.conjSubgroup_mono_left h hQM)
  have hA : E3.mQuot V (conjSubgroup D.M h) ≤ 1 := by
    have hmono : E3.mQuot V (V ⊓ conjSubgroup D.M h) ≤ E3.mQuot V (uOne V z) :=
      E3.mQuot_mono (le_inf inf_le_left hUconj)
    have heq : E3.mQuot V (conjSubgroup D.M h) = E3.mQuot V (V ⊓ conjSubgroup D.M h) :=
      (CFSG.LocalAnalysis.WeakClosure81.mQuot_inf_left V (conjSubgroup D.M h)).symm
    rw [heq]
    exact hmono.trans (le_of_eq hone)
  have hUhM : conjSubgroup (uOne V z) h ≤ D.M := by
    have hstep : conjSubgroup (uOne V z) h ≤ pCoreOf 2 (centralizer ({z} : Set G)) :=
      (E3.conjSubgroup_mono_left h
        (show uOne V z ≤ pCoreOf 2 (centralizer ({z} : Set G)) from inf_le_right)).trans
        (le_of_eq (s16c1_conjSubgroup_pCoreOf_self (centralizer ({z} : Set G)) hh))
    exact hstep.trans hQM
  have hB : E3.mQuot (conjSubgroup V h) D.M ≤ 1 := by
    have hmono : E3.mQuot (conjSubgroup V h) D.M ≤
        E3.mQuot (conjSubgroup V h) (conjSubgroup (uOne V z) h) :=
      E3.mQuot_mono hUhM
    rw [E3.mQuot_conjSubgroup] at hmono
    exact hmono.trans (le_of_eq hone)
  exact ⟨⟨hVM, hA, h1⟩, ⟨hMV, hB, h2⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Permutation.UnitaryThreeRecognition.Bridge3Fix

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)

theorem nrm_eq_one_of_fix {m : Kˣ} {c : Coord J} (hc : c ≠ 1)
    (h : hermitianTorusAction J m c = c) : (m : K) * J.conj (m : K) = 1 := by
  have hcb := coord_snd_ne_zero J hc
  have h2 := congrArg (fun v : Coord J => v.1.2) h
  change (hermitianTorusAction J m c).1.2 = c.1.2 at h2
  rw [torus_snd] at h2
  have hk0 : (m : K) ≠ 0 := m.ne_zero
  have hck0 : J.conj (m : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  field_simp at h2
  linear_combination -h2

theorem torus_fix_of_nrm {m : Kˣ} (hm : (m : K) * J.conj (m : K) = 1) {c : Coord J}
    (hc : c.1.1 = 0) : hermitianTorusAction J m c = c := by
  apply coord_ext
  · rw [torus_fst, hc]; ring
  · rw [torus_snd, mul_assoc, ← mul_inv, mul_comm (J.conj _), hm, inv_one, mul_one]

include S

theorem mem_swapFix_of_conjS {x : pairStab G a b} (hx : S.conjS x = x) :
    (x : G) ∈ swapFix G a b s := by
  have e' : s * (x : G) * s = x := congrArg Subtype.val hx
  refine mem_swapFix.mpr ⟨x.2, ?_⟩
  calc s * (x : G) = s * x * s * s := by rw [mul_assoc _ s s, S.hs2, mul_one]
    _ = x * s := by rw [e']

theorem sigma3_fix [Finite G] [Finite Ω] (k : Kˣ)
    (hk : ∀ c : Coord J, hermitianTorusAction J (C.sigma3 S k) c = hermitianTorusAction J k c) :
    (k : K) * J.conj (k : K) = 1 := by
  have e : C.torusPerm S (S.conjS (C.tOf k)) = C.torusPerm S (C.tOf k) := by
    rw [← tPerm_sigma3, torusPerm_tOf]; exact Equiv.ext hk
  have hx := C.torusPerm_injective S e
  obtain ⟨z, hz, hz1⟩ := S.exists_centQ_ne_one
  have hzQ : z ∈ Q := (mem_centQ.mp hz).1
  have hxz := S.swapFix_commute (mem_swapFix_of_conjS S hx) hz
  have hmem := S.root.normal _ (C.tOf k).2.1 z hzQ
  have hfix := C.tOf_spec k ⟨z, hzQ⟩ hmem
  have hzz : (⟨((C.tOf k : pairStab G a b) : G) * z * ((C.tOf k : pairStab G a b) : G)⁻¹,
      hmem⟩ : Q) = ⟨z, hzQ⟩ := Subtype.ext (by
    change ((C.tOf k : pairStab G a b) : G) * z * ((C.tOf k : pairStab G a b) : G)⁻¹ = z
    rw [hxz]; group)
  rw [hzz] at hfix
  exact nrm_eq_one_of_fix (phi_ne_one.mp hz1) hfix.symm

include C in
theorem conjS_eq_iff [Finite G] [Finite Ω] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    (hconj : ∀ x : K, J.conj x = x ^ (p ^ f)) (h3 : 3 ∣ p ^ f + 1) (x : pairStab G a b) :
    S.conjS x = x ↔ x ^ (p ^ f + 1) = 1 := by
  constructor
  · intro hx
    have hxW := mem_swapFix_of_conjS S hx
    have hW := S.root.card_swapFix_mul S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1 S.hsq S.hpp
      S.hp S.hf S.hpodd S.hd S.hQcard S.hΩcard S.hTcard S.hsa S.hs2
    have h1 : (⟨x, hxW⟩ : swapFix G a b s) ^ Nat.card (swapFix G a b s) = 1 := pow_card_eq_one'
    have h1' : (x : G) ^ Nat.card (swapFix G a b s) = 1 := by
      have := congrArg Subtype.val h1
      rwa [SubgroupClass.coe_pow] at this
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hW, pow_mul, h1', one_pow]
    rfl
  · intro hx
    set m := C.kOf x with hmdef
    have hq := S.hpodd.pow (n := f)
    have hm1 : tPerm J (m ^ (p ^ f + 1)) = 1 := by
      rw [map_pow, hmdef, ← torusPerm_apply C S, ← map_pow, hx, map_one]
    have hN3 := (tPerm_eq_one_iff hK hq hconj h3 _).mp hm1
    rw [Units.val_pow_eq_pow_val] at hN3
    have hsq := units_pow_sq hK m
    have hN : ((m : K) ^ (p ^ f + 1)) ^ (p ^ f - 1) = 1 := by
      rw [← pow_mul]
      have hq1 : 1 ≤ p ^ f := Nat.one_le_iff_ne_zero.mpr (by have := S.hp; positivity)
      have e : (p ^ f + 1) * (p ^ f - 1) + 1 = p ^ f * p ^ f := by
        zify [hq1, Nat.one_le_iff_ne_zero.mpr (show p ^ f * p ^ f ≠ 0 by positivity)]; ring
      have h' : (m : K) ^ ((p ^ f + 1) * (p ^ f - 1)) * m = m := by
        rw [← pow_succ, e, ← Units.val_pow_eq_pow_val, hsq]
      exact (mul_eq_right₀ m.ne_zero).mp h'
    obtain ⟨r, hr⟩ := h3
    have hr1 : 1 ≤ r := by have := S.q_ge; omega
    have e : p ^ f - 1 = 3 * (r - 1) + 1 := by omega
    rw [e, pow_succ, pow_mul, hN3, one_pow, one_mul] at hN
    have hnrm : (m : K) * J.conj (m : K) = 1 := by
      rw [hconj, ← pow_succ', hN]
    obtain ⟨z, hz, hz1⟩ := S.exists_centQ_ne_one
    have hzQ : z ∈ Q := (mem_centQ.mp hz).1
    have hza : (φ ⟨z, hzQ⟩).1.1 = 0 := (C.center ⟨z, hzQ⟩).mp hz
    have hmem := S.root.normal _ x.2.1 z hzQ
    have hy := C.kOf_act x ⟨z, hzQ⟩ hmem
    rw [← hmdef, torus_fix_of_nrm hnrm hza] at hy
    have hxz : (x : G) * z * (x : G)⁻¹ = z := congrArg Subtype.val (φ.injective hy)
    have htz : (x : G) * z = z * x := by
      calc (x : G) * z = (x : G) * z * (x : G)⁻¹ * x := by group
        _ = z * x := by rw [hxz]
    have hs : s⁻¹ = s := inv_eq_of_mul_eq_one_right S.hs2
    have := S.root.conj_eq_of_commute S.hb S.hsa S.hsb S.hcomm hzQ hz1 x.2 htz
    rw [hs] at this
    exact Subtype.ext this

theorem sigma3_step0 [Finite G] [Finite Ω] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    (hconj : ∀ x : K, J.conj x = x ^ (p ^ f)) (h3 : 3 ∣ p ^ f + 1) (k : Kˣ) :
    tPerm J ((C.sigma3 S k * k ^ (p ^ f)) ^ 2) = 1 := by
  let _ : CommGroup (pairStab G a b) :=
    { (inferInstance : Group (pairStab G a b)) with
      mul_comm := fun x y => Subtype.ext (S.hcomm x x.2 y y.2) }
  have hq1 : 1 ≤ p ^ f := Nat.one_le_iff_ne_zero.mpr (by have := S.hp; positivity)
  have hexp : ∀ x : pairStab G a b, x ^ (p ^ f * p ^ f) = x := by
    intro x
    obtain ⟨n, hn⟩ := S.hTdvd
    have h1 : x ^ (p ^ (2 * f) - 1) = 1 := by rw [hn, pow_mul, pow_card_eq_one', one_pow]
    have e : p ^ f * p ^ f = p ^ (2 * f) - 1 + 1 := by
      rw [← pow_add, ← two_mul, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (by have := S.hp; positivity))]
    rw [e, pow_succ, h1, one_mul]
  have key := sq_eq_one_of_involutive hq1 hexp S.conjS (S.conjS_conjS)
    (C.conjS_eq_iff S hK hconj h3) (C.tOf k)
  have := congrArg (C.torusPerm S) key
  rw [map_one, map_pow, map_mul, map_pow, torusPerm_tOf, ← tPerm_sigma3] at this
  rw [map_pow, map_mul, map_pow]
  exact this

end CoordHyp

end CFSG.UnitaryThreeRecognition

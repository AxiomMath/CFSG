module

public import CFSG.Permutation.UnitaryThreeRecognition.BridgeDefs

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
  [Finite G] [Finite Ω] {q : ℕ} (hconj : ∀ x : K, J.conj x = x ^ q)
  (hcop : Nat.Coprime 3 (q + 1))
include C S hconj hcop

omit C S hconj hcop [Finite G] [Finite Ω] in
theorem phi_ne_one {y : Q} : (y : G) ≠ 1 ↔ φ y ≠ 1 := by
  constructor
  · intro hy e; apply hy
    exact congrArg Subtype.val (φ.injective (e.trans (map_one φ).symm))
  · intro hy e; apply hy
    rw [show y = 1 from Subtype.ext e, map_one]

theorem kOf_symm (k : Kˣ) : C.kOf ((C.torusEquiv S hconj hcop).symm k) = k := by
  rw [← torusEquiv_apply C S hconj hcop, MulEquiv.apply_symm_apply]

theorem sigmaK_fix (k : Kˣ) : C.sigmaK S hconj hcop k = k ↔ (k : K) ^ (q + 1) = 1 := by
  set t := (C.torusEquiv S hconj hcop).symm k with htdef
  have hkt : C.kOf t = k := C.kOf_symm S hconj hcop k
  obtain ⟨z, hz, hz1⟩ := S.exists_centQ_ne_one
  have hzQ : z ∈ Q := (mem_centQ.mp hz).1
  have hza : (φ ⟨z, hzQ⟩).1.1 = 0 := (C.center ⟨z, hzQ⟩).mp hz
  have hzb : (φ ⟨z, hzQ⟩).1.2 ≠ 0 :=
    coord_snd_ne_zero J ((phi_ne_one (y := ⟨z, hzQ⟩)).mp hz1)
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hck0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  have hs : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, S.hs2]
  have h1 : C.sigmaK S hconj hcop k = k ↔ S.conjS t = t := by
    rw [sigmaK_apply, ← htdef]
    constructor
    · intro e
      apply (C.torusEquiv S hconj hcop).injective
      rw [torusEquiv_apply, torusEquiv_apply, e, hkt]
    · intro e; rw [e, hkt]
  rw [h1]
  let y : Q := ⟨(t : G) * z * (t : G)⁻¹, S.root.normal t t.2.1 z hzQ⟩
  have hy := C.kOf_spec' t ⟨z, hzQ⟩ y rfl
  rw [hkt] at hy
  constructor
  · intro e
    have hst : s * (t : G) = t * s := by
      have e' : s * (t : G) * s = t := congrArg Subtype.val e
      calc s * (t : G) = s * t * s * s := by rw [mul_assoc _ s s, S.hs2, mul_one]
        _ = t * s := by rw [e']
    have hw : (t : G) ∈ swapFix G a b s := mem_swapFix.mpr ⟨t.2, hst⟩
    have hc := S.swapFix_commute hw hz
    have hyz : y = ⟨z, hzQ⟩ := Subtype.ext (by
      change (t : G) * z * (t : G)⁻¹ = z
      rw [hc]; group)
    rw [hyz] at hy
    have h2 := congrArg (fun v : Coord J => v.1.2) hy
    change (φ ⟨z, hzQ⟩).1.2 = (hermitianTorusAction J k (φ ⟨z, hzQ⟩)).1.2 at h2
    rw [torus_snd] at h2
    rw [← nrm_eq_pow J hconj, nrm_def]
    field_simp at h2
    rw [mul_comm]; exact h2
  · intro hk
    have hN : (k : K) * J.conj (k : K) = 1 := by rw [← nrm_def, nrm_eq_pow J hconj, hk]
    have hyz : φ y = φ ⟨z, hzQ⟩ := by
      rw [hy]
      apply coord_ext
      · rw [torus_fst, hza]; ring
      · rw [torus_snd, mul_assoc, ← mul_inv, mul_comm (J.conj _), hN, inv_one, mul_one]
    have hyz' : (t : G) * z * (t : G)⁻¹ = z := congrArg Subtype.val (φ.injective hyz)
    have htz : (t : G) * z = z * t := by
      calc (t : G) * z = (t : G) * z * (t : G)⁻¹ * t := by group
        _ = z * t := by rw [hyz']
    have := S.root.conj_eq_of_commute S.hb S.hsa S.hsb S.hcomm hzQ hz1 t.2 htz
    rw [hs] at this
    exact Subtype.ext this

end CoordHyp

end CFSG.UnitaryThreeRecognition

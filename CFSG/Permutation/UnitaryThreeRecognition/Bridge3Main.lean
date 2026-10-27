module

public import CFSG.Permutation.UnitaryThreeRecognition.Bridge3Step
public import CFSG.Permutation.UnitaryThreeRecognition.BridgePoint
public import CFSG.Permutation.UnitaryThreeRecognition.DThreeNorm
public import CFSG.Permutation.UnitaryThreeRecognition.Bridge3Hyp

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
  [Finite G] [Finite Ω] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
  (hconj : ∀ x : K, J.conj x = x ^ (p ^ f)) (h3 : 3 ∣ p ^ f + 1) {g : G}
  (hg : s = g⁻¹ * j * g)
include C S hK hconj h3 hg

theorem smapHyp3 :
    DThree.SMapHyp3 J (p ^ f) (S.sMapCoord φ) (C.sigma3 S) (C.hmap3 S) where
  card := hK
  conj_pow := hconj
  q_odd := S.hpodd.pow
  q_ge := by
    have := S.q_ge
    obtain ⟨r, hr⟩ := S.hpodd.pow (n := f)
    omega
  three_dvd := h3
  F_ne _ hc := S.sMapCoord_ne_one φ hc
  F_F _ hc := S.sMapCoord_sMapCoord φ hc
  F_torus k _ hc := C.sMapCoord_torus3 S k hc
  σ_mul k k' := Equiv.ext_iff.mp (C.sigma3_mul S k k')
  σ_fix k hk := C.sigma3_fix S k hk
  σ_step0 k := Equiv.ext_iff.mp (C.sigma3_step0 S hK hconj h3 k)
  F_Z _ hc hca := S.sMapCoord_center φ S.hsj (C := C) hc hca
  F_moufang _ _ hu hv huv huv' := C.sMapCoord_moufang3 S hu hv huv huv'
  h_rel _ hu := C.hmap3_rel S hu
  h_torus k _ c hu := Equiv.ext_iff.mp (C.hmap3_torus S k hu) c
  fix_tor _ hu hF := Equiv.ext_iff.mp (C.hmap3_fix S hK S.hpodd.pow hconj h3 hu hF)
  fix_inv _ hu hF := C.sMapCoord_fix_inv S hK S.hpodd.pow hconj h3 hu hF
  fix_exists := exists_sMapCoord_fix S hg

theorem exists_point_weyl_of_three :
    ∃ s' : G, s' * s' = 1 ∧ s' • a = b ∧ ∀ u (hu : u ∈ Q), u ≠ 1 →
      s' • (u • b) = ((φ.symm (weylCoord J (φ ⟨u, hu⟩)) : Q) : G) • b := by
  obtain ⟨k₀, hk₀⟩ := (C.smapHyp3 S hK hconj h3 hg).exists_weyl_normalization
  exact C.exists_point_weyl S k₀ hk₀

end CoordHyp

end CFSG.UnitaryThreeRecognition

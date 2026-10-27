module

public import CFSG.Permutation.UnitaryThreeRecognition.BridgeHyp4
public import CFSG.Permutation.UnitaryThreeRecognition.BridgePoint
public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgFinal
public import CFSG.Permutation.UnitaryThreeRecognition.BridgeHyp3

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
  [Finite G] [Finite Ω] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
  (hconj : ∀ x : K, J.conj x = x ^ (p ^ f)) (hcop : Nat.Coprime 3 (p ^ f + 1))
include C S hK hconj hcop

omit [Finite K] in
theorem smapHyp :
    SMapHyp J (p ^ f) (S.sMapCoord φ) (C.sigmaK S hconj hcop) (C.hmap S hconj hcop) where
  card := hK
  conj_pow := hconj
  q_odd := S.hpodd.pow
  q_ge := S.q_ge
  coprime := hcop
  F_ne _ hc := S.sMapCoord_ne_one φ hc
  F_F _ hc := S.sMapCoord_sMapCoord φ hc
  σσ := C.sigmaK_sigmaK S hconj hcop
  σfix := C.sigmaK_fix S hconj hcop
  F_torus k _ hc := C.sMapCoord_torus S hconj hcop k hc
  F_Z _ hc hca := S.sMapCoord_center φ S.hsj (C := C) hc hca
  F_block _ hu _ _ hk hk' hk1 hk'1 := C.sMapCoord_block S hconj hcop hu hk hk' hk1 hk'1
  F_moufang _ _ hz hza hw := C.sMapCoord_moufang S hconj hcop hz hza hw
  h_rel _ hz _ := C.hmap_rel S hconj hcop hz
  h_torus k _ hz _ := C.hmap_torus S hconj hcop k hz

theorem exists_point_weyl_of_coprime :
    ∃ s' : G, s' * s' = 1 ∧ s' • a = b ∧ ∀ u (hu : u ∈ Q), u ≠ 1 →
      s' • (u • b) = ((φ.symm (weylCoord J (φ ⟨u, hu⟩)) : Q) : G) • b := by
  obtain ⟨k₀, hk₀⟩ := (C.smapHyp S hK hconj hcop).exists_weyl_normalization
  exact C.exists_point_weyl S k₀ hk₀

end CoordHyp

end CFSG.UnitaryThreeRecognition

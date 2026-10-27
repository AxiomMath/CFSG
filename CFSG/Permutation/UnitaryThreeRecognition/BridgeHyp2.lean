module

public import CFSG.Permutation.UnitaryThreeRecognition.BridgeHyp
public import CFSG.Permutation.UnitaryThreeRecognition.SMapMoufang

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace StdHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} (φ : Q ≃* Coord J)
  (S : StdHyp G Q a b j s p f d)
include S

theorem sMapCoord_ne_one {c : Coord J} (hc : c ≠ 1) : S.sMapCoord φ c ≠ 1 := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  have hu : (u : G) ≠ 1 := CoordHyp.phi_ne_one.mpr hc
  rw [S.sMapCoord_apply φ u hu]
  exact CoordHyp.phi_ne_one.mp (S.root.sLeft_ne_one S.hb S.hsa S.hs2 u.2 hu)

theorem sMapCoord_sMapCoord {c : Coord J} (hc : c ≠ 1) : S.sMapCoord φ (S.sMapCoord φ c) = c := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  have hu : (u : G) ≠ 1 := CoordHyp.phi_ne_one.mpr hc
  rw [S.sMapCoord_apply φ u hu, S.sMapCoord_apply φ _ (S.root.sLeft_ne_one S.hb S.hsa S.hs2 u.2 hu)]
  congr 1
  exact Subtype.ext (S.root.sLeft_sLeft S.hb S.hsa S.hs2 u.2 hu)

theorem conjS_conjS (t : pairStab G a b) : S.conjS (S.conjS t) = t := by
  apply Subtype.ext
  change s * (s * (t : G) * s) * s = t
  calc s * (s * (t : G) * s) * s = (s * s) * t * (s * s) := by group
    _ = t := by rw [S.hs2]; group

theorem sMapCoord_center (hsj : s * j = j * s) {C : CoordHyp Q a b j J φ} {c : Coord J}
    (hc : c ≠ 1) (hca : c.1.1 = 0) : (S.sMapCoord φ c).1.1 = 0 := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  have hu : (u : G) ≠ 1 := CoordHyp.phi_ne_one.mpr hc
  rw [S.sMapCoord_apply φ u hu]
  apply (C.center _).mp
  exact S.root.sLeft_mem_centQ S.hb S.hsa S.hs2 S.hj hsj ((C.center u).mpr hca) hu

end StdHyp

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
  [Finite G] [Finite Ω] {q : ℕ} (hconj : ∀ x : K, J.conj x = x ^ q)
  (hcop : Nat.Coprime 3 (q + 1))
include C S hconj hcop

theorem sigmaK_sigmaK (k : Kˣ) : C.sigmaK S hconj hcop (C.sigmaK S hconj hcop k) = k := by
  simp only [sigmaK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, S.conjS_conjS, MulEquiv.apply_symm_apply]

theorem phi_conj_symm (k : Kˣ) (u : Q) :
    φ ⟨((C.torusEquiv S hconj hcop).symm k : G) * u *
        ((C.torusEquiv S hconj hcop).symm k : G)⁻¹,
      S.root.normal _ ((C.torusEquiv S hconj hcop).symm k).2.1 u u.2⟩ =
      hermitianTorusAction J k (φ u) := by
  rw [C.kOf_spec' _ u _ rfl, C.kOf_symm S hconj hcop]

theorem sMapCoord_torus (k : Kˣ) {c : Coord J} (hc : c ≠ 1) :
    S.sMapCoord φ (hermitianTorusAction J k c) =
      hermitianTorusAction J (C.sigmaK S hconj hcop k) (S.sMapCoord φ c) := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  have hu : (u : G) ≠ 1 := phi_ne_one.mpr hc
  set t := (C.torusEquiv S hconj hcop).symm k with htdef
  set v : Q := ⟨(t : G) * u * (t : G)⁻¹, S.root.normal _ t.2.1 u u.2⟩ with hvdef
  have hv : (v : G) ≠ 1 := by
    intro e
    apply hu
    have e' : (t : G) * u * (t : G)⁻¹ = 1 := e
    calc (u : G) = (t : G)⁻¹ * ((t : G) * u * (t : G)⁻¹) * t := by group
      _ = 1 := by rw [e']; group
  rw [← C.phi_conj_symm S hconj hcop k u, ← htdef, ← hvdef, S.sMapCoord_apply φ v hv,
    S.sMapCoord_apply φ u hu]
  obtain ⟨hL, -, -⟩ := S.root.sFactors_conj S.hb S.hsa S.hs2 u.2 hu t.2
  have hσ : C.sigmaK S hconj hcop k = C.kOf (S.conjS t) := by rw [sigmaK_apply]
  rw [hσ]
  apply C.kOf_spec'
  rw [S.conjS_val]
  exact hL

end CoordHyp

end CFSG.UnitaryThreeRecognition

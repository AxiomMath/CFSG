module

public import CFSG.Permutation.UnitaryThreeRecognition.Bridge3Perm
public import CFSG.Permutation.UnitaryThreeRecognition.BridgeHyp4

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
include S

omit S in
theorem conj_ne_one {t : G} {u : G} (hu : u ≠ 1) : t * u * t⁻¹ ≠ 1 := by
  intro e
  apply hu
  calc u = t⁻¹ * (t * u * t⁻¹) * t := by group
    _ = 1 := by rw [e]; group

theorem sMapCoord_torus3 (k : Kˣ) {c : Coord J} (hc : c ≠ 1) :
    S.sMapCoord φ (hermitianTorusAction J k c) =
      hermitianTorusAction J (C.sigma3 S k) (S.sMapCoord φ c) := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  have hu : (u : G) ≠ 1 := phi_ne_one.mpr hc
  have hmem := S.root.normal _ (C.tOf k).2.1 u u.2
  have hv : (((C.tOf k : pairStab G a b) : G) * u * ((C.tOf k : pairStab G a b) : G)⁻¹) ≠ 1 :=
    conj_ne_one hu
  rw [← C.tOf_spec k u hmem, S.sMapCoord_apply φ _ hv, S.sMapCoord_apply φ u hu, sigma3_def]
  obtain ⟨hL, -, -⟩ := S.root.sFactors_conj S.hb S.hsa S.hs2 u.2 hu (C.tOf k).2
  apply C.kOf_spec'
  rw [S.conjS_val]
  exact hL

theorem sigma3_mul [Finite G] [Finite Ω] (k k' : Kˣ) :
    tPerm J (C.sigma3 S (k * k')) = tPerm J (C.sigma3 S k * C.sigma3 S k') := by
  have e : C.tOf (k * k') = C.tOf k * C.tOf k' := C.tOf_mul S k k'
  rw [map_mul, tPerm_sigma3, tPerm_sigma3, tPerm_sigma3, e, map_mul, map_mul]

theorem hmap3_torus (k : Kˣ) {c : Coord J} (hc : c ≠ 1) :
    tPerm J (C.hmap3 S (hermitianTorusAction J k c)) =
      tPerm J (C.sigma3 S k * C.hmap3 S c * k⁻¹) := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  have hu : (u : G) ≠ 1 := phi_ne_one.mpr hc
  have hmem := S.root.normal _ (C.tOf k).2.1 u u.2
  have hv : (((C.tOf k : pairStab G a b) : G) * u * ((C.tOf k : pairStab G a b) : G)⁻¹) ≠ 1 :=
    conj_ne_one hu
  rw [← C.tOf_spec k u hmem, C.hmap3_apply S _ hv, C.hmap3_apply S u hu]
  obtain ⟨-, hT, -⟩ := S.root.sFactors_conj S.hb S.hsa S.hs2 u.2 hu (C.tOf k).2
  have he : (⟨sTor Q a b s (((C.tOf k : pairStab G a b) : G) * u *
      ((C.tOf k : pairStab G a b) : G)⁻¹), S.root.sTor_mem S.hb S.hsa S.hs2 hmem hv⟩ :
        pairStab G a b) =
      S.conjS (C.tOf k) * ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu⟩ *
        (C.tOf k)⁻¹ := by
    apply Subtype.ext
    change sTor Q a b s (((C.tOf k : pairStab G a b) : G) * u *
      ((C.tOf k : pairStab G a b) : G)⁻¹) = _
    rw [hT]
    rfl
  rw [he]
  change C.torusPerm S _ = _
  simp only [map_mul, map_inv]
  rw [tPerm_sigma3, torusPerm_tOf]
  rfl

theorem sMapCoord_eq (u : Q) (hu : (u : G) ≠ 1) (y : Q) (hy : (y : G) = sLeft Q a b s u) :
    S.sMapCoord φ (φ u) = φ y := by
  rw [S.sMapCoord_apply φ u hu]
  congr 1
  exact Subtype.ext hy.symm

theorem sMapCoord_moufang3 {z w : Coord J} (hz : z ≠ 1) (hw : w ≠ 1)
    (hzw : z * S.sMapCoord φ w ≠ 1) (hzw' : (S.sMapCoord φ z⁻¹)⁻¹ * w ≠ 1) :
    S.sMapCoord φ (z * S.sMapCoord φ w) = S.sMapCoord φ z *
      hermitianTorusAction J (C.hmap3 S z)
        (S.sMapCoord φ ((S.sMapCoord φ z⁻¹)⁻¹ * w)) := by
  obtain ⟨u, rfl⟩ := φ.surjective z
  obtain ⟨v, rfl⟩ := φ.surjective w
  have hu1 : (u : G) ≠ 1 := phi_ne_one.mpr hz
  have hv1 : (v : G) ≠ 1 := phi_ne_one.mpr hw
  have hyQ := S.root.sLeft_mem S.hb S.hsa S.hs2 v.2 hv1
  set y : Q := ⟨sLeft Q a b s v, hyQ⟩ with hydef
  have hrQ := S.root.sRight_mem S.hb S.hsa S.hs2 u.2 hu1
  set r : Q := ⟨sRight Q a b s u, hrQ⟩ with hrdef
  rw [S.sMapCoord_apply φ v hv1, ← hydef, sMapCoord_inv_inv S u hu1, ← hrdef, ← map_mul,
    ← map_mul] at *
  have huy : ((u * y : Q) : G) ≠ 1 := phi_ne_one.mpr hzw
  have hrv : ((r * v : Q) : G) ≠ 1 := phi_ne_one.mpr hzw'
  have hM := S.root.sLeft_mul_sLeft S.hb S.hsa S.hs2 u.2 hu1 v.2 hv1 huy hrv
  rw [S.sMapCoord_apply φ _ huy, S.sMapCoord_apply φ _ hrv, C.hmap3_apply S u hu1,
    S.sMapCoord_apply φ u hu1]
  set τ : pairStab G a b := ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu1⟩
  rw [C.kOf_conj τ _ (S.root.normal τ τ.2.1 _
    (S.root.sLeft_mem S.hb S.hsa S.hs2 (r * v).2 hrv)), ← map_mul]
  congr 1
  apply Subtype.ext
  exact hM

theorem hmap3_rel {z : Coord J} (hz : z ≠ 1) :
    hermitianTorusAction J (C.hmap3 S z) (S.sMapCoord φ (S.sMapCoord φ z⁻¹)⁻¹) =
      (S.sMapCoord φ z)⁻¹ := by
  obtain ⟨u, rfl⟩ := φ.surjective z
  have hu1 : (u : G) ≠ 1 := phi_ne_one.mpr hz
  have hr1 := S.root.sRight_ne_one S.hb S.hsa S.hs2 u.2 hu1
  rw [sMapCoord_inv_inv S u hu1, S.sMapCoord_apply φ _ hr1, C.hmap3_apply S u hu1,
    S.sMapCoord_apply φ u hu1]
  set τ : pairStab G a b := ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu1⟩
  rw [C.kOf_conj τ _ (S.root.normal τ τ.2.1 _
    (S.root.sLeft_mem S.hb S.hsa S.hs2 (S.root.sRight_mem S.hb S.hsa S.hs2 u.2 hu1) hr1)),
    ← map_inv]
  congr 1
  apply Subtype.ext
  exact S.root.sTor_conj_sLeft_sRight S.hb S.hsa S.hs2 u.2 hu1

end CoordHyp

end CFSG.UnitaryThreeRecognition

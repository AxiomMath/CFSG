module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSU
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSUShort
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUDefs
public import CFSG.LieType.Universal.Catalog

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.StandardType CFSG.StandardType.LieKnownR2.Short CFSG.StandardType.RCKFlag CFSG.Open
open Matrix
open scoped Matrix

private theorem rckSPSU_linearIndependent {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {a b : F} (h : a • v + b • w = 0) : a = 0 ∧ b = 0 := by
  have h1 : (suH hc n).β (a • v + b • w) w' = 0 := by rw [h, (suH hc n).β_zero_left]
  rw [(suH hc n).add_left, (suH hc n).smul_left, (suH hc n).smul_left, hfr.1,
    hfr.2.2.2.2.2.1, mul_one, mul_zero, add_zero] at h1
  have h2 : (suH hc n).β (a • v + b • w) v' = 0 := by rw [h, (suH hc n).β_zero_left]
  rw [(suH hc n).add_left, (suH hc n).smul_left, (suH hc n).smul_left, hfr.2.2.2.2.1,
    hfr.2.1, mul_zero, mul_one, zero_add] at h2
  exact ⟨(map_eq_zero_iff _ (unitaryInvolution F 2 f).injective).mp h1,
    (map_eq_zero_iff _ (unitaryInvolution F 2 f).injective).mp h2⟩

theorem rckSPSU_suPair_core (n g : ℕ) (hg : 1 ≤ g)
    {v w v' w' : Fin n → GaloisField 2 (2 * g)}
    (hfr : SUFrame (card_galoisField_two_mul 2 g hg) n v w v' w')
    {r : SU (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) n}
    (hr : r ∈ suPair (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) n v w) (hr1 : r ≠ 1) :
    pCoreOf 2 (Subgroup.centralizer ({r} :
        Set (SU (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) n))) ≤
      Subgroup.centralizer (suPair (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) n v w :
        Set (SU (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) n)) := by
  let σ : GaloisField 2 (2 * g) ≃+* GaloisField 2 (2 * g) :=
    unitaryInvolution (GaloisField 2 (2 * g)) 2 g
  let B : ReflForm (GaloisField 2 (2 * g)) (Fin n → GaloisField 2 (2 * g)) :=
    suH (card_galoisField_two_mul 2 g hg) n
  let W : Submodule (GaloisField 2 (2 * g)) (Fin n → GaloisField 2 (2 * g)) :=
    Submodule.span (GaloisField 2 (2 * g)) {v, w}
  let H : Submodule (GaloisField 2 (2 * g)) (Fin n → GaloisField 2 (2 * g)) := B.perp W
  have hcent := rckFlagCent_SU n g hg
  refine hcent (suPair σ n v w) W H ?_ ?_ ?_ r hr hr1
  · exact suFrame_isTotallyIsotropic hfr
  · intro x hx hx1
    have hvv : B.β v v = 0 := hfr.2.2.1.1
    have hww : B.β w w = 0 := hfr.2.2.1.2.1
    have hvw : B.β v w = 0 := hfr.2.2.2.1
    obtain ⟨c, hc_mul⟩ := exists_mulVec_of_mem_suPair (card_galoisField_two_mul 2 g hg)
      hvv hww hvw hx
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hx1
      apply natRep_injective (SU σ n)
      refine LinearMap.ext fun y => ?_
      rw [hc_mul y, hc0]
      simp
    have hσc0 : σ c ≠ 0 := fun h => hc0 (σ.injective (by rw [h, map_zero]))
    set N : (Fin n → GaloisField 2 (2 * g)) →ₗ[GaloisField 2 (2 * g)]
        (Fin n → GaloisField 2 (2 * g)) :=
      Matrix.toLin' (((SU σ n).subtype x : GL (Fin n) (GaloisField 2 (2 * g))) - 1) with hNdef
    have hN_eq : N = natRep (SU σ n) x - 1 := by
      rw [hNdef, map_sub, Matrix.toLin'_one]
      congr 1
    have hN_apply : ∀ y, N y = (c * B.β w y) • v + (σ c * B.β v y) • w := by
      intro y
      rw [hN_eq, LinearMap.sub_apply, hc_mul y, Module.End.one_apply]
      simp only [B, σ]
      abel
    have hNrange : N.range = W := by
      refine le_antisymm ?_ ?_
      · rintro z ⟨y, rfl⟩
        rw [hN_apply y]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · rw [Submodule.span_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · refine ⟨c⁻¹ • v', ?_⟩
          rw [map_smul, hN_apply v', hfr.2.1, hfr.2.2.2.2.1, mul_one, mul_zero, zero_smul,
            add_zero, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        · refine ⟨(σ c)⁻¹ • w', ?_⟩
          rw [map_smul, hN_apply w', hfr.2.2.2.2.2.1, hfr.1, mul_zero, mul_one,
            zero_smul, zero_add, smul_smul, inv_mul_cancel₀ hσc0, one_smul]
    have hNker : N.ker = H := by
      ext z
      rw [LinearMap.mem_ker, hN_apply z, ReflForm.mem_perp]
      constructor
      · intro h x hx
        obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
        obtain ⟨hcw, hcv⟩ := rckSPSU_linearIndependent hfr h
        have hwz : B.β w z = 0 := (mul_eq_zero.mp hcw).resolve_left hc0
        have hvz : B.β v z = 0 := (mul_eq_zero.mp hcv).resolve_left hσc0
        rw [B.add_left, B.smul_left, B.smul_left, hvz, hwz, mul_zero, mul_zero, add_zero]
      · intro h
        have hv0 : B.β v z = 0 := h v (Submodule.subset_span (by simp))
        have hw0 : B.β w z = 0 := h w (Submodule.subset_span (by simp))
        rw [hv0, hw0, mul_zero, mul_zero, zero_smul, zero_smul, add_zero]
    exact ⟨hNrange, hNker⟩
  · intro b hb
    exact absurd hb (by simp)

end CFSG.StandardType.RCKC1

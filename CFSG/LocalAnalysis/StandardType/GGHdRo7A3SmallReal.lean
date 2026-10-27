module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Refl
import CFSG.LocalAnalysis.StandardType.GGWAutCommon
import CFSG.LocalAnalysis.StandardType.GGQTwoTransvectionFreeRules
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallBridge

public section

namespace CFSG.StandardType.HdRo7A3.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7A3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7A9RealAux_eq_sum {u : Fin 9 → ZMod 3} (hu : u ∈ a3Aug 3 9) :
    u = ∑ i, u i • a9E i 8 := by
  have hu' : ∑ i, u i = 0 := hu
  have hsum_single : ∑ i : Fin 9, u i • (Pi.single i (1 : ZMod 3) : Fin 9 → ZMod 3) = u := by
    ext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  calc u = ∑ i : Fin 9, u i • (Pi.single i (1 : ZMod 3) : Fin 9 → ZMod 3) := hsum_single.symm
    _ = ∑ i : Fin 9, (u i • (Pi.single i (1 : ZMod 3) : Fin 9 → ZMod 3) -
          u i • (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3)) +
          (∑ i : Fin 9, u i) • (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hu', zero_smul, sub_zero, add_zero]
    _ = ∑ i : Fin 9, u i • (Pi.single i (1 : ZMod 3) - Pi.single (8 : Fin 9) 1 :
          Fin 9 → ZMod 3) := by
          simp only [smul_sub, hu', zero_smul, add_zero]
    _ = ∑ i : Fin 9, u i • a9E i 8 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [a9E]

private lemma hdRo7A9RealAux_dual {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V} {φ' : Module.Dual (ZMod 3) V} {f : Fin 9 → ZMod 3}
    (hf : ∀ i, f i = φ' (θ (a9E i 8))) :
    ∀ u ∈ a3Aug 3 9, φ' (θ u) = ∑ i, f i * u i := by
  intro u hu
  conv_lhs => rw [hdRo7A9RealAux_eq_sum hu]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, ← hf i, smul_eq_mul, mul_comm]

theorem a9_real_holds : A9RealLeaf := by
  intro V _ _ θ z H A hD hM r hrH hrr hrz
  have hfr : A3Frame 3 9 θ z := hD.hfr
  have hpm : 3 ∣ 9 := hD.h3
  obtain ⟨c, φ, hφc, hreq⟩ := (CFSG.StandardType.ggLinRefl_iff_isReflLin r).mp hrr
  have hrf : ∀ v, r v = v - φ v • c := fun v => by
    rw [hreq, Module.reflection_apply]
  have hcM : c ∉ (a3Aug 3 9).map θ := by
    intro hc
    have hspan : ggLinMove r ≤ (a3Aug 3 9).map θ := by
      rintro w ⟨v, rfl⟩
      have hw : (r.toLinearMap - LinearMap.id : V →ₗ[ZMod 3] V) v = -(φ v • c) := by
        have h1 : (r.toLinearMap - LinearMap.id : V →ₗ[ZMod 3] V) v = r v - v := rfl
        rw [h1, hrf v]
        abel
      rw [hw, ← neg_smul]
      exact Submodule.smul_mem _ _ hc
    exact hrz (a3_reflM9_holds (p := 3) (m := 9) (V := V) (θ := θ) (z := z) (H := H) (A := A)
      hD hM rfl r hrH hrr hspan)
  obtain ⟨ĥ₀, hĥ₀U, c₀, hc₀⟩ := hfr.2.1 c
  have hc₀ne : c₀ ≠ 0 := by
    intro h0
    apply hcM
    rw [hc₀, h0, zero_smul, add_zero]
    exact Submodule.mem_map_of_mem hĥ₀U
  let hh : Fin 9 → ZMod 3 := c₀⁻¹ • ĥ₀
  have hhh : hh = c₀⁻¹ • ĥ₀ := rfl
  have hhU : hh ∈ a3Aug 3 9 := by
    rw [hhh]
    exact Submodule.smul_mem _ _ hĥ₀U
  have hcdecomp : c = c₀ • (θ hh + z) := by
    rw [hc₀]
    show θ ĥ₀ + c₀ • z = c₀ • (θ (c₀⁻¹ • ĥ₀) + z)
    rw [map_smul, smul_add, smul_smul, mul_inv_cancel₀ hc₀ne, one_smul]
  let φ' : Module.Dual (ZMod 3) V := c₀ • φ
  have hφ'root : φ' (θ hh + z) = 2 := by
    have h1 : φ (c₀ • (θ hh + z)) = c₀ • φ (θ hh + z) := map_smul φ c₀ (θ hh + z)
    have h2 : φ' (θ hh + z) = c₀ • φ (θ hh + z) := rfl
    rw [h2, ← h1, ← hcdecomp, hφc]
  have hφ'v_apply : ∀ v : V, φ' v = c₀ • φ v := fun v => rfl
  have hrf' : ∀ v, r v = v - φ' v • (θ hh + z) := by
    intro v
    have h1 : φ' v • (θ hh + z) = φ v • (c₀ • (θ hh + z)) := by
      rw [hφ'v_apply v, smul_eq_mul, smul_smul, mul_comm c₀ (φ v)]
    rw [hrf v, hcdecomp, h1]
  let f : Fin 9 → ZMod 3 := fun i => φ' (θ (a9E i 8))
  let d : ZMod 3 := φ' z
  have hφθ : ∀ u ∈ a3Aug 3 9, φ' (θ u) = ∑ i, f i * u i :=
    hdRo7A9RealAux_dual (φ' := φ') (f := f) (fun i => rfl)
  have hsumf : ∑ i, f i = 0 := by
    have h := hφθ (fun _ : Fin 9 => (1 : ZMod 3)) (a3_const_mem (p := 3) (m := 9) hpm 1)
    rw [hM, map_zero] at h
    simpa using h.symm
  have hfh : ∑ i, f i * hh i + d = 2 := by
    rw [← hφθ hh hhU]
    show φ' (θ hh) + φ' z = 2
    rw [← map_add]
    exact hφ'root
  have hlevel : ∀ i j, f i = f j ↔ hh i = hh j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · obtain ⟨t, ψ, htU, htz, hψU, hψz, htf, _htr⟩ :=
        a3_transp (p := 3) rfl hfr hpm (by norm_num : 3 ≤ 9) hij
      have htH : t ∈ H := hD.hPH t ⟨Equiv.swap i j, htU, htz⟩
      have hwij : (Pi.single i (1 : ZMod 3) - Pi.single j 1 : Fin 9 → ZMod 3) ∈ a3Aug 3 9 :=
        a3_single_sub_mem i j
      have hψw : ψ (θ (Pi.single i (1 : ZMod 3) - Pi.single j 1)) = 2 := by
        rw [hψU _ hwij]
        have hji : j ≠ i := Ne.symm hij
        have h1 : (Pi.single i (1 : ZMod 3) - Pi.single j 1 : Fin 9 → ZMod 3) i = 1 := by
          simp [Pi.sub_apply, hij]
        have h2 : (Pi.single i (1 : ZMod 3) - Pi.single j 1 : Fin 9 → ZMod 3) j = -1 := by
          simp [Pi.sub_apply, hji]
        rw [h1, h2]
        norm_num
      have hTF : CFSG.StandardType.QTwoLin.TransvectionFree A := fun g hg hgt =>
        hD.hNoT g hg (CFSG.StandardType.HdRo7SU.Small.c2Transv_of_isTransvectionLin g hgt)
      have hzp := CFSG.StandardType.QTwoLin.zero_pair_iff_of_transvectionFree (K := ZMod 3) hTF
        (hD.hHA hrH) (hD.hHA htH) hφ'root hψw hrf' htf
      have h1 : φ' (θ (Pi.single i (1 : ZMod 3) - Pi.single j 1)) = f i - f j := by
        have hfi : f i = φ' (θ (Pi.single i (1 : ZMod 3))) -
            φ' (θ (Pi.single (8 : Fin 9) (1 : ZMod 3))) := by
          dsimp only [f, a9E]
          rw [map_sub, map_sub]
        have hfj : f j = φ' (θ (Pi.single j (1 : ZMod 3))) -
            φ' (θ (Pi.single (8 : Fin 9) (1 : ZMod 3))) := by
          dsimp only [f, a9E]
          rw [map_sub, map_sub]
        rw [hfi, hfj, map_sub, map_sub]
        abel
      have h2 : ψ (θ hh + z) = hh i - hh j := by
        rw [map_add, hψU hh hhU, hψz, add_zero]
      rw [h1, h2] at hzp
      constructor
      · intro h
        exact sub_eq_zero.mp (hzp.mp (sub_eq_zero.mpr h))
      · intro h
        exact sub_eq_zero.mp (hzp.mpr (sub_eq_zero.mpr h))
  refine ⟨hh, f, d, hhU, hsumf, hfh, hlevel, ?_⟩
  intro u hu c
  have hφu : φ' (θ u) = ∑ i, f i * u i := hφθ u hu
  have hφcu : φ' (θ u + c • z) = ∑ i, f i * u i + c * d := by
    rw [map_add, map_smul, hφu]
    show ∑ i, f i * u i + c • φ' z = ∑ i, f i * u i + c * d
    rw [smul_eq_mul]
  set lam : ZMod 3 := ∑ i, f i * u i + c * d with hlam
  have hφcu' : φ' (θ u + c • z) = lam := by rw [hφcu, hlam]
  show r (θ u + c • z) = θ (u - lam • hh) + (c - lam) • z
  rw [hrf' (θ u + c • z), hφcu']
  have h1 : θ (u - lam • hh) = θ u - lam • θ hh := by rw [map_sub, map_smul]
  have h2 : (c - lam) • z = c • z - lam • z := sub_smul c lam z
  have h3 : lam • (θ hh + z) = lam • θ hh + lam • z := smul_add lam (θ hh) z
  rw [h1, h2, h3]
  abel

end CFSG.StandardType.HdRo7A3.Small

module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrthNonFull
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCompSgn
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenAsmB
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenGenB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankWitt

public section

namespace CFSG.StandardType

open Polynomial Module QuadraticMap
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem reflect_mul_reflect_mem_supportedFixedDerived
    (hx : OddOrderIsometry Q p x) {v w : V}
    (hv : v ∈ fixedSpace x) (hw : w ∈ fixedSpace x)
    (hQv : Q v ≠ 0) (hQw : Q w ≠ 0) :
    reflect Q v * reflect Q w ∈ supportedFixedDerived Q x := by
  have hR : (QuadraticMap.polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hblock : ∀ {y : V}, y ∈ fixedSpace x →
      reflect Q y ∈ supportedBlock Q x (X - 1) := by
    intro y hyS
    have hyx : x y = y := mem_fixedSpace.mp hyS
    have hcomm : x * reflect Q y = reflect Q y * x := by
      have h1 : x * reflect Q y * x⁻¹ = reflect Q y := by
        rw [reflect_conj (hx.mem), hyx]
      have h2 := congrArg (fun z => z * x) h1
      simpa [mul_assoc] using h2
    refine mem_supportedBlock.mpr ⟨?_, ?_⟩
    · rw [mem_isometryCentralizer]
      refine ⟨fun u => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (reflect_mem_orthogonalGroup Q y) u, fun u => ?_⟩
      calc reflect Q y (x u) = (reflect Q y * x) u := rfl
        _ = (x * reflect Q y) u := by rw [hcomm]
        _ = x (reflect Q y u) := rfl
    · intro u hu
      exact reflect_apply_of_polar_eq_zero (hx.fixed_others.2 y hyS u hu)
  have hres : ∀ {y : V} (hyS : y ∈ fixedSpace x) (hQy : Q y ≠ 0)
      (hb : reflect Q y ∈ supportedBlock Q x (X - 1)),
      restrictFixed Q x ⟨reflect Q y, hb⟩
        = reflect (Q.comp (fixedSpace x).subtype) ⟨y, hyS⟩ := by
    intro y hyS hQy hb
    ext u
    rw [CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictFixed]
    show reflect Q y (u : V) =
      ((reflect (Q.comp (fixedSpace x).subtype) ⟨y, hyS⟩) u : V)
    rw [reflect_apply hQy, reflect_apply (by simpa using hQy)]
    simp [QuadraticMap.comp_apply, polar_comp_subtype_cent]
  have hvblock : reflect Q v ∈ supportedBlock Q x (X - 1) := hblock hv
  have hwblock : reflect Q w ∈ supportedBlock Q x (X - 1) := hblock hw
  have helem : (⟨reflect Q v * reflect Q w, mul_mem hvblock hwblock⟩ :
      ↥(supportedBlock Q x (X - 1)))
      = ⟨reflect Q v, hvblock⟩ * ⟨reflect Q w, hwblock⟩ := rfl
  refine mem_supportedFixedDerived.mpr ⟨mul_mem hvblock hwblock, ?_⟩
  rw [helem, map_mul, hres hv hQv hvblock, hres hw hQw hwblock]
  exact CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.reflect_mul_reflect_mem_orthDerived hR
    (by simpa using hQv) (by simpa using hQw)


section PlaneFrameFixedSpace

open CFSG.StandardType.OmNsRootGen

open scoped Classical

variable {k : ℕ} {U : Fin k → Submodule K V} {e : Fin k → ↥(orthDerived Q)}
  {E : Subgroup ↥(orthDerived Q)}

private theorem mapsTo_of_mem_frame (hF : IsPlaneFrame Q p U e E)
    {y : ↥(orthDerived Q)} (hy : y ∈ E) (j : Fin k) :
    ∀ v ∈ U j, (y : V ≃ₗ[K] V) v ∈ U j := by
  intro v hv
  obtain ⟨m, hm⟩ := hF.exists_pow_apply_eq hy j
  have hpow : ∀ m : ℕ, ∀ v ∈ U j, ((e j : V ≃ₗ[K] V) ^ m) v ∈ U j := by
    intro m
    induction m with
    | zero => intro v hv; simpa using hv
    | succ m ih =>
        intro v hv
        rw [pow_succ, LinearEquiv.mul_apply]
        exact ih _ (hF.maps_to j v hv)
  rw [hm v hv]
  exact hpow m v hv

private theorem frameProj_eq_zero_of_not_triv (hF : IsPlaneFrame Q p U e E) (hp : p.Prime)
    {y : ↥(orthDerived Q)} (hy : y ∈ E) {s : V} (hs : s ∈ ⨆ j, U j)
    (hys : (y : V ≃ₗ[K] V) s = s) {j : Fin k}
    (hj : ¬ ∀ v ∈ U j, (y : V ≃ₗ[K] V) v = v) :
    frameProj hF j s = 0 := by
  classical
  have hsum : (y : V ≃ₗ[K] V) s - s =
      ∑ i, ((y : V ≃ₗ[K] V) (frameProj hF i s) - frameProj hF i s) := by
    have h1 : s = ∑ i, frameProj hF i s := eq_sum_frameProj hF hs
    calc (y : V ≃ₗ[K] V) s - s =
          (y : V ≃ₗ[K] V) (∑ i, frameProj hF i s) - ∑ i, frameProj hF i s := by
            conv_lhs => rw [h1]
      _ = ∑ i, ((y : V ≃ₗ[K] V) (frameProj hF i s) - frameProj hF i s) := by
            rw [map_sum, Finset.sum_sub_distrib]
  have h0 : frameProj hF j
      (∑ i, ((y : V ≃ₗ[K] V) (frameProj hF i s) - frameProj hF i s)) = 0 := by
    rw [← hsum, sub_eq_zero.mpr hys, map_zero]
  rw [map_sum, Finset.sum_eq_single (s := Finset.univ) (f := fun i =>
    frameProj hF j ((y : V ≃ₗ[K] V) (frameProj hF i s) - frameProj hF i s)) j] at h0
  · have hfix : (y : V ≃ₗ[K] V) (frameProj hF j s) = frameProj hF j s := by
      rw [map_sub, frameProj_apply_left hF j
          (mapsTo_of_mem_frame hF hy j _ (frameProj_mem hF j s)),
        frameProj_apply_left hF j (frameProj_mem hF j s), sub_eq_zero] at h0
      exact h0
    rcases hF.apply_eq_or_eq_zero hp hy j with hall | hzero
    · exact absurd hall hj
    · exact hzero _ (frameProj_mem hF j s) hfix
  · intro i _ hij
    refine frameProj_apply_right hF j (mem_polarPerp_iff.mpr fun v hv => ?_)
    rw [QuadraticMap.polar_comm]
    exact hF.perp i j hij _
      (Submodule.sub_mem _ (mapsTo_of_mem_frame hF hy i _
        (frameProj_mem hF i s)) (frameProj_mem hF i s)) v hv
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem fixedSpace_le_trivPlanes (hF : IsPlaneFrame Q p U e E) (hp : p.Prime)
    {y : ↥(orthDerived Q)} (hy : y ∈ E) :
    fixedSpace (y : V ≃ₗ[K] V) ≤
      (⨆ j ∈ Finset.univ.filter (fun j => ∀ v ∈ U j, (y : V ≃ₗ[K] V) v = v), U j) ⊔
        polarPerp Q (⨆ j, U j) := by
  classical
  intro v hv
  rw [mem_fixedSpace] at hv
  let T : Finset (Fin k) :=
    Finset.univ.filter (fun j => ∀ v ∈ U j, (y : V ≃ₗ[K] V) v = v)
  have htop : v ∈ (⨆ j, U j) ⊔ polarPerp Q (⨆ j, U j) := by
    rw [hF.toIsPlaneSystem.isCompl_iSup.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.mp htop
  have hys : (y : V ≃ₗ[K] V) s = s := by
    have h1 : (y : V ≃ₗ[K] V) (s + w) = s + w := hv
    rw [map_add, hF.apply_eq_of_mem_polarPerp_iSup hy hw] at h1
    exact add_right_cancel h1
  have hz : ∀ j, j ∉ T → frameProj hF j s = 0 := by
    intro j hj
    refine frameProj_eq_zero_of_not_triv hF hp hy hs hys ?_
    intro hall
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hall⟩)
  have hsT : s ∈ ⨆ j ∈ T, U j := by
    rw [eq_sum_frameProj hF hs]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ T
    · exact Submodule.mem_iSup_of_mem i
        (Submodule.mem_iSup_of_mem hi (frameProj_mem hF i s))
    · rw [hz i hi]
      exact Submodule.zero_mem _
  exact Submodule.mem_sup.mpr ⟨s, hsT, w, hw, rfl⟩

theorem exists_two_trivPlanes (hF : IsPlaneFrame Q p U e E) (hp : p.Prime)
    {y : ↥(orthDerived Q)} (hy : y ∈ E)
    (hW : Module.finrank K (polarPerp Q (⨆ j, U j)) = 2)
    (hfix : 6 ≤ Module.finrank K (fixedSpace (y : V ≃ₗ[K] V))) :
    ∃ a b : Fin k, a ≠ b ∧ (∀ v ∈ U a, (y : V ≃ₗ[K] V) v = v) ∧
      ∀ v ∈ U b, (y : V ≃ₗ[K] V) v = v := by
  classical
  let T : Finset (Fin k) :=
    Finset.univ.filter (fun j => ∀ v ∈ U j, (y : V ≃ₗ[K] V) v = v)
  by_contra h
  have hcard : T.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    exact h ⟨a, b, hab, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩
  have hle : fixedSpace (y : V ≃ₗ[K] V) ≤
      (⨆ j ∈ T, U j) ⊔ polarPerp Q (⨆ j, U j) := by
    simpa [T] using fixedSpace_le_trivPlanes hF hp hy
  have hdisj : Disjoint (⨆ j ∈ T, U j) (polarPerp Q (⨆ j, U j)) :=
    (hF.toIsPlaneSystem.isCompl_iSup).disjoint.mono_left
      (iSup₂_le fun j _ => le_iSup U j)
  have hdimSup : Module.finrank K
      ↥((⨆ j ∈ T, U j) ⊔ polarPerp Q (⨆ j, U j)) ≤ 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (⨆ j ∈ T, U j)
      (polarPerp Q (⨆ j, U j))
    rw [disjoint_iff.1 hdisj, finrank_bot, add_zero,
      hF.toIsPlaneSystem.finrank_biSup T, hW] at h
    have hcard2 : 2 * T.card ≤ 2 := by omega
    omega
  have hle4 : Module.finrank K (fixedSpace (y : V ≃ₗ[K] V)) ≤ 4 :=
    (Submodule.finrank_mono hle).trans hdimSup
  omega

end PlaneFrameFixedSpace

section CoherentFrameSignChange

open CFSG.StandardType.OmNsRootGen

open scoped Classical

variable {k : ℕ} {U : Fin k → Submodule K V} {e : Fin k → ↥(orthDerived Q)}
  {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : K}

private theorem signChange_mem_supportedFixedDerived
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q 3 U e E u c t) {v : V} (hQv : Q v ≠ 0)
    {y : V ≃ₗ[K] V} (hyIso : OddOrderIsometry Q 3 y) (hyv : y v = v)
    {i : Fin k} (hi : ∀ w ∈ U i, y w = w) :
    (⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩ : ↥(orthDerived Q)) ∈
      (supportedFixedDerived Q y).subgroupOf (orthDerived Q) := by
  refine Subgroup.mem_subgroupOf.mpr ?_
  change signChange Q u v i ∈ supportedFixedDerived Q y
  rw [signChange]
  exact reflect_mul_reflect_mem_supportedFixedDerived hyIso
    (mem_fixedSpace.mpr (hi (u i) (hF.mem i))) (mem_fixedSpace.mpr hyv)
    (by rw [hF.quad_eq i]; exact hF.c_ne_zero) hQv

theorem four_dvd_ggAutomizer_of_supportedFixedDerived
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q 3 U e E u c t) {ℓ : ℕ}
    (hdim : Module.finrank K V = 2 * ℓ) (hkℓ : k + 1 = ℓ)
    {f f' : V} (hf : f ∈ polarPerp Q (⨆ j, U j)) (hf' : f' ∈ polarPerp Q (⨆ j, U j))
    (hQf : Q f = 0) (hQf' : Q f' = 0) (hff' : QuadraticMap.polar Q f f' = 1)
    {y : ↥(orthDerived Q)} (hyE : y ∈ E) (hy3 : orderOf y = 3)
    (hfix : 6 ≤ Module.finrank K (fixedSpace (y : V ≃ₗ[K] V))) :
    4 ∣ Nat.card (ggAutomizer
      ((supportedFixedDerived Q (y : V ≃ₗ[K] V)).subgroupOf (orthDerived Q)) E) := by
  classical
  have hW : Module.finrank K (polarPerp Q (⨆ j, U j)) = 2 :=
    finrank_polarPerp_iSup_eq_two hdim hkℓ hF.toIsPlaneFrame.toIsPlaneSystem
  obtain ⟨a, b, hab, ha, hb⟩ :=
    exists_two_trivPlanes hF.toIsPlaneFrame Nat.prime_three hyE hW hfix
  let v : V := f + f'
  have hvW : v ∈ polarPerp Q (⨆ j, U j) := by
    dsimp only [v]
    rw [mem_polarPerp_iff] at hf hf' ⊢
    intro w hw
    rw [polar_add_right, hf w hw, hf' w hw, add_zero]
  have hQv : Q v = 1 := by
    dsimp only [v]
    exact quad_add_eq_one hQf hQf' hff'
  have hQv0 : Q v ≠ 0 := by
    rw [hQv]
    exact one_ne_zero
  have hyv : (y : V ≃ₗ[K] V) v = v :=
    hF.toIsPlaneFrame.apply_eq_of_mem_polarPerp_iSup hyE hvW
  have hyIso : OddOrderIsometry Q 3 (y : V ≃ₗ[K] V) := by
    refine oddOrderIsometry_of_orthDerived_pow_eq_one hQ Nat.prime_three
      (by norm_num) ?_
    rw [← hy3]
    exact pow_orderOf_eq_one y
  have hga := signChange_mem_supportedFixedDerived hQ hF hQv0 hyIso hyv ha
  have hgb := signChange_mem_supportedFixedDerived hQ hF hQv0 hyIso hyv hb
  have hmain := four_dvd_ggAutomizer_signChange_pair hQ hF hvW hQv0 rfl hab
    ((supportedFixedDerived Q (y : V ≃ₗ[K] V)).subgroupOf (orthDerived Q)) hga hgb
  simpa using hmain

end CoherentFrameSignChange

end CFSG.StandardType

end

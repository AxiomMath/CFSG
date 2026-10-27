module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOmegaBigCocycle

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Quasithin.JonesParshall

theorem w183_decomp {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {w : V} (hw : polar Q w P.e = 0) :
    w = polar Q w P.f • P.e + P.proj w := by
  conv_lhs => rw [P.eq_add_proj w]
  rw [hw, zero_smul, add_zero]

theorem w183_comb_polar {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (s : K) {k : V} (hk : k ∈ P.perp) :
    polar Q (s • P.e + k) P.f = s := by
  rw [polar_add_left, polar_smul_left_eq, P.polar_ef, polar_comm Q k P.f,
    (HypPair.mem_perp.mp hk).2]
  simp

theorem w183_comb_proj {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (s : K) {k : V} (hk : k ∈ P.perp) :
    P.proj (s • P.e + k) = k := by
  have h : polar Q (s • P.e + k) P.e = 0 := by
    rw [polar_add_left, polar_smul_left_eq, P.polar_ee, polar_comm Q k P.e,
      (HypPair.mem_perp.mp hk).1]
    simp
  rw [HypPair.proj, h, w183_comb_polar P s hk]
  simp

theorem w183_root_xperp {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {z : V → V}
    (hadd : ∀ u v, u ∈ P.perp → v ∈ P.perp → z (u + v) = z u + eichler Q P.e u (z v)) :
    ∀ u ∈ P.perp, polar Q (z u) P.e = 0 := by
  have hz0 : z 0 = 0 := by
    have h := hadd 0 0 P.perp.zero_mem P.perp.zero_mem
    rw [add_zero, eichler_zero_right] at h
    simpa using h
  intro u hu
  by_cases hu0 : u = 0
  · rw [hu0, hz0, polar_zero_left]
  have h1 := hadd u u hu hu
  rw [w183_self_add_eq_zero (K := K) u, hz0, eq_comm] at h1
  obtain ⟨hu_e, hu_f⟩ := HypPair.mem_perp.mp hu
  rw [eichler_apply P.Q_e hu_e] at h1
  set w := z u with hw
  have h2 : polar Q w P.e • u - (polar Q w u + Q u * polar Q w P.e) • P.e = 0 := by
    have h3 := w183_self_add_eq_zero (K := K) w
    calc _ = w + (w + polar Q w P.e • u - (polar Q w u + Q u * polar Q w P.e) • P.e) - (w + w) := by
            abel
      _ = 0 := by rw [h1, h3, sub_zero]
  have h5 : polar Q w u + Q u * polar Q w P.e = 0 := by
    have := congrArg (fun y => polar Q y P.f) h2
    simp only [polar_sub_left, polar_smul_left_eq, polar_zero_left, polar_comm Q u P.f, hu_f,
      P.polar_ef, mul_zero, mul_one, zero_sub, neg_eq_zero] at this
    exact this
  rw [h5, zero_smul, sub_zero] at h2
  exact (smul_eq_zero.mp h2).resolve_right hu0

theorem w183_root_alg {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {l : K} (hl0 : l ≠ 0) (hl1 : l ≠ 1) {z : V → V}
    (hx : ∀ u ∈ P.perp, polar Q (z u) P.e = 0)
    (hadd : ∀ u v, u ∈ P.perp → v ∈ P.perp → z (u + v) = z u + eichler Q P.e u (z v))
    (hconj : ∀ c : K, c ≠ 0 → ∃ d : V ≃ₗ[K] V, d P.e = c • P.e ∧ (∀ w ∈ P.perp, d w = w) ∧
      ∀ u ∈ P.perp, z (c • u) = d (z u)) :
    ∃ a : V → K, (∀ u ∈ P.perp, z u = a u • P.e) ∧
      (∀ u v, u ∈ P.perp → v ∈ P.perp → a (u + v) = a u + a v) ∧
      ∀ (t : K) (u : V), u ∈ P.perp → a (t • u) = t * a u := by
  obtain ⟨a, ha⟩ : ∃ a : V → K, ∀ u, a u = polar Q (z u) P.f := ⟨_, fun _ => rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : V → V, ∀ u, h u = P.proj (z u) := ⟨_, fun _ => rfl⟩
  have hhU : ∀ u, h u ∈ P.perp := fun u => by rw [hh]; exact P.proj_mem_perp _
  have hdec : ∀ u ∈ P.perp, z u = a u • P.e + h u := fun u hu => by
    rw [ha, hh]; exact w183_decomp P (hx u hu)
  have huniq : ∀ (s s' : K) (k k' : V), k ∈ P.perp → k' ∈ P.perp →
      s • P.e + k = s' • P.e + k' → s = s' ∧ k = k' := by
    intro s s' k k' hk hk' hkk
    refine ⟨?_, ?_⟩
    · have := congrArg (fun w => polar Q w P.f) hkk
      simpa [w183_comb_polar P s hk, w183_comb_polar P s' hk'] using this
    · have := congrArg P.proj hkk
      rwa [w183_comb_proj P s hk, w183_comb_proj P s' hk'] at this
  have htor : ∀ c : K, c ≠ 0 → ∀ u ∈ P.perp, a (c • u) = c * a u ∧ h (c • u) = h u := by
    intro c hc u hu
    obtain ⟨d, hde, hdU, hz⟩ := hconj c hc
    have h1 : z (c • u) = (c * a u) • P.e + h u := by
      rw [hz u hu]
      conv_lhs => rw [hdec u hu]
      rw [map_add, map_smul, hde, hdU _ (hhU u), smul_smul, mul_comm]
    have h2 := hdec (c • u) (P.perp.smul_mem c hu)
    rw [h1] at h2
    obtain ⟨e1, e2⟩ := huniq _ _ _ _ (hhU _) (hhU _) h2
    exact ⟨e1.symm, e2.symm⟩
  have hadd' : ∀ u v, u ∈ P.perp → v ∈ P.perp →
      a (u + v) = a u + a v - polar Q (h v) u ∧ h (u + v) = h u + h v := by
    intro u v hu hv
    have hu' := (HypPair.mem_perp.mp hu).1
    have h1 : eichler Q P.e u (z v) = z v - polar Q (z v) u • P.e := by
      rw [eichler_apply P.Q_e hu', hx v hv]
      simp
    have h2 : polar Q (z v) u = polar Q (h v) u := by
      rw [hdec v hv, polar_add_left, polar_smul_left_eq, hu']
      simp
    have h3 : z (u + v) = (a u + a v - polar Q (h v) u) • P.e + (h u + h v) := by
      rw [hadd u v hu hv, h1, h2]
      conv_lhs => rw [hdec u hu, hdec v hv]
      module
    have h4 := hdec (u + v) (P.perp.add_mem hu hv)
    rw [h3] at h4
    obtain ⟨e1, e2⟩ := huniq _ _ _ _ (P.perp.add_mem (hhU u) (hhU v)) (hhU _) h4
    exact ⟨e1.symm, e2.symm⟩
  have hl2 : l + 1 ≠ 0 := fun h0 => hl1 (by
    have := eq_neg_of_add_eq_zero_left h0
    rwa [CharTwo.neg_eq, ] at this)
  have hzero : ∀ u ∈ P.perp, h u = 0 := by
    intro w hw
    set u := (l + 1)⁻¹ • w with hu
    have huP : u ∈ P.perp := P.perp.smul_mem _ hw
    have hwu : w = (l + 1) • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hl2, one_smul]
    have hlu : h (l • u) = h u := (htor l hl0 u huP).2
    have := (hadd' (l • u) u (P.perp.smul_mem l huP) huP).2
    rw [hwu, add_smul, one_smul, this, hlu]
    exact w183_self_add_eq_zero (K := K) _
  have ha0 : ∀ u ∈ P.perp, z u = a u • P.e := fun u hu => by
    rw [hdec u hu, hzero u hu, add_zero]
  refine ⟨a, ha0, fun u v hu hv => ?_, fun t u hu => ?_⟩
  · rw [(hadd' u v hu hv).1, hzero v hv, polar_zero_left]
    simp
  · by_cases ht : t = 0
    · subst ht
      have h00 := (hadd' 0 0 P.perp.zero_mem P.perp.zero_mem).1
      rw [add_zero, hzero 0 P.perp.zero_mem, polar_zero_left, sub_zero] at h00
      rw [zero_smul, zero_mul]
      exact left_eq_add.mp h00
    · exact (htor t ht u hu).1

theorem w183_root_value {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {l : K} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    {f : ↥(elementaryGroup Q) → V} (hf : f ∈ Z1A (w183ElemAct Q))
    (hd : ∀ c : K, c ≠ 0 → ∃ d : ↥(elementaryGroup Q), (d : V ≃ₗ[K] V) P.e = c • P.e ∧
      (∀ w ∈ P.perp, (d : V ≃ₗ[K] V) w = w) ∧ f d = 0) :
    ∃ a : V → K, (∀ u ∈ P.perp, f (w183El Q P.e u) = a u • P.e) ∧
      (∀ u v, u ∈ P.perp → v ∈ P.perp → a (u + v) = a u + a v) ∧
      ∀ (t : K) (u : V), u ∈ P.perp → a (t • u) = t * a u := by
  have hadd := fun u v (hu : u ∈ P.perp) (hv : v ∈ P.perp) => w183_root_add hf P hu hv
  refine w183_root_alg P hl0 hl1 (z := fun u => f (w183El Q P.e u)) (w183_root_xperp P hadd)
    hadd fun c hc => ?_
  obtain ⟨d, hdx, hdU, hd0⟩ := hd c hc
  exact ⟨d, hdx, hdU, fun u hu => w183_root_conj hf P hd0 hdx hdU hu⟩

theorem w183_root_opposite {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {f : ↥(elementaryGroup Q) → V} (hf : f ∈ Z1A (w183ElemAct Q))
    (P : HypPair Q) {u : V} (hu : u ∈ P.perp) (hQu : Q u = 0) (hu0 : u ≠ 0) {a c : K}
    (hT : f (w183El Q P.e u) = a • P.e) (hR : f (w183El Q P.f u) = c • P.f) : a = c := by
  obtain ⟨hu_e, hu_f⟩ := HypPair.mem_perp.mp hu
  have hTu : eichler Q P.e u u = u := by
    rw [eichler_apply P.Q_e hu_e, polar_self_eq_zero hQu, polar_comm Q u P.e, hu_e]
    simp
  have hTf : eichler Q P.e u P.f = P.f + u := by
    rw [eichler_apply P.Q_e hu_e, P.polar_fe, hu_f]
    simp [hQu]
  have hRe : eichler Q P.f u P.e = P.e + u := by
    rw [eichler_apply P.Q_f hu_f, P.polar_ef, hu_e]
    simp [hQu]
  have hEq : eichler Q (P.f + u) u = eichler Q P.f u := LinearEquiv.ext fun z => by
    have h1 : Q (P.f + u) = 0 := by
      rw [QuadraticMap.map_add Q, P.Q_f, hQu, hu_f]; simp
    have h2 : polar Q (P.f + u) u = 0 := by
      rw [polar_add_left, hu_f, polar_self_eq_zero hQu]; simp
    rw [eichler_apply h1 h2, eichler_apply P.Q_f hu_f, polar_add_right, hQu]
    simp only [zero_mul, add_zero, smul_add]
    module
  have hcomm : eichler Q P.e u * eichler Q P.f u = eichler Q P.f u * eichler Q P.e u := by
    have h := eichler_conj (eichler_mem_orthogonalGroup Q P.e u) P.f u
    rw [hTu, hTf, hEq] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hcommE : w183El Q P.e u * w183El Q P.f u = w183El Q P.f u * w183El Q P.e u :=
    Subtype.ext hcomm
  have h1 := mem_Z1A.mp hf (w183El Q P.e u) (w183El Q P.f u)
  have h2 := mem_Z1A.mp hf (w183El Q P.f u) (w183El Q P.e u)
  rw [hcommE, h2, hT, hR] at h1
  have h3 : (c • P.f) + (w183ElemAct Q (w183El Q P.f u)) (a • P.e) =
      a • P.e + (w183ElemAct Q (w183El Q P.e u)) (c • P.f) := h1
  simp only [w183ElemAct_apply, w183El_coe, map_smul, hRe, hTf] at h3
  have h4 : (c - a) • u = 0 := by
    have : (a • P.e + c • (P.f + u)) - (c • P.f + a • (P.e + u)) = 0 := by rw [h3]; simp
    rw [sub_smul]
    calc c • u - a • u = (a • P.e + c • (P.f + u)) - (c • P.f + a • (P.e + u)) := by
          simp only [smul_add]; abel
      _ = 0 := this
  exact (sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hu0)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

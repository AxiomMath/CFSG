module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import Mathlib.Algebra.Field.ZMod
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenTrans
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenScalars
import CFSG.RankThree.Classical.OddQuadraticFrame
import CFSG.ClassicalGroups.Orthogonal.Restrict

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_finrank_perp_add_two [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (_hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) :
    Module.finrank (ZMod p) P.perp + 2 = Module.finrank (ZMod p) U := by
  let φ : U →ₗ[ZMod p] (ZMod p × ZMod p) := (polarBilin Q P.e).prod (polarBilin Q P.f)
  have hker : LinearMap.ker φ = P.perp := by
    ext x
    rw [LinearMap.mem_ker, HypPair.mem_perp]
    change ((polarBilin Q P.e) x, (polarBilin Q P.f) x) = (0 : ZMod p × ZMod p) ↔
      polar Q P.e x = 0 ∧ polar Q P.f x = 0
    simp only [Prod.mk_eq_zero, polarBilin_apply_apply]
  have hsurj : Function.Surjective φ := by
    intro y
    refine ⟨y.2 • P.e + y.1 • P.f, ?_⟩
    change ((polarBilin Q P.e) (y.2 • P.e + y.1 • P.f),
      (polarBilin Q P.f) (y.2 • P.e + y.1 • P.f)) = y
    simp only [polarBilin_apply_apply, polar_add_right, polar_smul_right_eq, P.polar_ee, P.polar_ef,
      P.polar_fe, P.polar_ff, mul_zero, mul_one, add_zero, zero_add]
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h2 : Module.finrank (ZMod p) (ZMod p × ZMod p) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, finrank_top, hker, h2] at h
  omega

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_perp_ker_proj (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    {A : Submodule (ZMod p) U} {a : U} (ha : a ∈ A) (hQa : Q a ≠ 0) :
    ∀ x ∈ A, x - (polar Q a x / polar Q a a) • a ∈ A ⊓ LinearMap.ker (polarBilin Q a) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have haa : polar Q a a ≠ 0 := by
    rw [polar_self_eq_two_mul]
    exact mul_ne_zero h2 hQa
  intro x hx
  refine ⟨A.sub_mem hx (A.smul_mem _ ha), ?_⟩
  show polar Q a (x - (polar Q a x / polar Q a a) • a) = 0
  rw [polar_sub_right, polar_smul_right_eq, div_mul_cancel₀ _ haa, sub_self]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_perp_ker_decomp (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    {A : Submodule (ZMod p) U} {a : U} (ha : a ∈ A) (hQa : Q a ≠ 0) :
    A = Submodule.span (ZMod p) {a} ⊔ (A ⊓ LinearMap.ker (polarBilin Q a)) := by
  have hproj := ocg_perp_ker_proj hp ha hQa
  apply le_antisymm
  · intro x hx
    have hx' := hproj x hx
    rw [show x = (polar Q a x / polar Q a a) • a + (x - (polar Q a x / polar Q a a) • a)
      from by abel]
    exact Submodule.add_mem_sup
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton a))) hx'
  · refine sup_le ?_ inf_le_left
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ha)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_perp_ker_disj (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    {A : Submodule (ZMod p) U} {a : U} (hQa : Q a ≠ 0) :
    Submodule.span (ZMod p) {a} ⊓ (A ⊓ LinearMap.ker (polarBilin Q a)) = ⊥ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have haa : polar Q a a ≠ 0 := by
    rw [polar_self_eq_two_mul]
    exact mul_ne_zero h2 hQa
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf, Submodule.mem_span_singleton] at hx
  obtain ⟨⟨s, rfl⟩, hxW⟩ := hx
  have hp0 : polar Q a (s • a) = 0 := by
    simpa [LinearMap.mem_ker, polarBilin_apply_apply] using hxW.2
  rw [polar_smul_right_eq] at hp0
  have hs : s = 0 := by
    rcases mul_eq_zero.mp hp0 with h | h
    · exact h
    · exact absurd h haa
  rw [hs, zero_smul]
  exact Submodule.zero_mem _

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_perp_ker_fin [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} {A : Submodule (ZMod p) U} {a : U} (ha : a ∈ A)
    (hQa : Q a ≠ 0) :
    Module.finrank (ZMod p) ↥(A ⊓ LinearMap.ker (polarBilin Q a)) + 1 =
      Module.finrank (ZMod p) A := by
  have hdecomp := ocg_perp_ker_decomp hp ha hQa
  have hdisj : Submodule.span (ZMod p) {a} ⊓ (A ⊓ LinearMap.ker (polarBilin Q a)) = ⊥ :=
    ocg_perp_ker_disj hp hQa
  have ha_ne : a ≠ 0 := fun h => hQa (by rw [h, QuadraticMap.map_zero])
  have hspanfin : Module.finrank (ZMod p) (Submodule.span (ZMod p) {a}) = 1 :=
    finrank_span_singleton ha_ne
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod p) {a})
    (A ⊓ LinearMap.ker (polarBilin Q a))
  rw [← hdecomp, hdisj, hspanfin, finrank_bot, add_zero] at h
  omega

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_perp_ker_nd [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} {A : Submodule (ZMod p) U} (hA : PolarNondegOn Q A)
    {a : U} (ha : a ∈ A) (hQa : Q a ≠ 0) :
    PolarNondegOn Q (A ⊓ LinearMap.ker (polarBilin Q a)) := by
  have hproj := ocg_perp_ker_proj hp ha hQa
  intro x hxW hx
  apply hA x hxW.1
  intro z hzA
  have hz' : z - (polar Q a z / polar Q a a) • a ∈ A ⊓ LinearMap.ker (polarBilin Q a) :=
    hproj z hzA
  have hza : polar Q x a = 0 := by
    have h1 : polar Q a x = 0 := by
      simpa [LinearMap.mem_ker, polarBilin_apply_apply] using hxW.2
    rw [polar_comm]
    exact h1
  rw [show z = (z - (polar Q a z / polar Q a a) • a) + (polar Q a z / polar Q a a) • a
    from by abel, polar_add_right, hx _ hz', polar_smul_right_eq, hza, mul_zero, add_zero]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_perp_ker [Module.Finite (ZMod p) U] (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    {A : Submodule (ZMod p) U} (hA : PolarNondegOn Q A) {a : U} (ha : a ∈ A) (hQa : Q a ≠ 0) :
    PolarNondegOn Q (A ⊓ LinearMap.ker (polarBilin Q a)) ∧
      A = Submodule.span (ZMod p) {a} ⊔ (A ⊓ LinearMap.ker (polarBilin Q a)) ∧
      Module.finrank (ZMod p) ↥(A ⊓ LinearMap.ker (polarBilin Q a)) + 1 =
        Module.finrank (ZMod p) A :=
  ⟨ocg_perp_ker_nd hp hA ha hQa, ocg_perp_ker_decomp hp ha hQa, ocg_perp_ker_fin hp ha hQa⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_quad_hyp {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) (s t : ZMod p) :
    Q (s • P.e + t • P.f) = s * t := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, P.Q_e, P.Q_f,
    polar_smul_left_eq, polar_smul_right_eq, P.polar_ef]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_polar_hyp {Q : QuadraticForm (ZMod p) U} (P : HypPair Q)
    (s t s' t' : ZMod p) :
    polar Q (s • P.e + t • P.f) (s' • P.e + t' • P.f) = s * t' + t * s' := by
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, P.polar_ee,
    P.polar_ef, P.polar_fe, P.polar_ff]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_sp_build (hp3 : p ≠ 3)
    {Q : QuadraticForm (ZMod p) U} {W : Submodule (ZMod p) U} {m : ℕ}
    (_hm : Module.finrank (ZMod p) W = m) (h2 : 2 ≤ m) {d : ZMod p} (hd : d ≠ 0)
    (v : Module.Basis (Fin m) (ZMod p) W)
    (hvorth : ∀ i j, i ≠ j → polar (Q.restrict W) (v i) (v j) = 0)
    (hvnorm : ∀ i : Fin m, (i : ℕ) + 1 < m → (Q.restrict W) (v i) = d)
    (hvlast : (Q.restrict W) (v ⟨m - 1, by omega⟩) ≠ 0) :
    ∃ (w' : Fin m → W) (zero last : Fin m) (s t : ZMod p),
      zero ≠ last ∧ t ≠ 0 ∧ (last : ℕ) = m - 1 ∧ (∀ i, i ≠ last → w' i = v i) ∧
        w' last = s • v zero + t • v last ∧ (Q.restrict W) (w' last) = d := by
  let zero : Fin m := ⟨0, by omega⟩
  let last : Fin m := ⟨m - 1, by omega⟩
  have hzero_ne_last : zero ≠ last := by
    simp [zero, last]
    omega
  have hv0 : (Q.restrict W) (v zero) = d := hvnorm zero (by simp [zero]; omega)
  have horth0 : polar (Q.restrict W) (v zero) (v last) = 0 := hvorth zero last hzero_ne_last
  set k : ZMod p := (Q.restrict W) (v last) / d with hk
  have hkne : k ≠ 0 := by
    rw [hk]
    exact div_ne_zero hvlast hd
  obtain ⟨s, t, ht, hst⟩ := exists_conic_point_snd_ne_zero hp3 hkne
  have hQvl : (Q.restrict W) (v last) = k * d := by
    rw [hk, div_mul_cancel₀ _ hd]
  let w' : Fin m → W := Function.update (fun i => v i) last (s • v zero + t • v last)
  refine ⟨w', zero, last, s, t, hzero_ne_last, ht, rfl, ?_, ?_, ?_⟩
  · intro i hi
    exact Function.update_of_ne hi _ (fun i => v i)
  · exact Function.update_self last _ (fun i => v i)
  · have hw' : w' last = s • v zero + t • v last := Function.update_self last _ (fun i => v i)
    rw [hw']
    rw [CFSG.RankThree.Classical.quad_smul_add_smul (Q.restrict W) horth0 s t, hv0, hQvl]
    calc s ^ 2 * d + t ^ 2 * (k * d) = d * (s ^ 2 + k * t ^ 2) := by ring
      _ = d := by rw [hst, mul_one]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_sp_span
    {W : Submodule (ZMod p) U} {m : ℕ} (v : Module.Basis (Fin m) (ZMod p) W)
    {w' : Fin m → W} {zero last : Fin m} (hzero_ne_last : zero ≠ last)
    (w'_of_ne : ∀ i, i ≠ last → w' i = v i) {s t : ZMod p} (ht : t ≠ 0)
    (hlast : w' last = s • v zero + t • v last) :
    W ≤ Submodule.span (ZMod p) (Set.range fun i => (w' i : U)) := by
  have htop : Submodule.span (ZMod p) (Set.range fun i => ((v i : W) : U)) = W := by
    rw [← Submodule.span_range_subtype_eq_top_iff W (s := fun i => (v i : U))
      (fun i => (v i).2)]
    simp
  have hle : Submodule.span (ZMod p) (Set.range fun i => ((v i : W) : U)) ≤
      Submodule.span (ZMod p) (Set.range fun i => (w' i : U)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    change ((v i : W) : U) ∈ Submodule.span (ZMod p) (Set.range fun i => (w' i : U))
    by_cases hi : i = last
    · rw [hi]
      have hy0 : ((w' zero : W) : U) = ((v zero : W) : U) := by
        rw [w'_of_ne zero hzero_ne_last]
      have hlast' : ((w' last : W) : U) =
          s • ((v zero : W) : U) + t • ((v last : W) : U) := by
        rw [hlast]
        rfl
      have hrepr : ((v last : W) : U) =
          t⁻¹ • (((w' last : W) : U) - s • ((w' zero : W) : U)) := by
        rw [hlast', hy0, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [hrepr]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨last, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨zero, rfl⟩)))
    · have : ((v i : W) : U) = ((w' i : W) : U) := by rw [w'_of_ne i hi]
      rw [this]
      exact Submodule.subset_span ⟨i, rfl⟩
  exact htop.ge.trans hle

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem exists_spanning_map_eq_of_polarNondegOn (hp : p ≠ 2)
    (hp3 : p ≠ 3) {Q : QuadraticForm (ZMod p) U} {W : Submodule (ZMod p) U}
    (hW : PolarNondegOn Q W) {m : ℕ} (hm : Module.finrank (ZMod p) W = m) (h2 : 2 ≤ m)
    {d : ZMod p} (hd : d ≠ 0) :
    ∃ y : Fin m → U, (∀ i, y i ∈ W ∧ Q (y i) = d) ∧ W ≤ Submodule.span (ZMod p) (Set.range y) := by
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp
  have hfin : FiniteDimensional (ZMod p) W :=
    Module.finite_of_finrank_pos (by omega)
  obtain ⟨v, hvorth, hvnorm, hvlast⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq (K := ZMod p) (V := W)
      hodd (d := m) hm h2 (Q.restrict W) (nondegenerate_polarBilin_restrict hW) hd
  obtain ⟨w', zero, last, s, t, hzero_ne_last, ht, hlast_eq, w'_of_ne, hlast, hnew⟩ :=
    ocg_sp_build hp3 hm h2 hd v hvorth hvnorm hvlast
  let y : Fin m → U := fun i => (w' i : U)
  refine ⟨y, ?_, ocg_sp_span v hzero_ne_last w'_of_ne ht hlast⟩
  intro i
  refine ⟨(w' i).2, ?_⟩
  by_cases hi : i = last
  · rw [hi]
    show Q ((w' last : W) : U) = d
    rw [hlast] at hnew ⊢
    exact hnew
  · show Q ((w' i : W) : U) = d
    rw [w'_of_ne i hi]
    exact hvnorm i (by
      have := i.isLt
      have hne : (i : ℕ) ≠ m - 1 := fun h => hi (Fin.ext (h.trans hlast_eq.symm))
      omega)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_cf4_polar_facts (hp5 : p = 5) {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    (P : HypPair Q) :
    polar Q (P.e + c • P.f) ((2 : ZMod p) • P.e + (3 * c) • P.f) = 0 ∧
      polar Q ((2 : ZMod p) • P.e + (3 * c) • P.f) (P.e + c • P.f) = 0 ∧
      (∀ w ∈ P.perp, polar Q (P.e + c • P.f) w = 0) ∧
      (∀ w ∈ P.perp, polar Q ((2 : ZMod p) • P.e + (3 * c) • P.f) w = 0) ∧
      (∀ w ∈ P.perp, polar Q w (P.e + c • P.f) = 0) ∧
      (∀ w ∈ P.perp, polar Q w ((2 : ZMod p) • P.e + (3 * c) • P.f) = 0) := by
  have h5' : (5 : ZMod p) = 0 := by
    have h : (5 : ZMod p) = (p : ZMod p) := congrArg (fun n : ℕ => (n : ZMod p)) hp5.symm
    rw [h, ZMod.natCast_self]
  have h01 : polar Q (P.e + c • P.f) ((2 : ZMod p) • P.e + (3 * c) • P.f) = 0 := by
    have h := ocg_polar_hyp (Q := Q) P 1 c 2 (3 * c)
    simpa only [one_smul, show (1 : ZMod p) * (3 * c) + c * 2 = 0 by
      rw [show (1 : ZMod p) * (3 * c) + c * 2 = 5 * c by ring, h5', zero_mul]] using h
  have h10 : polar Q ((2 : ZMod p) • P.e + (3 * c) • P.f) (P.e + c • P.f) = 0 := by
    have h := ocg_polar_hyp (Q := Q) P 2 (3 * c) 1 c
    simpa only [one_smul, show (2 : ZMod p) * c + (3 * c) * 1 = 0 by
      rw [show (2 : ZMod p) * c + (3 * c) * 1 = 5 * c by ring, h5', zero_mul]] using h
  have h0perp : ∀ w ∈ P.perp, polar Q (P.e + c • P.f) w = 0 := by
    intro w hw
    have h1 := (HypPair.mem_perp.mp hw).1
    have h2 := (HypPair.mem_perp.mp hw).2
    rw [polar_add_left, polar_smul_left_eq, h1, h2, mul_zero, add_zero]
  have h1perp : ∀ w ∈ P.perp, polar Q ((2 : ZMod p) • P.e + (3 * c) • P.f) w = 0 := by
    intro w hw
    have h1 := (HypPair.mem_perp.mp hw).1
    have h2 := (HypPair.mem_perp.mp hw).2
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h1, h2, mul_zero, mul_zero,
      add_zero]
  have h0perp' : ∀ w ∈ P.perp, polar Q w (P.e + c • P.f) = 0 := by
    intro w hw
    have h1 := (HypPair.mem_perp.mp hw).1
    have h2 := (HypPair.mem_perp.mp hw).2
    rw [polar_add_right, polar_smul_right_eq, polar_comm Q w P.e, polar_comm Q w P.f, h1, h2,
      mul_zero, add_zero]
  have h1perp' : ∀ w ∈ P.perp, polar Q w ((2 : ZMod p) • P.e + (3 * c) • P.f) = 0 := by
    intro w hw
    have h1 := (HypPair.mem_perp.mp hw).1
    have h2 := (HypPair.mem_perp.mp hw).2
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_comm Q w P.e,
      polar_comm Q w P.f, h1, h2, mul_zero, mul_zero, add_zero]
  exact ⟨h01, h10, h0perp, h1perp, h0perp', h1perp'⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_cf4_four_orth {Q : QuadraticForm (ZMod p) U} {c : ZMod p} (P : HypPair Q)
    {b0 b1 : U} (r : ZMod p) (hb0mem : b0 ∈ P.perp) (hb1mem : b1 ∈ P.perp)
    (hb01 : polar Q b0 b1 = 0)
    (h01 : polar Q (P.e + c • P.f) ((2 : ZMod p) • P.e + (3 * c) • P.f) = 0)
    (h10 : polar Q ((2 : ZMod p) • P.e + (3 * c) • P.f) (P.e + c • P.f) = 0)
    (h0perp : ∀ w ∈ P.perp, polar Q (P.e + c • P.f) w = 0)
    (h1perp : ∀ w ∈ P.perp, polar Q ((2 : ZMod p) • P.e + (3 * c) • P.f) w = 0)
    (h0perp' : ∀ w ∈ P.perp, polar Q w (P.e + c • P.f) = 0)
    (h1perp' : ∀ w ∈ P.perp, polar Q w ((2 : ZMod p) • P.e + (3 * c) • P.f) = 0) :
    ∀ i j, i ≠ j →
      polar Q (![P.e + c • P.f, (2 : ZMod p) • P.e + (3 * c) • P.f, b0, r⁻¹ • b1] i)
        (![P.e + c • P.f, (2 : ZMod p) • P.e + (3 * c) • P.f, b0, r⁻¹ • b1] j) = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · change polar Q (P.e + c • P.f) (P.e + c • P.f) = 0; exact absurd rfl hij
  · change polar Q (P.e + c • P.f) ((2 : ZMod p) • P.e + (3 * c) • P.f) = 0; exact h01
  · change polar Q (P.e + c • P.f) b0 = 0; exact h0perp b0 hb0mem
  · change polar Q (P.e + c • P.f) (r⁻¹ • b1) = 0
    rw [polar_smul_right_eq, h0perp b1 hb1mem, mul_zero]
  · change polar Q ((2 : ZMod p) • P.e + (3 * c) • P.f) (P.e + c • P.f) = 0; exact h10
  · change polar Q ((2 : ZMod p) • P.e + (3 * c) • P.f)
        ((2 : ZMod p) • P.e + (3 * c) • P.f) = 0
    exact absurd rfl hij
  · change polar Q ((2 : ZMod p) • P.e + (3 * c) • P.f) b0 = 0; exact h1perp b0 hb0mem
  · change polar Q ((2 : ZMod p) • P.e + (3 * c) • P.f) (r⁻¹ • b1) = 0
    rw [polar_smul_right_eq, h1perp b1 hb1mem, mul_zero]
  · change polar Q b0 (P.e + c • P.f) = 0; exact h0perp' b0 hb0mem
  · change polar Q b0 ((2 : ZMod p) • P.e + (3 * c) • P.f) = 0; exact h1perp' b0 hb0mem
  · change polar Q b0 b0 = 0; exact absurd rfl hij
  · change polar Q b0 (r⁻¹ • b1) = 0; rw [polar_smul_right_eq, hb01, mul_zero]
  · change polar Q (r⁻¹ • b1) (P.e + c • P.f) = 0
    rw [polar_smul_left_eq, h0perp' b1 hb1mem, mul_zero]
  · change polar Q (r⁻¹ • b1) ((2 : ZMod p) • P.e + (3 * c) • P.f) = 0
    rw [polar_smul_left_eq, h1perp' b1 hb1mem, mul_zero]
  · change polar Q (r⁻¹ • b1) b0 = 0
    rw [polar_smul_left_eq, polar_comm, hb01, mul_zero]
  · change polar Q (r⁻¹ • b1) (r⁻¹ • b1) = 0; exact absurd rfl hij

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_cf4_four_norm {Q : QuadraticForm (ZMod p) U} {c : ZMod p} (P : HypPair Q)
    {b0 b1 : U} (r : ZMod p) (hr0 : r ≠ 0) (hr : Q b1 / c = r * r) (h6' : (6 : ZMod p) = 1)
    (hb0 : Q b0 = c) (hb1k : Q b1 = (Q b1 / c) * c) :
    ∀ i, Q (![P.e + c • P.f, (2 : ZMod p) • P.e + (3 * c) • P.f, b0, r⁻¹ • b1] i) = c := by
  intro i
  fin_cases i
  · change Q (P.e + c • P.f) = c
    have h := ocg_quad_hyp (Q := Q) P 1 c
    simpa using h
  · change Q ((2 : ZMod p) • P.e + (3 * c) • P.f) = c
    have h := ocg_quad_hyp (Q := Q) P 2 (3 * c)
    rw [show (2 : ZMod p) * (3 * c) = 6 * c by ring, h6', one_mul] at h
    exact h
  · change Q b0 = c; exact hb0
  · change Q (r⁻¹ • b1) = c
    rw [map_smul_eq_sq, hb1k, hr]
    field_simp [hr0]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_cf4_orth [Module.Finite (ZMod p) U] (hp5 : p = 5)
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    (hc : c ≠ 0) (P : HypPair Q) {b0 b1 : U} (r : ZMod p) (hr0 : r ≠ 0)
    (hr : Q b1 / c = r * r) (hb0mem : b0 ∈ P.perp) (hb1mem : b1 ∈ P.perp) (hb0 : Q b0 = c)
    (hb1k : Q b1 = (Q b1 / c) * c) (hb01 : polar Q b0 b1 = 0) (h2 : (2 : ZMod p) ≠ 0)
    (h4 : Module.finrank (ZMod p) U = 4) :
    ∃ b : Fin 4 → U, (∀ i j, i ≠ j → polar Q (b i) (b j) = 0) ∧ (∀ i, Q (b i) = c) ∧
      ⊤ ≤ Submodule.span (ZMod p) (Set.range b) := by
  have h6' : (6 : ZMod p) = 1 := by
    have h5' : (5 : ZMod p) = 0 := by
      have h : (5 : ZMod p) = (p : ZMod p) := congrArg (fun n : ℕ => (n : ZMod p)) hp5.symm
      rw [h, ZMod.natCast_self]
    have h : (6 : ZMod p) = 1 + 5 := by norm_num
    rw [h, h5', add_zero]
  obtain ⟨h01, h10, h0perp, h1perp, h0perp', h1perp'⟩ := ocg_cf4_polar_facts hp5 P
  have horth := ocg_cf4_four_orth P r hb0mem hb1mem hb01 h01 h10 h0perp h1perp h0perp' h1perp'
  have hnorm := ocg_cf4_four_norm P r hr0 hr h6' hb0 hb1k
  refine ⟨_, horth, hnorm, ?_⟩
  have hli := (CFSG.RankThree.Classical.nondegenerate_restrict_span h2 Q horth
    (fun i => by rw [hnorm i]; exact hc)).1
  exact (hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, h4])).ge

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_cf4_conic (hp : p ≠ 2) (hp3 : p ≠ 3) {Q : QuadraticForm (ZMod p) U}
    {c : ZMod p} (hc : c ≠ 0) (P : HypPair Q) {k : ZMod p} (hkne : k ≠ 0)
    (hconic : p = 5 → ¬ IsSquare k) {b0 b1 : U} (hb0mem : b0 ∈ P.perp) (hb1mem : b1 ∈ P.perp)
    (hb0 : Q b0 = c) (hb1k : Q b1 = k * c) (hb01 : polar Q b0 b1 = 0)
    (h2 : (2 : ZMod p) ≠ 0) (vb : Module.Basis (Fin 2) (ZMod p) P.perp)
    (hb1 : b1 = (vb 1 : U)) (hb0v : b0 = (vb 0 : U)) :
    ∃ a : Fin 2 → U, (∀ i, a i ∈ P.perp ∧ Q (a i) = c) ∧ polar Q (a 0) (a 1) ≠ 0 ∧
      P.perp ≤ Submodule.span (ZMod p) (Set.range a) := by
  obtain ⟨s, t, hs, ht, hst⟩ := exists_conic_point_ne_zero hp hp3 hkne hconic
  let a : Fin 2 → U := ![b0, s • b0 + t • b1]
  refine ⟨a, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨hb0mem, hb0⟩
    · refine ⟨P.perp.add_mem (P.perp.smul_mem _ hb0mem) (P.perp.smul_mem _ hb1mem), ?_⟩
      change Q (s • b0 + t • b1) = c
      rw [CFSG.RankThree.Classical.quad_smul_add_smul Q hb01 s t, hb0, hb1k]
      calc s ^ 2 * c + t ^ 2 * (k * c) = c * (s ^ 2 + k * t ^ 2) := by ring
        _ = c := by rw [hst, mul_one]
  · change polar Q b0 (s • b0 + t • b1) ≠ 0
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_self_eq_two_mul, hb0,
      hb01, mul_zero, add_zero]
    exact mul_ne_zero hs (mul_ne_zero h2 hc)
  · have htop : Submodule.span (ZMod p) (Set.range fun i => ((vb i : P.perp) : U)) = P.perp := by
      rw [← Submodule.span_range_subtype_eq_top_iff P.perp (s := fun i => (vb i : U))
        (fun i => (vb i).2)]
      simp
    rw [← htop]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    change ((vb i : P.perp) : U) ∈ Submodule.span (ZMod p) (Set.range a)
    fin_cases i
    · have h : a 0 = ((vb 0 : P.perp) : U) := (show a 0 = b0 from rfl).trans hb0v
      exact Submodule.subset_span ⟨0, h⟩
    · have hb1eq : ((vb 1 : P.perp) : U) = t⁻¹ • (a 1 - s • a 0) := by
        rw [← hb1]
        change b1 = t⁻¹ • (s • b0 + t • b1 - s • b0)
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
      change ((vb 1 : P.perp) : U) ∈ Submodule.span (ZMod p) (Set.range a)
      rw [hb1eq]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.subset_span ⟨1, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)))

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem exists_conic_config_or_orthogonal [Module.Finite (ZMod p) U] (hp : p ≠ 2) (hp3 : p ≠ 3)
    (h4 : Module.finrank (ZMod p) U = 4) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) (P : HypPair Q) :
    (∃ a : Fin 2 → U, (∀ i, a i ∈ P.perp ∧ Q (a i) = c) ∧ polar Q (a 0) (a 1) ≠ 0 ∧
      P.perp ≤ Submodule.span (ZMod p) (Set.range a)) ∨
    ∃ b : Fin 4 → U, (∀ i j, i ≠ j → polar Q (b i) (b j) = 0) ∧ (∀ i, Q (b i) = c) ∧
      ⊤ ≤ Submodule.span (ZMod p) (Set.range b) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hA : PolarNondegOn Q P.perp := P.polarNondegOn_perp hQ
  have hAfin : Module.finrank (ZMod p) P.perp = 2 := by
    have h := ocg_finrank_perp_add_two hQ P
    omega
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp
  have hfin : FiniteDimensional (ZMod p) P.perp := Module.finite_of_finrank_pos (by omega)
  obtain ⟨vb, hborth, hbnorm, hblast⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq (K := ZMod p) (V := P.perp)
      hodd (d := 2) hAfin (by norm_num) (Q.restrict P.perp)
      (nondegenerate_polarBilin_restrict hA) hc
  let b0 : U := (vb 0 : U)
  let b1 : U := (vb 1 : U)
  have hb0mem : b0 ∈ P.perp := (vb 0).2
  have hb1mem : b1 ∈ P.perp := (vb 1).2
  have hb0 : Q b0 = c := hbnorm 0 (by norm_num)
  have hb1ne : Q b1 ≠ 0 := by simpa [b1] using hblast
  have hb01 : polar Q b0 b1 = 0 := by
    rw [← polar_restrict]
    exact hborth 0 1 (by norm_num)
  have hkne : Q b1 / c ≠ 0 := div_ne_zero hb1ne hc
  have hb1k : Q b1 = (Q b1 / c) * c := by rw [div_mul_cancel₀ _ hc]
  by_cases h5 : p = 5 ∧ IsSquare (Q b1 / c)
  · obtain ⟨hp5, r, hr⟩ := h5
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, mul_zero] at hr
      exact hkne hr
    exact Or.inr (ocg_cf4_orth hp5 hc P r hr0 hr hb0mem hb1mem hb0 hb1k hb01 h2 h4)
  · refine Or.inl (ocg_cf4_conic hp hp3 hc P hkne ?_ hb0mem hb1mem hb0 hb1k hb01 h2 vb rfl rfl)
    exact fun hp5 his => h5 ⟨hp5, his⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_star_span [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    {P : HypPair Q} {a₀ : U} {m : ℕ} {y : Fin m → U} (a : Fin (m + 1) → U)
    (ha0 : a 0 = a₀) (hasucc : ∀ i, a (Fin.succ i) = (2 : ZMod p) • a₀ + y i)
    (hyspan : P.perp ⊓ LinearMap.ker (polarBilin Q a₀) ≤ Submodule.span (ZMod p) (Set.range y))
    (hdecomp : P.perp = Submodule.span (ZMod p) {a₀} ⊔
      (P.perp ⊓ LinearMap.ker (polarBilin Q a₀))) :
    P.perp ≤ Submodule.span (ZMod p) (Set.range a) := by
  have hWspan : P.perp ⊓ LinearMap.ker (polarBilin Q a₀) ≤
      Submodule.span (ZMod p) (Set.range a) := by
    refine hyspan.trans ?_
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hyi : y i = a (Fin.succ i) - (2 : ZMod p) • a 0 := by rw [hasucc i, ha0]; abel
    rw [hyi]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨Fin.succ i, rfl⟩)
      (Submodule.smul_mem _ (2 : ZMod p) (Submodule.subset_span ⟨0, rfl⟩))
  have ha0span : a₀ ∈ Submodule.span (ZMod p) (Set.range a) := by
    rw [← ha0]
    exact Submodule.subset_span ⟨0, rfl⟩
  rw [hdecomp]
  exact sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ha0span)) hWspan

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem exists_star_config [Module.Finite (ZMod p) U] (hp : p ≠ 2) (hp3 : p ≠ 3) {m : ℕ}
    (hm : Module.finrank (ZMod p) U = m + 3) (h2 : 2 ≤ m) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) (P : HypPair Q) :
    ∃ a : Fin (m + 1) → U, (∀ i, a i ∈ P.perp ∧ Q (a i) = c) ∧
      (∀ i, i ≠ 0 → polar Q (a 0) (a i) ≠ 0) ∧ P.perp ≤ Submodule.span (ZMod p) (Set.range a) := by
  have h2z : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hA : PolarNondegOn Q P.perp := P.polarNondegOn_perp hQ
  have hAfin : Module.finrank (ZMod p) P.perp = m + 1 := by
    have h := ocg_finrank_perp_add_two hQ P
    omega
  obtain ⟨a₀, ha₀A, ha₀Q⟩ := exists_mem_map_eq_of_two_le_finrank hp hA (by omega) c
  have ha₀ne : Q a₀ ≠ 0 := by rw [ha₀Q]; exact hc
  obtain ⟨hW', hdecomp, hWfin'⟩ := ocg_perp_ker hp hA ha₀A ha₀ne
  have hWfin : Module.finrank (ZMod p) ↥(P.perp ⊓ LinearMap.ker (polarBilin Q a₀)) = m := by
    omega
  have hd : (-3 * c : ZMod p) ≠ 0 := by
    have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
    exact mul_ne_zero (neg_ne_zero.mpr h3) hc
  obtain ⟨y, hy, hyspan⟩ := exists_spanning_map_eq_of_polarNondegOn hp hp3 hW' hWfin h2 hd
  let a : Fin (m + 1) → U := Fin.cons a₀ (fun i => (2 : ZMod p) • a₀ + y i)
  have ha0 : a 0 = a₀ := rfl
  have hasucc : ∀ i, a (Fin.succ i) = (2 : ZMod p) • a₀ + y i := fun i => rfl
  have hyW : ∀ i, y i ∈ P.perp ⊓ LinearMap.ker (polarBilin Q a₀) := fun i => (hy i).1
  have hyQ : ∀ i, Q (y i) = -3 * c := fun i => (hy i).2
  have hyB : ∀ i, polar Q a₀ (y i) = 0 := fun i =>
    by simpa [LinearMap.mem_ker, polarBilin_apply_apply] using (hyW i).2
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero h2z h2z
  refine ⟨a, ?_, ?_, ocg_star_span a ha0 hasucc hyspan hdecomp⟩
  · intro i
    cases i using Fin.cases with
    | zero => rw [ha0]; exact ⟨ha₀A, ha₀Q⟩
    | succ i =>
      rw [hasucc]
      refine ⟨P.perp.add_mem (P.perp.smul_mem (2 : ZMod p) ha₀A) ((hyW i).1), ?_⟩
      rw [QuadraticMap.map_add Q, map_smul_eq_sq, ha₀Q, hyQ, polar_smul_left_eq, hyB]
      ring
  · intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    rw [ha0, hasucc, polar_add_right, polar_smul_right_eq, polar_self_eq_two_mul, ha₀Q, hyB]
    intro h
    have h4c : (4 : ZMod p) * c ≠ 0 := mul_ne_zero h4 hc
    rw [show (2 : ZMod p) * (2 * c) + 0 = 4 * c by ring] at h
    exact h4c h

end CFSG.StandardType.ZS

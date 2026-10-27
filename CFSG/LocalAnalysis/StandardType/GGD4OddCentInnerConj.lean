module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClassFour

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

namespace D4Inner

open Module CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.StandardType.D4Rank QuadraticMap
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Range

variable {x : Om8 K}

omit [Finite K] [CharP K 2] in
theorem act_mem_range_sub_one {v : Fin (2 * 4) → K} (hv : v ∈ LinearMap.range (omRep x - 1)) :
    act x v ∈ LinearMap.range (omRep x - 1) := by
  obtain ⟨y, rfl⟩ := hv
  refine ⟨act x y, ?_⟩
  change act x (act x y) - act x y = act x (act x y - y)
  rw [act_sub]

omit [Finite K] in
theorem act_sq_of_mem_range_sub_one (hx3 : x ^ 3 = 1) {v : Fin (2 * 4) → K}
    (hv : v ∈ LinearMap.range (omRep x - 1)) : act x (act x v) = act x v + v := by
  obtain ⟨y, rfl⟩ := hv
  exact act_sq_of_range hx3 y

omit [Finite K] [CharP K 2] in
theorem polar_fix_mem_range_sub_one {c v : Fin (2 * 4) → K} (hc : act x c = c)
    (hv : v ∈ LinearMap.range (omRep x - 1)) : polar (coordinateQuadPlus 4 K) c v = 0 := by
  obtain ⟨y, rfl⟩ := hv
  exact polar_fix_range hc y

omit [Finite K] [CharP K 2] in
theorem finrank_range_sub_one (hd : omFixDim x = 2) :
    finrank K (LinearMap.range (omRep x - 1)) = 6 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (omRep x - 1)
  rw [Module.finrank_fin_fun] at hrn
  have : finrank K (LinearMap.ker (omRep x - 1)) = 2 := hd
  omega

omit [Finite K] in
theorem eq_zero_of_orth_range_sub_one (hx3 : x ^ 3 = 1) {p : Fin (2 * 4) → K}
    (hp : p ∈ LinearMap.range (omRep x - 1))
    (h : ∀ q ∈ LinearMap.range (omRep x - 1), polar (coordinateQuadPlus 4 K) p q = 0) :
    p = 0 := by
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  refine hnd.1 _ fun t => ?_
  rw [polarBilin_apply_apply, decomp (x := x) t, polar_add_right, polar_comm,
    polar_fix_mem_range_sub_one (act_fixPart hx3 t) hp, zero_add]
  exact h _ ⟨act x t, rfl⟩

omit [Finite K] in
theorem act_eq_of_orth_range_sub_one (hx3 : x ^ 3 = 1) {y : Fin (2 * 4) → K}
    (hy : ∀ q ∈ LinearMap.range (omRep x - 1), polar (coordinateQuadPlus 4 K) y q = 0) :
    act x y = y := by
  have hyd := decomp (x := x) y
  have h0 : act x (act x y) - act x y = 0 := by
    refine eq_zero_of_orth_range_sub_one hx3 ⟨act x y, rfl⟩ fun q hq => ?_
    have h := hy q hq
    rw [hyd, polar_add_left, polar_fix_mem_range_sub_one (act_fixPart hx3 y) hq, zero_add] at h
    exact h
  rw [h0, add_zero] at hyd
  calc act x y = act x (y + act x y + act x (act x y)) := congrArg (act x) hyd
    _ = y + act x y + act x (act x y) := act_fixPart hx3 y
    _ = y := hyd.symm

end Range

section Frame

variable {x : Om8 K}

omit [Finite K] [CharP K 2] in
theorem polar_act_right_of_act_sq {a b : Fin (2 * 4) → K} (hb : act x (act x b) = act x b + b) :
    polar (coordinateQuadPlus 4 K) a (act x b) =
      polar (coordinateQuadPlus 4 K) (act x a) b + polar (coordinateQuadPlus 4 K) a b := by
  rw [← polar_act x a (act x b), hb, polar_add_right, polar_act, add_comm]

omit [Finite K] in
theorem polar_act_rangeFrame (hx3 : x ^ 3 = 1) {k : ℕ} {v : Fin k → Fin (2 * 4) → K}
    (hv : IsFrame x v) (hvP : ∀ j, v j ∈ LinearMap.range (omRep x - 1)) (j : Fin k) :
    polar (coordinateQuadPlus 4 K) (v j) (act x (v j)) = 1 :=
  polar_v_act_v (hv.1 j) (act_sq_of_mem_range_sub_one hx3 (hvP j))

omit [Finite K] in
theorem polar_frameProj_of_polar_one {k : ℕ} {v : Fin k → Fin (2 * 4) → K} (hv : IsFrame x v)
    (hvx : ∀ j, polar (coordinateQuadPlus 4 K) (v j) (act x (v j)) = 1) (y : Fin (2 * 4) → K)
    (i : Fin k) :
    polar (coordinateQuadPlus 4 K) (frameProj x v y) (v i) = 0 ∧
      polar (coordinateQuadPlus 4 K) (frameProj x v y) (act x (v i)) = 0 := by
  have h1 : ∀ j, polar (coordinateQuadPlus 4 K) (v j) (v i) = 0 := by
    intro j
    by_cases hji : j = i
    · rw [hji, D4Rank.polar_self_zero]
    · exact (hv.2 j i hji).1
  have h2 : ∀ j, polar (coordinateQuadPlus 4 K) (act x (v j)) (v i) =
      if j = i then 1 else 0 := by
    intro j
    split_ifs with hji
    · rw [hji, polar_comm, hvx]
    · rw [polar_comm]
      exact (hv.2 i j (Ne.symm hji)).2
  have h3 : ∀ j, polar (coordinateQuadPlus 4 K) (v j) (act x (v i)) =
      if j = i then 1 else 0 := by
    intro j
    split_ifs with hji
    · rw [hji, hvx]
    · exact (hv.2 j i hji).2
  have h4 : ∀ j, polar (coordinateQuadPlus 4 K) (act x (v j)) (act x (v i)) = 0 := by
    intro j
    rw [polar_act]
    exact h1 j
  constructor
  · rw [frameProj, polar_sub_left, polar_frame_sum]
    simp only [h1, h2, mul_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, sub_self]
  · rw [frameProj, polar_sub_left, polar_frame_sum]
    simp only [h3, h4, mul_zero, add_zero, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, sub_self]

@[expose] noncomputable def rangeFam (x : Om8 K) {k : ℕ} (v : Fin k → Fin (2 * 4) → K)
    (p : Fin k × Fin 2) : Fin (2 * 4) → K :=
  ![v p.1, act x (v p.1)] p.2

omit [Finite K] [CharP K 2] in
theorem rangeFam_mem {k : ℕ} {v : Fin k → Fin (2 * 4) → K}
    (hvP : ∀ j, v j ∈ LinearMap.range (omRep x - 1)) (p : Fin k × Fin 2) :
    rangeFam x v p ∈ LinearMap.range (omRep x - 1) := by
  obtain ⟨i, a⟩ := p
  fin_cases a
  · exact hvP i
  · exact act_mem_range_sub_one (hvP i)

omit [Finite K] [CharP K 2] in
theorem Q_rangeFam {k : ℕ} {v : Fin k → Fin (2 * 4) → K} (hv : IsFrame x v)
    (p : Fin k × Fin 2) : coordinateQuadPlus 4 K (rangeFam x v p) = 1 := by
  obtain ⟨i, a⟩ := p
  fin_cases a
  · exact hv.1 i
  · change coordinateQuadPlus 4 K (act x (v i)) = 1
    rw [Q_act]
    exact hv.1 i

omit [Finite K] in
theorem polar_rangeFam {k : ℕ} {v : Fin k → Fin (2 * 4) → K} (hv : IsFrame x v)
    (hvx : ∀ j, polar (coordinateQuadPlus 4 K) (v j) (act x (v j)) = 1) (p q : Fin k × Fin 2) :
    polar (coordinateQuadPlus 4 K) (rangeFam x v p) (rangeFam x v q) =
      if p.1 = q.1 ∧ p.2 ≠ q.2 then 1 else 0 := by
  have h00 : ∀ i j, polar (coordinateQuadPlus 4 K) (v i) (v j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij, D4Rank.polar_self_zero]
    · exact (hv.2 i j hij).1
  have h01 : ∀ i j, polar (coordinateQuadPlus 4 K) (v i) (act x (v j)) =
      if i = j then 1 else 0 := by
    intro i j
    split_ifs with hij
    · rw [hij, hvx]
    · exact (hv.2 i j hij).2
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  fin_cases a <;> fin_cases b
  · simp [rangeFam, h00]
  · simp [rangeFam, h01]
  · simp only [rangeFam]
    simp [polar_comm _ (act x (v i)) (v j), h01, eq_comm]
  · show polar _ (act x (v i)) (act x (v j)) = _
    rw [polar_act, h00]
    simp

omit [Finite K] in
theorem linIndep_rangeFam {k : ℕ} {v : Fin k → Fin (2 * 4) → K} (hv : IsFrame x v)
    (hvx : ∀ j, polar (coordinateQuadPlus 4 K) (v j) (act x (v j)) = 1) :
    LinearIndependent K (rangeFam x v) := by
  refine linIndep_of_dual (w := fun q => rangeFam x v (q.1, Fin.rev q.2)) fun p q => ?_
  rw [polar_rangeFam hv hvx]
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  fin_cases a <;> fin_cases b <;> simp [Prod.ext_iff]

theorem exists_rangeFrame_ext (hx3 : x ^ 3 = 1) (hd : omFixDim x = 2) {k : ℕ} (hk : k < 3)
    {v : Fin k → Fin (2 * 4) → K} (hv : IsFrame x v)
    (hvP : ∀ j, v j ∈ LinearMap.range (omRep x - 1)) :
    ∃ w ∈ LinearMap.range (omRep x - 1), coordinateQuadPlus 4 K w = 1 ∧
      ∀ j, polar (coordinateQuadPlus 4 K) w (v j) = 0 ∧
        polar (coordinateQuadPlus 4 K) w (act x (v j)) = 0 := by
  have horth := polar_frameProj_of_polar_one hv (polar_act_rangeFrame hx3 hv hvP)
  have hprojP : ∀ p ∈ LinearMap.range (omRep x - 1),
      frameProj x v p ∈ LinearMap.range (omRep x - 1) := fun p hp =>
    Submodule.sub_mem _ hp (Submodule.sum_mem _ fun j _ => Submodule.add_mem _
      (Submodule.smul_mem _ _ (hvP j)) (Submodule.smul_mem _ _ (act_mem_range_sub_one (hvP j))))
  obtain ⟨p, hp, hQp⟩ : ∃ p ∈ LinearMap.range (omRep x - 1),
      coordinateQuadPlus 4 K (frameProj x v p) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : LinearMap.range (omRep x - 1) ≤ Submodule.span K (Set.range (rangeFam x v)) := by
      intro p hp
      have h0 : frameProj x v p = 0 := by
        refine eq_zero_of_orth_range_sub_one hx3 (hprojP p hp) fun p' hp' => ?_
        have hz : p' = frameProj x v p' + (p' - frameProj x v p') := by abel
        have e1 : polar (coordinateQuadPlus 4 K) (frameProj x v p) (frameProj x v p') = 0 := by
          rw [polar, ← frameProj_add, hcon _ (Submodule.add_mem _ hp hp'), hcon p hp,
            hcon p' hp', sub_zero, sub_zero]
        rw [hz, polar_add_right, e1, frameProj_sub, zero_add, polar_comm, polar_frame_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [polar_comm _ (v j) (frameProj x v p), (horth p j).1,
          polar_comm _ (act x (v j)) (frameProj x v p), (horth p j).2, mul_zero, mul_zero,
          add_zero]
      have hp' : p = p - frameProj x v p := by rw [h0, sub_zero]
      rw [hp', frameProj_sub]
      refine Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, 0), rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, 1), rfl⟩)
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_range_le_card (R := K) (rangeFam x v)
    rw [Set.finrank, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h2
    rw [finrank_range_sub_one hd] at h1
    omega
  obtain ⟨t, ht⟩ := isSquare_of_charTwo' (coordinateQuadPlus 4 K (frameProj x v p))⁻¹
  refine ⟨t • frameProj x v p, Submodule.smul_mem _ _ (hprojP p hp), ?_, fun j => ?_⟩
  · rw [QuadraticMap.map_smul, smul_eq_mul, ← ht, inv_mul_cancel₀ hQp]
  · rw [polar_smul_left, polar_smul_left, (horth p j).1, (horth p j).2, smul_zero]
    exact ⟨rfl, rfl⟩

theorem exists_rangeFrame (hx3 : x ^ 3 = 1) (hd : omFixDim x = 2) :
    ∀ k, k ≤ 3 → ∃ v : Fin k → Fin (2 * 4) → K, IsFrame x v ∧
      ∀ j, v j ∈ LinearMap.range (omRep x - 1) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hv, hvP⟩ := ih (by omega)
    obtain ⟨w, hwP, hw1, hw⟩ := exists_rangeFrame_ext hx3 hd (by omega) hv hvP
    refine ⟨Fin.snoc v w, ⟨fun i => ?_, fun i j hij => ?_⟩, fun i => ?_⟩
    · induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hw1
      | cast i => rw [Fin.snoc_castSucc]; exact hv.1 i
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => rw [Fin.snoc_last, Fin.snoc_castSucc]; exact hw j
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          refine ⟨by rw [polar_comm]; exact (hw i).1, ?_⟩
          rw [polar_act_right_of_act_sq (act_sq_of_mem_range_sub_one hx3 hwP), polar_comm,
            (hw i).2, polar_comm, (hw i).1, add_zero]
        | cast j =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hv.2 i j fun h => hij (by rw [h])
    · induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hwP
      | cast i => rw [Fin.snoc_castSucc]; exact hvP i

omit [Finite K] in
theorem span_rangeFam (hx3 : x ^ 3 = 1) (hd : omFixDim x = 2) {v : Fin 3 → Fin (2 * 4) → K}
    (hv : IsFrame x v) (hvP : ∀ j, v j ∈ LinearMap.range (omRep x - 1)) :
    Submodule.span K (Set.range (rangeFam x v)) = LinearMap.range (omRep x - 1) := by
  have hli := linIndep_rangeFam hv (polar_act_rangeFrame hx3 hv hvP)
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact rangeFam_mem hvP p
  · rw [finrank_span_eq_card hli, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      finrank_range_sub_one hd]

omit [Finite K] in
theorem act_eq_of_orth_rangeFam (hx3 : x ^ 3 = 1) (hd : omFixDim x = 2)
    {v : Fin 3 → Fin (2 * 4) → K} (hv : IsFrame x v)
    (hvP : ∀ j, v j ∈ LinearMap.range (omRep x - 1)) {y : Fin (2 * 4) → K}
    (hy : ∀ p, polar (coordinateQuadPlus 4 K) y (rangeFam x v p) = 0) : act x y = y := by
  refine act_eq_of_orth_range_sub_one hx3 fun q hq => ?_
  rw [← span_rangeFam hx3 hd hv hvP] at hq
  have hle : Submodule.span K (Set.range (rangeFam x v)) ≤
      LinearMap.ker (polarBilin (coordinateQuadPlus 4 K) y) := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact LinearMap.mem_ker.mpr (by rw [polarBilin_apply_apply]; exact hy p)
  have h := LinearMap.mem_ker.mp (hle hq)
  rwa [polarBilin_apply_apply] at h

end Frame

section Conj

theorem exists_fix_Q_one {z : Om8 K} (hz3 : z ^ 3 = 1) (hd : omFixDim z ≠ 0) :
    ∃ u, coordinateQuadPlus 4 K u = 1 ∧ act z u = u := by
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  obtain ⟨u, hu, hQ⟩ : ∃ u, act z u = u ∧ coordinateQuadPlus 4 K u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hd (Submodule.finrank_eq_zero.mpr (eq_bot_iff.mpr fun c hc => ?_))
    have hc' : act z c = c := mem_ker_iff_act.mp hc
    refine (Submodule.mem_bot K).mpr (hnd.1 _ fun t => ?_)
    have h2 := act_fixPart hz3 t
    have hcs : act z (c + (t + act z t + act z (act z t))) =
        c + (t + act z t + act z (act z t)) := by
      rw [act_add, hc', h2]
    rw [polarBilin_apply_apply, decomp (x := z) t, polar_add_right, polar_fix_range hc' (act z t),
      add_zero, polar, hcon _ hcs, hcon c hc', hcon _ h2, sub_zero, sub_zero]
  obtain ⟨t, ht⟩ := isSquare_of_charTwo' (coordinateQuadPlus 4 K u)⁻¹
  refine ⟨t • u, ?_, by rw [act_smul, hu]⟩
  rw [QuadraticMap.map_smul, smul_eq_mul, ← ht, inv_mul_cancel₀ hQ]

theorem exists_conj_of_intertwine {x z : Om8 K}
    {g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 4 K))
    (key : ∀ y, act x (g y) = g (act z y)) {u : Fin (2 * 4) → K}
    (hu : coordinateQuadPlus 4 K u = 1) (hzu : act z u = u) : ∃ h : Om8 K, x = h * z * h⁻¹ := by
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have hT := (regular_coordinateQuadPlus 4 K (by norm_num)).2
  set G := matrixLinearIso.symm g
  have hGI := symm_mem_isometries hgO
  have hunit : (x : GL (Fin (2 * 4)) K) * G = G * (z : GL (Fin (2 * 4)) K) := by
    refine gl_eq_of_mulVec fun y => ?_
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, symm_mulVec,
      symm_mulVec]
    exact key y
  have hu0 : coordinateQuadPlus 4 K u ≠ 0 := by
    rw [hu]
    exact one_ne_zero
  rcases mem_or_mul_reflMat_mem hnd hT hGI u hu0 with hGΩ | hGrΩ
  · exact ⟨⟨G, hGΩ⟩, Subtype.ext (eq_mul_inv_of_mul_eq hunit)⟩
  · refine ⟨⟨G * reflMat (coordinateQuadPlus 4 K) u hu0, hGrΩ⟩, Subtype.ext ?_⟩
    change (x : GL (Fin (2 * 4)) K) = G * reflMat (coordinateQuadPlus 4 K) u hu0 *
      (z : GL (Fin (2 * 4)) K) * (G * reflMat (coordinateQuadPlus 4 K) u hu0)⁻¹
    calc (x : GL (Fin (2 * 4)) K) = G * (z : GL (Fin (2 * 4)) K) * G⁻¹ :=
          eq_mul_inv_of_mul_eq hunit
      _ = G * (reflMat (coordinateQuadPlus 4 K) u hu0 * (z : GL (Fin (2 * 4)) K)) *
          (G * reflMat (coordinateQuadPlus 4 K) u hu0)⁻¹ := by
          rw [reflMat_comm hu hu0 hzu, mul_inv_rev]
          group
      _ = _ := by group

theorem exists_conj_of_omFixDim_two {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    {x z : Om8 K} (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) (hdx : D4Rank.omFixDim x = 2)
    (hdz : D4Rank.omFixDim z = 2) : ∃ h : Om8 K, x = h * z * h⁻¹ := by
  obtain ⟨vx, hvx, hvxP⟩ := exists_rangeFrame hx3 hdx 3 le_rfl
  obtain ⟨vz, hvz, hvzP⟩ := exists_rangeFrame hz3 hdz 3 le_rfl
  have hx1 := polar_act_rangeFrame hx3 hvx hvxP
  have hz1 := polar_act_rangeFrame hz3 hvz hvzP
  set e : Fin 3 × Fin 2 ≃ Fin (3 * 2) := finProdFinEquiv
  obtain ⟨g, hgO, hg⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    (regular_coordinateQuadPlus 4 K (by norm_num)).1 (rangeFam z vz ∘ e.symm)
    (rangeFam x vx ∘ e.symm) ((linIndep_rangeFam hvz hz1).comp _ e.symm.injective)
    ((linIndep_rangeFam hvx hx1).comp _ e.symm.injective)
    (fun a => by simp only [Function.comp, Q_rangeFam hvx, Q_rangeFam hvz])
    (fun a b => by simp only [Function.comp, polar_rangeFam hvx hx1, polar_rangeFam hvz hz1])
  have hg' : ∀ p, g (rangeFam z vz p) = rangeFam x vx p := fun p => by
    simpa only [Function.comp, Equiv.symm_apply_apply] using hg (e p)
  have hP : ∀ p ∈ LinearMap.range (omRep z - 1), act x (g p) = g (act z p) := by
    intro p hp
    rw [← span_rangeFam hz3 hdz hvz hvzP] at hp
    induction hp using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨⟨i, b⟩, rfl⟩ := h
      have h0 : g (vz i) = vx i := hg' (i, 0)
      have h1 : g (act z (vz i)) = act x (vx i) := hg' (i, 1)
      fin_cases b
      · change act x (g (vz i)) = g (act z (vz i))
        rw [h0, h1]
      · change act x (g (act z (vz i))) = g (act z (act z (vz i)))
        rw [h1, act_sq_of_mem_range_sub_one hz3 (hvzP i), map_add, h1, h0,
          act_sq_of_mem_range_sub_one hx3 (hvxP i)]
    | zero => simp [act]
    | add a b _ _ ha hb => rw [map_add, act_add, ha, hb, act_add, map_add]
    | smul c a _ ha => rw [map_smul, act_smul, ha, act_smul, map_smul]
  have hC : ∀ c, act z c = c → act x (g c) = g c := fun c hc =>
    act_eq_of_orth_rangeFam hx3 hdx hvx hvxP fun p => by
      rw [← hg' p, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO]
      exact polar_fix_mem_range_sub_one hc (rangeFam_mem hvzP p)
  obtain ⟨u, hu, hzu⟩ := exists_fix_Q_one hz3 (by rw [hdz]; norm_num)
  refine exists_conj_of_intertwine hgO (fun y => ?_) hu hzu
  have hyd := decomp (x := z) y
  calc act x (g y) = act x (g (y + act z y + act z (act z y))) +
        act x (g (act z (act z y) - act z y)) := by rw [← act_add, ← map_add, ← hyd]
    _ = g (act z (y + act z y + act z (act z y))) + g (act z (act z (act z y) - act z y)) := by
        rw [hC _ (act_fixPart hz3 y), act_fixPart hz3 y,
          hP (act z (act z y) - act z y) ⟨act z y, rfl⟩]
    _ = g (act z y) := by rw [← map_add, ← act_add, ← hyd]

end Conj

end D4Inner

end CFSG.StandardType

end

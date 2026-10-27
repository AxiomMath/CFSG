module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45PgAx
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Sl2
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3

public section

namespace CFSG.Quasithin.H13.F431.F45

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3
  CFSG.Quasithin

namespace PgGeom

variable {F : Type} [Field F]

section Vectors

theorem mulVec_q1 (a c : F) (v : V3 F) :
    ((xMat a * wMat c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ![v 0 + a * v 1 + c * v 2, v 1, v 2] := by
  show (xM a * wM c) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]
  ext i
  fin_cases i
  · simp [xM, wM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  · simp [xM, wM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [xM, wM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mulVec_q2 (b c : F) (v : V3 F) :
    ((yMat b * wMat c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ![v 0 + c * v 2, v 1 + b * v 2, v 2] := by
  show (yM b * wM c) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]
  ext i
  fin_cases i <;> simp [yM, wM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end Vectors

section Levi

@[expose] def dMat (N : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, N 0 0, N 0 1; 0, N 1 0, N 1 1]

@[expose] def eMat (N : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![N 0 0, N 0 1, 0; N 1 0, N 1 1, 0; 0, 0, 1]

theorem det_dMat (N : SpecialLinearGroup (Fin 2) F) :
    (dMat (N : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
  have h := N.2
  rw [Matrix.det_fin_two] at h
  rw [Matrix.det_fin_three]
  simp [dMat]
  linear_combination h

theorem det_eMat (N : SpecialLinearGroup (Fin 2) F) :
    (eMat (N : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
  have h := N.2
  rw [Matrix.det_fin_two] at h
  rw [Matrix.det_fin_three]
  simp [eMat]
  linear_combination h

@[expose] def dSL (N : SpecialLinearGroup (Fin 2) F) : SpecialLinearGroup (Fin 3) F :=
  ⟨dMat (N : Matrix (Fin 2) (Fin 2) F), det_dMat N⟩

@[expose] def eSL (N : SpecialLinearGroup (Fin 2) F) : SpecialLinearGroup (Fin 3) F :=
  ⟨eMat (N : Matrix (Fin 2) (Fin 2) F), det_eMat N⟩

theorem mulVec_dSL (N : SpecialLinearGroup (Fin 2) F) (v : V3 F) :
    (dSL N : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ![v 0, N 0 0 * v 1 + N 0 1 * v 2, N 1 0 * v 1 + N 1 1 * v 2] := by
  ext i
  fin_cases i <;> simp [dSL, dMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mulVec_eSL (N : SpecialLinearGroup (Fin 2) F) (v : V3 F) :
    (eSL N : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ![N 0 0 * v 0 + N 0 1 * v 1, N 1 0 * v 0 + N 1 1 * v 1, v 2] := by
  ext i
  fin_cases i <;> simp [eSL, eMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end Levi

section General

theorem mem_slMap {M : SpecialLinearGroup (Fin 3) F} {U : Submodule F (V3 F)} {w : V3 F} :
    w ∈ slMap M U ↔ ∃ v ∈ U, (M : Matrix (Fin 3) (Fin 3) F) *ᵥ v = w :=
  Submodule.mem_map

theorem proj_smul_eq_of_forall {n : ℕ} (M : SpecialLinearGroup (Fin 3) F) (p q : Sub3 F n)
    (h : ∀ v ∈ p.1, (M : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ q.1) : proj 3 F M • p = q := by
  apply Subtype.ext
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_slMap.mp hw
    exact h v hv
  · rw [q.2]
    exact (finrank_xPerm _ _).trans p.2

theorem proj_smul_eq_of_gens (M : SpecialLinearGroup (Fin 3) F) (L L' : Ln F) {v₁ v₂ : V3 F}
    (hL : L.1 = Submodule.span F {v₁} ⊔ Submodule.span F {v₂})
    (h₁ : (M : Matrix (Fin 3) (Fin 3) F) *ᵥ v₁ ∈ L'.1)
    (h₂ : (M : Matrix (Fin 3) (Fin 3) F) *ᵥ v₂ ∈ L'.1) : proj 3 F M • L = L' := by
  refine proj_smul_eq_of_forall M L L' fun v hv => ?_
  rw [hL] at hv
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  exact L'.1.add_mem (L'.1.smul_mem _ h₁) (L'.1.smul_mem _ h₂)

theorem mkPt_ne_of {u v : V3 F} (hu : u ≠ 0) (hv : v ≠ 0) (h : ∀ c : F, c • u ≠ v) :
    mkPt u hu ≠ mkPt v hv := by
  intro heq
  have hmem : v ∈ (mkPt u hu).1 := by
    rw [heq]
    exact mem_mkPt hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact h c hc

theorem line_eq_span_pair {L : Ln F} {u₁ u₂ : V3 F} (h₁ : u₁ ∈ L.1) (h₂ : u₂ ∈ L.1) (hu₁ : u₁ ≠ 0)
    (hu₂ : u₂ ≠ 0) (hne : ∀ c : F, c • u₁ ≠ u₂) :
    L.1 = Submodule.span F {u₁} ⊔ Submodule.span F {u₂} :=
  line_eq_sup (p := mkPt u₁ hu₁) (p' := mkPt u₂ hu₂) (mkPt_ne_of hu₁ hu₂ hne)
    (inc_mkPt_iff.mpr h₁) (inc_mkPt_iff.mpr h₂)

end General

section Base

@[expose] def p0 : Pt F := ⟨flagSpace 3 F 1, finrank_flagSpace (by norm_num)⟩

@[expose] def l0 : Ln F := ⟨flagSpace 3 F 2, finrank_flagSpace (by norm_num)⟩

theorem mem_p0 (v : V3 F) : v ∈ (p0 : Pt F).1 ↔ v 1 = 0 ∧ v 2 = 0 := by
  show v ∈ flagSpace 3 F 1 ↔ _
  rw [mem_flagSpace]
  constructor
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide)⟩
  · rintro ⟨h1, h2⟩ j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact h1
    · exact h2

theorem mem_l0 (v : V3 F) : v ∈ (l0 : Ln F).1 ↔ v 2 = 0 := by
  show v ∈ flagSpace 3 F 2 ↔ _
  rw [mem_flagSpace]
  constructor
  · intro h
    exact h 2 (by decide)
  · intro h2 j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · exact h2

theorem ev0_mem_p0 : (ev 0 : V3 F) ∈ (p0 : Pt F).1 :=
  (mem_p0 _).mpr ⟨by simp [ev_apply], by simp [ev_apply]⟩

theorem eq_smul_ev0 {v : V3 F} (h : v ∈ (p0 : Pt F).1) : v = v 0 • ev 0 := by
  obtain ⟨h1, h2⟩ := (mem_p0 v).mp h
  ext i
  fin_cases i <;> simp [ev_apply, h1, h2]

theorem p0_eq_epts : (p0 : Pt F) = epts 0 := by
  apply Subtype.ext
  apply le_antisymm
  · intro v hv
    rw [eq_smul_ev0 hv]
    exact Submodule.smul_mem _ _ (mem_mkPt (ev_ne_zero 0))
  · intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact Submodule.smul_mem _ _ ev0_mem_p0

theorem inc_p0_iff {L : Ln F} : inc (p0 : Pt F) L ↔ (ev 0 : V3 F) ∈ L.1 := by
  constructor
  · intro h
    exact h ev0_mem_p0
  · intro h v hv
    rw [eq_smul_ev0 hv]
    exact L.1.smul_mem _ h

theorem inc_p0_l0 : inc (p0 : Pt F) l0 := fun v hv => (mem_l0 v).mpr ((mem_p0 v).mp hv).2

end Base

section PointSide

theorem q1_eq (a c : F) : xP a * wP c = proj 3 F (xMat a * wMat c) := (map_mul _ _ _).symm

theorem eq_zero_of_smul_ev0_mem {L : Ln F} (hL : ¬ inc (p0 : Pt F) L) {t : F}
    (h : t • (ev 0 : V3 F) ∈ L.1) : t = 0 := by
  by_contra ht
  apply hL
  rw [inc_p0_iff]
  have := L.1.smul_mem t⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this

theorem q1_fix_line {a c : F} {L : Ln F} (hL : inc (p0 : Pt F) L) : (xP a * wP c) • L = L := by
  rw [q1_eq]
  refine proj_smul_eq_of_forall _ L L fun v hv => ?_
  rw [mulVec_q1]
  have h : (![v 0 + a * v 1 + c * v 2, v 1, v 2] : V3 F) = v + (a * v 1 + c * v 2) • ev 0 := by
    ext i
    fin_cases i <;> simp [ev_apply, add_assoc]
  rw [h]
  exact L.1.add_mem hv (L.1.smul_mem _ (inc_p0_iff.mp hL))

theorem opp_line_inf {L : Ln F} (h : ¬ inc (p0 : Pt F) L) : L.1 ⊓ (p0 : Pt F).1 = ⊥ := by
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply h
  have hv' := eq_smul_ev0 hv.2
  have h0 : v 0 ≠ 0 := by
    intro h0
    apply hv0
    rw [hv', h0, zero_smul]
  have key : (ev 0 : V3 F) = (v 0)⁻¹ • v := by
    conv_lhs => rw [← inv_smul_smul₀ h0 (ev 0)]
    rw [← hv']
  rw [inc_p0_iff, key]
  exact L.1.smul_mem _ hv.1

theorem opp_line_top {L : Ln F} (hinf : L.1 ⊓ (p0 : Pt F).1 = ⊥) : L.1 ⊔ (p0 : Pt F).1 = ⊤ := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq L.1 (p0 : Pt F).1
  rw [hinf, finrank_bot, L.2, (p0 : Pt F).2] at h
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_v3]
  omega

theorem exists_opp_gen {L : Ln F} (h : ¬ inc (p0 : Pt F) L) :
    ∃ α γ : F, (![α, 1, 0] : V3 F) ∈ L.1 ∧ (![γ, 0, 1] : V3 F) ∈ L.1 := by
  have htop := opp_line_top (opp_line_inf h)
  have h1 : (ev 1 : V3 F) ∈ L.1 ⊔ (p0 : Pt F).1 := by rw [htop]; trivial
  have h2 : (ev 2 : V3 F) ∈ L.1 ⊔ (p0 : Pt F).1 := by rw [htop]; trivial
  obtain ⟨l, hl, m, hm, hlm⟩ := Submodule.mem_sup.mp h1
  obtain ⟨l', hl', m', hm', hlm'⟩ := Submodule.mem_sup.mp h2
  obtain ⟨hm1, hm2⟩ := (mem_p0 m).mp hm
  obtain ⟨hm1', hm2'⟩ := (mem_p0 m').mp hm'
  have l1 : l 1 = 1 := by
    have := congrFun hlm 1
    simpa [ev_apply, hm1] using this
  have l2 : l 2 = 0 := by
    have := congrFun hlm 2
    simpa [ev_apply, hm2] using this
  have l1' : l' 1 = 0 := by
    have := congrFun hlm' 1
    simpa [ev_apply, hm1'] using this
  have l2' : l' 2 = 1 := by
    have := congrFun hlm' 2
    simpa [ev_apply, hm2'] using this
  refine ⟨l 0, l' 0, ?_, ?_⟩
  · have : (![l 0, 1, 0] : V3 F) = l := by
      ext i
      fin_cases i <;> simp [l1, l2]
    rw [this]
    exact hl
  · have : (![l' 0, 0, 1] : V3 F) = l' := by
      ext i
      fin_cases i <;> simp [l1', l2']
    rw [this]
    exact hl'

theorem q1_smul_opp {a c α γ α' γ' : F} {L L' : Ln F} (h1 : (![α, 1, 0] : V3 F) ∈ L.1)
    (h2 : (![γ, 0, 1] : V3 F) ∈ L.1) (h1' : (![α', 1, 0] : V3 F) ∈ L'.1)
    (h2' : (![γ', 0, 1] : V3 F) ∈ L'.1) (ha : α' = α + a) (hc : γ' = γ + c) :
    (xP a * wP c) • L = L' := by
  rw [q1_eq]
  have hne : ∀ t : F, t • (![α, 1, 0] : V3 F) ≠ ![γ, 0, 1] := by
    intro t ht
    have := congrFun ht 2
    simp at this
  have hz1 : (![α, 1, 0] : V3 F) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  have hz2 : (![γ, 0, 1] : V3 F) ≠ 0 := by
    intro h
    have := congrFun h 2
    simp at this
  refine proj_smul_eq_of_gens _ L L' (line_eq_span_pair h1 h2 hz1 hz2 hne) ?_ ?_
  · have : ((xMat a * wMat c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (![α, 1, 0] : V3 F) = ![α', 1, 0] := by
      rw [mulVec_q1]
      ext i
      fin_cases i <;> simp [ha]
    rw [this]
    exact h1'
  · have : ((xMat a * wMat c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (![γ, 0, 1] : V3 F) = ![γ', 0, 1] := by
      rw [mulVec_q1]
      ext i
      fin_cases i <;> simp [hc]
    rw [this]
    exact h2'

theorem q1_fix_opp {a c : F} {L : Ln F} (hL : ¬ inc (p0 : Pt F) L)
    (hq : (xP a * wP c) • L = L) : a = 0 ∧ c = 0 := by
  obtain ⟨α, γ, h1, h2⟩ := exists_opp_gen hL
  rw [q1_eq] at hq
  have hL' : slMap (xMat a * wMat c) L.1 = L.1 := congrArg Subtype.val hq
  have m1 : ((xMat a * wMat c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (![α, 1, 0] : V3 F) ∈ L.1 := by
    rw [← hL']
    exact mem_slMap.mpr ⟨_, h1, rfl⟩
  have m2 : ((xMat a * wMat c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (![γ, 0, 1] : V3 F) ∈ L.1 := by
    rw [← hL']
    exact mem_slMap.mpr ⟨_, h2, rfl⟩
  rw [mulVec_q1] at m1 m2
  refine ⟨eq_zero_of_smul_ev0_mem hL ?_, eq_zero_of_smul_ev0_mem hL ?_⟩
  · have := L.1.sub_mem m1 h1
    convert this using 1
    ext i
    fin_cases i <;> simp [ev_apply]
  · have := L.1.sub_mem m2 h2
    convert this using 1
    ext i
    fin_cases i <;> simp [ev_apply]

end PointSide

section PointLevi

@[expose] def vec (s t : F) : V3 F := ![0, s, t]

theorem vec_ne_zero {s t : F} (h : s ≠ 0 ∨ t ≠ 0) : vec s t ≠ 0 := by
  intro h0
  rcases h with h | h
  · exact h (by simpa [vec] using congrFun h0 1)
  · exact h (by simpa [vec] using congrFun h0 2)

theorem exists_dir_line {L : Ln F} (hL : inc (p0 : Pt F) L) :
    ∃ s t : F, (s ≠ 0 ∨ t ≠ 0) ∧ vec s t ∈ L.1 := by
  have hnle : ¬ L.1 ≤ (p0 : Pt F).1 := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [L.2, (p0 : Pt F).2] at this
    exact absurd this (by norm_num)
  obtain ⟨v, hvL, hvp⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hw : vec (v 1) (v 2) = v - v 0 • ev 0 := by
    ext i
    fin_cases i <;> simp [vec, ev_apply]
  refine ⟨v 1, v 2, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    exact hvp ((mem_p0 v).mpr ⟨hcon.1, hcon.2⟩)
  · rw [hw]
    exact L.1.sub_mem hvL (L.1.smul_mem _ (inc_p0_iff.mp hL))

theorem not_mem_p0_vec {s t : F} (h : s ≠ 0 ∨ t ≠ 0) : vec s t ∉ (p0 : Pt F).1 := by
  intro hv
  obtain ⟨h1, h2⟩ := (mem_p0 _).mp hv
  rcases h with h | h
  · exact h (by simpa [vec] using h1)
  · exact h (by simpa [vec] using h2)

theorem line_eq_p0_sup {L : Ln F} (hL : inc (p0 : Pt F) L) {s t : F} (hd : s ≠ 0 ∨ t ≠ 0)
    (hv : vec s t ∈ L.1) :
    L.1 = Submodule.span F {ev 0} ⊔ Submodule.span F {(vec s t : V3 F)} := by
  refine line_eq_span_pair (inc_p0_iff.mp hL) hv (ev_ne_zero 0) (vec_ne_zero hd) fun c hc => ?_
  have h := congrFun hc 1
  have h2 := congrFun hc 2
  simp [ev_apply, vec] at h h2
  rcases hd with hd | hd
  · exact hd h.symm
  · exact hd h2.symm

theorem det_ne_p0 {L L' : Ln F} (hL : inc (p0 : Pt F) L) (hL' : inc (p0 : Pt F) L') {s t s' t' : F}
    (hd : s ≠ 0 ∨ t ≠ 0) (hd' : s' ≠ 0 ∨ t' ≠ 0) (hv : vec s t ∈ L.1) (hv' : vec s' t' ∈ L'.1)
    (hne : L ≠ L') : s * t' - t * s' ≠ 0 := by
  intro h0
  apply hne
  obtain ⟨l, hl0, hs, ht⟩ := Sl2.exists_scalar hd hd' h0
  have hmem : vec s t ∈ L'.1 := by
    have : vec s t = l • vec s' t' := by
      ext i
      fin_cases i <;> simp [vec, hs, ht]
    rw [this]
    exact L'.1.smul_mem _ hv'
  have hpt : (p0 : Pt F) ≠ mkPt (vec s t) (vec_ne_zero hd) := by
    intro h
    exact not_mem_p0_vec hd (by rw [h]; exact mem_mkPt _)
  exact two_pts (p0 : Pt F) (mkPt (vec s t) (vec_ne_zero hd)) L L' hL (inc_mkPt_iff.mpr hv) hL'
    (inc_mkPt_iff.mpr hmem) hpt

theorem two_trans_p0 {L L' M M' : Ln F} (hL : inc (p0 : Pt F) L) (hL' : inc (p0 : Pt F) L')
    (hM : inc (p0 : Pt F) M) (hM' : inc (p0 : Pt F) M') (hne : L ≠ L') (hne' : M ≠ M') :
    ∃ g : projectiveSL 3 F, g • (p0 : Pt F) = p0 ∧ g • L = M ∧ g • L' = M' := by
  obtain ⟨s, t, hd, hv⟩ := exists_dir_line hL
  obtain ⟨s', t', hd', hv'⟩ := exists_dir_line hL'
  obtain ⟨u, v, he, hu⟩ := exists_dir_line hM
  obtain ⟨u', v', he', hu'⟩ := exists_dir_line hM'
  have hΔ := det_ne_p0 hL hL' hd hd' hv hv' hne
  have hΔz := det_ne_p0 hM hM' he he' hu hu' hne'
  obtain ⟨N, κ, hκ, e1, e2, e3, e4⟩ := Sl2.sl2_two_trans s t s' t' u v u' v' hΔ hΔz
  have hfix : (dSL N : Matrix (Fin 3) (Fin 3) F) *ᵥ (ev 0 : V3 F) = ev 0 := by
    rw [mulVec_dSL]
    ext i
    fin_cases i <;> simp [ev_apply]
  refine ⟨proj 3 F (dSL N), ?_, ?_, ?_⟩
  · refine proj_smul_eq_of_forall _ _ _ fun w hw => ?_
    rw [eq_smul_ev0 hw, Matrix.mulVec_smul, hfix]
    exact (p0 : Pt F).1.smul_mem _ ev0_mem_p0
  · refine proj_smul_eq_of_gens _ L M (line_eq_p0_sup hL hd hv) ?_ ?_
    · rw [hfix]
      exact inc_p0_iff.mp hM
    · have : (dSL N : Matrix (Fin 3) (Fin 3) F) *ᵥ (vec s t : V3 F) = vec u v := by
        rw [mulVec_dSL]
        ext i
        fin_cases i <;> simp [vec, e1, e2]
      rw [this]
      exact hu
  · refine proj_smul_eq_of_gens _ L' M' (line_eq_p0_sup hL' hd' hv') ?_ ?_
    · rw [hfix]
      exact inc_p0_iff.mp hM'
    · have : (dSL N : Matrix (Fin 3) (Fin 3) F) *ᵥ (vec s' t' : V3 F) = κ • vec u' v' := by
        rw [mulVec_dSL]
        ext i
        fin_cases i <;> simp [vec, e3, e4]
      rw [this]
      exact M'.1.smul_mem _ hu'

end PointLevi

section LineSide

theorem q2_eq (b c : F) : yP b * wP c = proj 3 F (yMat b * wMat c) := (map_mul _ _ _).symm

theorem pt_eq_span_of_mem {p : Pt F} {u : V3 F} (hu : u ∈ p.1) (hu0 : u ≠ 0) :
    p.1 = Submodule.span F {u} := by
  have hle : Submodule.span F {u} ≤ p.1 := by
    rw [Submodule.span_le]
    simpa using hu
  symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_span_singleton hu0]
  exact p.2.symm

theorem proj_smul_pt_eq {M : SpecialLinearGroup (Fin 3) F} {p q : Pt F} {u : V3 F} (hu : u ∈ p.1)
    (hu0 : u ≠ 0) (h : (M : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ q.1) : proj 3 F M • p = q := by
  refine proj_smul_eq_of_forall M p q fun v hv => ?_
  rw [pt_eq_span_of_mem hu hu0] at hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [Matrix.mulVec_smul]
  exact q.1.smul_mem _ h

theorem q2_fix_pt {b c : F} {p : Pt F} (hp : inc p (l0 : Ln F)) : (yP b * wP c) • p = p := by
  rw [q2_eq]
  refine proj_smul_eq_of_forall _ p p fun v hv => ?_
  have h2 : v 2 = 0 := (mem_l0 v).mp (hp hv)
  rw [mulVec_q2]
  have : (![v 0 + c * v 2, v 1 + b * v 2, v 2] : V3 F) = v := by
    ext i
    fin_cases i <;> simp [h2]
  rw [this]
  exact hv

theorem exists_opp_pt {p : Pt F} (hp : ¬ inc p (l0 : Ln F)) :
    ∃ a₁ a₂ : F, (![a₁, a₂, 1] : V3 F) ∈ p.1 := by
  obtain ⟨v, hv0, hv⟩ := pt_eq_span p
  have hv2 : v 2 ≠ 0 := by
    intro h2
    apply hp
    show p.1 ≤ (l0 : Ln F).1
    rw [hv, Submodule.span_le]
    simpa using (mem_l0 v).mpr h2
  refine ⟨v 0 / v 2, v 1 / v 2, ?_⟩
  have : (![v 0 / v 2, v 1 / v 2, 1] : V3 F) = (v 2)⁻¹ • v := by
    ext i
    fin_cases i <;> simp [div_eq_inv_mul, hv2]
  rw [this, hv]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem one_vec_ne_zero (a₁ a₂ : F) : (![a₁, a₂, 1] : V3 F) ≠ 0 := by
  intro h
  have := congrFun h 2
  simp at this

theorem q2_smul_opp {b c a₁ a₂ a₁' a₂' : F} {p p' : Pt F} (h : (![a₁, a₂, 1] : V3 F) ∈ p.1)
    (h' : (![a₁', a₂', 1] : V3 F) ∈ p'.1) (ha₁ : a₁' = a₁ + c) (ha₂ : a₂' = a₂ + b) :
    (yP b * wP c) • p = p' := by
  rw [q2_eq]
  refine proj_smul_pt_eq h (one_vec_ne_zero a₁ a₂) ?_
  have : ((yMat b * wMat c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (![a₁, a₂, 1] : V3 F) = ![a₁', a₂', 1] := by
    rw [mulVec_q2]
    ext i
    fin_cases i <;> simp [ha₁, ha₂]
  rw [this]
  exact h'

theorem q2_fix_opp {b c : F} {p : Pt F} (hp : ¬ inc p (l0 : Ln F))
    (hq : (yP b * wP c) • p = p) : b = 0 ∧ c = 0 := by
  obtain ⟨a₁, a₂, h⟩ := exists_opp_pt hp
  rw [q2_eq] at hq
  have hp' : slMap (yMat b * wMat c) p.1 = p.1 := congrArg Subtype.val hq
  have m : ((yMat b * wMat c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (![a₁, a₂, 1] : V3 F) ∈ p.1 := by
    rw [← hp']
    exact mem_slMap.mpr ⟨_, h, rfl⟩
  rw [pt_eq_span_of_mem h (one_vec_ne_zero a₁ a₂)] at m
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp m
  rw [mulVec_q2] at hl
  have e0 := congrFun hl 0
  have e1 := congrFun hl 1
  have e2 := congrFun hl 2
  simp at e0 e1 e2
  subst e2
  constructor
  · linear_combination -e1
  · linear_combination -e0

end LineSide

section LineLevi

@[expose] def vec' (s t : F) : V3 F := ![s, t, 0]

theorem exists_dir_pt {p : Pt F} (hp : inc p (l0 : Ln F)) :
    ∃ s t : F, (s ≠ 0 ∨ t ≠ 0) ∧ p.1 = Submodule.span F {(vec' s t : V3 F)} := by
  obtain ⟨v, hv0, hv⟩ := pt_eq_span p
  have hvL : v ∈ (l0 : Ln F).1 := hp (by rw [hv]; exact Submodule.mem_span_singleton_self v)
  have h2 := (mem_l0 v).mp hvL
  have hv' : v = vec' (v 0) (v 1) := by
    ext i
    fin_cases i <;> simp [vec', h2]
  refine ⟨v 0, v 1, ?_, by rw [hv, ← hv']⟩
  by_contra hcon
  push Not at hcon
  apply hv0
  rw [hv']
  ext i
  fin_cases i <;> simp [vec', hcon.1, hcon.2]

theorem det_ne_pt {p p' : Pt F} {s t s' t' : F} (hd : s ≠ 0 ∨ t ≠ 0) (hd' : s' ≠ 0 ∨ t' ≠ 0)
    (hp : p.1 = Submodule.span F {(vec' s t : V3 F)})
    (hp' : p'.1 = Submodule.span F {(vec' s' t' : V3 F)}) (hne : p ≠ p') : s * t' - t * s' ≠ 0 := by
  intro h0
  apply hne
  obtain ⟨l, hl0, hs, ht⟩ := Sl2.exists_scalar hd hd' h0
  have hle : p.1 ≤ p'.1 := by
    rw [hp, Submodule.span_le]
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    have : vec' s t = l • vec' s' t' := by
      ext i
      fin_cases i <;> simp [vec', hs, ht]
    rw [this, hp']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by rw [p.2, p'.2]))

theorem two_trans_l0 {p p' q q' : Pt F} (hp : inc p (l0 : Ln F)) (hp' : inc p' (l0 : Ln F))
    (hq : inc q (l0 : Ln F)) (hq' : inc q' (l0 : Ln F)) (hne : p ≠ p') (hne' : q ≠ q') :
    ∃ g : projectiveSL 3 F, g • (l0 : Ln F) = l0 ∧ g • p = q ∧ g • p' = q' := by
  obtain ⟨s, t, hd, hpg⟩ := exists_dir_pt hp
  obtain ⟨s', t', hd', hpg'⟩ := exists_dir_pt hp'
  obtain ⟨u, v, he, hqg⟩ := exists_dir_pt hq
  obtain ⟨u', v', he', hqg'⟩ := exists_dir_pt hq'
  have hΔ := det_ne_pt hd hd' hpg hpg' hne
  have hΔz := det_ne_pt he he' hqg hqg' hne'
  obtain ⟨N, κ, hκ, e1, e2, e3, e4⟩ := Sl2.sl2_two_trans s t s' t' u v u' v' hΔ hΔz
  have hvec : ∀ s t : F, (s ≠ 0 ∨ t ≠ 0) → (vec' s t : V3 F) ≠ 0 := by
    intro s t hd h
    rcases hd with hd | hd
    · exact hd (by simpa [vec'] using congrFun h 0)
    · exact hd (by simpa [vec'] using congrFun h 1)
  refine ⟨proj 3 F (eSL N), ?_, ?_, ?_⟩
  · refine proj_smul_eq_of_forall _ _ _ fun w hw => ?_
    rw [mem_l0] at hw ⊢
    rw [mulVec_eSL]
    simpa using hw
  · refine proj_smul_pt_eq (u := vec' s t) (hpg ▸ Submodule.mem_span_singleton_self _)
      (hvec s t hd) ?_
    have : (eSL N : Matrix (Fin 3) (Fin 3) F) *ᵥ (vec' s t : V3 F) = vec' u v := by
      rw [mulVec_eSL]
      ext i
      fin_cases i <;> simp [vec', e1, e2]
    rw [this, hqg]
    exact Submodule.mem_span_singleton_self _
  · refine proj_smul_pt_eq (u := vec' s' t') (hpg' ▸ Submodule.mem_span_singleton_self _)
      (hvec s' t' hd') ?_
    have : (eSL N : Matrix (Fin 3) (Fin 3) F) *ᵥ (vec' s' t' : V3 F) = κ • vec' u' v' := by
      rw [mulVec_eSL]
      ext i
      fin_cases i <;> simp [vec', e3, e4]
    rw [this, hqg']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end LineLevi

section Final

theorem nbrs_card_inl {A B : Type} {r : A → B → Prop} (a : A) :
    Nat.card ((incGraph r).neighborSet (Sum.inl a)) = {b | r a b}.ncard := by
  rw [neighborSet_inl, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Sum.inr_injective]

theorem nbrs_card_inr {A B : Type} {r : A → B → Prop} (b : B) :
    Nat.card ((incGraph r).neighborSet (Sum.inr b)) = {a | r a b}.ncard := by
  rw [neighborSet_inr, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Sum.inl_injective]

theorem three_p0 [Finite F] : 3 ≤ Nat.card ((Gr F).neighborSet (Sum.inl (p0 : Pt F))) := by
  rw [nbrs_card_inl]
  have d01 : (0 : Fin 3) ≠ 1 := by decide
  have d02 : (0 : Fin 3) ≠ 2 := by decide
  have hd11 : (1 : F) ≠ 0 ∨ (1 : F) ≠ 0 := Or.inl one_ne_zero
  have hpt : (p0 : Pt F) ≠ mkPt (vec 1 1) (vec_ne_zero hd11) := by
    intro h
    exact not_mem_p0_vec hd11 (by rw [h]; exact mem_mkPt _)
  let M₁ : Ln F := eline 0 1 d01
  let M₂ : Ln F := eline 0 2 d02
  let M₃ : Ln F := mkLine (p0 : Pt F) (mkPt (vec 1 1) (vec_ne_zero hd11)) hpt
  have i1 : inc (p0 : Pt F) M₁ := by
    rw [p0_eq_epts]
    exact inc_eline_left d01
  have i2 : inc (p0 : Pt F) M₂ := by
    rw [p0_eq_epts]
    exact inc_eline_left d02
  have i3 : inc (p0 : Pt F) M₃ := inc_mkLine_left _ _ _
  have e1 : (ev 1 : V3 F) ∈ M₁.1 := ev_mem_eline_right d01
  have v3 : (vec 1 1 : V3 F) ∈ M₃.1 := inc_mkLine_right _ _ _ (mem_mkPt _)
  have h12 : M₁ ≠ M₂ := by
    intro h
    have : (ev 1 : V3 F) ∈ M₂.1 := h ▸ e1
    have := eline_apply_third d02 (k := 1) (by decide) (by decide) this
    simp [ev_apply] at this
  have h13 : M₁ ≠ M₃ := by
    intro h
    have : (vec 1 1 : V3 F) ∈ M₁.1 := h ▸ v3
    have := eline_apply_third d01 (k := 2) (by decide) (by decide) this
    simp [vec] at this
  have h23 : M₂ ≠ M₃ := by
    intro h
    have : (vec 1 1 : V3 F) ∈ M₂.1 := h ▸ v3
    have := eline_apply_third d02 (k := 1) (by decide) (by decide) this
    simp [vec] at this
  have hsub : ({M₁, M₂, M₃} : Set (Ln F)) ⊆ {b | inc (p0 : Pt F) b} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact i1
    · exact i2
    · exact i3
  have h3 : ({M₁, M₂, M₃} : Set (Ln F)).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨M₁, M₂, M₃, h12, h13, h23, rfl⟩
  rw [← h3]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem three_l0 [Finite F] : 3 ≤ Nat.card ((Gr F).neighborSet (Sum.inr (l0 : Ln F))) := by
  rw [nbrs_card_inr]
  have hd11 : (1 : F) ≠ 0 ∨ (1 : F) ≠ 0 := Or.inl one_ne_zero
  have hv : (vec' 1 1 : V3 F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [vec'] at this
  let P₀ : Pt F := epts 0
  let P₁ : Pt F := epts 1
  let P₂ : Pt F := mkPt (vec' 1 1) hv
  have h01 : P₀ ≠ P₁ := epts_ne (by decide)
  have h02 : P₀ ≠ P₂ := mkPt_ne_of _ _ fun c hc => by
    have := congrFun hc 1
    simp [ev_apply, vec'] at this
  have h12 : P₁ ≠ P₂ := mkPt_ne_of _ _ fun c hc => by
    have := congrFun hc 0
    simp [ev_apply, vec'] at this
  have i0 : inc P₀ (l0 : Ln F) := by
    show inc (epts 0) (l0 : Ln F)
    rw [← p0_eq_epts]
    exact inc_p0_l0
  have i1 : inc P₁ (l0 : Ln F) := inc_mkPt_iff.mpr ((mem_l0 _).mpr (by simp [ev_apply]))
  have i2 : inc P₂ (l0 : Ln F) := inc_mkPt_iff.mpr ((mem_l0 _).mpr (by simp [vec']))
  have hsub : ({P₀, P₁, P₂} : Set (Pt F)) ⊆ {a | inc a (l0 : Ln F)} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact i0
    · exact i1
    · exact i2
  have h3 : ({P₀, P₁, P₂} : Set (Pt F)).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨P₀, P₁, P₂, h01, h02, h12, rfl⟩
  rw [← h3]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

end Final

section ModelBases

variable [CharP F 2]

theorem modelBase_p0 :
    ModelBase (Gr F) 3 (Sum.inl (p0 : Pt F)) (V1 : Subgroup (projectiveSL 3 F)) where
  Qfix w hw q hq := by
    obtain ⟨L, rfl, hL⟩ := incGraph_adj_inl hw
    obtain ⟨a, c, rfl⟩ := mem_V1.mp hq
    rw [Sum.smul_inr, q1_fix_line hL]
  Qtrans b c hb hc := by
    cases b with
    | inl p => exact absurd hb (ppAxioms.dist_inl_inl_ne_three _ _)
    | inr L =>
      cases c with
      | inl p' => exact absurd hc (ppAxioms.dist_inl_inl_ne_three _ _)
      | inr L' =>
        have h1 : ¬ inc (p0 : Pt F) L := (ppAxioms.dist_inl_inr_eq_three _ _).mp hb
        have h2 : ¬ inc (p0 : Pt F) L' := (ppAxioms.dist_inl_inr_eq_three _ _).mp hc
        obtain ⟨α, γ, h1a, h1b⟩ := exists_opp_gen h1
        obtain ⟨α', γ', h2a, h2b⟩ := exists_opp_gen h2
        refine ⟨xP (α' - α) * wP (γ' - γ), ⟨_, _, rfl⟩, ?_⟩
        rw [Sum.smul_inr, q1_smul_opp h1a h1b h2a h2b (by ring) (by ring)]
  Qfree b hb q hq hqb := by
    cases b with
    | inl p => exact absurd hb (ppAxioms.dist_inl_inl_ne_three _ _)
    | inr L =>
      obtain ⟨a, c, rfl⟩ := mem_V1.mp hq
      have hL : ¬ inc (p0 : Pt F) L := (ppAxioms.dist_inl_inr_eq_three _ _).mp hb
      rw [Sum.smul_inr] at hqb
      obtain ⟨rfl, rfl⟩ := q1_fix_opp hL (Sum.inr.inj hqb)
      rw [xP_zero, wP_zero, mul_one]
  two b c b' c' hb hc hbc hb' hc' hbc' := by
    obtain ⟨L, rfl, hL⟩ := incGraph_adj_inl hb
    obtain ⟨L', rfl, hL'⟩ := incGraph_adj_inl hc
    obtain ⟨M, rfl, hM⟩ := incGraph_adj_inl hb'
    obtain ⟨M', rfl, hM'⟩ := incGraph_adj_inl hc'
    obtain ⟨g, hg1, hg2, hg3⟩ := two_trans_p0 hL hL' hM hM' (fun h => hbc (by rw [h]))
      (fun h => hbc' (by rw [h]))
    exact ⟨g, by rw [Sum.smul_inl, hg1], by rw [Sum.smul_inr, hg2], by rw [Sum.smul_inr, hg3]⟩

theorem modelBase_l0 :
    ModelBase (Gr F) 3 (Sum.inr (l0 : Ln F)) (V2 : Subgroup (projectiveSL 3 F)) where
  Qfix w hw q hq := by
    obtain ⟨p, rfl, hp⟩ := incGraph_adj_inr hw
    obtain ⟨b, c, rfl⟩ := mem_V2.mp hq
    rw [Sum.smul_inl, q2_fix_pt hp]
  Qtrans b c hb hc := by
    cases b with
    | inl p =>
      cases c with
      | inl p' =>
        have h1 : ¬ inc p (l0 : Ln F) := (ppAxioms.dist_inr_inl_eq_three _ _).mp hb
        have h2 : ¬ inc p' (l0 : Ln F) := (ppAxioms.dist_inr_inl_eq_three _ _).mp hc
        obtain ⟨a₁, a₂, ha⟩ := exists_opp_pt h1
        obtain ⟨a₁', a₂', ha'⟩ := exists_opp_pt h2
        refine ⟨yP (a₂' - a₂) * wP (a₁' - a₁), ⟨_, _, rfl⟩, ?_⟩
        rw [Sum.smul_inl, q2_smul_opp ha ha' (by ring) (by ring)]
      | inr L' => exact absurd hc (ppAxioms.dist_inr_inr_ne_three _ _)
    | inr L => exact absurd hb (ppAxioms.dist_inr_inr_ne_three _ _)
  Qfree b hb q hq hqb := by
    cases b with
    | inl p =>
      obtain ⟨b, c, rfl⟩ := mem_V2.mp hq
      have hp : ¬ inc p (l0 : Ln F) := (ppAxioms.dist_inr_inl_eq_three _ _).mp hb
      rw [Sum.smul_inl] at hqb
      obtain ⟨rfl, rfl⟩ := q2_fix_opp hp (Sum.inl.inj hqb)
      rw [yP_zero, wP_zero, mul_one]
    | inr L => exact absurd hb (ppAxioms.dist_inr_inr_ne_three _ _)
  two b c b' c' hb hc hbc hb' hc' hbc' := by
    obtain ⟨p, rfl, hp⟩ := incGraph_adj_inr hb
    obtain ⟨p', rfl, hp'⟩ := incGraph_adj_inr hc
    obtain ⟨q, rfl, hq⟩ := incGraph_adj_inr hb'
    obtain ⟨q', rfl, hq'⟩ := incGraph_adj_inr hc'
    obtain ⟨g, hg1, hg2, hg3⟩ := two_trans_l0 hp hp' hq hq' (fun h => hbc (by rw [h]))
      (fun h => hbc' (by rw [h]))
    exact ⟨g, by rw [Sum.smul_inr, hg1], by rw [Sum.smul_inl, hg2], by rw [Sum.smul_inl, hg3]⟩

end ModelBases

section Stabilizers

theorem proj_smul_eq_self_iff {n : ℕ} (M : SpecialLinearGroup (Fin 3) F) (p : Sub3 F n)
    (W : Submodule F (V3 F)) (hW : p.1 = W) :
    proj 3 F M • p = p ↔ M ∈ stabilizer W := by
  rw [mem_stabilizer]
  constructor
  · intro h
    have h2 : slMap M p.1 = p.1 := congrArg Subtype.val h
    rw [hW] at h2
    exact h2
  · intro h
    apply Subtype.ext
    show slMap M p.1 = p.1
    rw [hW]
    exact h

theorem mem_map_proj_stabilizer_iff (W : Submodule F (V3 F)) (M : SpecialLinearGroup (Fin 3) F) :
    proj 3 F M ∈ (stabilizer W).map (proj 3 F) ↔ M ∈ stabilizer W := by
  constructor
  · rintro ⟨M', hM', h⟩
    have hs : M'⁻¹ * M ∈ stabilizer W := scalars_le_stabilizer W (proj_eq_proj_iff.mp h)
    have e : M = M' * (M'⁻¹ * M) := by group
    rw [e]
    exact mul_mem hM' hs
  · exact fun h => ⟨M, h, rfl⟩

theorem smul_p0_iff (y : projectiveSL 3 F) :
    y • (p0 : Pt F) = p0 ↔ y ∈ (stabilizer (flagSpace 3 F 1)).map (proj 3 F) := by
  obtain ⟨M, rfl⟩ := proj_surjective 3 F y
  rw [mem_map_proj_stabilizer_iff]
  exact proj_smul_eq_self_iff M p0 _ rfl

theorem smul_l0_iff (y : projectiveSL 3 F) :
    y • (l0 : Ln F) = l0 ↔ y ∈ (stabilizer (flagSpace 3 F 2)).map (proj 3 F) := by
  obtain ⟨M, rfl⟩ := proj_surjective 3 F y
  rw [mem_map_proj_stabilizer_iff]
  exact proj_smul_eq_self_iff M l0 _ rfl

end Stabilizers

end PgGeom

end CFSG.Quasithin.H13.F431.F45

module

public import CFSG.RankThree.Lattice.SteinbergBIPrimeKernel

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley Matrix Polynomial CFSG.RankThree.Lattice

structure LineRow where
  rep : List ℤ
  fc : List ℤ
  a : List ℤ
  b : List ℤ
  cls : ℕ
  q1 : List ℤ
  u1 : List ℤ
  u2 : List ℤ
  d : ℤ
  q2 : List ℤ
  orbit : List (List ℤ)
  deriving Inhabited

structure LineClass where
  A : List ℤ
  B : List ℤ
  u1 : List ℤ
  u2 : List ℤ
  d : ℤ
  q : List ℤ
  deriving Inhabited

structure CrossCert where
  i : ℕ
  j : ℕ
  u : List ℤ
  d : ℤ
  q : List ℤ
  deriving Inhabited

@[expose] def LineRow.check (n : ℕ) (W : List (List ℤ)) (F : List (List ℤ)) (β₁ β₂ Φ : List ℤ)
    (m : ℕ) (cl : LineClass) (r : LineRow) : Bool :=
  decide (vadd n (vcombo n F r.fc) (vadd n (lpolyVec n W r.a β₁) (lpolyVec n W r.b β₂)) =
      r.rep) &&
    decide (pnorm (padd (pmul r.a cl.B) (pscale (-1) (pmul r.b cl.A))) = pnorm (pmul r.q1 Φ)) &&
    decide (pnorm (padd (padd (pmul r.u1 r.a) (pmul r.u2 r.b)) [-r.d]) =
      pnorm (pmul r.q2 Φ)) &&
    decide (r.orbit = lorbit n W r.rep m)

@[expose] def LineClass.check (Φ : List ℤ) (cl : LineClass) : Bool :=
  decide (pnorm (padd (padd (pmul cl.u1 cl.A) (pmul cl.u2 cl.B)) [-cl.d]) =
    pnorm (pmul cl.q Φ))

@[expose] def CrossCert.check (Φ : List ℤ) (classes : List LineClass) (c : CrossCert) : Bool :=
  decide (pnorm (padd (pmul c.u (padd (pmul (classes.getD c.i default).A
      (classes.getD c.j default).B)
    (pscale (-1) (pmul (classes.getD c.j default).A (classes.getD c.i default).B)))) [-c.d]) =
      pnorm (pmul c.q Φ))

variable {F' : Type*} [Field F']

theorem peval_eq_zero_of_cong {P Q Φ : List ℤ} (h : pnorm P = pnorm (pmul Q Φ)) {ρ : F'}
    (hΦ : peval Φ ρ = 0) : peval P ρ = 0 := by
  have := congrArg (fun cs => peval cs ρ) h
  simp only [peval_pnorm, peval_pmul, hΦ, mul_zero] at this
  exact this

theorem lineRow_cross {n : ℕ} {W F : List (List ℤ)} {β₁ β₂ Φ : List ℤ} {m : ℕ} {cl : LineClass}
    {r : LineRow} (hr : r.check n W F β₁ β₂ Φ m cl = true) {ρ : F'} (hΦ : peval Φ ρ = 0) :
    peval r.a ρ * peval cl.B ρ = peval r.b ρ * peval cl.A ρ := by
  simp only [LineRow.check, Bool.and_eq_true, decide_eq_true_eq] at hr
  have h := peval_eq_zero_of_cong hr.1.1.2 hΦ
  simp only [peval_padd, peval_pmul, peval_pscale] at h
  push_cast at h
  linear_combination h

theorem lineRow_unit {n : ℕ} {W F : List (List ℤ)} {β₁ β₂ Φ : List ℤ} {m : ℕ} {cl : LineClass}
    {r : LineRow} (hr : r.check n W F β₁ β₂ Φ m cl = true) {ρ : F'} (hΦ : peval Φ ρ = 0) :
    peval r.u1 ρ * peval r.a ρ + peval r.u2 ρ * peval r.b ρ = (r.d : F') := by
  simp only [LineRow.check, Bool.and_eq_true, decide_eq_true_eq] at hr
  have h := peval_eq_zero_of_cong hr.1.2 hΦ
  simp only [peval_padd, peval_pmul, peval_cons, peval_nil, Int.cast_neg] at h
  linear_combination h

theorem lineClass_unit {Φ : List ℤ} {cl : LineClass} (hc : cl.check Φ = true) {ρ : F'}
    (hΦ : peval Φ ρ = 0) :
    peval cl.u1 ρ * peval cl.A ρ + peval cl.u2 ρ * peval cl.B ρ = (cl.d : F') := by
  simp only [LineClass.check, decide_eq_true_eq] at hc
  have h := peval_eq_zero_of_cong hc hΦ
  simp only [peval_padd, peval_pmul, peval_cons, peval_nil, Int.cast_neg] at h
  linear_combination h

theorem crossCert_unit {Φ : List ℤ} {classes : List LineClass} {c : CrossCert}
    (hc : c.check Φ classes = true) {ρ : F'} (hΦ : peval Φ ρ = 0) :
    peval c.u ρ * (peval (classes.getD c.i default).A ρ * peval (classes.getD c.j default).B ρ -
      peval (classes.getD c.j default).A ρ * peval (classes.getD c.i default).B ρ) =
        (c.d : F') := by
  simp only [CrossCert.check, decide_eq_true_eq] at hc
  have h := peval_eq_zero_of_cong hc hΦ
  simp only [peval_padd, peval_pmul, peval_pscale, peval_cons, peval_nil, Int.cast_neg] at h
  push_cast at h
  linear_combination h

variable {n : ℕ}

theorem lineRow_pair_eq_zero_iff {W F : List (List ℤ)} {β₁ β₂ Φ : List ℤ} {m : ℕ} {cl : LineClass}
    {r : LineRow} (hr : r.check n W F β₁ β₂ Φ m cl = true) (hcl : cl.check Φ = true)
    {z : Fin n → F'} {ρ : F'}
    (hz : ((toMat n W).map (Int.cast : ℤ → F'))ᵀ *ᵥ z = ρ • z) (hΦ : peval Φ ρ = 0)
    (hF : ∀ x ∈ F, pair (toVec n x) z = 0) (hd : (r.d : F') ≠ 0) (hdcl : (cl.d : F') ≠ 0) :
    pair (toVec n r.rep) z = 0 ↔
      peval cl.A ρ * pair (toVec n β₁) z + peval cl.B ρ * pair (toVec n β₂) z = 0 := by
  have hrep : pair (toVec n r.rep) z =
      peval r.a ρ * pair (toVec n β₁) z + peval r.b ρ * pair (toVec n β₂) z := by
    have h1 : r.rep = vadd n (vcombo n F r.fc) (vadd n (lpolyVec n W r.a β₁)
        (lpolyVec n W r.b β₂)) := by
      simp only [LineRow.check, Bool.and_eq_true, decide_eq_true_eq] at hr
      exact hr.1.1.1.symm
    rw [h1, toVec_vadd, pair_add, pair_vcombo_eq_zero F r.fc hF, zero_add, toVec_vadd, pair_add,
      pair_lpolyVec hz, pair_lpolyVec hz]
  have hcr := lineRow_cross hr hΦ
  have hru := lineRow_unit hr hΦ
  have hcu := lineClass_unit hcl hΦ
  set s := pair (toVec n β₁) z
  set t := pair (toVec n β₂) z
  set κ := peval cl.A ρ * s + peval cl.B ρ * t with hκ
  have e1 : peval cl.A ρ * pair (toVec n r.rep) z = peval r.a ρ * κ := by
    rw [hrep, hκ]
    linear_combination (-t) * hcr
  have e2 : peval cl.B ρ * pair (toVec n r.rep) z = peval r.b ρ * κ := by
    rw [hrep, hκ]
    linear_combination s * hcr
  constructor
  · intro h0
    by_contra hκ0
    rw [h0, mul_zero] at e1 e2
    have ha : peval r.a ρ = 0 := (mul_eq_zero.1 e1.symm).resolve_right hκ0
    have hb : peval r.b ρ = 0 := (mul_eq_zero.1 e2.symm).resolve_right hκ0
    rw [ha, hb, mul_zero, mul_zero, add_zero] at hru
    exact hd hru.symm
  · intro h0
    by_contra hp0
    rw [h0, mul_zero] at e1 e2
    have ha : peval cl.A ρ = 0 := (mul_eq_zero.1 e1).resolve_right hp0
    have hb : peval cl.B ρ = 0 := (mul_eq_zero.1 e2).resolve_right hp0
    rw [ha, hb, mul_zero, mul_zero, add_zero] at hcu
    exact hdcl hcu.symm

@[expose] def lineClassRoots (rows : List LineRow) (j : ℕ) : List (List ℤ) :=
  (rows.filter fun r => r.cls == j).flatMap LineRow.orbit

theorem mem_lineClassRoots {rows : List LineRow} {j : ℕ} {l : List ℤ} :
    l ∈ lineClassRoots rows j ↔ ∃ r ∈ rows, r.cls = j ∧ l ∈ r.orbit := by
  simp only [lineClassRoots, List.mem_flatMap, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨r, ⟨hr, hj⟩, hl⟩
    exact ⟨r, hr, hj, hl⟩
  · rintro ⟨r, hr, hj, hl⟩
    exact ⟨r, ⟨hr, hj⟩, hl⟩

theorem pair_orbit_eq_zero_iff {W F : List (List ℤ)} {β₁ β₂ Φ : List ℤ} {m : ℕ} {cl : LineClass}
    {r : LineRow} (hr : r.check n W F β₁ β₂ Φ m cl = true) (hcl : cl.check Φ = true)
    {z : Fin n → F'} {ρ : F'}
    (hz : ((toMat n W).map (Int.cast : ℤ → F'))ᵀ *ᵥ z = ρ • z) (hρ : ρ ≠ 0) (hΦ : peval Φ ρ = 0)
    (hF : ∀ x ∈ F, pair (toVec n x) z = 0) (hd : (r.d : F') ≠ 0) (hdcl : (cl.d : F') ≠ 0)
    {l : List ℤ} (hl : l ∈ r.orbit) :
    pair (toVec n l) z = 0 ↔
      peval cl.A ρ * pair (toVec n β₁) z + peval cl.B ρ * pair (toVec n β₂) z = 0 := by
  have horb : r.orbit = lorbit n W r.rep m := by
    simp only [LineRow.check, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact hr.2
  rw [horb, lorbit, List.mem_map] at hl
  obtain ⟨k, -, rfl⟩ := hl
  rw [toVec_lmulVec, toMat_lpow, pair_pow_mulVec hz]
  rw [← lineRow_pair_eq_zero_iff hr hcl hz hΦ hF hd hdcl]
  constructor
  · intro h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero k hρ)
  · intro h
    rw [h, mul_zero]

theorem rootKernel_eq_of_lines {τ : Tag} {W F : List (List ℤ)}
    {β₁ β₂ Φ : List ℤ} {m : ℕ}
    (rows : List LineRow) (classes : List LineClass) (crosses : List CrossCert)
    (S0 : List (List ℤ))
    (hrows : ∀ r ∈ rows, r.check τ.rank W F β₁ β₂ Φ m (classes.getD r.cls default) = true)
    (hcls : ∀ r ∈ rows, r.cls < classes.length)
    (hclasses : ∀ c ∈ classes, c.check Φ = true)
    (hcross : ∀ i j, i < classes.length → j < classes.length → i ≠ j →
      ∃ c ∈ crosses, (c.i = i ∧ c.j = j) ∨ (c.i = j ∧ c.j = i))
    (hcrosschk : ∀ c ∈ crosses, c.check Φ classes = true)
    (hcover : ∀ l ∈ τ.artifactRoots, l ∈ S0 ∨ ∃ r ∈ rows, l ∈ r.orbit)
    (hS0 : ∀ l ∈ S0, l ∈ τ.artifactRoots)
    (horb : ∀ r ∈ rows, ∀ l ∈ r.orbit, l ∈ τ.artifactRoots)
    {z : Fin τ.rank → F'} {ρ : F'}
    (hz : ((toMat τ.rank W).map (Int.cast : ℤ → F'))ᵀ *ᵥ z = ρ • z) (hρ : ρ ≠ 0)
    (hΦ : peval Φ ρ = 0) (hF : ∀ x ∈ F, pair (toVec τ.rank x) z = 0)
    (hS0z : ∀ l ∈ S0, pair (toVec τ.rank l) z = 0)
    (hst : ¬ (pair (toVec τ.rank β₁) z = 0 ∧ pair (toVec τ.rank β₂) z = 0))
    (hdrow : ∀ r ∈ rows, (r.d : F') ≠ 0) (hdcl : ∀ c ∈ classes, (c.d : F') ≠ 0)
    (hdcross : ∀ c ∈ crosses, (c.d : F') ≠ 0) :
    ({α | IsRoot τ α ∧ pair α z = 0} = {α | ∃ l ∈ S0, α = toVec τ.rank l}) ∨
      ∃ j < classes.length, {α | IsRoot τ α ∧ pair α z = 0} =
        {α | ∃ l ∈ S0, α = toVec τ.rank l} ∪
          {α | ∃ l ∈ lineClassRoots rows j, α = toVec τ.rank l} := by
  set s := pair (toVec τ.rank β₁) z with hs
  set t := pair (toVec τ.rank β₂) z with ht
  set κ : ℕ → F' := fun j => peval (classes.getD j default).A ρ * s +
    peval (classes.getD j default).B ρ * t with hκ
  have hclsmem : ∀ j < classes.length, classes.getD j default ∈ classes := fun j hj => by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hzero : ∀ r ∈ rows, ∀ l ∈ r.orbit, pair (toVec τ.rank l) z = 0 ↔ κ r.cls = 0 :=
    fun r hr l hl => pair_orbit_eq_zero_iff (hrows r hr)
      (hclasses _ (hclsmem _ (hcls r hr))) hz hρ hΦ hF (hdrow r hr)
      (hdcl _ (hclsmem _ (hcls r hr))) hl
  have huniq : ∀ i j, i < classes.length → j < classes.length → κ i = 0 → κ j = 0 → i = j := by
    intro i j hi hj hki hkj
    by_contra hij
    obtain ⟨c, hc, hcij⟩ := hcross i j hi hj hij
    have hu := crossCert_unit (hcrosschk c hc) hΦ
    have hu' : ∃ u : F', u * (peval (classes.getD i default).A ρ *
        peval (classes.getD j default).B ρ - peval (classes.getD j default).A ρ *
          peval (classes.getD i default).B ρ) = (c.d : F') ∨
        u * (peval (classes.getD j default).A ρ * peval (classes.getD i default).B ρ -
          peval (classes.getD i default).A ρ * peval (classes.getD j default).B ρ) =
            (c.d : F') := by
      rcases hcij with ⟨hci, hcj⟩ | ⟨hcj, hci⟩
      · rw [hci, hcj] at hu
        exact ⟨_, Or.inl hu⟩
      · rw [hci, hcj] at hu
        exact ⟨_, Or.inr hu⟩
    obtain ⟨uu, hu⟩ := hu'
    set Ai := peval (classes.getD i default).A ρ
    set Bi := peval (classes.getD i default).B ρ
    set Aj := peval (classes.getD j default).A ρ
    set Bj := peval (classes.getD j default).B ρ
    have hCs : (Ai * Bj - Aj * Bi) * s = 0 := by
      have h1 : Ai * s = -(Bi * t) := by
        have : Ai * s + Bi * t = 0 := hki
        linear_combination this
      have h2 : Aj * s = -(Bj * t) := by
        have : Aj * s + Bj * t = 0 := hkj
        linear_combination this
      linear_combination Bj * h1 - Bi * h2
    have hCt : (Ai * Bj - Aj * Bi) * t = 0 := by
      have h1 : Bi * t = -(Ai * s) := by
        have : Ai * s + Bi * t = 0 := hki
        linear_combination this
      have h2 : Bj * t = -(Aj * s) := by
        have : Aj * s + Bj * t = 0 := hkj
        linear_combination this
      linear_combination (-Aj) * h1 + Ai * h2
    have hCne : Ai * Bj - Aj * Bi ≠ 0 := by
      intro h0
      rcases hu with hu | hu
      · rw [h0, mul_zero] at hu
        exact hdcross c hc hu.symm
      · have h1 : Aj * Bi - Ai * Bj = 0 := by linear_combination -h0
        rw [h1, mul_zero] at hu
        exact hdcross c hc hu.symm
    exact hst ⟨(mul_eq_zero.1 hCs).resolve_left hCne, (mul_eq_zero.1 hCt).resolve_left hCne⟩
  have hker : ∀ α, (IsRoot τ α ∧ pair α z = 0) ↔
      ((∃ l ∈ S0, α = toVec τ.rank l) ∨
        ∃ r ∈ rows, ∃ l ∈ r.orbit, α = toVec τ.rank l ∧ κ r.cls = 0) := by
    intro α
    constructor
    · rintro ⟨hα, h0⟩
      obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
      rcases hcover l hl with hS | ⟨r, hr, hlr⟩
      · exact Or.inl ⟨l, hS, rfl⟩
      · exact Or.inr ⟨r, hr, l, hlr, rfl, (hzero r hr l hlr).1 h0⟩
    · rintro (⟨l, hl, rfl⟩ | ⟨r, hr, l, hlr, rfl, hk⟩)
      · exact ⟨isRoot_toVec (hS0 l hl), hS0z l hl⟩
      · exact ⟨isRoot_toVec (horb r hr l hlr), (hzero r hr l hlr).2 hk⟩
  by_cases hex : ∃ j < classes.length, κ j = 0
  · right
    obtain ⟨j, hj, hkj⟩ := hex
    refine ⟨j, hj, ?_⟩
    ext α
    rw [Set.mem_ofPred_eq, hker]
    simp only [Set.mem_union, Set.mem_ofPred_eq, mem_lineClassRoots]
    constructor
    · rintro (h | ⟨r, hr, l, hlr, hα, hk⟩)
      · exact Or.inl h
      · refine Or.inr ⟨l, ⟨r, hr, ?_, hlr⟩, hα⟩
        exact huniq _ _ (hcls r hr) hj hk hkj
    · rintro (h | ⟨l, ⟨r, hr, hrj, hlr⟩, hα⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r, hr, l, hlr, hα, by rw [hrj]; exact hkj⟩
  · left
    push Not at hex
    ext α
    rw [Set.mem_ofPred_eq, hker]
    constructor
    · rintro (h | ⟨r, hr, l, hlr, hα, hk⟩)
      · exact h
      · exact absurd hk (hex _ (hcls r hr))
    · intro h
      exact Or.inl h

end CFSG.RankThree.PartOne.KE

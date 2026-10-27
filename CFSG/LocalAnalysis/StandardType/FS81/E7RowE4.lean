module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowE3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

local notation:max "↑ₘ" g:max => ((g : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))

variable {X : Subgroup (GL (Fin 8) (ZMod 3))} {δ : ZMod 3}

structure E8Data (X : Subgroup (GL (Fin 8) (ZMod 3))) (δ : ZMod 3) : Prop where
  core : CoreHyp X
  hδ : δ = 1 ∨ δ = -1
  horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v
  t0 : ∃ t ∈ X, ↑ₘt = t0M
  root : ∃ g ∈ X, IsRoot7 δ (↑ₘg *ᵥ Pi.single 0 1)

@[expose] def Phi (X : Subgroup (GL (Fin 8) (ZMod 3))) : Set (Coords 8) :=
  {v | ∃ y ∈ X, ↑ₘy *ᵥ Pi.single 0 1 = v}

theorem e0_mem_phi : (Pi.single 0 1 : Coords 8) ∈ Phi X :=
  ⟨1, X.one_mem, by rw [Units.val_one, Matrix.one_mulVec]⟩

theorem phi_mul {x : GL (Fin 8) (ZMod 3)} (hx : x ∈ X) {v : Coords 8} (hv : v ∈ Phi X) :
    ↑ₘx *ᵥ v ∈ Phi X := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨x * y, X.mul_mem hx hy, mulVec_gmul x y _⟩

namespace E8Data

variable (D : E8Data X δ)
include D

theorem iso {x : GL (Fin 8) (ZMod 3)} (hx : x ∈ X) (u w : Coords 8) :
    b8 (↑ₘx *ᵥ u) (↑ₘx *ᵥ w) = b8 u w := by
  obtain ⟨t, ht, htM⟩ := D.t0
  obtain ⟨g, hg, hgr⟩ := D.root
  exact X_b8 D.core D.hδ D.horb ht htM hg hgr hx u w

theorem phi_reflM {v : Coords 8} (hv : v ∈ Phi X) : (∃ m ∈ X, ↑ₘm = reflM v) ∧ b8 v v = 1 := by
  obtain ⟨t, ht, htM⟩ := D.t0
  obtain ⟨g, hg, hgr⟩ := D.root
  obtain ⟨y, hy, rfl⟩ := hv
  obtain ⟨e1, e2⟩ := conj_t0_eq_reflM D.core D.hδ D.horb ht htM hg hgr hy
  exact ⟨⟨y * t * y⁻¹, X.mul_mem (X.mul_mem hy ht) (X.inv_mem hy), e1⟩, e2⟩

theorem phi_neg {v : Coords 8} (hv : v ∈ Phi X) : -v ∈ Phi X := by
  obtain ⟨t, ht, htM⟩ := D.t0
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨y * t, X.mul_mem hy ht, by rw [mulVec_gmul, htM, t0M_e0, Matrix.mulVec_neg]⟩

theorem phi_root {r : Coords 8} (hr : IsRoot7 δ r) : r ∈ Phi X := by
  obtain ⟨g, hg, hgr⟩ := D.root
  obtain ⟨y, hy, hye⟩ := root_orbit D.horb hg hgr hr
  exact ⟨y, hy, hye⟩

theorem phi_zero {v : Coords 8} (hv : v ∈ Phi X) (hv0 : v 0 = 0) : IsRoot7 δ v := by
  obtain ⟨t, ht, htM⟩ := D.t0
  obtain ⟨y, hy, rfl⟩ := hv
  exact (conj_t0_of_zero D.core D.hδ D.horb ht htM hy hv0).1

end E8Data

@[expose] def mixS (X : Subgroup (GL (Fin 8) (ZMod 3))) : Set (Coords 8) :=
  {u | u 0 = 0 ∧ u ≠ 0 ∧ Pi.single 0 1 + u ∈ Phi X}

@[expose] def M56 (δ : ZMod 3) (u : Coords 8) : Prop :=
  u 0 = 0 ∧ (nf u = cand 9 ∨ nf u = cvec 0 6 (-δ))

instance (δ : ZMod 3) (u : Coords 8) : Decidable (M56 δ u) := by
  unfold M56
  infer_instance

@[expose] def reflMe (r w : Coords 8) : Coords 8 := w + b8e w r • r

theorem reflM_mulVec_e (r w : Coords 8) : reflM r *ᵥ w = reflMe r w := by
  rw [reflM_mulVec, b8_eq_b8e, reflMe]

theorem b8_e0_right (w : Coords 8) : b8 w (Pi.single 0 1) = w 0 := by
  rw [b8_comm, b8_e0_left]

set_option maxRecDepth 100000 in
theorem iso_classes : ∀ u : Coords 8, u 0 = 0 → u ≠ 0 → b8e u u = 0 →
    nf u = cand 3 ∨ nf u = cand 12 ∨ nf u = cand 9 ∨ nf u = cvec 0 6 1 ∨ nf u = cvec 0 6 (-1) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem excl_facts (hδ : δ = 1 ∨ δ = -1) :
    nf ![0, 0, 0, 0, -1, 0, 1, 1] = cand 3 ∧ b8e (cand 3) ![0, 0, 0, 0, -1, 0, 1, 1] = 1 ∧
      ¬ IsRoot7 δ (![0, 0, 0, 0, -1, 0, 1, 1] - cand 3) ∧
    nf ![0, 1, 0, 0, 1, -1, 1, 1] = cand 12 ∧ b8e (cand 12) ![0, 1, 0, 0, 1, -1, 1, 1] = 1 ∧
      ¬ IsRoot7 δ (![0, 1, 0, 0, 1, -1, 1, 1] - cand 12) ∧
    IsRoot7 δ ![0, 1, 1, 1, 1, 1, -1, -δ] ∧
      nf (reflMe ![0, 1, 1, 1, 1, 1, -1, -δ] (cvec 0 6 δ)) = cand 12 ∧
    IsRoot7 δ ![0, 1, -1, 1, 1, 1, 1, -δ] ∧
      nf (reflMe ![0, 1, -1, 1, 1, 1, 1, -δ] (cand 9)) = cvec 0 6 (-δ) ∧
      cvec 0 6 δ 0 = 0 ∧ cand 9 0 = 0 ∧ cvec 0 6 (-δ) 0 = 0 ∧ cand 3 0 = 0 ∧ cand 12 0 = 0 := by
  rcases hδ with rfl | rfl <;> decide +kernel

namespace E8Data

variable (D : E8Data X δ)
include D

theorem mixS_b8 {u : Coords 8} (hu : u ∈ mixS X) : b8 u u = 0 := by
  obtain ⟨hu0, -, hu⟩ := hu
  have e := (D.phi_reflM hu).2
  rw [b8_add_left, b8_add_right, b8_add_right, b8_e0_left, b8_e0_left, Pi.single_eq_same,
    b8_e0_right, hu0, add_zero, zero_add] at e
  have k : ∀ x : ZMod 3, 1 + x = 1 → x = 0 := by decide
  exact k _ e

theorem mixS_X1 {x : GL (Fin 8) (ZMod 3)} (hx : x ∈ X ⊓ fixE0 7) {u : Coords 8} (hu : u ∈ mixS X) :
    ↑ₘx *ᵥ u ∈ mixS X := by
  obtain ⟨hu0, hune, hu⟩ := hu
  refine ⟨D.core.hA x hx.1 (mem_fixE0.mp hx.2) u hu0, fun e => hune ?_, ?_⟩
  · have := mulVec_inv_mulVec x u
    rw [e, Matrix.mulVec_zero] at this
    exact this.symm
  · have := phi_mul hx.1 hu
    rwa [Matrix.mulVec_add, mem_fixE0.mp hx.2] at this

theorem mixS_nf (u : Coords 8) : u ∈ mixS X ↔ nf u ∈ mixS X := by
  apply mem_iff_nf_mem
  intro g hg v hv
  obtain ⟨x, hx, hxA⟩ := D.core.exists_fix (Gen.mat_mem hg)
  rw [← Gen.mat_mulVec, ← hxA]
  exact D.mixS_X1 hx hv

theorem mixS_diff {u u' : Coords 8} (hu : u ∈ mixS X) (hu' : u' ∈ mixS X) (h1 : b8 u u' = 1) :
    IsRoot7 δ (u' - u) := by
  obtain ⟨⟨m, hm, hmr⟩, -⟩ := D.phi_reflM hu.2.2
  have hmem := phi_mul hm hu'.2.2
  rw [hmr, reflM_mulVec, b8_add_left, b8_add_right, b8_add_right, b8_e0_left, b8_e0_left,
    Pi.single_eq_same, b8_e0_right, hu.1, hu'.1, b8_comm u' u, h1] at hmem
  obtain ⟨c, hc, hmem'⟩ : ∃ c : ZMod 3, c = -1 ∧
      Pi.single 0 1 + u' + c • (Pi.single 0 1 + u) ∈ Phi X := ⟨_, by decide, hmem⟩
  rw [hc, neg_one_smul, show (Pi.single 0 1 + u' + -(Pi.single 0 1 + u) : Coords 8) = u' - u by
    abel] at hmem'
  apply D.phi_zero hmem'
  simp [hu.1, hu'.1]

theorem cand3_not : cand 3 ∉ mixS X := by
  intro h3
  obtain ⟨n3, b3, r3, -, -, -, -, -, -, -, -, -, -, -, -⟩ := excl_facts D.hδ
  have hw : (![0, 0, 0, 0, -1, 0, 1, 1] : Coords 8) ∈ mixS X := by
    rw [D.mixS_nf, n3, ← (nf_cand 3).1, ← D.mixS_nf]
    exact h3
  exact r3 (D.mixS_diff h3 hw (by rw [b8_eq_b8e]; exact b3))

theorem cand12_not : cand 12 ∉ mixS X := by
  intro h12
  obtain ⟨-, -, -, n12, b12, r12, -, -, -, -, -, -, -, -, -⟩ := excl_facts D.hδ
  have hw : (![0, 1, 0, 0, 1, -1, 1, 1] : Coords 8) ∈ mixS X := by
    rw [D.mixS_nf, n12, ← (nf_cand 12).1, ← D.mixS_nf]
    exact h12
  exact r12 (D.mixS_diff h12 hw (by rw [b8_eq_b8e]; exact b12))

theorem cvec_not : cvec 0 6 δ ∉ mixS X := by
  intro hc
  obtain ⟨-, -, -, -, -, -, rr, nr, -, -, -, -, -, -, -⟩ := excl_facts D.hδ
  obtain ⟨m, hm, hmr⟩ := exists_reflM_mem D.core D.hδ D.horb rr
  have := D.mixS_X1 hm hc
  rw [hmr, reflM_mulVec_e, D.mixS_nf, nr] at this
  exact D.cand12_not this

theorem mixS_sub {u : Coords 8} (hu : u ∈ mixS X) : M56 δ u := by
  refine ⟨hu.1, ?_⟩
  have hq := D.mixS_b8 hu
  rw [b8_eq_b8e] at hq
  rcases iso_classes u hu.1 hu.2.1 hq with h | h | h | h | h
  · exact absurd ((D.mixS_nf u).mp hu) (h ▸ D.cand3_not)
  · exact absurd ((D.mixS_nf u).mp hu) (h ▸ D.cand12_not)
  · exact Or.inl h
  · rcases D.hδ with rfl | rfl
    · exact absurd ((D.mixS_nf u).mp hu) (h ▸ D.cvec_not)
    · right
      rw [h]
      rfl
  · rcases D.hδ with rfl | rfl
    · right
      exact h
    · exact absurd ((D.mixS_nf u).mp hu) (h ▸ D.cvec_not)

theorem mixS_nonempty : ∃ u, u ∈ mixS X := by
  obtain ⟨r1, -, rf, -⟩ := root7_facts D.hδ
  obtain ⟨z, hz, hze⟩ := D.phi_root r1
  obtain ⟨yf, hyf, hyfe⟩ := D.phi_root rf
  have hz0 : ↑ₘ(z⁻¹) *ᵥ Pi.single 1 1 = Pi.single 0 1 := by
    rw [← hze, mulVec_inv_mulVec]
  have hw0 : (↑ₘ(z⁻¹) *ᵥ fRoot δ) 0 = 1 := by
    rw [← b8_e0_left (↑ₘ(z⁻¹) *ᵥ fRoot δ), ← hz0, D.iso (X.inv_mem hz), b8_comm, b8_single]
    simp [fRoot]
  refine ⟨↑ₘ(z⁻¹) *ᵥ fRoot δ - Pi.single 0 1, ?_, ?_, ?_⟩
  · rw [Pi.sub_apply, hw0, Pi.single_eq_same, sub_self]
  · intro e
    have hw : ↑ₘ(z⁻¹) *ᵥ fRoot δ = Pi.single 0 1 := sub_eq_zero.mp e
    have := congrArg (fun v => ↑ₘz *ᵥ v) hw
    simp only [mulVec_mulVec_inv, hze] at this
    have := congrFun this 2
    simp [fRoot] at this
  · rw [show (Pi.single 0 1 + (↑ₘ(z⁻¹) *ᵥ fRoot δ - Pi.single 0 1) : Coords 8) =
      ↑ₘ(z⁻¹) *ᵥ fRoot δ by abel]
    exact ⟨z⁻¹ * yf, X.mul_mem (X.inv_mem hz) hyf, by rw [mulVec_gmul, hyfe]⟩

theorem M56_sub {u : Coords 8} (hu : M56 δ u) : u ∈ mixS X := by
  obtain ⟨-, -, -, -, -, -, -, -, rr9, nr9, -, -, -, -, -⟩ := excl_facts D.hδ
  obtain ⟨m, hm, hmr⟩ := exists_reflM_mem D.core D.hδ D.horb rr9
  have hinv : ∀ w : Coords 8, ↑ₘm *ᵥ (↑ₘm *ᵥ w) = w := by
    intro w
    rw [hmr, Matrix.mulVec_mulVec, reflM_mul_self (root7_b8 D.hδ rr9), Matrix.one_mulVec]
  obtain ⟨u₀, hu₀⟩ := D.mixS_nonempty
  have h9 : cand 9 ∈ mixS X ∧ cvec 0 6 (-δ) ∈ mixS X := by
    rcases (D.mixS_sub hu₀).2 with h | h
    · have c9 : cand 9 ∈ mixS X := by
        rw [← h]
        exact (D.mixS_nf u₀).mp hu₀
      refine ⟨c9, ?_⟩
      have := D.mixS_X1 hm c9
      rwa [D.mixS_nf, hmr, reflM_mulVec_e, nr9] at this
    · have cc : cvec 0 6 (-δ) ∈ mixS X := by
        rw [← h]
        exact (D.mixS_nf u₀).mp hu₀
      refine ⟨?_, cc⟩
      have hv : ↑ₘm *ᵥ cand 9 ∈ mixS X := by
        rw [D.mixS_nf, hmr, reflM_mulVec_e, nr9]
        exact cc
      have := D.mixS_X1 hm hv
      rwa [hinv] at this
  rw [D.mixS_nf]
  rcases hu.2 with h | h
  · rw [h]
    exact h9.1
  · rw [h]
    exact h9.2

end E8Data

@[expose] def PhiPred (δ : ZMod 3) (v : Coords 8) : Prop :=
  v = Pi.single 0 1 ∨ v = -Pi.single 0 1 ∨ IsRoot7 δ v ∨ (v 0 = 1 ∧ M56 δ (v - Pi.single 0 1)) ∨
    (v 0 = -1 ∧ M56 δ (-v - Pi.single 0 1))

instance (δ : ZMod 3) (v : Coords 8) : Decidable (PhiPred δ v) := by
  unfold PhiPred
  infer_instance

@[expose] def wtE (e : Coords 8) : ℕ :=
  (if e 0 = 0 then 0 else 1) + (if e 1 = 0 then 0 else 1) + (if e 2 = 0 then 0 else 1) +
    (if e 3 = 0 then 0 else 1) + (if e 4 = 0 then 0 else 1) + (if e 5 = 0 then 0 else 1) +
    (if e 6 = 0 then 0 else 1) + (if e 7 = 0 then 0 else 1)

theorem wt_eq_wtE (e : Coords 8) : wt e = wtE e := by
  rw [wt, Finset.card_filter, Fin.sum_univ_eight]
  simp only [wtE, ne_eq, ite_not]

theorem prod_eq_prodF (e : Coords 8) : ∏ i : Fin 6, e i.succ.succ = prodF e := by
  rw [Fin.prod_univ_six, prodF]
  rfl

@[expose] def E8e (δ : ZMod 3) (e : Coords 8) : Prop :=
  (wtE e = 1 ∧ (e 0 ≠ 0 ∨ e 1 ≠ 0)) ∨ (wtE e = 2 ∧ e 0 = 0 ∧ e 1 = 0) ∨
    (wtE e = 3 ∧ e 0 ≠ 0 ∧ e 1 ≠ 0) ∨ (wtE e = 7 ∧ e 0 = 0 ∧ prodF e = δ) ∨
    (wtE e = 7 ∧ e 1 = 0 ∧ prodF e = -δ)

instance (δ : ZMod 3) (e : Coords 8) : Decidable (E8e δ e) := by
  unfold E8e
  infer_instance

theorem e8RootLine_iff (δ : ZMod 3) (e : Coords 8) : E8RootLine δ e ↔ E8e δ e := by
  rw [E8RootLine, E8e, wt_eq_wtE, prod_eq_prodF]
  exact Iff.rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem phiPred_iff_e8e (hδ : δ = 1 ∨ δ = -1) :
    ∀ v : Coords 8, v ≠ 0 → (PhiPred δ v ↔ E8e δ v) := by
  rcases hδ with rfl | rfl <;> decide +kernel

theorem phiPred_iff_e8 (hδ : δ = 1 ∨ δ = -1) {v : Coords 8} (hv : v ≠ 0) :
    PhiPred δ v ↔ E8RootLine δ v := by
  rw [e8RootLine_iff, phiPred_iff_e8e hδ v hv]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem card_phiPred (hδ : δ = 1 ∨ δ = -1) : (Finset.univ.filter (PhiPred δ)).card = 240 := by
  rcases hδ with rfl | rfl <;> decide +kernel

namespace E8Data

variable (D : E8Data X δ)
include D

theorem phi_iff (v : Coords 8) : v ∈ Phi X ↔ PhiPred δ v := by
  have k : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide
  constructor
  · intro hv
    by_cases h0 : v 0 = 0
    · exact Or.inr (Or.inr (Or.inl (D.phi_zero hv h0)))
    rcases k _ h0 with h1 | h1
    · by_cases he : v = Pi.single 0 1
      · exact Or.inl he
      · refine Or.inr (Or.inr (Or.inr (Or.inl
          ⟨h1, D.mixS_sub ⟨by simp [h1], sub_ne_zero.mpr he, ?_⟩⟩)))
        rw [show (Pi.single 0 1 + (v - Pi.single 0 1) : Coords 8) = v by abel]
        exact hv
    · by_cases he : v = -Pi.single 0 1
      · exact Or.inr (Or.inl he)
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, D.mixS_sub ⟨by simp [h1], fun e => he ?_, ?_⟩⟩)))
        · rw [sub_eq_zero] at e
          rw [← e, neg_neg]
        · rw [show (Pi.single 0 1 + (-v - Pi.single 0 1) : Coords 8) = -v by abel]
          exact D.phi_neg hv
  · rintro (h | h | h | ⟨-, h⟩ | ⟨-, h⟩)
    · rw [h]
      exact e0_mem_phi
    · rw [h]
      exact D.phi_neg e0_mem_phi
    · exact D.phi_root h
    · have := (D.M56_sub h).2.2
      rwa [show (Pi.single 0 1 + (v - Pi.single 0 1) : Coords 8) = v by abel] at this
    · have := D.phi_neg (D.M56_sub h).2.2
      rwa [show (-(Pi.single 0 1 + (-v - Pi.single 0 1)) : Coords 8) = v by abel] at this

theorem phi_iff_e8RootLine {v : Coords 8} (hv : v ≠ 0) : v ∈ Phi X ↔ E8RootLine δ v := by
  rw [D.phi_iff, phiPred_iff_e8 D.hδ hv]

attribute [local instance] glAct in
theorem card_X : Nat.card X = 696729600 := by
  have horb : MulAction.orbit ↥X (Pi.single 0 1 : Coords 8) = Phi X := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hncard : (Phi X).ncard = 240 := by
    have : Phi X = ↑(Finset.univ.filter (PhiPred δ)) := by
      ext v
      simp [D.phi_iff]
    rw [this, Set.ncard_coe_finset, card_phiPred D.hδ]
  have hstab : Nat.card ↥(MulAction.stabilizer ↥X (Pi.single 0 1 : Coords 8)) = 2903040 := by
    rw [← D.core.hcard]
    have hmem : ∀ x : ↥(MulAction.stabilizer ↥X (Pi.single 0 1 : Coords 8)),
        ((x : ↥X) : GL (Fin 8) (ZMod 3)) ∈ X ⊓ fixE0 7 := by
      rintro ⟨⟨x, hxX⟩, hx⟩
      exact ⟨hxX, mem_fixE0.mpr hx⟩
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨_, hmem x⟩) ⟨?_, ?_⟩)
    · intro a b e
      have e' := congrArg (fun y : ↥(X ⊓ fixE0 7) => (y : GL (Fin 8) (ZMod 3))) e
      exact Subtype.ext (Subtype.ext e')
    · rintro ⟨x, hxX, hxF⟩
      exact ⟨⟨⟨x, hxX⟩, mem_fixE0.mp hxF⟩, rfl⟩
  have hidx := MulAction.index_stabilizer ↥X (Pi.single 0 1 : Coords 8)
  have hmul := Subgroup.index_mul_card (MulAction.stabilizer ↥X (Pi.single 0 1 : Coords 8))
  rw [hidx, horb, hncard, hstab] at hmul
  omega

end E8Data

end CFSG.StandardType.FrameRoute.FS81.E7Row

end

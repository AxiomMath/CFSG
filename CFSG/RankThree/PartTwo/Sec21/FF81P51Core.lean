module

public import CFSG.RankThree.PartTwo.Sec21.FF81P51Checks
public import CFSG.RankThree.PartTwo.Sec21.FF81P51Classify
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51


open Matrix

abbrev GL4 := Matrix.GeneralLinearGroup (Fin 4) (ZMod 3)

structure Hyp (Γ : Subgroup GL4) : Prop where
  t0 : ∃ g ∈ Γ, (g : Mat) = T0
  s1 : ∃ g ∈ Γ, (g : Mat) = S1
  tau : ∃ g ∈ Γ, (g : Mat) = Tau
  cyc : ∃ g ∈ Γ, (g : Mat) = Cyc
  stab : ∀ g ∈ Γ, ((g : Mat) *ᵥ e 0 = e 0 ∨ (g : Mat) *ᵥ e 0 = -e 0) →
    (g : Mat) *ᵥ e 1 ∈ SU ∧ (g : Mat) *ᵥ e 2 ∈ SU ∧ (g : Mat) *ᵥ e 3 ∈ SU
  meet : ∃ g ∈ Γ, ((g : Mat) *ᵥ e 0) 0 = 0

variable {Γ : Subgroup GL4}

def GM (Γ : Subgroup GL4) : Submonoid Mat := Γ.toSubmonoid.map (Units.coeHom Mat)

theorem mem_GM {A : Mat} : A ∈ GM Γ ↔ ∃ g ∈ Γ, (g : Mat) = A := by
  simp [GM]

theorem coe_mem_GM {g : GL4} (hg : g ∈ Γ) : (g : Mat) ∈ GM Γ := mem_GM.2 ⟨g, hg, rfl⟩

def Om (Γ : Subgroup GL4) : Set V := {v | ∃ g ∈ Γ, (g : Mat) *ᵥ e 0 = v}

theorem mulVec_inj (g : GL4) {v w : V} (h : (g : Mat) *ᵥ v = (g : Mat) *ᵥ w) : v = w := by
  have := congrArg (((g⁻¹ : GL4) : Mat) *ᵥ ·) h
  simpa [Matrix.mulVec_mulVec] using this

theorem ne_zero_of_mem_Om {v : V} (hv : v ∈ Om Γ) : v ≠ 0 := by
  obtain ⟨g, -, rfl⟩ := hv
  intro h
  exact e0_ne_zero (mulVec_inj g (by rw [h, Matrix.mulVec_zero]))

theorem e0_mem_Om : e 0 ∈ Om Γ := ⟨1, Γ.one_mem, by simp⟩

theorem mulVec_mem_Om {A : Mat} (hA : A ∈ GM Γ) {v : V} (hv : v ∈ Om Γ) : A *ᵥ v ∈ Om Γ := by
  obtain ⟨k, hk, rfl⟩ := mem_GM.1 hA
  obtain ⟨g, hg, rfl⟩ := hv
  exact ⟨k * g, Γ.mul_mem hk hg, by simp [Matrix.mulVec_mulVec]⟩

theorem H0L_sub (h : Hyp Γ) : ∀ A ∈ H0L, A ∈ GM Γ := by
  have hmm : ∀ {b c : M16}, b.toM ∈ GM Γ → c.toM ∈ GM Γ → (M16.mul b c).toM ∈ GM Γ :=
    fun hb hc => by rw [M16.toM_mul]; exact Submonoid.mul_mem _ hb hc
  have hpow : ∀ {b : M16}, b.toM ∈ GM Γ → ∀ k, (M16.pow b k).toM ∈ GM Γ := fun hb k => by
    rw [M16.toM_pow]; exact Submonoid.pow_mem _ hb _
  have gT0 : T0D.toM ∈ GM Γ := T0_eqD ▸ mem_GM.2 h.t0
  have gS1 : S1D.toM ∈ GM Γ := S1_eqD ▸ mem_GM.2 h.s1
  have gTau : TauD.toM ∈ GM Γ := Tau_eqD ▸ mem_GM.2 h.tau
  have gCyc : CycD.toM ∈ GM Γ := Cyc_eqD ▸ mem_GM.2 h.cyc
  have g2 : X2D.toM ∈ GM Γ := hmm (hmm gTau gS1) gTau
  have g3 : X3D.toM ∈ GM Γ := hmm (hmm gCyc g2) (hmm gCyc gCyc)
  intro A hA
  rw [H0L_eq, List.mem_map] at hA
  obtain ⟨a, ha, rfl⟩ := hA
  have ha := H0D_sub_H0WD a ha
  simp only [H0WD, List.mem_flatMap, List.mem_map] at ha
  obtain ⟨a₀, -, a₁, -, a₂, -, a₃, -, p, hp, rfl⟩ := ha
  refine hmm (hmm (hmm (hmm (hpow gT0 _) (hpow gS1 _)) (hpow g2 _)) (hpow g3 _)) ?_
  simp only [permWD, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [M16.toM_one]; exact Submonoid.one_mem _
  · exact gTau
  · exact gCyc
  · exact hmm gCyc gCyc
  · exact hmm gTau gCyc
  · exact hmm gTau (hmm gCyc gCyc)

theorem ofCols_cols (A : Mat) : ofCols ![A *ᵥ e 0, A *ᵥ e 1, A *ᵥ e 2, A *ᵥ e 3] = A := by
  ext i j
  fin_cases j <;> simp [ofCols, e, Matrix.mulVec_single_one]

theorem mem_H0L_of {g : GL4} (h0 : (g : Mat) *ᵥ e 0 = e 0 ∨ (g : Mat) *ᵥ e 0 = -e 0)
    (h1 : (g : Mat) *ᵥ e 1 ∈ SU) (h2 : (g : Mat) *ᵥ e 2 ∈ SU) (h3 : (g : Mat) *ᵥ e 3 ∈ SU) :
    (g : Mat) ∈ H0L := by
  have h0' : (g : Mat) *ᵥ e 0 ∈ E0L := by rcases h0 with h0 | h0 <;> simp [E0L, h0]
  have key : ∀ i j : Fin 4, i ≠ j → (g : Mat) *ᵥ e i ≠ (g : Mat) *ᵥ e j ∧
      (g : Mat) *ᵥ e i ≠ -((g : Mat) *ᵥ e j) := fun i j hij => by
    refine ⟨fun hh => (e_ne i j hij).1 (mulVec_inj g hh), fun hh => (e_ne i j hij).2 ?_⟩
    exact mulVec_inj g (by rw [hh, Matrix.mulVec_neg])
  rcases H0L_cols _ h0' _ h1 _ h2 _ h3 with hm | hc | hc | hc | hc | hc | hc
  · rwa [ofCols_cols] at hm
  · exact absurd hc (key 1 2 (by decide)).1
  · exact absurd hc (key 1 2 (by decide)).2
  · exact absurd hc (key 1 3 (by decide)).1
  · exact absurd hc (key 1 3 (by decide)).2
  · exact absurd hc (key 2 3 (by decide)).1
  · exact absurd hc (key 2 3 (by decide)).2

theorem stab_H0L (h : Hyp Γ) {g : GL4} (hg : g ∈ Γ)
    (h0 : (g : Mat) *ᵥ e 0 = e 0 ∨ (g : Mat) *ᵥ e 0 = -e 0) : (g : Mat) ∈ H0L := by
  obtain ⟨h1, h2, h3⟩ := h.stab g hg h0
  exact mem_H0L_of h0 h1 h2 h3

theorem stab_comm (h : Hyp Γ) {g : GL4} (hg : g ∈ Γ)
    (h0 : (g : Mat) *ᵥ e 0 = e 0 ∨ (g : Mat) *ᵥ e 0 = -e 0) : (g : Mat) * T0 = T0 * g := by
  have := H0L_comm_T0 _ (stab_H0L h hg h0)
  rwa [mm_eq, mm_eq] at this

theorem inv_eq_transpose {k : GL4} (hk : (k : Mat) ∈ H0L) : ((k⁻¹ : GL4) : Mat) = (k : Mat)ᵀ := by
  have h1 := (H0L_transpose _ hk).1
  rw [mm_eq] at h1
  calc ((k⁻¹ : GL4) : Mat) = ((k⁻¹ : GL4) : Mat) * ((k : Mat) * (k : Mat)ᵀ) := by rw [h1, mul_one]
    _ = (k : Mat)ᵀ := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem conj_T0 (g : GL4) :
    (g : Mat) * T0 * ((g⁻¹ : GL4) : Mat) =
      1 + vecMulVec ((g : Mat) *ᵥ e 0) (e 0 ᵥ* ((g⁻¹ : GL4) : Mat)) := by
  rw [T0_eq, mul_add, mul_one, add_mul, Units.mul_inv, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

def Real (Γ : Subgroup GL4) (v ψ : V) : Prop :=
  ∃ g ∈ Γ, (g : Mat) *ᵥ e 0 = v ∧ e 0 ᵥ* ((g⁻¹ : GL4) : Mat) = ψ

theorem real_of_mem {v : V} (hv : v ∈ Om Γ) : ∃ ψ, Real Γ v ψ := by
  obtain ⟨g, hg, rfl⟩ := hv
  exact ⟨_, g, hg, rfl, rfl⟩

theorem mem_of_real {v ψ : V} (h : Real Γ v ψ) : v ∈ Om Γ := by
  obtain ⟨g, hg, rfl, -⟩ := h
  exact ⟨g, hg, rfl⟩

theorem vecMulVec_cancel {v ψ ψ' : V} (hv : v ≠ 0) (h : vecMulVec v ψ = vecMulVec v ψ') :
    ψ = ψ' := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    exact hv (funext fun i => not_not.1 fun hi => hc ⟨i, hi⟩)
  have cancel : ∀ a b c : ZMod 3, a ≠ 0 → a * b = a * c → b = c := by decide
  funext j
  have := congrFun (congrFun h i) j
  simp only [vecMulVec_apply] at this
  exact cancel _ _ _ hi this

theorem conj_eq_of_comm (a k : GL4) (t : Mat) (hk : (k : Mat) * t = t * k) :
    ((a * k : GL4) : Mat) * t * (((a * k)⁻¹ : GL4) : Mat) = (a : Mat) * t * ((a⁻¹ : GL4) : Mat) := by
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  calc (a : Mat) * k * t * (((k⁻¹ : GL4) : Mat) * ((a⁻¹ : GL4) : Mat))
      = (a : Mat) * ((k : Mat) * t) * ((k⁻¹ : GL4) : Mat) * ((a⁻¹ : GL4) : Mat) := by
        simp only [mul_assoc]
    _ = (a : Mat) * t * ((k : Mat) * ((k⁻¹ : GL4) : Mat)) * ((a⁻¹ : GL4) : Mat) := by
        rw [hk]; simp only [mul_assoc]
    _ = (a : Mat) * t * ((a⁻¹ : GL4) : Mat) := by rw [Units.mul_inv, mul_one]

theorem conj_T0_eq (h : Hyp Γ) {g g' : GL4} (hg : g ∈ Γ) (hg' : g' ∈ Γ)
    (hv : (g : Mat) *ᵥ e 0 = (g' : Mat) *ᵥ e 0 ∨ (g : Mat) *ᵥ e 0 = -((g' : Mat) *ᵥ e 0)) :
    (g : Mat) * T0 * ((g⁻¹ : GL4) : Mat) = (g' : Mat) * T0 * ((g'⁻¹ : GL4) : Mat) := by
  have hk : ((g'⁻¹ * g : GL4) : Mat) *ᵥ e 0 = e 0 ∨ ((g'⁻¹ * g : GL4) : Mat) *ᵥ e 0 = -e 0 := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    rcases hv with hv | hv
    · left; rw [hv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · right; rw [hv, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hc := stab_comm h (Γ.mul_mem (Γ.inv_mem hg') hg) hk
  have := conj_eq_of_comm g' (g'⁻¹ * g) T0 hc
  rwa [mul_inv_cancel_left] at this

theorem real_unique (h : Hyp Γ) {v ψ ψ' : V} (h1 : Real Γ v ψ) (h2 : Real Γ v ψ') : ψ = ψ' := by
  obtain ⟨g, hg, hv, rfl⟩ := h1
  obtain ⟨g', hg', hv', rfl⟩ := h2
  have := conj_T0_eq h hg hg' (Or.inl (hv.trans hv'.symm))
  rw [conj_T0, conj_T0, hv, hv'] at this
  exact vecMulVec_cancel (hv ▸ ne_zero_of_mem_Om ⟨g, hg, rfl⟩) (add_left_cancel this)

theorem real_mul {v ψ : V} (hr : Real Γ v ψ) {k : GL4} (hk : k ∈ Γ) :
    Real Γ ((k : Mat) *ᵥ v) (ψ ᵥ* ((k⁻¹ : GL4) : Mat)) := by
  obtain ⟨g, hg, rfl, rfl⟩ := hr
  refine ⟨k * g, Γ.mul_mem hk hg, by simp [Matrix.mulVec_mulVec], ?_⟩
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.vecMul_vecMul]

theorem real_e0 : Real Γ (e 0) (e 0) := ⟨1, Γ.one_mem, by simp, by simp⟩

theorem real_refl (h : Hyp Γ) {v ψ : V} (hr : Real Γ v ψ) :
    ∃ r ∈ Γ, (r : Mat) = 1 + vecMulVec v ψ ∧ ((r⁻¹ : GL4) : Mat) = 1 + vecMulVec v ψ := by
  obtain ⟨t, ht, htT⟩ := h.t0
  obtain ⟨g, hg, rfl, rfl⟩ := hr
  have htt : t⁻¹ = t := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, htT, Units.val_one]
    exact mm_eq T0 T0 ▸ T0_sq
  refine ⟨g * t * g⁻¹, Γ.mul_mem (Γ.mul_mem hg ht) (Γ.inv_mem hg), ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, htT, conj_T0]
  · rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, htt, ← mul_assoc, Units.val_mul, Units.val_mul, htT,
      conj_T0]

theorem real_dot {v ψ : V} (hr : Real Γ v ψ) : ψ ⬝ᵥ v = 1 := by
  obtain ⟨g, hg, rfl, rfl⟩ := hr
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  exact e0_dot

theorem real_comm (h : Hyp Γ) {v ψ : V} (hr : Real Γ v ψ) {k : GL4} (hk : k ∈ Γ)
    (hkv : (k : Mat) *ᵥ v = v ∨ (k : Mat) *ᵥ v = -v) :
    (k : Mat) * (1 + vecMulVec v ψ) = (1 + vecMulVec v ψ) * k := by
  obtain ⟨g, hg, rfl, rfl⟩ := hr
  have hj : ((g⁻¹ * k * g : GL4) : Mat) *ᵥ e 0 = e 0 ∨
      ((g⁻¹ * k * g : GL4) : Mat) *ᵥ e 0 = -e 0 := by
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rcases hkv with hkv | hkv
    · left; rw [hkv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · right; rw [hkv, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hc := stab_comm h (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) hk) hg) hj
  rw [← conj_T0]
  have hk' : (k : Mat) = g * ((g⁻¹ * k * g : GL4) : Mat) * ((g⁻¹ : GL4) : Mat) := by
    simp only [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [hk']
  calc (g : Mat) * ((g⁻¹ * k * g : GL4) : Mat) * ((g⁻¹ : GL4) : Mat) *
        ((g : Mat) * T0 * ((g⁻¹ : GL4) : Mat))
      = (g : Mat) * (((g⁻¹ * k * g : GL4) : Mat) * T0) * ((g⁻¹ : GL4) : Mat) := by
        simp only [mul_assoc, Units.inv_mul_cancel_left]
    _ = (g : Mat) * (T0 * ((g⁻¹ * k * g : GL4) : Mat)) * ((g⁻¹ : GL4) : Mat) := by rw [hc]
    _ = (g : Mat) * T0 * ((g⁻¹ : GL4) : Mat) *
          ((g : Mat) * ((g⁻¹ * k * g : GL4) : Mat) * ((g⁻¹ : GL4) : Mat)) := by
        simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem real_ok (h : Hyp Γ) {v ψ : V} (hr : Real Γ v ψ) : OkB v ψ := by
  refine ⟨fun A hA hAv => ?_, fun hre => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := mem_GM.1 (H0L_sub h A hA)
    simp only [mv_eq, mm_eq, refl_eq] at hAv ⊢
    exact real_comm h hr hk hAv
  · obtain ⟨r, hr', hrv, -⟩ := real_refl h hr
    simp only [mv_eq, refl_eq] at hre ⊢
    rw [← hrv] at hre ⊢
    exact stab_H0L h hr' hre

theorem real_orbital (h : Hyp Γ) (n : ℕ)
    (hT : ∀ v ψ, Real Γ v ψ → (T0 * (1 + vecMulVec v ψ)) ^ n = 1) {v ψ v' ψ' : V}
    (hr : Real Γ v ψ) (hr' : Real Γ v' ψ') :
    ((1 + vecMulVec v ψ) * (1 + vecMulVec v' ψ')) ^ n = 1 := by
  obtain ⟨g, hg, rfl, rfl⟩ := hr
  obtain ⟨g', hg', rfl, rfl⟩ := hr'
  set j := g⁻¹ * g' with hj
  have hjΓ : j ∈ Γ := Γ.mul_mem (Γ.inv_mem hg) hg'
  have hT' := hT _ _ ⟨j, hjΓ, rfl, rfl⟩
  simp only [← conj_T0] at hT' ⊢
  have hg'j : g' = g * j := by rw [hj, mul_inv_cancel_left]
  have key : (g : Mat) * T0 * ((g⁻¹ : GL4) : Mat) * ((g' : Mat) * T0 * ((g'⁻¹ : GL4) : Mat)) =
      (g : Mat) * (T0 * ((j : Mat) * T0 * ((j⁻¹ : GL4) : Mat))) * ((g⁻¹ : GL4) : Mat) := by
    rw [hg'j, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.val_mul]
  rw [key]
  have hpow : ∀ (X : Mat) (m : ℕ), ((g : Mat) * X * ((g⁻¹ : GL4) : Mat)) ^ m =
      (g : Mat) * X ^ m * ((g⁻¹ : GL4) : Mat) := by
    intro X m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [hpow, hT', mul_one, Units.mul_inv]

open _root_.Classical in
noncomputable def psiOf (Γ : Subgroup GL4) (v : V) : V :=
  if hv : v ∈ Om Γ then Classical.choose (real_of_mem hv) else 0

theorem real_psiOf {v : V} (hv : v ∈ Om Γ) : Real Γ v (psiOf Γ v) := by
  rw [psiOf, dif_pos hv]
  exact Classical.choose_spec (real_of_mem hv)

open _root_.Classical in
noncomputable def cfgOf (Γ : Subgroup GL4) : Cfg :=
  mkCfg (decide (rep 1 ∈ Om Γ)) (decide (rep 2 ∈ Om Γ)) (decide (rep 4 ∈ Om Γ))
    (decide (rep 5 ∈ Om Γ)) (decide (rep 6 ∈ Om Γ)) (psiOf Γ (rep 1)) (psiOf Γ (rep 2))
    (psiOf Γ (rep 4)) (psiOf Γ (rep 5)) (psiOf Γ (rep 6))

theorem not_mem_rep3 (h : Hyp Γ) : rep 3 ∉ Om Γ := fun hv => by
  have hr := real_psiOf hv
  have := ok_rep 3 _ (mem_allV _) (real_dot hr) (real_ok h hr)
  simp [okL] at this

theorem cfgOf_fst (h : Hyp Γ) (k : Fin 7) : (cfgOf Γ).1 k = true ↔ rep k ∈ Om Γ := by
  fin_cases k
  · simp only [cfgOf, mkCfg]; simp [rep_zero ▸ (e0_mem_Om (Γ := Γ))]
  all_goals first
    | (simp only [cfgOf, mkCfg]; simpa using not_mem_rep3 h)
    | (simp [cfgOf, mkCfg])

theorem cfgOf_snd (h : Hyp Γ) (k : Fin 7) (hk : rep k ∈ Om Γ) : Real Γ (rep k) ((cfgOf Γ).2 k) := by
  fin_cases k
  · simp only [cfgOf, mkCfg]
    simpa [vec_e0, rep_zero] using (real_e0 (Γ := Γ))
  · exact real_psiOf hk
  · exact real_psiOf hk
  · exact absurd hk (not_mem_rep3 h)
  all_goals exact real_psiOf hk

theorem cfgOf_opt (h : Hyp Γ) (k : Fin 7) (hk : k ≠ 0 ∧ k ≠ 3) :
    (cfgOf Γ).2 k ∈ optL k ((cfgOf Γ).1 k) := by
  by_cases hm : rep k ∈ Om Γ
  · have hr := cfgOf_snd h k hm
    rw [(cfgOf_fst h k).2 hm, optL, if_pos rfl]
    exact ok_rep k _ (mem_allV _) (real_dot hr) (real_ok h hr)
  · have h1 : (cfgOf Γ).1 k = false := by
      cases hc : (cfgOf Γ).1 k
      · rfl
      · exact absurd ((cfgOf_fst h k).1 hc) hm
    rw [h1, optL, if_neg (by simp)]
    obtain ⟨h0, h3⟩ := hk
    fin_cases k <;> simp_all [cfgOf, mkCfg, psiOf]

theorem memOm_iff (h : Hyp Γ) {v : V} (hv : v ∈ nonzeroL) :
    memOm (cfgOf Γ) v = true ↔ v ∈ Om Γ := by
  obtain ⟨hh, hvh⟩ := tab_spec v hv
  have hv0 : v ≠ 0 := fun h0 => not_zero_mem_nonzeroL (h0 ▸ hv)
  obtain ⟨k, hk, hkA⟩ := mem_GM.1 (H0L_sub h _ hh)
  rw [memOm, Bool.and_eq_true, decide_eq_true_iff, cfgOf_fst h]
  rw [mv_eq] at hvh
  constructor
  · rintro ⟨-, hr⟩
    rw [← hvh]
    exact mulVec_mem_Om (H0L_sub h _ hh) hr
  · intro hm
    refine ⟨hv0, ?_⟩
    have : rep (tab v).1 = ((k⁻¹ : GL4) : Mat) *ᵥ v := by
      conv_rhs => rw [← hvh, ← hkA]
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [this]
    exact mulVec_mem_Om (coe_mem_GM (Γ.inv_mem hk)) hm

theorem real_psiC (h : Hyp Γ) {v : V} (hv : v ∈ nonzeroL) (hm : v ∈ Om Γ) :
    Real Γ v (psiC (cfgOf Γ) v) := by
  obtain ⟨hh, hvh⟩ := tab_spec v hv
  obtain ⟨k, hk, hkA⟩ := mem_GM.1 (H0L_sub h _ hh)
  have hrep : rep (tab v).1 ∈ Om Γ := by
    have := (memOm_iff h hv).2 hm
    rw [memOm, Bool.and_eq_true] at this
    exact (cfgOf_fst h _).1 this.2
  have hvh' : (tab v).2 *ᵥ rep (tab v).1 = v := by rw [← mv_eq]; exact hvh
  have hkH : (k : Mat) ∈ H0L := by rw [hkA]; exact hh
  have := real_mul (cfgOf_snd h _ hrep) hk
  rw [inv_eq_transpose hkH, Matrix.vecMul_transpose, hkA, hvh'] at this
  rw [psiC, mv_eq]
  exact this

theorem rC_eq (h : Hyp Γ) {v : V} (hv : v ∈ nonzeroL) (hm : v ∈ Om Γ) :
    ∃ r ∈ Γ, (r : Mat) = rC (cfgOf Γ) v ∧ ((r⁻¹ : GL4) : Mat) = rC (cfgOf Γ) v := by
  obtain ⟨r, hr, h1, h2⟩ := real_refl h (real_psiC h hv hm)
  exact ⟨r, hr, by rw [h1, rC, refl_eq], by rw [h2, rC, refl_eq]⟩

theorem cfgOf_C1 (h : Hyp Γ) : C1 (cfgOf Γ) := by
  intro w hw hmw w' hw' hmw'
  rw [memOm_iff h hw] at hmw
  rw [memOm_iff h hw'] at hmw'
  obtain ⟨r, hr, h1, h2⟩ := rC_eq h hw hmw
  have hreal := real_mul (real_psiC h hw' hmw') hr
  rw [h1, h2] at hreal
  have hu := mem_of_real hreal
  have hun : mv (rC (cfgOf Γ) w) w' ∈ nonzeroL := by
    rw [mv_eq]; exact mem_nonzeroL _ (ne_zero_of_mem_Om hu)
  refine ⟨(memOm_iff h hun).2 (by rw [mv_eq]; exact hu), ?_⟩
  rw [vmm_eq]
  refine real_unique h (real_psiC h hun (by rw [mv_eq]; exact hu)) ?_
  rw [mv_eq]; exact hreal

theorem cfgOf_C3 (h : Hyp Γ) : C3 (cfgOf Γ) := by
  obtain ⟨g, hg, h0⟩ := h.meet
  have hm : (g : Mat) *ᵥ e 0 ∈ Om Γ := ⟨g, hg, rfl⟩
  have hn := mem_nonzeroL _ (ne_zero_of_mem_Om hm)
  exact ⟨_, hn, (memOm_iff h hn).2 hm, h0⟩

theorem cfgOf_C4 (h : Hyp Γ) (n : ℕ) : C4 (cfgOf Γ) n := by
  intro hT w hw hmw w' hw' hmw'
  rw [memOm_iff h hw] at hmw
  rw [memOm_iff h hw'] at hmw'
  have hT' : ∀ v ψ, Real Γ v ψ → (T0 * (1 + vecMulVec v ψ)) ^ n = 1 := by
    intro v ψ hr
    have hm := mem_of_real hr
    have hn := mem_nonzeroL _ (ne_zero_of_mem_Om hm)
    have := hT v hn ((memOm_iff h hn).2 hm)
    rwa [mpow_eq, mm_eq, rC, refl_eq, real_unique h (real_psiC h hn hm) hr] at this
  have := real_orbital h n hT' (real_psiC h hw hmw) (real_psiC h hw' hmw')
  rwa [mpow_eq, mm_eq, rC, rC, refl_eq, refl_eq]

open _root_.Classical in
theorem cfgOf_good (h : Hyp Γ) : Good (cfgOf Γ) :=
  classify (decide (rep 1 ∈ Om Γ)) (decide (rep 2 ∈ Om Γ)) (decide (rep 4 ∈ Om Γ))
    (decide (rep 5 ∈ Om Γ)) (decide (rep 6 ∈ Om Γ)) (psiOf Γ (rep 1)) (cfgOf_opt h 1 (by decide))
    (psiOf Γ (rep 2)) (cfgOf_opt h 2 (by decide)) (psiOf Γ (rep 4)) (cfgOf_opt h 4 (by decide))
    (psiOf Γ (rep 5)) (cfgOf_opt h 5 (by decide)) (psiOf Γ (rep 6)) (cfgOf_opt h 6 (by decide))
    (cfgOf_C1 h) (cfgOf_C3 h) (cfgOf_C4 h 2) (cfgOf_C4 h 4)

theorem om_iff (h : Hyp Γ) (v : V) :
    v ∈ Om Γ ↔ v ∈ nonzeroL ∧ (cfgOf Γ).1 (tab v).1 = true := by
  constructor
  · intro hv
    have hn := mem_nonzeroL _ (ne_zero_of_mem_Om hv)
    have := (memOm_iff h hn).2 hv
    rw [memOm, Bool.and_eq_true] at this
    exact ⟨hn, this.2⟩
  · rintro ⟨hn, hm⟩
    refine (memOm_iff h hn).1 ?_
    rw [memOm, hm, Bool.and_true, decide_eq_true_iff]
    exact fun h0 => not_zero_mem_nonzeroL (h0 ▸ hn)

theorem cyc4_of_sig01 (h : Hyp Γ) (hs : Sig01 ∈ GM Γ) : Cyc4 ∈ GM Γ := by
  have h1 : Sig01 * Cyc4 ∈ H0L := mm_eq Sig01 Cyc4 ▸ sig01_cyc4
  have h2 : Sig01 * Sig01 = 1 := mm_eq Sig01 Sig01 ▸ sig01_sq
  have : Cyc4 = Sig01 * (Sig01 * Cyc4) := by rw [← mul_assoc, h2, one_mul]
  rw [this]
  exact Submonoid.mul_mem _ hs (H0L_sub h _ h1)

theorem sig01_of_W (h : Hyp Γ) (hW : W (cfgOf Γ)) : Sig01 ∈ GM Γ := by
  obtain ⟨a, ha, hma, b, hb, hmb, hab⟩ := hW
  obtain ⟨ra, hra, hra1, hra2⟩ := rC_eq h ha ((memOm_iff h ha).1 hma)
  obtain ⟨rb, hrb, hrb1, hrb2⟩ := rC_eq h hb ((memOm_iff h hb).1 hmb)
  rw [mm_eq, mm_eq] at hab
  have hinv : ∀ (r : GL4) (A : Mat), (r : Mat) = A → ((r⁻¹ : GL4) : Mat) = A → A * A = 1 :=
    fun r A h1 h2 => by
      calc A * A = (r : Mat) * ((r⁻¹ : GL4) : Mat) := by rw [h1, h2]
        _ = 1 := Units.mul_inv r
  have e1 : Sig01 = rC (cfgOf Γ) b * rC (cfgOf Γ) a *
      (rC (cfgOf Γ) a * rC (cfgOf Γ) b * Sig01) := by
    simp only [← mul_assoc]
    rw [mul_assoc (rC (cfgOf Γ) b), hinv ra _ hra1 hra2, mul_one, hinv rb _ hrb1 hrb2, one_mul]
  rw [e1]
  refine Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) (H0L_sub h _ hab)
  · rw [← hrb1]; exact coe_mem_GM hrb
  · rw [← hra1]; exact coe_mem_GM hra

theorem e_mem_Om (h : Hyp Γ) (hA : (cfgOf Γ).1 = mA) (j : Fin 4) : e j ∈ Om Γ :=
  (om_iff h _).2 ⟨(mA_e j).1, hA ▸ (mA_e j).2⟩

theorem mon_of_mA (h : Hyp Γ) (hA : (cfgOf Γ).1 = mA) {g : GL4} (hg : g ∈ Γ) (j : Fin 4) :
    (g : Mat) *ᵥ e j ∈ Fr8 := by
  have hm := mulVec_mem_Om (coe_mem_GM hg) (e_mem_Om h hA j)
  obtain ⟨hn, hk⟩ := (om_iff h _).1 hm
  exact mA_sub_Fr8 _ hn (hA ▸ hk)

theorem sig01_of_mA (h : Hyp Γ) (hA : (cfgOf Γ).1 = mA) : Sig01 ∈ GM Γ := by
  obtain ⟨g, hg, hge⟩ := e_mem_Om h hA 1
  let s : GL4 := ⟨Sig01, Sig01, mm_eq Sig01 Sig01 ▸ sig01_sq, mm_eq Sig01 Sig01 ▸ sig01_sq⟩
  have hcol : ∀ j : Fin 4, j ≠ 0 → ((s * g : GL4) : Mat) *ᵥ e j ∈ SU := by
    intro j hj
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    refine sig01_Fr8 _ (mon_of_mA h hA hg j) (fun hh => ?_) (fun hh => ?_)
    · exact (e_ne j 0 hj).1 (mulVec_inj g (by rw [hh, hge]))
    · exact (e_ne j 0 hj).2 (mulVec_inj g (by rw [hh, Matrix.mulVec_neg, hge]))
  have h0 : ((s * g : GL4) : Mat) *ᵥ e 0 = e 0 := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hge]; exact sig01_e1
  have hmem := mem_H0L_of (Or.inl h0) (hcol 1 (by decide)) (hcol 2 (by decide)) (hcol 3 (by decide))
  have : Sig01 = ((s * g : GL4) : Mat) * ((g⁻¹ : GL4) : Mat) := by
    rw [Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact Submonoid.mul_mem _ (H0L_sub h _ hmem) (coe_mem_GM (Γ.inv_mem hg))

@[reducible] def vecAction : MulAction GL4 V where
  smul g v := (g : Mat) *ᵥ v
  one_smul v := by
    show ((1 : GL4) : Mat) *ᵥ v = v
    rw [Units.val_one, Matrix.one_mulVec]
  mul_smul g k v := by
    show ((g * k : GL4) : Mat) *ᵥ v = (g : Mat) *ᵥ ((k : Mat) *ᵥ v)
    rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem card_eq (h : Hyp Γ) : Nat.card Γ = 48 * (Om Γ).ncard := by
  letI := vecAction
  have horb : MulAction.orbit Γ (e 0) = Om Γ := by
    ext v
    simp only [MulAction.mem_orbit_iff, Om, Set.mem_setOf_eq, Subtype.exists, Subgroup.mk_smul]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩
  let S48 : Finset Mat := (H0L.filter fun A => decide (mv A (e 0) = e 0)).toFinset
  have hstab : Nat.card (MulAction.stabilizer Γ (e 0)) = 48 := by
    let f : MulAction.stabilizer Γ (e 0) → S48 := fun g => ⟨(((g : Γ) : GL4) : Mat), by
      have hg0 : (((g : Γ) : GL4) : Mat) *ᵥ e 0 = e 0 := g.2
      simp only [S48, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mv_eq]
      exact ⟨stab_H0L h (g : Γ).2 (Or.inl hg0), hg0⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨fun x y hxy => ?_, fun ⟨A, hA⟩ => ?_⟩
      · have : (((x : Γ) : GL4) : Mat) = (((y : Γ) : GL4) : Mat) := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext (Units.ext this))
      · simp only [S48, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mv_eq] at hA
        obtain ⟨g, hg, rfl⟩ := mem_GM.1 (H0L_sub h _ hA.1)
        exact ⟨⟨⟨g, hg⟩, hA.2⟩, rfl⟩
    rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]
    exact card_stab
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Γ (e 0)), Nat.card_prod, hstab,
    horb, Nat.card_coe_set_eq, mul_comm]

end CFSG.RankThree.PartTwo.Sec21.FF81.P51

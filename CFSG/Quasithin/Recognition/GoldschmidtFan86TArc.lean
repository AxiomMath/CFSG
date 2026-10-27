module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Arcs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def omega1 (H : Subgroup G) : Subgroup G := Subgroup.closure {x | x ∈ H ∧ x * x = 1}

@[expose] def Track.fixer (T : Track Γ G) : Subgroup G :=
  CFSG.Quasithin.Fan86.fixSet G (Set.range T.line.vert)

@[expose] def Track.subFixer (T : Track Γ G) (a b : ℤ) : Subgroup G :=
  CFSG.Quasithin.Fan86.fixSet G (T.line.vert '' Set.Icc a b)

@[expose] def IsTArc (T : Track Γ G) (a b : ℤ) : Prop :=
  a < b ∧ ¬ omega1 (T.subFixer a b) ≤ T.subFixer (a - 1) b ∧
    ¬ omega1 (T.subFixer a b) ≤ T.subFixer a (b + 1) ∧
    omega1 (T.subFixer (a - 1) (b + 1)) ≤ T.fixer

@[expose] def IsQuasiTArc (T : Track Γ G) (a b : ℤ) : Prop :=
  a < b ∧ ¬ T.subFixer a b ≤ T.subFixer (a - 1) b ∧ ¬ T.subFixer a b ≤ T.subFixer a (b + 1) ∧
    omega1 (T.subFixer (a - 1) (b + 1)) ≤ T.fixer

variable (T : Track Γ G)

theorem Track.mem_fixer {g : G} : g ∈ T.fixer ↔ ∀ i, g • T.line.vert i = T.line.vert i := by
  simp [Track.fixer, CFSG.Quasithin.Fan86.mem_fixSet]

theorem Track.mem_subFixer {a b : ℤ} {g : G} :
    g ∈ T.subFixer a b ↔ ∀ i, a ≤ i → i ≤ b → g • T.line.vert i = T.line.vert i := by
  simp only [Track.subFixer, CFSG.Quasithin.Fan86.mem_fixSet, Set.mem_image, Set.mem_Icc,
    forall_exists_index, and_imp]
  constructor
  · intro h i h1 h2
    exact h _ i h1 h2 rfl
  · rintro h _ i h1 h2 rfl
    exact h i h1 h2

theorem Track.fixer_le_subFixer (a b : ℤ) : T.fixer ≤ T.subFixer a b := fun _ hg =>
  (T.mem_subFixer).2 fun i _ _ => (T.mem_fixer).1 hg i

theorem Track.subFixer_anti {a b a' b' : ℤ} (h1 : a' ≤ a) (h2 : b ≤ b') :
    T.subFixer a' b' ≤ T.subFixer a b := fun _ hg =>
  (T.mem_subFixer).2 fun i hi1 hi2 => (T.mem_subFixer).1 hg i (by omega) (by omega)

theorem omega1_mono {H K : Subgroup G} (h : H ≤ K) : omega1 H ≤ omega1 K :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem omega1_le (H : Subgroup G) : omega1 H ≤ H := by
  rw [omega1, Subgroup.closure_le]
  exact fun _ hx => hx.1

theorem omega1_conj_mem {H H' : Subgroup G} {g : G} (hg : ∀ h ∈ H', g * h * g⁻¹ ∈ H) {y : G}
    (hy : y ∈ omega1 H') : g * y * g⁻¹ ∈ omega1 H := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨hg x hx.1, ?_⟩
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx.2]; simp
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact (omega1 H).mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact (omega1 H).inv_mem hx

theorem Track.adj_pred (i : ℤ) : Γ.Adj (T.line.vert i) (T.line.vert (i - 1)) := by
  have := (T.line.adj (i - 1)).symm
  rwa [sub_add_cancel] at this

theorem Track.ne_pred_succ (i : ℤ) : T.line.vert (i - 1) ≠ T.line.vert (i + 1) := by
  have := T.line.nb (i - 1)
  rwa [show i - 1 + 2 = i + 1 by omega] at this

theorem nbrStab_conj_mem (F : FanTree Γ G) {v : V} {g : G} (hg : g • v = v) {h : G}
    (hh : h ∈ nbrStab Γ G v) : g * h * g⁻¹ ∈ nbrStab Γ G v := by
  intro w hw
  have hw' : Γ.Adj v (g⁻¹ • w) := by
    have := (F.adj_smul g⁻¹ v w).2 hw
    rwa [inv_smul_eq_iff.2 hg.symm] at this
  rw [mul_smul, mul_smul, hh _ hw', smul_inv_smul]

theorem Track.subFixer_pred_succ (F : FanTree Γ G) {a b : ℤ} (hab : a < b) :
    T.subFixer (a - 1) (b + 1) =
      T.subFixer a b ⊓ nbrStab Γ G (T.line.vert a) ⊓ nbrStab Γ G (T.line.vert b) := by
  ext g
  constructor
  · intro hg
    have hf : ∀ i, a - 1 ≤ i → i ≤ b + 1 → g • T.line.vert i = T.line.vert i :=
      fun i h1 h2 => (T.mem_subFixer).1 hg i h1 h2
    refine ⟨⟨(T.subFixer_anti (a := a) (b := b) (by omega) (by omega)) hg, ?_⟩, ?_⟩
    · intro w hw
      exact F.frobenius_two (T.line.vert a) (T.line.vert (a - 1)) (T.line.vert (a + 1))
        (T.adj_pred a) (T.line.adj a) (T.ne_pred_succ a) g
        (MulAction.mem_stabilizer_iff.2 (hf a (by omega) (by omega)))
        (hf (a - 1) (by omega) (by omega)) (hf (a + 1) (by omega) (by omega)) w hw
    · intro w hw
      exact F.frobenius_two (T.line.vert b) (T.line.vert (b - 1)) (T.line.vert (b + 1))
        (T.adj_pred b) (T.line.adj b) (T.ne_pred_succ b) g
        (MulAction.mem_stabilizer_iff.2 (hf b (by omega) (by omega)))
        (hf (b - 1) (by omega) (by omega)) (hf (b + 1) (by omega) (by omega)) w hw
  · rintro ⟨⟨hθ, ha⟩, hb⟩
    refine (T.mem_subFixer).2 fun i h1 h2 => ?_
    by_cases hi1 : i = a - 1
    · subst hi1
      exact ha _ (by simpa using (T.adj_pred a))
    by_cases hi2 : i = b + 1
    · subst hi2
      exact hb _ (T.line.adj b)
    exact (T.mem_subFixer).1 hθ i (by omega) (by omega)

theorem omega1_subFixer_eq {a b : ℤ} (h : omega1 (T.subFixer (a - 1) (b + 1)) ≤ T.fixer) :
    omega1 (T.subFixer (a - 1) (b + 1)) = omega1 T.fixer := by
  refine le_antisymm ?_ (omega1_mono (T.fixer_le_subFixer _ _))
  rw [omega1, Subgroup.closure_le]
  intro x hx
  exact Subgroup.subset_closure ⟨h (Subgroup.subset_closure hx), hx.2⟩

theorem IsQuasiTArc.fixer_normal (F : FanTree Γ G) {a b : ℤ} (h : IsQuasiTArc T a b) :
    omega1 T.fixer ≤ T.subFixer a b ∧
      T.subFixer a b ≤ Subgroup.normalizer (omega1 T.fixer : Set G) := by
  obtain ⟨hab, -, -, hLR⟩ := h
  have heq := omega1_subFixer_eq T hLR
  refine ⟨(omega1_le _).trans (T.fixer_le_subFixer a b), fun g hg => ?_⟩
  have hdecomp := T.subFixer_pred_succ F hab
  have hmem : ∀ h ∈ T.subFixer (a - 1) (b + 1), g * h * g⁻¹ ∈ T.subFixer (a - 1) (b + 1) := by
    intro h hh
    rw [hdecomp] at hh ⊢
    obtain ⟨⟨hθ, ha⟩, hb⟩ := hh
    refine ⟨⟨(T.subFixer a b).mul_mem ((T.subFixer a b).mul_mem hg hθ)
      ((T.subFixer a b).inv_mem hg), ?_⟩, ?_⟩
    · exact nbrStab_conj_mem F ((T.mem_subFixer).1 hg a le_rfl hab.le) ha
    · exact nbrStab_conj_mem F ((T.mem_subFixer).1 hg b hab.le le_rfl) hb
  have key : ∀ g ∈ T.subFixer a b, ∀ y ∈ omega1 T.fixer, g * y * g⁻¹ ∈ omega1 T.fixer := by
    intro g hg y hy
    rw [← heq] at hy ⊢
    exact omega1_conj_mem (fun h hh => by
      have hgh := hdecomp ▸ hh
      rw [hdecomp] at hh ⊢
      obtain ⟨⟨hθ, ha⟩, hb⟩ := hh
      exact ⟨⟨(T.subFixer a b).mul_mem ((T.subFixer a b).mul_mem hg hθ)
        ((T.subFixer a b).inv_mem hg),
        nbrStab_conj_mem F ((T.mem_subFixer).1 hg a le_rfl hab.le) ha⟩,
        nbrStab_conj_mem F ((T.mem_subFixer).1 hg b hab.le le_rfl) hb⟩) hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => key g hg y hy
  · intro hy
    have := key g⁻¹ ((T.subFixer a b).inv_mem hg) _ hy
    simpa [mul_assoc] using this

theorem Track.conj_mem_subFixer (k : ℤ) {a b : ℤ} {h : G} :
    T.τ ^ k * h * (T.τ ^ k)⁻¹ ∈ T.subFixer (a + 2 * k) (b + 2 * k) ↔ h ∈ T.subFixer a b := by
  rw [T.mem_subFixer, T.mem_subFixer]
  constructor
  · intro H i h1 h2
    have := H (i + 2 * k) (by omega) (by omega)
    rw [← T.zpow_smul_vert k i, mul_smul, mul_smul, inv_smul_smul] at this
    exact MulAction.injective (T.τ ^ k) this
  · intro H i h1 h2
    have hi : T.line.vert i = T.τ ^ k • T.line.vert (i - 2 * k) := by
      rw [T.zpow_smul_vert, sub_add_cancel]
    rw [hi, mul_smul, mul_smul, inv_smul_smul, H (i - 2 * k) (by omega) (by omega)]

theorem Track.conj_mem_fixer (k : ℤ) {h : G} :
    T.τ ^ k * h * (T.τ ^ k)⁻¹ ∈ T.fixer ↔ h ∈ T.fixer := by
  rw [T.mem_fixer, T.mem_fixer]
  constructor
  · intro H i
    have := H (i + 2 * k)
    rw [← T.zpow_smul_vert k i, mul_smul, mul_smul, inv_smul_smul] at this
    exact MulAction.injective (T.τ ^ k) this
  · intro H i
    have hi : T.line.vert i = T.τ ^ k • T.line.vert (i - 2 * k) := by
      rw [T.zpow_smul_vert, sub_add_cancel]
    rw [hi, mul_smul, mul_smul, inv_smul_smul, H (i - 2 * k)]

theorem IsQuasiTArc.translate {a b : ℤ} (h : IsQuasiTArc T a b) (k : ℤ) :
    IsQuasiTArc T (a + 2 * k) (b + 2 * k) := by
  obtain ⟨hab, hL, hR, hLR⟩ := h
  refine ⟨by omega, fun hle => hL fun g hg => ?_, fun hle => hR fun g hg => ?_, ?_⟩
  · have := hle ((T.conj_mem_subFixer k).2 hg)
    rw [show a + 2 * k - 1 = a - 1 + 2 * k by omega] at this
    exact (T.conj_mem_subFixer k).1 this
  · have := hle ((T.conj_mem_subFixer k).2 hg)
    rw [show b + 2 * k + 1 = b + 1 + 2 * k by omega] at this
    exact (T.conj_mem_subFixer k).1 this
  · intro y hy
    have hy' := omega1_conj_mem (H := T.subFixer (a - 1) (b + 1))
      (H' := T.subFixer (a + 2 * k - 1) (b + 2 * k + 1)) (g := (T.τ ^ k)⁻¹) (fun h hh => by
        have := (T.conj_mem_subFixer k (a := a - 1) (b := b + 1) (h := (T.τ ^ k)⁻¹ * h * T.τ ^ k)).1
          (by
            rw [show a - 1 + 2 * k = a + 2 * k - 1 by omega,
              show b + 1 + 2 * k = b + 2 * k + 1 by omega]
            simpa [mul_assoc] using hh)
        simpa using this) hy
    have h3 := hLR hy'
    have h4 := (T.conj_mem_fixer k).2 (by simpa using h3 : (T.τ ^ k)⁻¹ * y * T.τ ^ k ∈ T.fixer)
    simpa [mul_assoc] using h4

end CFSG.Quasithin.Fan86

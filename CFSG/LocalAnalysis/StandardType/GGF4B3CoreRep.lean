module

public import CFSG.LocalAnalysis.StandardType.GGF4WeylMat
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.F4Model

structure F4Rep (W : Type) [Group W] where
  s : Fin 4 → W
  ρ : W →* Matrix (Fin 4) (Fin 4) ℤ
  inj : Function.Injective ρ
  hs : ∀ i, ρ (s i) = (Sm i).toMat
  gen : Subgroup.closure (Set.range s) = ⊤

theorem pow_four_eq {M : Type*} [Monoid M] (z : M) : z ^ 4 = z * z * (z * z) := by
  have e1 : z ^ 4 = z ^ 2 * z ^ 2 := pow_add z 2 2
  rw [e1, pow_two]

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

@[expose] def IsRefl (t : W) : Prop := ∃ (g : W) (j : Fin 4), t = g * R.s j * g⁻¹

@[expose] def wd (l : List (Fin 4)) : W := (l.map R.s).prod

theorem s_sq (i : Fin 4) : R.s i * R.s i = 1 := by
  apply R.inj
  rw [map_mul, R.hs, ← M4.toMat_mul, Sm_sq i, M4.toMat_one, map_one]

theorem s_inv (i : Fin 4) : (R.s i)⁻¹ = R.s i := inv_eq_of_mul_eq_one_right (R.s_sq i)

theorem rho_mul {a b : W} {x y : M4} (ha : R.ρ a = x.toMat) (hb : R.ρ b = y.toMat) :
    R.ρ (a * b) = (x.mul y).toMat := by
  rw [map_mul, ha, hb, M4.toMat_mul]

theorem rho_mul3 {a b c : W} {x y z : M4} (ha : R.ρ a = x.toMat) (hb : R.ρ b = y.toMat)
    (hc : R.ρ c = z.toMat) : R.ρ (a * b * c) = (x.mul (y.mul z)).toMat := by
  rw [map_mul, map_mul, ha, hb, hc, M4.toMat_mul, M4.toMat_mul, mul_assoc]

theorem rho_wd (l : List (Fin 4)) : R.ρ (R.wd l) = (evalW l).toMat := by
  induction l with
  | nil => simp [wd, evalW, M4.toMat_one]
  | cons i l ih =>
    have h : R.wd (i :: l) = R.s i * R.wd l := by simp [wd]
    rw [h, map_mul, ih, R.hs, ← M4.toMat_mul]
    rfl

theorem wd_reverse (l : List (Fin 4)) : R.wd l.reverse = (R.wd l)⁻¹ := by
  induction l with
  | nil => simp [wd]
  | cons i l ih =>
    have h1 : R.wd (i :: l).reverse = R.wd l.reverse * R.s i := by simp [wd]
    have h2 : R.wd (i :: l) = R.s i * R.wd l := by simp [wd]
    rw [h1, h2, mul_inv_rev, ih, R.s_inv]

theorem rho_conj_wd (w : List (Fin 4)) {t : W} {x : M4} (hx : R.ρ t = x.toMat) :
    R.ρ (R.wd w * t * (R.wd w)⁻¹) = (conjW w x).toMat := by
  rw [← R.wd_reverse]
  exact R.rho_mul3 (R.rho_wd w) hx (R.rho_wd w.reverse)

theorem conj_wd_eq {w : List (Fin 4)} {t u : W} {x y : M4} (hx : R.ρ t = x.toMat)
    (hy : R.ρ u = y.toMat) (h : conjW w x = y) : R.wd w * t * (R.wd w)⁻¹ = u := by
  apply R.inj
  rw [R.rho_conj_wd w hx, h, hy]

theorem IsRefl.conj {R : F4Rep W} {t : W} (ht : R.IsRefl t) (g : W) : R.IsRefl (g * t * g⁻¹) := by
  obtain ⟨h, j, rfl⟩ := ht
  exact ⟨g * h, j, by simp [mul_assoc]⟩

@[expose] def ConjR (g : W) : Prop :=
  ∀ x, x < 24 → ∃ y, y < 24 ∧ R.ρ g * (Rm x).toMat * R.ρ g⁻¹ = (Rm y).toMat

theorem ConjR.mul {g h : W} (hg : R.ConjR g) (hh : R.ConjR h) : R.ConjR (g * h) := by
  intro x hx
  obtain ⟨y, hy, e1⟩ := hh x hx
  obtain ⟨z, hz, e2⟩ := hg y hy
  refine ⟨z, hz, ?_⟩
  rw [← e2, ← e1]
  simp [map_mul, mul_inv_rev, mul_assoc]

theorem ConjR.one : R.ConjR 1 := by
  intro x hx
  exact ⟨x, hx, by simp⟩

theorem ConjR.gen (i : Fin 4) : R.ConjR (R.s i) := by
  intro x hx
  obtain ⟨y, hy, e⟩ := R_conj_closed i x hx
  refine ⟨y, hy, ?_⟩
  rw [R.s_inv i, R.hs i, ← e, M4.toMat_mul, M4.toMat_mul]
  exact mul_assoc _ _ _

theorem conjR2 (g : W) : R.ConjR g ∧ R.ConjR g⁻¹ := by
  have hg : g ∈ Subgroup.closure (Set.range R.s) := by rw [R.gen]; exact Subgroup.mem_top g
  refine Subgroup.closure_induction (p := fun g _ => R.ConjR g ∧ R.ConjR g⁻¹) ?_ ?_ ?_ ?_ hg
  · rintro x ⟨i, rfl⟩
    exact ⟨ConjR.gen R i, by rw [R.s_inv i]; exact ConjR.gen R i⟩
  · exact ⟨ConjR.one R, by rw [inv_one]; exact ConjR.one R⟩
  · intro x y _ _ hx hy
    exact ⟨ConjR.mul R hx.1 hy.1, by rw [mul_inv_rev]; exact ConjR.mul R hy.2 hx.2⟩
  · intro x _ hx
    exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem refl_rep {t : W} (ht : R.IsRefl t) : ∃ x, x < 24 ∧ R.ρ t = (Rm x).toMat := by
  obtain ⟨g, j, rfl⟩ := ht
  obtain ⟨x, hx, hxj⟩ := Sm_mem_R j
  obtain ⟨y, hy, e⟩ := (R.conjR2 g).1 x hx
  refine ⟨y, hy, ?_⟩
  rw [map_mul, map_mul, R.hs j, hxj, ← e]

theorem orderOf_conj_eq (g a : W) : orderOf (g * a * g⁻¹) = orderOf a := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [conj_pow]
  constructor
  · intro h
    have h2 : g * a ^ n = g := mul_inv_eq_one.mp h
    calc a ^ n = g⁻¹ * (g * a ^ n) := (inv_mul_cancel_left g (a ^ n)).symm
      _ = g⁻¹ * g := by rw [h2]
      _ = 1 := inv_mul_cancel g
  · intro h
    rw [h]
    simp

theorem relM_of_orders {a0 a1 a2 : W} {x0 x1 x2 : M4} (h0 : R.ρ a0 = x0.toMat)
    (h1 : R.ρ a1 = x1.toMat) (h2 : R.ρ a2 = x2.toMat) (o01 : orderOf (a0 * a1) = 3)
    (o12 : orderOf (a1 * a2) = 4) (o02 : orderOf (a0 * a2) = 2) : relM x0 x1 x2 := by
  rw [relM_iff]
  have ord01 : orderOf ((x0.mul x1).toMat) = 3 := by
    rw [← R.rho_mul h0 h1, orderOf_injective R.ρ R.inj, o01]
  have ord12 : orderOf ((x1.mul x2).toMat) = 4 := by
    rw [← R.rho_mul h1 h2, orderOf_injective R.ρ R.inj, o12]
  have ord02 : orderOf ((x0.mul x2).toMat) = 2 := by
    rw [← R.rho_mul h0 h2, orderOf_injective R.ρ R.inj, o02]
  have hne : ∀ (z : M4) (n : ℕ), orderOf z.toMat = n → n ≠ 1 → z ≠ M4.one := by
    intro z n hz hn hzo
    rw [hzo, M4.toMat_one, orderOf_one] at hz
    exact hn hz.symm
  refine ⟨?_, hne _ 3 ord01 (by norm_num), ?_, ?_, ?_, hne _ 2 ord02 (by norm_num)⟩
  · apply M4.toMat_injective
    rw [M4.toMat_pw3, M4.toMat_one, ← pow_three]
    have h := pow_orderOf_eq_one ((x0.mul x1).toMat)
    rwa [ord01] at h
  · apply M4.toMat_injective
    rw [M4.toMat_pw4, M4.toMat_one]
    have h := pow_orderOf_eq_one ((x1.mul x2).toMat)
    rw [ord12, pow_four_eq] at h
    exact h
  · intro h
    have h' := congrArg M4.toMat h
    rw [M4.toMat_pw2, M4.toMat_one, ← pow_two] at h'
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [ord12]; norm_num) h'
  · apply M4.toMat_injective
    rw [M4.toMat_pw2, M4.toMat_one, ← pow_two]
    have h := pow_orderOf_eq_one ((x0.mul x2).toMat)
    rwa [ord02] at h

theorem stage1_conj {a : W} (h : R.IsRefl a) :
    ∃ (g : W) (T : Fin 4), (T = 1 ∨ T = 2) ∧ g * a * g⁻¹ = R.s T := by
  obtain ⟨x, hx, ρx⟩ := R.refl_rep h
  obtain ⟨hT, hc⟩ := stage1 x hx
  exact ⟨R.wd (W1 x), T1 x, hT, R.conj_wd_eq ρx (R.hs (T1 x)) hc⟩

theorem stage2B_conj {a0 a2 : W} (h0 : R.IsRefl a0) (h2 : R.IsRefl a2)
    (o01 : orderOf (a0 * R.s 1) = 3) (o12 : orderOf (R.s 1 * a2) = 4)
    (o02 : orderOf (a0 * a2) = 2) :
    ∃ g : W, g * a0 * g⁻¹ = R.s 0 ∧ g * R.s 1 * g⁻¹ = R.s 1 ∧ g * a2 * g⁻¹ = R.s 2 := by
  obtain ⟨x0, hx0, ρ0⟩ := R.refl_rep h0
  obtain ⟨x2, hx2, ρ2⟩ := R.refl_rep h2
  have hrel : relM (Rm x0) (Sm 1) (Rm x2) := R.relM_of_orders ρ0 (R.hs 1) ρ2 o01 o12 o02
  obtain ⟨k, hk, c0, c2, c1⟩ := stage2B x0 hx0 x2 hx2 hrel
  exact ⟨R.wd (W2B k), R.conj_wd_eq ρ0 (R.hs 0) c0, R.conj_wd_eq (R.hs 1) (R.hs 1) c1,
    R.conj_wd_eq ρ2 (R.hs 2) c2⟩

theorem stage2C_conj {a0 a2 : W} (h0 : R.IsRefl a0) (h2 : R.IsRefl a2)
    (o01 : orderOf (a0 * R.s 2) = 3) (o12 : orderOf (R.s 2 * a2) = 4)
    (o02 : orderOf (a0 * a2) = 2) :
    ∃ g : W, g * a0 * g⁻¹ = R.s 3 ∧ g * R.s 2 * g⁻¹ = R.s 2 ∧ g * a2 * g⁻¹ = R.s 1 := by
  obtain ⟨x0, hx0, ρ0⟩ := R.refl_rep h0
  obtain ⟨x2, hx2, ρ2⟩ := R.refl_rep h2
  have hrel : relM (Rm x0) (Sm 2) (Rm x2) := R.relM_of_orders ρ0 (R.hs 2) ρ2 o01 o12 o02
  obtain ⟨k, hk, c0, c2, c1⟩ := stage2C x0 hx0 x2 hx2 hrel
  exact ⟨R.wd (W2C k), R.conj_wd_eq ρ0 (R.hs 3) c0, R.conj_wd_eq (R.hs 2) (R.hs 2) c1,
    R.conj_wd_eq ρ2 (R.hs 1) c2⟩

theorem classify {a0 a1 a2 : W} (h0 : R.IsRefl a0) (h1 : R.IsRefl a1) (h2 : R.IsRefl a2)
    (o01 : orderOf (a0 * a1) = 3) (o12 : orderOf (a1 * a2) = 4) (o02 : orderOf (a0 * a2) = 2) :
    ∃ g : W, (g * a0 * g⁻¹ = R.s 0 ∧ g * a1 * g⁻¹ = R.s 1 ∧ g * a2 * g⁻¹ = R.s 2) ∨
      (g * a0 * g⁻¹ = R.s 3 ∧ g * a1 * g⁻¹ = R.s 2 ∧ g * a2 * g⁻¹ = R.s 1) := by
  obtain ⟨g1, T, hT, e1⟩ := R.stage1_conj h1
  have o01' : orderOf (g1 * a0 * g1⁻¹ * R.s T) = 3 := by
    rw [← e1, show g1 * a0 * g1⁻¹ * (g1 * a1 * g1⁻¹) = g1 * (a0 * a1) * g1⁻¹ by group,
      orderOf_conj_eq, o01]
  have o12' : orderOf (R.s T * (g1 * a2 * g1⁻¹)) = 4 := by
    rw [← e1, show g1 * a1 * g1⁻¹ * (g1 * a2 * g1⁻¹) = g1 * (a1 * a2) * g1⁻¹ by group,
      orderOf_conj_eq, o12]
  have o02' : orderOf (g1 * a0 * g1⁻¹ * (g1 * a2 * g1⁻¹)) = 2 := by
    rw [show g1 * a0 * g1⁻¹ * (g1 * a2 * g1⁻¹) = g1 * (a0 * a2) * g1⁻¹ by group,
      orderOf_conj_eq, o02]
  rcases hT with rfl | rfl
  · obtain ⟨g2, c0, c1, c2⟩ := R.stage2B_conj (h0.conj g1) (h2.conj g1) o01' o12' o02'
    refine ⟨g2 * g1, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rw [show g2 * g1 * a0 * (g2 * g1)⁻¹ = g2 * (g1 * a0 * g1⁻¹) * g2⁻¹ by group]
      exact c0
    · rw [show g2 * g1 * a1 * (g2 * g1)⁻¹ = g2 * (g1 * a1 * g1⁻¹) * g2⁻¹ by group, e1]
      exact c1
    · rw [show g2 * g1 * a2 * (g2 * g1)⁻¹ = g2 * (g1 * a2 * g1⁻¹) * g2⁻¹ by group]
      exact c2
  · obtain ⟨g2, c0, c1, c2⟩ := R.stage2C_conj (h0.conj g1) (h2.conj g1) o01' o12' o02'
    refine ⟨g2 * g1, Or.inr ⟨?_, ?_, ?_⟩⟩
    · rw [show g2 * g1 * a0 * (g2 * g1)⁻¹ = g2 * (g1 * a0 * g1⁻¹) * g2⁻¹ by group]
      exact c0
    · rw [show g2 * g1 * a1 * (g2 * g1)⁻¹ = g2 * (g1 * a1 * g1⁻¹) * g2⁻¹ by group, e1]
      exact c1
    · rw [show g2 * g1 * a2 * (g2 * g1)⁻¹ = g2 * (g1 * a2 * g1⁻¹) * g2⁻¹ by group]
      exact c2


@[expose] def ClSet (Cl : List ℕ) : Set W := {n | ∃ c, c ∈ Cl ∧ R.ρ n = (Rm c).toMat}

theorem mem_ClSet {Cl : List ℕ} {n : W} :
    n ∈ R.ClSet Cl ↔ ∃ c, c ∈ Cl ∧ R.ρ n = (Rm c).toMat := Iff.rfl

theorem closure_eq_top_of {S : Set W} (h : ∀ i, R.s i ∈ Subgroup.closure S) :
    Subgroup.closure S = ⊤ := by
  rw [eq_top_iff, ← R.gen]
  exact (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact h i)

theorem mem_normalizer {Cl : List ℕ} {t : W} {y : M4} (ht : R.ρ t = y.toMat)
    (hy : y.mul y = M4.one) (hn : normM y Cl) : t ∈ Subgroup.normalizer (R.ClSet Cl) := by
  have htt : t * t = 1 := by
    apply R.inj
    rw [R.rho_mul ht ht, hy, M4.toMat_one, map_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  rw [hti]
  constructor
  · intro hn0
    obtain ⟨c, hc, hρ⟩ := (R.mem_ClSet).1 hn0
    obtain ⟨c', hc', e⟩ := hn c hc
    refine (R.mem_ClSet).2 ⟨c', hc', ?_⟩
    rw [R.rho_mul3 ht hρ ht, e]
  · intro hn0
    obtain ⟨c, hc, hρ⟩ := (R.mem_ClSet).1 hn0
    obtain ⟨c', hc', e⟩ := hn c hc
    refine (R.mem_ClSet).2 ⟨c', hc', ?_⟩
    have hn' : n = t * (t * n * t) * t := by
      calc n = (t * t) * n * (t * t) := by rw [htt]; simp
        _ = t * (t * n * t) * t := by group
    rw [hn', R.rho_mul3 ht hρ ht, e]

theorem std_B : ∃ H : Subgroup W, H ≠ ⊤ ∧ R.s 0 ∈ H ∧ R.s 1 ∈ H ∧ R.s 2 ∈ H ∧
    ∀ t, R.IsRefl t → t ∈ H ∨ Subgroup.closure ({R.s 0, R.s 1, R.s 2, t} : Set W) = ⊤ := by
  have hi4 : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  refine ⟨Subgroup.normalizer (R.ClSet ClB), ?_, ?_, ?_, ?_, ?_⟩
  · intro htop
    have h3 : R.s 3 ∈ Subgroup.normalizer (R.ClSet ClB) := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_set_normalizer_iff] at h3
    obtain ⟨c, hc, hcm⟩ := stdB_mem
    have hs2 : R.s 2 ∈ R.ClSet ClB := (R.mem_ClSet).2 ⟨c, hc, by rw [R.hs 2, hcm]⟩
    obtain ⟨c', hc', hρ⟩ := (R.mem_ClSet).1 ((h3 (R.s 2)).1 hs2)
    rw [R.s_inv 3, R.rho_mul3 (R.hs 3) (R.hs 2) (R.hs 3)] at hρ
    exact stdB_notnorm c' hc' (M4.toMat_injective hρ)
  · exact R.mem_normalizer (R.hs 0) (Sm_sq 0) stdB_norm.1
  · exact R.mem_normalizer (R.hs 1) (Sm_sq 1) stdB_norm.2.1
  · exact R.mem_normalizer (R.hs 2) (Sm_sq 2) stdB_norm.2.2
  · intro t ht
    obtain ⟨y, hy, ρy⟩ := R.refl_rep ht
    rcases dichB y hy with hn | ⟨hc, hlet⟩
    · exact Or.inl (R.mem_normalizer ρy (Rm_sq y hy) hn)
    · right
      have heq : R.wd (WB y) * R.s 3 * (R.wd (WB y))⁻¹ = t := R.conj_wd_eq (R.hs 3) ρy hc
      have hg : R.wd (WB y) ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2, t} : Set W) := by
        unfold wd
        apply list_prod_mem
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        refine Subgroup.subset_closure ?_
        have hne := hlet i hi
        rcases hi4 i with rfl | rfl | rfl | rfl
        · simp
        · simp
        · simp
        · exact absurd rfl hne
      have h3 : R.s 3 ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2, t} : Set W) := by
        have h' : R.s 3 = (R.wd (WB y))⁻¹ * t * R.wd (WB y) := by rw [← heq]; group
        rw [h']
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg)
          (Subgroup.subset_closure (by simp))) hg
      apply R.closure_eq_top_of
      intro i
      rcases hi4 i with rfl | rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact h3

theorem std_C : ∃ H : Subgroup W, H ≠ ⊤ ∧ R.s 3 ∈ H ∧ R.s 2 ∈ H ∧ R.s 1 ∈ H ∧
    ∀ t, R.IsRefl t → t ∈ H ∨ Subgroup.closure ({R.s 3, R.s 2, R.s 1, t} : Set W) = ⊤ := by
  have hi4 : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  refine ⟨Subgroup.normalizer (R.ClSet ClC), ?_, ?_, ?_, ?_, ?_⟩
  · intro htop
    have h0 : R.s 0 ∈ Subgroup.normalizer (R.ClSet ClC) := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_set_normalizer_iff] at h0
    obtain ⟨c, hc, hcm⟩ := stdC_mem
    have hs1 : R.s 1 ∈ R.ClSet ClC := (R.mem_ClSet).2 ⟨c, hc, by rw [R.hs 1, hcm]⟩
    obtain ⟨c', hc', hρ⟩ := (R.mem_ClSet).1 ((h0 (R.s 1)).1 hs1)
    rw [R.s_inv 0, R.rho_mul3 (R.hs 0) (R.hs 1) (R.hs 0)] at hρ
    exact stdC_notnorm c' hc' (M4.toMat_injective hρ)
  · exact R.mem_normalizer (R.hs 3) (Sm_sq 3) stdC_norm.1
  · exact R.mem_normalizer (R.hs 2) (Sm_sq 2) stdC_norm.2.1
  · exact R.mem_normalizer (R.hs 1) (Sm_sq 1) stdC_norm.2.2
  · intro t ht
    obtain ⟨y, hy, ρy⟩ := R.refl_rep ht
    rcases dichC y hy with hn | ⟨hc, hlet⟩
    · exact Or.inl (R.mem_normalizer ρy (Rm_sq y hy) hn)
    · right
      have heq : R.wd (WC y) * R.s 0 * (R.wd (WC y))⁻¹ = t := R.conj_wd_eq (R.hs 0) ρy hc
      have hg : R.wd (WC y) ∈ Subgroup.closure ({R.s 3, R.s 2, R.s 1, t} : Set W) := by
        unfold wd
        apply list_prod_mem
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        refine Subgroup.subset_closure ?_
        have hne := hlet i hi
        rcases hi4 i with rfl | rfl | rfl | rfl
        · exact absurd rfl hne
        · simp
        · simp
        · simp
      have h0 : R.s 0 ∈ Subgroup.closure ({R.s 3, R.s 2, R.s 1, t} : Set W) := by
        have h' : R.s 0 = (R.wd (WC y))⁻¹ * t * R.wd (WC y) := by rw [← heq]; group
        rw [h']
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg)
          (Subgroup.subset_closure (by simp))) hg
      apply R.closure_eq_top_of
      intro i
      rcases hi4 i with rfl | rfl | rfl | rfl
      · exact h0
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)

@[expose] def conjSub (g : W) (H : Subgroup W) : Subgroup W where
  carrier := {w | g * w * g⁻¹ ∈ H}
  mul_mem' := by
    intro a b ha hb
    have h : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    show g * (a * b) * g⁻¹ ∈ H
    rw [h]
    exact H.mul_mem ha hb
  one_mem' := by
    show g * 1 * g⁻¹ ∈ H
    simp
  inv_mem' := by
    intro a ha
    have h : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    show g * a⁻¹ * g⁻¹ ∈ H
    rw [h]
    exact H.inv_mem ha

theorem mem_conjSub {g : W} {H : Subgroup W} {w : W} :
    w ∈ conjSub g H ↔ g * w * g⁻¹ ∈ H := Iff.rfl

theorem transport {a0 a1 a2 b0 b1 b2 : W} (g : W) (e0 : g * a0 * g⁻¹ = b0)
    (e1 : g * a1 * g⁻¹ = b1) (e2 : g * a2 * g⁻¹ = b2) {H₀ : Subgroup W} (hne : H₀ ≠ ⊤)
    (hb0 : b0 ∈ H₀) (hb1 : b1 ∈ H₀) (hb2 : b2 ∈ H₀)
    (hd : ∀ t, R.IsRefl t → t ∈ H₀ ∨ Subgroup.closure ({b0, b1, b2, t} : Set W) = ⊤) :
    ∃ H : Subgroup W, H ≠ ⊤ ∧ a0 ∈ H ∧ a1 ∈ H ∧ a2 ∈ H ∧
      ∀ t, R.IsRefl t → t ∈ H ∨ Subgroup.closure ({a0, a1, a2, t} : Set W) = ⊤ := by
  refine ⟨conjSub g H₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro htop
    apply hne
    rw [eq_top_iff]
    intro x _
    have h1 : g⁻¹ * x * g ∈ conjSub g H₀ := by rw [htop]; exact Subgroup.mem_top _
    rw [mem_conjSub] at h1
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [h2] at h1
  · rw [mem_conjSub, e0]; exact hb0
  · rw [mem_conjSub, e1]; exact hb1
  · rw [mem_conjSub, e2]; exact hb2
  · intro t ht
    rcases hd (g * t * g⁻¹) (ht.conj g) with h | h
    · exact Or.inl (mem_conjSub.2 h)
    · right
      rw [eq_top_iff]
      intro w _
      have hw : g * w * g⁻¹ ∈ Subgroup.closure ({b0, b1, b2, g * t * g⁻¹} : Set W) := by
        rw [h]; exact Subgroup.mem_top _
      have hle : Subgroup.closure ({b0, b1, b2, g * t * g⁻¹} : Set W) ≤
          conjSub g⁻¹ (Subgroup.closure ({a0, a1, a2, t} : Set W)) := by
        rw [Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rw [SetLike.mem_coe, mem_conjSub]
        rcases hx with hx | hx | hx | hx
        · rw [hx, ← e0, show g⁻¹ * (g * a0 * g⁻¹) * g⁻¹⁻¹ = a0 by group]
          exact Subgroup.subset_closure (by simp)
        · rw [hx, ← e1, show g⁻¹ * (g * a1 * g⁻¹) * g⁻¹⁻¹ = a1 by group]
          exact Subgroup.subset_closure (by simp)
        · rw [hx, ← e2, show g⁻¹ * (g * a2 * g⁻¹) * g⁻¹⁻¹ = a2 by group]
          exact Subgroup.subset_closure (by simp)
        · rw [hx, show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group]
          exact Subgroup.subset_closure (by simp)
      have hw' := hle hw
      rw [mem_conjSub, show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at hw'
      exact hw'

theorem core_of_rep {a : Fin 3 → W} (ha : ∀ i, R.IsRefl (a i)) (o01 : orderOf (a 0 * a 1) = 3)
    (o12 : orderOf (a 1 * a 2) = 4) (o02 : orderOf (a 0 * a 2) = 2) :
    ∃ H : Subgroup W, H ≠ ⊤ ∧ (∀ i, a i ∈ H) ∧
      ∀ t, R.IsRefl t → t ∈ H ∨ Subgroup.closure ({a 0, a 1, a 2, t} : Set W) = ⊤ := by
  have hi3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  obtain ⟨g, hg | hg⟩ := R.classify (ha 0) (ha 1) (ha 2) o01 o12 o02
  · obtain ⟨H₀, hne, h0, h1, h2, hd⟩ := R.std_B
    obtain ⟨H, hne', ha0, ha1, ha2, hd'⟩ := R.transport g hg.1 hg.2.1 hg.2.2 hne h0 h1 h2 hd
    refine ⟨H, hne', ?_, hd'⟩
    intro i
    rcases hi3 i with rfl | rfl | rfl
    · exact ha0
    · exact ha1
    · exact ha2
  · obtain ⟨H₀, hne, h0, h1, h2, hd⟩ := R.std_C
    obtain ⟨H, hne', ha0, ha1, ha2, hd'⟩ := R.transport g hg.1 hg.2.1 hg.2.2 hne h0 h1 h2 hd
    refine ⟨H, hne', ?_, hd'⟩
    intro i
    rcases hi3 i with rfl | rfl | rfl
    · exact ha0
    · exact ha1
    · exact ha2

end F4Rep

end CFSG.StandardType.F4Model

end

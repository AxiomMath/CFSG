module

public import CFSG.Quasithin.H13.L32NKGG22

public section

namespace CFSG.Quasithin.H13.KGSp6

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (B : LinearMap.BilinForm (ZMod 2) V)

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

theorem zmod2_eq_one {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a; decide

theorem alt_symm (halt : ∀ v, B v v = 0) (x y : V) : B x y = B y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact (key _ _ h).symm

@[expose] def IsFrame (k : ℕ) (e f : ℕ → V) : Prop :=
  ∀ i j, i < k → j < k →
    B (e i) (f j) = (if i = j then 1 else 0) ∧ B (e i) (e j) = 0 ∧ B (f i) (f j) = 0

@[expose] def proj (k : ℕ) (e f : ℕ → V) (g : V) : V :=
  g + ∑ m ∈ Finset.range k, B g (f m) • e m + ∑ m ∈ Finset.range k, B g (e m) • f m

theorem proj_orth (halt : ∀ v, B v v = 0) {k : ℕ} {e f : ℕ → V} (hF : IsFrame B k e f) (g : V)
    {j : ℕ} (hj : j < k) : B (proj B k e f g) (e j) = 0 ∧ B (proj B k e f g) (f j) = 0 := by
  have hef : ∀ m, m < k → B (f m) (e j) = if j = m then 1 else 0 := fun m hm => by
    rw [alt_symm B halt]; exact (hF j m hj hm).1
  constructor
  · simp only [proj, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    have h1 : ∑ m ∈ Finset.range k, B g (f m) * B (e m) (e j) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [(hF m j (Finset.mem_range.1 hm) hj).2.1, mul_zero]
    have h2 : ∑ m ∈ Finset.range k, B g (e m) * B (f m) (e j) = B g (e j) := by
      rw [Finset.sum_congr rfl fun m hm => by rw [hef m (Finset.mem_range.1 hm)]]
      simp [mul_ite, Finset.sum_ite_eq, hj]
    rw [h1, h2, add_zero]
    exact zmod2_add_self _
  · simp only [proj, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    have h1 : ∑ m ∈ Finset.range k, B g (e m) * B (f m) (f j) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [(hF m j (Finset.mem_range.1 hm) hj).2.2, mul_zero]
    have h2 : ∑ m ∈ Finset.range k, B g (f m) * B (e m) (f j) = B g (f j) := by
      rw [Finset.sum_congr rfl fun m hm => by rw [(hF m j (Finset.mem_range.1 hm) hj).1]]
      simp [mul_ite, Finset.sum_ite_eq', hj]
    rw [h1, h2, add_zero]
    exact zmod2_add_self _


variable [Finite V]

theorem card_eq_64 (hdim : Module.finrank (ZMod 2) V = 6) : Nat.card V = 64 := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [hdim] at h
  simpa [Nat.card_zmod] using h

theorem exists_next (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hdim : Module.finrank (ZMod 2) V = 6) {k : ℕ} (hk : k < 3) {e f : ℕ → V}
    (hF : IsFrame B k e f) : ∃ e' f' : ℕ → V, IsFrame B (k + 1) e' f' := by
  classical
  have hcard := card_eq_64 hdim
  have hfin : Fintype V := Fintype.ofFinite V
  obtain ⟨e₀, hne, he₀'⟩ : ∃ e₀ : V, e₀ ≠ 0 ∧ ∀ i, i < k → B e₀ (e i) = 0 ∧ B e₀ (f i) = 0 := by
    let φ : V → (Fin k ⊕ Fin k → ZMod 2) := fun v =>
      Sum.elim (fun i => B v (e i)) (fun i => B v (f i))
    have hlt : Fintype.card (Fin k ⊕ Fin k → ZMod 2) < Fintype.card V := by
      rw [← Nat.card_eq_fintype_card (α := V), hcard, Fintype.card_fun, Fintype.card_sum,
        Fintype.card_fin, ZMod.card]
      interval_cases k <;> norm_num
    obtain ⟨x, y, hxy, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hlt
    have hyy : ∀ v : V, v + v = 0 := fun v => by
      rw [← two_smul (ZMod 2) v]
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_smul]
    refine ⟨x + y, fun h => hxy ?_, fun i hi => ?_⟩
    · calc x = x + (y + y) := by rw [hyy, add_zero]
        _ = (x + y) + y := by rw [add_assoc]
        _ = y := by rw [h, zero_add]
    have h1 : B x (e i) = B y (e i) := congrFun hφ (Sum.inl ⟨i, hi⟩)
    have h2 : B x (f i) = B y (f i) := congrFun hφ (Sum.inr ⟨i, hi⟩)
    refine ⟨?_, ?_⟩
    · rw [map_add, LinearMap.add_apply, h1]
      exact zmod2_add_self _
    · rw [map_add, LinearMap.add_apply, h2]
      exact zmod2_add_self _
  obtain ⟨g, hg⟩ : ∃ g, B e₀ g ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (hnd e₀ h)
  have hg1 : B e₀ g = 1 := zmod2_eq_one hg
  have hf₀ : ∀ j, j < k → B (proj B k e f g) (e j) = 0 ∧ B (proj B k e f g) (f j) = 0 :=
    fun j hj => proj_orth B halt hF g hj
  have hef₀ : B e₀ (proj B k e f g) = 1 := by
    have h1 : ∑ m ∈ Finset.range k, B g (f m) * B e₀ (e m) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [(he₀' m (Finset.mem_range.1 hm)).1, mul_zero]
    have h2 : ∑ m ∈ Finset.range k, B g (e m) * B e₀ (f m) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [(he₀' m (Finset.mem_range.1 hm)).2, mul_zero]
    simp only [proj, map_add, map_sum, map_smul, smul_eq_mul]
    rw [h1, h2, add_zero, add_zero, hg1]
  set f₀ := proj B k e f g with hf₀def
  refine ⟨fun i => if i = k then e₀ else e i, fun i => if i = k then f₀ else f i, ?_⟩
  intro i j hi hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hik <;>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hjk
  · simpa [ne_of_lt hi', ne_of_lt hj'] using hF i j hi' hj'
  · have h1 : B (e i) f₀ = 0 := (alt_symm B halt _ _).trans (hf₀ i hi').1
    have h2 : B (e i) e₀ = 0 := (alt_symm B halt _ _).trans (he₀' i hi').1
    have h3 : B (f i) f₀ = 0 := (alt_symm B halt _ _).trans (hf₀ i hi').2
    simp [hjk, ne_of_lt hi', h1, h2, h3]
  · have hkj : k ≠ j := by omega
    have h1 : B e₀ (f j) = 0 := (he₀' j hj').2
    have h2 : B e₀ (e j) = 0 := (he₀' j hj').1
    have h3 : B f₀ (f j) = 0 := (hf₀ j hj').2
    simp [hik, ne_of_lt hj', hkj, h1, h2, h3]
  · simp [hik, hjk, hef₀, halt]

theorem exists_frame (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hdim : Module.finrank (ZMod 2) V = 6) : ∀ k, k ≤ 3 → ∃ e f : ℕ → V, IsFrame B k e f := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨fun _ => 0, fun _ => 0, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨e, f, hF⟩ := ih (by omega)
    exact exists_next B halt hnd hdim (by omega) hF


theorem exists_darboux (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hdim : Module.finrank (ZMod 2) V = 6) :
    ∃ b : Module.Basis (Fin 6) (ZMod 2) V, ∀ i j, B (b i) (b j) = KGCert.g22Form i j := by
  obtain ⟨e, f, hF⟩ := exists_frame B halt hnd hdim 3 le_rfl
  have fee : ∀ i j, i < 3 → j < 3 → B (e i) (e j) = 0 := fun i j hi hj => (hF i j hi hj).2.1
  have fff : ∀ i j, i < 3 → j < 3 → B (f i) (f j) = 0 := fun i j hi hj => (hF i j hi hj).2.2
  have fef : ∀ i j, i < 3 → j < 3 → B (e i) (f j) = if i = j then 1 else 0 :=
    fun i j hi hj => (hF i j hi hj).1
  have ffe : ∀ i j, i < 3 → j < 3 → B (f i) (e j) = if j = i then 1 else 0 := fun i j hi hj => by
    rw [alt_symm B halt]
    exact fef j i hj hi
  let b : Fin 6 → V := fun i => if (i : ℕ) < 3 then e i else f (i - 3)
  have hgram : ∀ i j, B (b i) (b j) = KGCert.g22Form i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [b, KGCert.g22Form, fee, fff, fef, ffe]
  have hli : LinearIndependent (ZMod 2) b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have key : ∀ j : Fin 6, ∑ i, c i * KGCert.g22Form i j = 0 := fun j => by
      have h := congrArg (fun v => B v (b j)) hc
      simpa [map_sum, hgram] using h
    fin_cases i
    · simpa [Fin.sum_univ_six, KGCert.g22Form] using key 3
    · simpa [Fin.sum_univ_six, KGCert.g22Form] using key 4
    · simpa [Fin.sum_univ_six, KGCert.g22Form] using key 5
    · simpa [Fin.sum_univ_six, KGCert.g22Form] using key 0
    · simpa [Fin.sum_univ_six, KGCert.g22Form] using key 1
    · simpa [Fin.sum_univ_six, KGCert.g22Form] using key 2
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [hdim]; rfl), fun i j => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact hgram i j

end CFSG.Quasithin.H13.KGSp6

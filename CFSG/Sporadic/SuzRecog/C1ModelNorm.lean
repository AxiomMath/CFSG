module

public import CFSG.Sporadic.SuzRecog.C1ModelT0

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.C1Model

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog

theorem card_le_card_mul_of_conj {G : Type*} [Group G] [Finite G] (K : Subgroup G) (x : G)
    (X : Set G) (hX : ∀ k ∈ K, k * x * k⁻¹ ∈ X) :
    Nat.card K ≤ Nat.card X * Nat.card ↥(K ⊓ centralizer ({x} : Set G)) := by
  classical
  let rep : G → G := fun y => if h : ∃ k ∈ K, k * x * k⁻¹ = y then h.choose else 1
  have hrep : ∀ k ∈ K, rep (k * x * k⁻¹) ∈ K ∧
      rep (k * x * k⁻¹) * x * (rep (k * x * k⁻¹))⁻¹ = k * x * k⁻¹ := by
    intro k hk
    have h : ∃ k' ∈ K, k' * x * k'⁻¹ = k * x * k⁻¹ := ⟨k, hk, rfl⟩
    simp only [rep, dite_eq_left h]
    exact h.choose_spec
  have hmem : ∀ k : K, (rep ((k : G) * x * (k : G)⁻¹))⁻¹ * k ∈ K ⊓ centralizer ({x} : Set G) := by
    intro k
    obtain ⟨h1, h2⟩ := hrep k k.2
    refine mem_inf.mpr ⟨mul_mem (inv_mem h1) k.2, mem_centralizer_singleton_iff.mpr ?_⟩
    calc (rep ((k : G) * x * (k : G)⁻¹))⁻¹ * k * x =
        (rep ((k : G) * x * (k : G)⁻¹))⁻¹ * ((k : G) * x * (k : G)⁻¹) * k := by group
      _ = (rep ((k : G) * x * (k : G)⁻¹))⁻¹ * (rep ((k : G) * x * (k : G)⁻¹) * x *
          (rep ((k : G) * x * (k : G)⁻¹))⁻¹) * k := by rw [h2]
      _ = x * ((rep ((k : G) * x * (k : G)⁻¹))⁻¹ * k) := by group
  let F : K → X × ↥(K ⊓ centralizer ({x} : Set G)) := fun k =>
    (⟨(k : G) * x * (k : G)⁻¹, hX k k.2⟩, ⟨_, hmem k⟩)
  have hF : Function.Injective F := by
    intro k k' hkk'
    have h1 : (k : G) * x * (k : G)⁻¹ = k' * x * (k' : G)⁻¹ :=
      congrArg (fun p => (p.1 : G)) hkk'
    have h2 : (rep ((k : G) * x * (k : G)⁻¹))⁻¹ * k =
        (rep ((k' : G) * x * (k' : G)⁻¹))⁻¹ * k' := congrArg (fun p => (p.2 : G)) hkk'
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective F hF

theorem card_mul_le_card_of_conj {G : Type*} [Group G] [Finite G] {K V : Subgroup G} {x : G}
    (hV : V ≤ K) (hVx : V ≤ centralizer ({x} : Set G)) (Y : Set G)
    (hY : ∀ y ∈ Y, ∃ k ∈ K, k * x * k⁻¹ = y) : Nat.card Y * Nat.card V ≤ Nat.card K := by
  classical
  choose f hfK hfx using hY
  have hconj : ∀ {v : G}, v ∈ V → v * x * v⁻¹ = x := fun hv => by
    rw [mem_centralizer_singleton_iff.mp (hVx hv), mul_inv_cancel_right]
  let F : Y × V → K := fun p => ⟨f p.1 p.1.2 * p.2, mul_mem (hfK _ _) (hV p.2.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨y, hy⟩, ⟨v, hv⟩⟩ ⟨⟨y', hy'⟩, ⟨v', hv'⟩⟩ h
    have h' : f y hy * v = f y' hy' * v' := congrArg Subtype.val h
    have e : ∀ (a b : G), b * x * b⁻¹ = x → a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := fun a b hb => by
      rw [show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group, hb]
    have hyy : y = y' := by
      rw [← hfx y hy, ← hfx y' hy', ← e (f y hy) v (hconj hv), ← e (f y' hy') v' (hconj hv'), h']
    subst hyy
    have hvv : v = v' := mul_left_cancel h'
    subst hvv
    rfl
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective F hF

theorem card_orbit_of_orbitOK {n : ℕ} {gens ginv : Array Tab} {E : Enum}
    {A : Set (Equiv.Perm (Fin n))} {x₀ : Equiv.Perm (Fin n)} {root : Tab}
    (hA : ∀ a ∈ A, ∃ j < gens.size, TabRep gens[j]! a)
    (hgens : ∀ j < gens.size, ∃ a ∈ A, TabRep gens[j]! a) (hroot : TabRep root x₀)
    (h : orbitOK n gens ginv root E = true) :
    Nat.card {g | ∃ c ∈ closure A, c * x₀ * c⁻¹ = g} = E.tabs.size := by
  obtain ⟨h1, h2, h3⟩ := conj_orbit hA hgens hroot h
  rw [← Array.length_toList]
  refine card_set_of_tabs (fun t ht => ?_) (fun g hg => ?_) h3
  · obtain ⟨c, hc, hrep⟩ := h1 t ht
    exact ⟨_, ⟨c, hc, rfl⟩, hrep⟩
  · obtain ⟨c, hc, rfl⟩ := hg
    exact h2 c hc

@[expose] noncomputable def b0Gen (j : ℕ) : Equiv.Perm (Fin 1782) :=
  if j < 4 then t0Gen j else if j = 4 then Model.w0 else if j = 5 then Model.rho1 else tau0

section Norm

theorem norm_parts : orbitOK 1782 b0Tabs b0Invs w0T b0Orbit = true ∧ b0Orbit.tabs.size = 3 ∧
    normalOK 1782 t0Enum.tabs nt0Tabs nt0Invs t0Tabs = true ∧
    orbitOK 1782 nt0Tabs nt0Invs w0T nt0Orbit = true ∧ nt0Orbit.tabs.size = 24 := by
  have h := c1Norm_check
  unfold normCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h2, beq_iff_eq.mp h3, h4, h5, beq_iff_eq.mp h6⟩

theorem tabRep_b0Tab (j : ℕ) : TabRep (b0Tab j) (b0Gen j) := by
  unfold b0Tab b0Gen
  split_ifs with h1 h2 h3
  · exact tabRep_t0Tab h1
  · exact tabRep_w0
  · exact tabRep_rho1
  · exact tabRep_tau0

theorem b0Gen_mem_B0 (j : ℕ) : b0Gen j ∈ Model.B0 := by
  have hcomm : ∀ {g : Equiv.Perm (Fin 1782)}, g ∈ invE 1 → g * Model.w0 = Model.w0 * g →
      g * r1 = r1 * g → g ∈ Model.B0 := fun hg h0 h1 =>
    ⟨hg, mem_normalizer_R0 (by rw [h0, mul_inv_cancel_right]; exact w0_mem_R0)
      (by rw [h1, mul_inv_cancel_right]; exact r1_mem_R0)⟩
  unfold b0Gen
  split_ifs with h1 h2 h3
  · exact hcomm (t0Gen_mem_invE h1) (mem_J0_iff.mp (t0Gen_mem_J0 h1)).1
      (mem_J0_iff.mp (t0Gen_mem_J0 h1)).2.1
  · exact hcomm w0_mem_invE rfl w0_comm_r1
  · exact rho1_mem_B0
  · exact tau0_mem_B0

theorem b0Gen_set : {g | ∃ j < 7, b0Gen j = g} =
    {g | ∃ i < 4, t0Gen i = g} ∪ {Model.w0, Model.rho1, tau0} := by
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    unfold b0Gen
    split_ifs with h1 h2 h3
    · exact Or.inl ⟨j, h1, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (⟨i, hi, rfl⟩ | rfl | rfl | rfl)
    · exact ⟨i, by omega, by simp [b0Gen, hi]⟩
    · exact ⟨4, by norm_num, by simp [b0Gen]⟩
    · exact ⟨5, by norm_num, by simp [b0Gen]⟩
    · exact ⟨6, by norm_num, by simp [b0Gen]⟩

theorem b0Tabs_spec : (∀ a ∈ {g | ∃ j < 7, b0Gen j = g}, ∃ j < b0Tabs.size, TabRep b0Tabs[j]! a) ∧
    ∀ j < b0Tabs.size, ∃ a ∈ {g | ∃ j < 7, b0Gen j = g}, TabRep b0Tabs[j]! a := by
  have hsize : b0Tabs.size = 7 := Array.size_ofFn
  have hget : ∀ {j : ℕ}, j < 7 → b0Tabs[j]! = b0Tab j := fun hj => getElem!_ofFn' _ hj
  refine ⟨fun a ha => ?_, fun j hj => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := ha
    exact ⟨j, by rw [hsize]; exact hj, by rw [hget hj]; exact tabRep_b0Tab j⟩
  · rw [hsize] at hj
    exact ⟨_, ⟨j, hj, rfl⟩, by rw [hget hj]; exact tabRep_b0Tab j⟩

theorem V0_le_closure_b0Gen :
    V0 ≤ closure {g | ∃ j < 7, b0Gen j = g} := by
  rw [V0_eq_closure_v0Gen, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hb : ∀ k < 7, b0Gen k ∈ closure {g | ∃ j < 7, b0Gen j = g} := fun k hk =>
    subset_closure ⟨k, hk, rfl⟩
  unfold v0Gen
  split_ifs with h1 h2 h3
  · simpa [b0Gen, h1] using hb j (by omega)
  · simpa [b0Gen] using hb 4 (by norm_num)
  · have hw := hb 4 (by norm_num)
    have hr := hb 5 (by norm_num)
    simp only [b0Gen] at hw hr
    norm_num at hw hr
    exact mul_mem (mul_mem hr hw) (inv_mem hr)
  · simpa [b0Gen] using hb 6 (by norm_num)

theorem card_B0 : Nat.card Model.B0 = 1536 := by
  have hle : closure {g | ∃ j < 7, b0Gen j = g} ≤ Model.B0 := by
    rw [closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact b0Gen_mem_B0 j
  refine le_antisymm ?_ ?_
  · have h := card_le_card_mul_of_conj Model.B0 Model.w0 {Model.w0, r1, r2} fun b hb => by
      have hR : b * Model.w0 * b⁻¹ ∈ Model.R0 :=
        (mem_normalizer_iff.mp (mem_inf.mp hb).2 Model.w0).mp w0_mem_R0
      have h1 : b * Model.w0 * b⁻¹ ≠ 1 := fun h => w0_ne_one (by
        calc Model.w0 = b⁻¹ * (b * Model.w0 * b⁻¹) * b := by group
          _ = 1 := by rw [h, mul_one, inv_mul_cancel])
      rcases mem_R0_iff.mp hR with h' | h' | h' | h'
      · exact (h1 h').elim
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    have h3 : Nat.card ↥({Model.w0, r1, r2} : Set (Equiv.Perm (Fin 1782))) ≤ 3 := by
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_pair r2_ne_r1.symm])
    have h4 : Nat.card ↥(Model.B0 ⊓ centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782)))) ≤
        512 := by
      rw [← card_V0]
      exact card_le_of_le fun g hg =>
        mem_inf.mpr ⟨(mem_inf.mp hg).2, (mem_inf.mp (mem_inf.mp hg).1).1⟩
    calc Nat.card Model.B0 ≤ _ := h
      _ ≤ 3 * 512 := Nat.mul_le_mul h3 h4
  · have hY := card_orbit_of_orbitOK b0Tabs_spec.1 b0Tabs_spec.2 tabRep_w0 norm_parts.1
    rw [norm_parts.2.1] at hY
    have h := card_mul_le_card_of_conj (V := V0) (V0_le_closure_b0Gen) (fun g hg =>
      (mem_inf.mp hg).1) {g | ∃ c ∈ closure {g | ∃ j < 7, b0Gen j = g}, c * Model.w0 * c⁻¹ = g}
      fun y hy => hy
    rw [hY, card_V0] at h
    exact h.trans (card_le_of_le hle)

theorem B0_eq :
    Model.B0 = closure ({g | ∃ i < 4, t0Gen i = g} ∪ {Model.w0, Model.rho1, tau0}) := by
  rw [← b0Gen_set]
  have hle : closure {g | ∃ j < 7, b0Gen j = g} ≤ Model.B0 := by
    rw [closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact b0Gen_mem_B0 j
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_B0]
  have hY := card_orbit_of_orbitOK b0Tabs_spec.1 b0Tabs_spec.2 tabRep_w0 norm_parts.1
  rw [norm_parts.2.1] at hY
  have h := card_mul_le_card_of_conj (V := V0) (V0_le_closure_b0Gen) (fun g hg =>
    (mem_inf.mp hg).1) {g | ∃ c ∈ closure {g | ∃ j < 7, b0Gen j = g}, c * Model.w0 * c⁻¹ = g}
    fun y hy => hy
  rwa [hY, card_V0] at h

end Norm

end CFSG.Sporadic.SuzRecog.C1Model

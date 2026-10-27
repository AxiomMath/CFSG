module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Sub
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin1

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.Quasithin.B3

@[expose] def tauL : Tab := [0, 1, 2, 3, 5, 4]

@[expose] def Z1l : List Tab := [[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 5, 4]]

theorem subOK_Z1 : subOK 6 Z1l = true := by decide +kernel

noncomputable abbrev Z1 : Subgroup (Gp 6) := subOf 6 Z1l

theorem mem_Z1 {σ : Gp 6} : σ ∈ Z1 ↔ tab σ ∈ Z1l := mem_subOf subOK_Z1

theorem tab_swap45 : tab (Equiv.swap (4 : Fin 6) 5) = tauL := by decide +kernel

theorem swap45_mem_R1 : Equiv.swap (4 : Fin 6) 5 ∈ R1 := by
  rw [mem_R1, tab_swap45]
  decide +kernel

theorem swap45_mem_Z1 : Equiv.swap (4 : Fin 6) 5 ∈ Z1 := by
  rw [mem_Z1, tab_swap45]
  decide +kernel

theorem Z1_le_R1 : Z1 ≤ R1 := fun σ hσ => by
  rw [mem_Z1] at hσ
  rw [mem_R1]
  revert hσ
  generalize tab σ = t
  decide +revert +kernel

set_option maxRecDepth 100000 in
theorem R1_big_list : ∀ X ∈ R1l.sublists, subOK 6 X = true → 1 < X.length →
    32 ≤ Fval 6 Mod.ut0 X → tauL ∈ X := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem R1_F_list : ∀ X ∈ R1l.sublists, subOK 6 X = true → Fval 6 Mod.ut0 X ≤ 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem R1_normal_list : ∀ X ∈ R1l.sublists, subOK 6 X = true → tauL ∈ X →
    (∀ h ∈ H1l, ∀ x ∈ X, cjT h x ∈ X) → (∀ t ∈ X, t ∈ Z1l) ∨ (∀ t ∈ R1l, t ∈ X) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem R1_cent_list : ∀ t ∈ R1l, (∀ m ∈ List.range 64, inWk 6 Mod.ut0 m = true →
    inNk 6 Mod.ut0 (actM 6 tauL m ^^^ m) = true → inNk 6 Mod.ut0 (actM 6 t m ^^^ m) = true) →
    t ∈ Z1l := by
  decide +kernel

theorem subOf_eq_bot_of_length_le_one {X : List Tab} (hX : subOK 6 X = true)
    (hl : X.length ≤ 1) : subOf 6 X = ⊥ := by
  have hid : idT 6 ∈ X := (subOK_spec hX).2.1
  have hall : ∀ t ∈ X, t = idT 6 := by
    intro t ht
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 (le_antisymm hl (List.length_pos_of_mem hid))
    rw [ha] at ht hid
    simp only [List.mem_singleton] at ht hid
    rw [ht, hid]
  ext x
  rw [mem_subOf hX, Subgroup.mem_bot]
  constructor
  · intro hx
    apply tab_injective
    rw [hall _ hx, tab_one]
  · intro hx
    rw [hx, tab_one]
    exact hid

theorem R1_swap_mem {K : Subgroup (Gp 6)} (hK : K ≤ R1) (hK1 : K ≠ ⊥)
    (hF : 16 ≤ Nat.card (K.map (Mod.act 6 Mod.ut0)) *
      Nat.card (fixV (K.map (Mod.act 6 Mod.ut0)))) : Equiv.swap (4 : Fin 6) 5 ∈ K := by
  revert hK1 hF
  refine forall_le_subOf subOK_lists.2.2.2.1 (fun K => K ≠ ⊥ → 16 ≤
    Nat.card (K.map (Mod.act 6 Mod.ut0)) * Nat.card (fixV (K.map (Mod.act 6 Mod.ut0))) →
      Equiv.swap (4 : Fin 6) 5 ∈ K) ?_ K hK
  intro X hXL hX hne hF
  have h2 := card_mul_fix_eq hX
  have hlen : 1 < X.length := by
    by_contra hle
    exact hne (subOf_eq_bot_of_length_le_one hX (by omega))
  have := R1_big_list X (List.mem_sublists.2 hXL) hX hlen (by omega)
  rw [mem_subOf hX, tab_swap45]
  exact this

theorem R1_F_le {K : Subgroup (Gp 6)} (hK : K ≤ R1) :
    Nat.card (K.map (Mod.act 6 Mod.ut0)) * Nat.card (fixV (K.map (Mod.act 6 Mod.ut0))) ≤ 16 := by
  refine forall_le_subOf subOK_lists.2.2.2.1 (fun K =>
    Nat.card (K.map (Mod.act 6 Mod.ut0)) * Nat.card (fixV (K.map (Mod.act 6 Mod.ut0))) ≤ 16) ?_
    K hK
  intro X hXL hX
  have h2 := card_mul_fix_eq hX
  have := R1_F_list X (List.mem_sublists.2 hXL) hX
  omega

theorem tab_cj (h k : Gp 6) : tab (h * k * h⁻¹) = cjT (tab h) (tab k) := by
  unfold cjT
  rw [tab_mul, tab_mul, tab_inv]

theorem R1_normal_cases {K : Subgroup (Gp 6)} (hK : K ≤ R1) (hτ : Equiv.swap (4 : Fin 6) 5 ∈ K)
    (hN : ∀ h ∈ H1, ∀ k ∈ K, h * k * h⁻¹ ∈ K) : K = Z1 ∨ K = R1 := by
  revert hτ hN
  refine forall_le_subOf subOK_lists.2.2.2.1 (fun K => Equiv.swap (4 : Fin 6) 5 ∈ K →
    (∀ h ∈ H1, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → K = Z1 ∨ K = R1) ?_ K hK
  intro X hXL hX hτ hN
  have hτX : tauL ∈ X := by
    rw [mem_subOf hX, tab_swap45] at hτ
    exact hτ
  have hidX : idT 6 ∈ X := (subOK_spec hX).2.1
  have hcj : ∀ h ∈ H1l, ∀ x ∈ X, cjT h x ∈ X := by
    intro h' hh' x hx
    obtain ⟨h, rfl⟩ := exists_tab_eq ((subOK_spec subOK_lists.2.1).1 h' hh')
    obtain ⟨k, rfl⟩ := exists_tab_eq ((subOK_spec hX).1 x hx)
    rw [← tab_cj, ← mem_subOf hX]
    exact hN h ((mem_H1).2 hh') k ((mem_subOf hX).2 hx)
  rcases R1_normal_list X (List.mem_sublists.2 hXL) hX hτX hcj with h1 | h1
  · left
    apply le_antisymm
    · intro σ hσ
      rw [mem_subOf hX] at hσ
      rw [mem_Z1]
      exact h1 _ hσ
    · intro σ hσ
      rw [mem_Z1] at hσ
      rw [mem_subOf hX]
      simp only [Z1l, List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with h2 | h2
      · rw [h2]; exact hidX
      · rw [h2]; exact hτX
  · right
    apply le_antisymm
    · intro σ hσ
      rw [mem_subOf hX] at hσ
      exact (mem_R1).2 (hXL.subset hσ)
    · intro σ hσ
      rw [mem_R1] at hσ
      rw [mem_subOf hX]
      exact h1 _ hσ

theorem R1_cent_fix {σ : Gp 6} (hσ : σ ∈ R1)
    (h : ∀ v ∈ fixV (Z1.map (Mod.act 6 Mod.ut0)), Mod.act 6 Mod.ut0 σ v = v) : σ ∈ Z1 := by
  rw [mem_Z1]
  refine R1_cent_list _ ((mem_R1).1 hσ) fun m _ hmW hτm => ?_
  have hmem : toV 6 Mod.ut0 m ∈ fixV (Z1.map (Mod.act 6 Mod.ut0)) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    rw [mem_Z1] at hz
    simp only [Z1l, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz
    · have : z = 1 := tab_injective (by rw [hz, tab_one]; rfl)
      subst this
      simp
    · have : z = Equiv.swap (4 : Fin 6) 5 := tab_injective (by rw [hz, tab_swap45]; rfl)
      subst this
      exact (act_fix_iff hmW _).2 (by rw [tab_swap45]; exact hτm)
  exact (act_fix_iff hmW σ).1 (h _ hmem)

theorem rank_R1 : rk R1 = 3 ∧ rkIdx (fixV (R1.map (Mod.act 6 Mod.ut0))) = 3 := by
  have h := rank_data (n := 6) (by norm_num) Mod.ut0 subOK_lists.2.2.2.1 (r := 3) (s := 3)
    (by decide +kernel) (by decide +kernel)
  exact ⟨h.1, h.2.1⟩

theorem rank_Z1 : rk Z1 = 1 ∧ rkIdx (fixV (Z1.map (Mod.act 6 Mod.ut0))) = 1 := by
  have h := rank_data (n := 6) (by norm_num) Mod.ut0 subOK_Z1 (r := 1) (s := 1)
    (by decide +kernel) (by decide +kernel)
  exact ⟨h.1, h.2.1⟩

end CFSG.Quasithin.H13.U3.GC137

module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionData
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentFusion

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

theorem vecE_mem_E (a : Fin 4 → ZMod 2) : D.vecE a ∈ D.E := by
  unfold vecE
  exact D.E.mul_mem (D.E.mul_mem (D.E.mul_mem
    (D.E.pow_mem (subset_closure (by simp)) _)
    (D.E.pow_mem (subset_closure (by simp)) _))
    (D.E.pow_mem (subset_closure (by simp)) _))
    (D.E.pow_mem (subset_closure (by simp)) _)

theorem vecE_zero : D.vecE 0 = 1 := by
  simp [vecE]

private theorem pow_add_zmod2 {x : G} (hx : x ^ 2 = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  have hord : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have hmod : a.val + b.val ≡ (a + b).val [MOD 2] := by
    rw [ZMod.val_add]
    exact (Nat.mod_modEq (a.val + b.val) 2).symm
  have hmod' : a.val + b.val ≡ (a + b).val [MOD orderOf x] :=
    Nat.ModEq.of_dvd hord hmod
  rw [← pow_add, pow_eq_pow_iff_modEq.mpr hmod']

theorem vecE_add (a b : Fin 4 → ZMod 2) : D.vecE (a + b) = D.vecE a * D.vecE b := by
  change D.eb 0 ^ ((a + b) 0).val * D.eb 1 ^ ((a + b) 1).val *
    D.eb 2 ^ ((a + b) 2).val * D.eb 3 ^ ((a + b) 3).val =
    (D.eb 0 ^ (a 0).val * D.eb 1 ^ (a 1).val * D.eb 2 ^ (a 2).val *
      D.eb 3 ^ (a 3).val) * (D.eb 0 ^ (b 0).val * D.eb 1 ^ (b 1).val *
      D.eb 2 ^ (b 2).val * D.eb 3 ^ (b 3).val)
  simp only [Pi.add_apply]
  rw [pow_add_zmod2 (by rw [pow_two]; exact D.t_mul_t),
    pow_add_zmod2 (by rw [pow_two]; exact D.u_mul_u),
    pow_add_zmod2 (by rw [pow_two]; exact D.v_mul_v),
    pow_add_zmod2 (by rw [pow_two]; exact D.w_mul_w)]
  have hcomm : ∀ i j : Fin 4, Commute (D.eb i) (D.eb j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [eb, D.t_commute_u, D.commute_t_v, D.commute_t_w, D.commute_u_v,
        D.commute_u_w, D.commute_v_w, D.t_commute_u.symm, D.commute_t_v.symm,
        D.commute_t_w.symm, D.commute_u_v.symm, D.commute_u_w.symm, D.commute_v_w.symm]
  have hpc : ∀ i j : Fin 4, D.eb i ^ (a i).val * D.eb j ^ (b j).val =
      D.eb j ^ (b j).val * D.eb i ^ (a i).val :=
    fun i j => (hcomm i j).pow_pow _ _ |>.eq
  grind

private theorem vecE_mul_self (a : Fin 4 → ZMod 2) : D.vecE a * D.vecE a = 1 := by
  rw [← D.vecE_add]
  have h : a + a = 0 := funext fun i => CharTwo.add_self_eq_zero (a i)
  rw [h, D.vecE_zero]

theorem mem_E_iff {x : G} : x ∈ D.E ↔ ∃ a, D.vecE a = x := by
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun x _ => ∃ a, D.vecE a = x) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨![1, 0, 0, 0], by simp [vecE, ZMod.val_one]⟩
      · exact ⟨![0, 1, 0, 0], by simp [vecE, ZMod.val_one]⟩
      · exact ⟨![0, 0, 1, 0], by simp [vecE, ZMod.val_one]⟩
      · exact ⟨![0, 0, 0, 1], by simp [vecE, ZMod.val_one]⟩
    · exact ⟨0, D.vecE_zero⟩
    · rintro x y _ _ ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a + b, by rw [D.vecE_add, ha, hb]⟩
    · rintro x _ ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [← ha]
      exact (inv_eq_of_mul_eq_one_right (D.vecE_mul_self a)).symm
  · rintro ⟨a, rfl⟩
    exact D.vecE_mem_E a

theorem vecE_injective : Function.Injective D.vecE := by
  classical
  let f : (Fin 4 → ZMod 2) → D.E := fun a => ⟨D.vecE a, D.vecE_mem_E a⟩
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha⟩ := D.mem_E_iff.mp y.2
    exact ⟨a, Subtype.ext ha⟩
  have hcard : Nat.card (Fin 4 → ZMod 2) = Nat.card D.E := by
    rw [D.card_E]
    simp
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcard⟩
  intro a b hab
  exact hbij.1 (Subtype.ext hab)

theorem E_le_S : D.E ≤ D.S := by
  change closure {D.t, D.u, D.v, D.w} ≤ D.S
  refine (Subgroup.closure_le D.S).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have ht : D.h1 ^ 2 = D.t := by
      rw [h1, ← map_pow, hM_sq, ← D.t_eq_i1]
    rw [← ht]
    exact D.S.pow_mem (subset_closure (by simp)) 2
  · exact subset_closure (by simp)
  · rw [v]
    exact D.S.mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · rw [w]
    exact D.S.mul_mem (subset_closure (by simp)) (subset_closure (by simp))

private theorem conj_h1_t : D.h1⁻¹ * D.t * D.h1 = D.t :=
  (D.t_commute_i1 hM).symm.inv_mul_cancel

private theorem conj_h1_u : D.h1⁻¹ * D.u * D.h1 = D.t * D.u * D.v := by
  have h1inv : D.h1⁻¹ = D.t * D.h1 := by
    rw [h1, ← map_inv, ← neg_hM, D.i1_neg, ← h1]
  calc D.h1⁻¹ * D.u * D.h1
      = D.h1⁻¹ * (D.u * D.h1) := by group
    _ = D.h1⁻¹ * (D.h2 * D.u) := by rw [h1, D.u_mul_i1, ← h2]
    _ = (D.h1⁻¹ * D.h2) * D.u := by group
    _ = ((D.t * D.h1) * D.h2) * D.u := by rw [h1inv]
    _ = (D.t * (D.h1 * D.h2)) * D.u := by
        rw [mul_assoc (D.t) (D.h1) (D.h2)]
    _ = (D.t * D.v) * D.u := by rw [← v]
    _ = D.t * (D.v * D.u) := by group
    _ = D.t * (D.u * D.v) := by rw [D.commute_u_v.eq.symm]
    _ = D.t * D.u * D.v := by group

private theorem conj_h1_v : D.h1⁻¹ * D.v * D.h1 = D.v := by
  have hv : Commute D.h1 D.v := by
    rw [v]
    exact Commute.mul_right (Commute.refl D.h1) (D.commute hM hM)
  exact hv.inv_mul_cancel

private theorem conj_h1_w : D.h1⁻¹ * D.w * D.h1 = D.t * D.w := by
  have hc1 : D.h1⁻¹ * D.c1 * D.h1 = D.t * D.c1 := by
    have h : D.h1⁻¹ * D.c1 * D.h1 = D.i1 (hM⁻¹ * cM * hM) := by
      rw [h1, c1, ← map_inv, ← map_mul, ← map_mul]
    rw [h, show hM⁻¹ * cM * hM = -cM by decide, D.i1_neg, c1]
  have hc2 : D.h1⁻¹ * D.c2 * D.h1 = D.c2 :=
    (D.commute hM cM).inv_mul_cancel
  calc D.h1⁻¹ * D.w * D.h1
      = (D.h1⁻¹ * D.c1 * D.h1) * (D.h1⁻¹ * D.c2 * D.h1) := by
        rw [w]; group
    _ = (D.t * D.c1) * D.c2 := by rw [hc1, hc2]
    _ = D.t * D.w := by rw [w, mul_assoc]

theorem conj_h1_eb : D.h1⁻¹ * D.t * D.h1 = D.t ∧ D.h1⁻¹ * D.u * D.h1 = D.t * D.u * D.v ∧
    D.h1⁻¹ * D.v * D.h1 = D.v ∧ D.h1⁻¹ * D.w * D.h1 = D.t * D.w :=
  ⟨D.conj_h1_t, D.conj_h1_u, D.conj_h1_v, D.conj_h1_w⟩

private theorem conj_c1_t : D.c1⁻¹ * D.t * D.c1 = D.t :=
  (D.t_commute_i1 cM).symm.inv_mul_cancel

private theorem conj_c1_u : D.c1⁻¹ * D.u * D.c1 = D.t * D.u * D.w := by
  have hc1inv : D.c1⁻¹ = D.t * D.c1 := by
    rw [c1, ← map_inv, show cM⁻¹ = -cM by decide, D.i1_neg, ← c1]
  calc D.c1⁻¹ * D.u * D.c1
      = D.c1⁻¹ * (D.u * D.c1) := by group
    _ = D.c1⁻¹ * (D.c2 * D.u) := by rw [c1, D.u_mul_i1, ← c2]
    _ = (D.c1⁻¹ * D.c2) * D.u := by group
    _ = ((D.t * D.c1) * D.c2) * D.u := by rw [hc1inv]
    _ = (D.t * (D.c1 * D.c2)) * D.u := by
        rw [mul_assoc (D.t) (D.c1) (D.c2)]
    _ = (D.t * D.w) * D.u := by rw [← w]
    _ = D.t * (D.w * D.u) := by group
    _ = D.t * (D.u * D.w) := by rw [D.commute_u_w.eq.symm]
    _ = D.t * D.u * D.w := by group

private theorem conj_c1_v : D.c1⁻¹ * D.v * D.c1 = D.t * D.v := by
  have hh1 : D.c1⁻¹ * D.h1 * D.c1 = D.t * D.h1 := by
    have h : D.c1⁻¹ * D.h1 * D.c1 = D.i1 (cM⁻¹ * hM * cM) := by
      rw [h1, c1, ← map_inv, ← map_mul, ← map_mul]
    rw [h, cM_inv_mul_hM_mul_cM, ← neg_hM, D.i1_neg, ← h1]
  have hh2 : D.c1⁻¹ * D.h2 * D.c1 = D.h2 :=
    (D.commute cM hM).inv_mul_cancel
  calc D.c1⁻¹ * D.v * D.c1
      = (D.c1⁻¹ * D.h1 * D.c1) * (D.c1⁻¹ * D.h2 * D.c1) := by
        rw [v]; group
    _ = (D.t * D.h1) * D.h2 := by rw [hh1, hh2]
    _ = D.t * D.v := by rw [v]; group

private theorem conj_c1_w : D.c1⁻¹ * D.w * D.c1 = D.w := by
  have hw : Commute D.c1 D.w := by
    rw [w]
    exact Commute.mul_right (Commute.refl D.c1) (D.commute cM cM)
  exact hw.inv_mul_cancel

theorem conj_c1_eb : D.c1⁻¹ * D.t * D.c1 = D.t ∧ D.c1⁻¹ * D.u * D.c1 = D.t * D.u * D.w ∧
    D.c1⁻¹ * D.v * D.c1 = D.t * D.v ∧ D.c1⁻¹ * D.w * D.c1 = D.w :=
  ⟨D.conj_c1_t, D.conj_c1_u, D.conj_c1_v, D.conj_c1_w⟩

private theorem conj_f12_t : D.f12⁻¹ * D.t * D.f12 = D.t :=
  (D.d_commute_t fM).inv_mul_cancel

private theorem conj_f12_u : D.f12⁻¹ * D.u * D.f12 = D.u :=
  (D.d_commute_u fM).inv_mul_cancel

private theorem conj_f12_v : D.f12⁻¹ * D.v * D.f12 = D.w := by
  have h : D.f12⁻¹ * D.v * D.f12 = D.d (fM⁻¹ * hM * fM) := by
    rw [f12, D.v_eq_d, ← map_inv, ← map_mul, ← map_mul]
  rw [h, show fM⁻¹ * hM * fM = -cM by decide, D.d_neg, D.w_eq_d]

private theorem conj_f12_w : D.f12⁻¹ * D.w * D.f12 = D.v * D.w := by
  have h : D.f12⁻¹ * D.w * D.f12 = D.d (fM⁻¹ * cM * fM) := by
    rw [f12, D.w_eq_d, ← map_inv, ← map_mul, ← map_mul]
  rw [h, show fM⁻¹ * cM * fM = hM * cM by decide, map_mul, ← D.v_eq_d, ← D.w_eq_d]

theorem conj_f12_eb : D.f12⁻¹ * D.t * D.f12 = D.t ∧ D.f12⁻¹ * D.u * D.f12 = D.u ∧
    D.f12⁻¹ * D.v * D.f12 = D.w ∧ D.f12⁻¹ * D.w * D.f12 = D.v * D.w :=
  ⟨D.conj_f12_t, D.conj_f12_u, D.conj_f12_v, D.conj_f12_w⟩

private theorem mem_normalizer_E_of_conj {g : G}
    (ht : g⁻¹ * D.t * g ∈ D.E) (hu : g⁻¹ * D.u * g ∈ D.E)
    (hv : g⁻¹ * D.v * g ∈ D.E) (hw : g⁻¹ * D.w * g ∈ D.E) :
    g ∈ normalizer (D.E : Set G) := by
  have hfin : Finite D.E :=
    Nat.finite_of_card_ne_zero (by rw [D.card_E]; norm_num)
  have hg : g⁻¹ ∈ normalizer (D.E : Set G) := by
    refine @Subgroup.mem_normalizer_fintype G _ (D.E : Set G) hfin g⁻¹ ?_
    intro n hn
    have hn' : g⁻¹ * n * g ∈ (D.E : Set G) := by
      refine Subgroup.closure_induction (p := fun x _ => g⁻¹ * x * g ∈ D.E) ?_ ?_ ?_ ?_ hn
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        exacts [ht, hu, hv, hw]
      · simp
      · rintro x y _ _ hx hy
        rw [show g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) by group]
        exact D.E.mul_mem hx hy
      · rintro x _ hx
        rw [show g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ by group]
        exact D.E.inv_mem hx
    simpa only [inv_inv] using hn'
  simpa using (normalizer (D.E : Set G)).inv_mem hg

theorem h1_mem_normalizer_E : D.h1 ∈ normalizer (D.E : Set G) := by
  have ht : D.t ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![1, 0, 0, 0]
  have hu : D.u ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 1, 0, 0]
  have hv : D.v ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 0, 1, 0]
  have hw : D.w ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 0, 0, 1]
  refine D.mem_normalizer_E_of_conj ?_ ?_ ?_ ?_
  · rw [D.conj_h1_t]; exact ht
  · rw [D.conj_h1_u]; exact D.E.mul_mem (D.E.mul_mem ht hu) hv
  · rw [D.conj_h1_v]; exact hv
  · rw [D.conj_h1_w]; exact D.E.mul_mem ht hw

theorem c1_mem_normalizer_E : D.c1 ∈ normalizer (D.E : Set G) := by
  have ht : D.t ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![1, 0, 0, 0]
  have hu : D.u ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 1, 0, 0]
  have hv : D.v ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 0, 1, 0]
  have hw : D.w ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 0, 0, 1]
  refine D.mem_normalizer_E_of_conj ?_ ?_ ?_ ?_
  · rw [D.conj_c1_t]; exact ht
  · rw [D.conj_c1_u]; exact D.E.mul_mem (D.E.mul_mem ht hu) hw
  · rw [D.conj_c1_v]; exact D.E.mul_mem ht hv
  · rw [D.conj_c1_w]; exact hw

theorem f12_mem_normalizer_E : D.f12 ∈ normalizer (D.E : Set G) := by
  have ht : D.t ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![1, 0, 0, 0]
  have hu : D.u ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 1, 0, 0]
  have hv : D.v ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 0, 1, 0]
  have hw : D.w ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 0, 0, 1]
  refine D.mem_normalizer_E_of_conj ?_ ?_ ?_ ?_
  · rw [D.conj_f12_t]; exact ht
  · rw [D.conj_f12_u]; exact hu
  · rw [D.conj_f12_v]; exact hw
  · rw [D.conj_f12_w]; exact D.E.mul_mem hv hw

private theorem h2_eq : D.h2 = D.h1 * (D.t * D.v) := by
  have hh1sq : D.h1 * D.h1 = D.t := by
    rw [h1, ← map_mul, show hM * hM = -1 by rw [← pow_two, hM_sq], ← D.t_eq_i1]
  have hcomm : D.h1 * D.t = D.t * D.h1 := (D.t_commute_i1 hM).eq.symm
  rw [v]
  have h : D.h1 * (D.t * (D.h1 * D.h2)) = D.h2 := by
    calc D.h1 * (D.t * (D.h1 * D.h2))
        = (D.h1 * D.t) * D.h1 * D.h2 := by group
      _ = (D.t * D.h1) * D.h1 * D.h2 := by rw [hcomm]
      _ = D.t * (D.h1 * D.h1) * D.h2 := by group
      _ = D.t * D.t * D.h2 := by rw [hh1sq]
      _ = D.h2 := by rw [D.t_mul_t, one_mul]
  exact h.symm

private theorem c2_eq : D.c2 = D.c1 * (D.t * D.w) := by
  have hc1sq : D.c1 * D.c1 = D.t := by
    rw [c1, ← map_mul, show cM * cM = -1 by rw [← pow_two, cM_sq], ← D.t_eq_i1]
  have hcomm : D.c1 * D.t = D.t * D.c1 := (D.t_commute_i1 cM).eq.symm
  rw [w]
  have h : D.c1 * (D.t * (D.c1 * D.c2)) = D.c2 := by
    calc D.c1 * (D.t * (D.c1 * D.c2))
        = (D.c1 * D.t) * D.c1 * D.c2 := by group
      _ = (D.t * D.c1) * D.c1 * D.c2 := by rw [hcomm]
      _ = D.t * (D.c1 * D.c1) * D.c2 := by group
      _ = D.t * D.t * D.c2 := by rw [hc1sq]
      _ = D.c2 := by rw [D.t_mul_t, one_mul]
  exact h.symm

theorem S_le_normalizer_E : D.S ≤ normalizer (D.E : Set G) := by
  have ht : D.t ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![1, 0, 0, 0]
  have hu : D.u ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 1, 0, 0]
  have hv : D.v ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 0, 1, 0]
  have hw : D.w ∈ D.E := by simpa [vecE, ZMod.val_one] using D.vecE_mem_E ![0, 0, 0, 1]
  have hEN : D.E ≤ normalizer (D.E : Set G) := Subgroup.le_normalizer
  have htN : D.t ∈ normalizer (D.E : Set G) := hEN ht
  have hvN : D.v ∈ normalizer (D.E : Set G) := hEN hv
  have hwN : D.w ∈ normalizer (D.E : Set G) := hEN hw
  have huN : D.u ∈ normalizer (D.E : Set G) := hEN hu
  have h1N : D.h1 ∈ normalizer (D.E : Set G) := D.h1_mem_normalizer_E
  have hc1N : D.c1 ∈ normalizer (D.E : Set G) := D.c1_mem_normalizer_E
  have h2N : D.h2 ∈ normalizer (D.E : Set G) := by
    rw [D.h2_eq]
    exact (normalizer (D.E : Set G)).mul_mem h1N
      ((normalizer (D.E : Set G)).mul_mem htN hvN)
  have hc2N : D.c2 ∈ normalizer (D.E : Set G) := by
    rw [D.c2_eq]
    exact (normalizer (D.E : Set G)).mul_mem hc1N
      ((normalizer (D.E : Set G)).mul_mem htN hwN)
  refine (Subgroup.closure_le (normalizer (D.E : Set G))).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact h1N
  · exact hc1N
  · exact h2N
  · exact hc2N
  · exact huN

end SwapData

end CFSG.OddTranspositions.PartThree.Wong

module

public import CFSG.Milestones.ASVolI.F48.D43.Unip
public import CFSG.Milestones.ASVolI.F48.D43.Stab3

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.CosetTable

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

theorem burnsideF48d_W2_eq {H : Type*} [Group H] (g : Fin 17 → H)
    (h : burnsideF48s_ev g burnsideF48d_W2 = 1) :
    g 0 = g 5 * (g 0 * g 1 * g 0) * g 12 * (g 0 * g 1 * g 0)⁻¹ * g 5 := by
  have e : burnsideF48s_ev g burnsideF48d_W2 =
      g 5 * (g 0 * g 1 * g 0) * g 12 * (g 0 * g 1 * g 0)⁻¹ * g 5 * (g 0)⁻¹ := by
    simp only [burnsideF48d_W2, burnsideF48s_ev, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, cond_true, cond_false]
    group
  rw [e] at h
  exact (mul_inv_eq_one.1 h).symm

theorem burnsideF48d_key1 {H : Type*} [Group H] {a b c n : H} (hc : c = (a * b)⁻¹ * n) :
    a = n * c⁻¹ * b⁻¹ := by
  subst hc; group

theorem burnsideF48d_key2 {H : Type*} [Group H] {a b c n : H} (hc : c = (a * b)⁻¹ * n) :
    a * b * a = n * (a⁻¹ * c)⁻¹ := by
  subst hc; group

theorem burnsideF48d_card_inv {Y : Subgroup ↥burnsideF48d_X} (reps : Finset (Fin 26572))
    (hcov : ∀ q : Fin 26572, ∃ r ∈ reps, ∃ y ∈ Y,
      ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) r = q)
    (hdis : ∀ r ∈ reps, ∀ r' ∈ reps,
      (∃ y ∈ Y, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) r = r') → r = r')
    {S : Finset (Fin 26572)}
    (hS : ∀ y ∈ Y, ∀ q ∈ S, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) q ∈ S) :
    S.card = ∑ r ∈ reps, if r ∈ S then burnsideF48d_ol Y r else 0 := by
  classical
  let piece : Fin 26572 → Finset (Fin 26572) := fun r =>
    S.filter (fun q => ∃ y ∈ Y, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) r = q)
  have hS_eq : S = reps.biUnion piece := by
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_filter, piece]
    constructor
    · intro hq
      obtain ⟨r, hr, hy⟩ := hcov q
      exact ⟨r, hr, hq, hy⟩
    · rintro ⟨r, -, hq, -⟩
      exact hq
  have hdisj : ∀ r ∈ reps, ∀ r' ∈ reps, r ≠ r' → Disjoint (piece r) (piece r') := by
    intro r hr r' hr' hne
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [Finset.mem_filter, piece] at hq hq'
    obtain ⟨-, y, hy, rfl⟩ := hq
    obtain ⟨-, y', hy', he⟩ := hq'
    apply hne
    apply hdis r hr r' hr'
    refine ⟨y'⁻¹ * y, Y.mul_mem (Y.inv_mem hy') hy, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, ← he, Equiv.Perm.inv_eq_iff_eq]
  have hpiece : ∀ r ∈ reps, (piece r).card = if r ∈ S then burnsideF48d_ol Y r else 0 := by
    intro r _
    split_ifs with hrS
    · unfold burnsideF48d_ol
      have : MulAction.orbit ↥Y r = ((piece r : Finset (Fin 26572)) : Set (Fin 26572)) := by
        ext q
        simp only [Finset.mem_coe, Finset.mem_filter, piece, burnsideF48d_orbit_iff]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨hS y hy r hrS, y, hy, rfl⟩
        · rintro ⟨-, h⟩
          exact h
      rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro q hq
      simp only [Finset.mem_filter, piece] at hq
      obtain ⟨hqS, y, hy, rfl⟩ := hq
      apply hrS
      have := hS y⁻¹ (Y.inv_mem hy) _ hqS
      have e : ((y⁻¹ : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572))
          (((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) r) = r := by
        rw [Subgroup.coe_inv, Equiv.Perm.inv_eq_iff_eq]
      rwa [e] at this
  calc S.card = (reps.biUnion piece).card := congrArg Finset.card hS_eq
    _ = ∑ r ∈ reps, (piece r).card := Finset.card_biUnion hdisj
    _ = _ := Finset.sum_congr rfl hpiece

section Model


theorem burnsideF48d_ol_P1 : burnsideF48d_ol burnsideF48d_P1 0 = 1 ∧
    burnsideF48d_ol burnsideF48d_P1 6 = 84 ∧ burnsideF48d_ol burnsideF48d_P1 479 = 6804 ∧
    burnsideF48d_ol burnsideF48d_P1 15916 = 6804 ∧ burnsideF48d_ol burnsideF48d_P1 26571 = 19683 := by
  obtain ⟨o0, o6, -, o479, o15916, o26571⟩ := burnsideF48d_oc_values
  exact ⟨o0, o6, o479, o15916, o26571⟩

theorem burnsideF48d_cov_P1 (q : Fin 26572) : ∃ r ∈ ({0, 6, 479, 26571} : Finset (Fin 26572)),
    ∃ y ∈ burnsideF48d_P1, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) r = q := by
  obtain ⟨-, -, -, covP1, -⟩ := burnsideF48d_orb_P1
  by_cases h0 : q = 0
  · subst h0
    exact ⟨0, by decide, 1, burnsideF48d_P1.one_mem, rfl⟩
  rcases covP1 q h0 with h | h | h
  · exact ⟨6, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩
  · exact ⟨479, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩
  · exact ⟨26571, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩

theorem burnsideF48d_dis_P1 : ∀ r ∈ ({0, 6, 479, 26571} : Finset (Fin 26572)),
    ∀ r' ∈ ({0, 6, 479, 26571} : Finset (Fin 26572)),
    (∃ y ∈ burnsideF48d_P1, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) r = r') → r = r' := by
  intro r hr r' hr' h
  have he := burnsideF48d_ol_of_mem h
  obtain ⟨o0, o6, o479, -, o26571⟩ := burnsideF48d_ol_P1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr hr'
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hr' with rfl | rfl | rfl | rfl <;>
    first | rfl | (simp only [o0, o6, o479, o26571] at he; omega)

theorem burnsideF48d_card_inv_P1 {S : Finset (Fin 26572)}
    (hS : ∀ y ∈ burnsideF48d_P1, ∀ q ∈ S, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) q ∈ S) :
    S.card = (if (0 : Fin 26572) ∈ S then 1 else 0) + (if (6 : Fin 26572) ∈ S then 84 else 0) +
      (if (479 : Fin 26572) ∈ S then 6804 else 0) +
      (if (26571 : Fin 26572) ∈ S then 19683 else 0) := by
  rw [burnsideF48d_card_inv _ burnsideF48d_cov_P1 burnsideF48d_dis_P1 hS]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  obtain ⟨o0, o6, o479, -, o26571⟩ := burnsideF48d_ol_P1
  rw [o0, o6, o479, o26571]
  ring

theorem burnsideF48d_ol_Uv : burnsideF48d_ol burnsideF48d_U 0 = 1 ∧
    burnsideF48d_ol burnsideF48d_U 6 = 3 ∧ burnsideF48d_ol burnsideF48d_U 186 = 81 ∧
    burnsideF48d_ol burnsideF48d_U 479 = 243 ∧ burnsideF48d_ol burnsideF48d_U 15916 = 6561 ∧
    burnsideF48d_ol burnsideF48d_U 26571 = 19683 := by
  obtain ⟨-, sU186, sU479, sU15916, sU26571, -⟩ := burnsideF48d_orb_U
  exact ⟨burnsideF48d_ol_fix burnsideF48d_U_fix0,
    burnsideF48d_ol_U_126 (Or.inr (Or.inr rfl)), sU186, sU479, sU15916, sU26571⟩

theorem burnsideF48d_cov_U (q : Fin 26572) :
    ∃ r ∈ ({0, 6, 186, 479, 15916, 26571} : Finset (Fin 26572)),
    ∃ y ∈ burnsideF48d_U, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) r = q := by
  obtain ⟨-, -, -, -, -, covU, -⟩ := burnsideF48d_orb_U
  by_cases h0 : q = 0
  · subst h0
    exact ⟨0, by decide, 1, burnsideF48d_U.one_mem, rfl⟩
  rcases covU q h0 with h | h | h | h | h
  · exact ⟨6, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩
  · exact ⟨186, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩
  · exact ⟨479, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩
  · exact ⟨15916, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩
  · exact ⟨26571, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩

theorem burnsideF48d_dis_U : ∀ r ∈ ({0, 6, 186, 479, 15916, 26571} : Finset (Fin 26572)),
    ∀ r' ∈ ({0, 6, 186, 479, 15916, 26571} : Finset (Fin 26572)),
    (∃ y ∈ burnsideF48d_U, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) r = r') → r = r' := by
  intro r hr r' hr' h
  have he := burnsideF48d_ol_of_mem h
  obtain ⟨o0, o6, o186, o479, o15916, o26571⟩ := burnsideF48d_ol_Uv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr hr'
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (simp only [o0, o6, o186, o479, o15916, o26571] at he; omega)

theorem burnsideF48d_card_inv_U {S : Finset (Fin 26572)}
    (hS : ∀ y ∈ burnsideF48d_U, ∀ q ∈ S, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) q ∈ S) :
    S.card = (if (0 : Fin 26572) ∈ S then 1 else 0) + (if (6 : Fin 26572) ∈ S then 3 else 0) +
      (if (186 : Fin 26572) ∈ S then 81 else 0) + (if (479 : Fin 26572) ∈ S then 243 else 0) +
      (if (15916 : Fin 26572) ∈ S then 6561 else 0) +
      (if (26571 : Fin 26572) ∈ S then 19683 else 0) := by
  rw [burnsideF48d_card_inv _ burnsideF48d_cov_U burnsideF48d_dis_U hS]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  obtain ⟨o0, o6, o186, o479, o15916, o26571⟩ := burnsideF48d_ol_Uv
  rw [o0, o6, o186, o479, o15916, o26571]
  ring

theorem burnsideF48d_ol_P2 : burnsideF48d_ol burnsideF48d_P2 0 = 4 ∧
    burnsideF48d_ol burnsideF48d_P2 186 = 324 ∧ burnsideF48d_ol burnsideF48d_P2 26571 = 26244 := by
  obtain ⟨hL0, s186, s26571, -⟩ := burnsideF48d_orb_P2
  refine ⟨?_, s186, s26571⟩
  unfold burnsideF48d_ol
  rw [hL0, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rfl

theorem burnsideF48d_cov_P2 (q : Fin 26572) : ∃ r ∈ ({0, 186, 26571} : Finset (Fin 26572)),
    ∃ y ∈ burnsideF48d_P2, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) r = q := by
  obtain ⟨-, -, -, cov⟩ := burnsideF48d_orb_P2
  rcases cov q with h | h | h
  · exact ⟨0, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩
  · exact ⟨186, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩
  · exact ⟨26571, by decide, (burnsideF48d_orbit_iff _ _).1 h⟩

theorem burnsideF48d_dis_P2 : ∀ r ∈ ({0, 186, 26571} : Finset (Fin 26572)),
    ∀ r' ∈ ({0, 186, 26571} : Finset (Fin 26572)),
    (∃ y ∈ burnsideF48d_P2, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) r = r') → r = r' := by
  intro r hr r' hr' h
  have he := burnsideF48d_ol_of_mem h
  obtain ⟨o0, o186, o26571⟩ := burnsideF48d_ol_P2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr hr'
  rcases hr with rfl | rfl | rfl <;> rcases hr' with rfl | rfl | rfl <;>
    first | rfl | (simp only [o0, o186, o26571] at he; omega)

theorem burnsideF48d_card_inv_P2 {S : Finset (Fin 26572)}
    (hS : ∀ y ∈ burnsideF48d_P2, ∀ q ∈ S, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) q ∈ S) :
    S.card = (if (0 : Fin 26572) ∈ S then 4 else 0) + (if (186 : Fin 26572) ∈ S then 324 else 0) +
      (if (26571 : Fin 26572) ∈ S then 26244 else 0) := by
  rw [burnsideF48d_card_inv _ burnsideF48d_cov_P2 burnsideF48d_dis_P2 hS]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  obtain ⟨o0, o186, o26571⟩ := burnsideF48d_ol_P2
  rw [o0, o186, o26571]
  ring

@[expose] noncomputable def burnsideF48d_orbF (R : Subgroup ↥burnsideF48d_X) (p : Fin 26572) :
    Finset (Fin 26572) := by
  classical
  exact Finset.univ.filter fun q => ∃ r ∈ R, ((r : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = q

theorem burnsideF48d_mem_orbF {R : Subgroup ↥burnsideF48d_X} {p q : Fin 26572} :
    q ∈ burnsideF48d_orbF R p ↔ ∃ r ∈ R, ((r : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = q := by
  unfold burnsideF48d_orbF
  simp

theorem burnsideF48d_card_orbF (R : Subgroup ↥burnsideF48d_X) (p : Fin 26572) :
    Nat.card (MulAction.orbit ↥R p) = (burnsideF48d_orbF R p).card := by
  have : MulAction.orbit ↥R p = ((burnsideF48d_orbF R p : Finset (Fin 26572)) : Set (Fin 26572)) := by
    ext q
    rw [Finset.mem_coe, burnsideF48d_mem_orbF, burnsideF48d_orbit_iff]
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem burnsideF48d_orbF_inv {R Y : Subgroup ↥burnsideF48d_X} (hYR : Y ≤ R) (p : Fin 26572) :
    ∀ y ∈ Y, ∀ q ∈ burnsideF48d_orbF R p,
      ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) q ∈ burnsideF48d_orbF R p := by
  intro y hy q hq
  rw [burnsideF48d_mem_orbF] at hq ⊢
  obtain ⟨r, hr, rfl⟩ := hq
  exact ⟨y * r, R.mul_mem (hYR hy) hr, rfl⟩

theorem burnsideF48d_self_mem_orbF (R : Subgroup ↥burnsideF48d_X) (p : Fin 26572) :
    p ∈ burnsideF48d_orbF R p :=
  burnsideF48d_mem_orbF.2 ⟨1, R.one_mem, rfl⟩

theorem burnsideF48d_card_R (R : Subgroup ↥burnsideF48d_X) (p : Fin 26572) :
    Nat.card ↥R = (burnsideF48d_orbF R p).card *
      Nat.card ↥(R ⊓ MulAction.stabilizer ↥burnsideF48d_X p) := by
  rw [card_eq_orbit_mul_inf R p, burnsideF48d_card_orbF]

theorem burnsideF48d_stab0 (R : Subgroup ↥burnsideF48d_X) :
    R ⊓ MulAction.stabilizer ↥burnsideF48d_X (0 : Fin 26572) = R ⊓ burnsideF48d_P1 := by
  ext z
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨hz, hz0⟩
    exact ⟨hz, (burnsideF48d_mem_P1 z).2 hz0⟩
  · rintro ⟨hz, hz1⟩
    exact ⟨hz, (burnsideF48d_mem_P1 z).1 hz1⟩

theorem burnsideF48d_P1_max : burnsideF48d_P1 ⊓ burnsideF48d_P2 ≤ burnsideF48d_P1 ∧
    burnsideF48d_P1 ≤ ⊤ ∧ burnsideF48d_P1 ≠ ⊤ ∧
    ∀ R : Subgroup ↥burnsideF48d_X, burnsideF48d_P1 < R → R ≤ ⊤ → R = ⊤ := by
  refine ⟨inf_le_left, le_top, fun h => ?_, fun R hR _ => ?_⟩
  · have h1 : burnsideF48d_L 1 ∈ burnsideF48d_P1 := h ▸ Subgroup.mem_top _
    rw [burnsideF48d_mem_P1, burnsideF48d_xy_apt.2.2.2.2.2.2.1] at h1
    exact absurd h1 (by decide)
  · have hcard := burnsideF48d_card_inv_P1 (burnsideF48d_orbF_inv hR.le 0)
    rw [if_pos (burnsideF48d_self_mem_orbF R 0)] at hcard
    have hRS : Nat.card ↥R = (burnsideF48d_orbF R 0).card * 773778096 := by
      rw [burnsideF48d_card_R R 0, burnsideF48d_stab0, inf_eq_right.2 hR.le, burnsideF48d_card_P1]
    have hdvd : (burnsideF48d_orbF R 0).card ∣ 26572 := by
      have h := Subgroup.card_subgroup_dvd_card R
      rw [hRS, burnsideF48d_card_X, show (20560831566912 : ℕ) = 26572 * 773778096 by norm_num] at h
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h
    have hcases : (burnsideF48d_orbF R 0).card = 1 ∨ (burnsideF48d_orbF R 0).card = 26572 := by
      rw [hcard] at hdvd ⊢
      split_ifs at hdvd ⊢ <;> first | (norm_num at hdvd; done) | norm_num
    rcases hcases with h1 | h1
    · exfalso
      have hle : Nat.card ↥R ≤ Nat.card ↥burnsideF48d_P1 := by
        rw [hRS, h1, burnsideF48d_card_P1]
      exact hR.ne (Subgroup.eq_of_le_of_card_ge hR.le hle)
    · apply Subgroup.eq_top_of_card_eq
      rw [hRS, h1, burnsideF48d_card_X]

theorem burnsideF48d_P1_6_eq (Q : Subgroup ↥burnsideF48d_X) (h1 : burnsideF48d_P1 ⊓ burnsideF48d_P2 ≤ Q)
    (h2 : Q ≤ burnsideF48d_P1) :
    Q ⊓ MulAction.stabilizer ↥burnsideF48d_X (6 : Fin 26572) =
      burnsideF48d_P1 ⊓ MulAction.stabilizer ↥burnsideF48d_X (6 : Fin 26572) := by
  apply le_antisymm (inf_le_inf_right _ h2)
  intro z hz
  have hzB : z ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2 := by
    rw [burnsideF48d_B_eq_closure]; exact burnsideF48d_P1_6_le_B hz
  exact ⟨h1 hzB, hz.2⟩

theorem burnsideF48d_B_max {Q : Subgroup ↥burnsideF48d_X} (h1 : burnsideF48d_P1 ⊓ burnsideF48d_P2 ≤ Q)
    (h2 : Q ≤ burnsideF48d_P1) : Q = burnsideF48d_P1 ⊓ burnsideF48d_P2 ∨ Q = burnsideF48d_P1 := by
  have hUQ : burnsideF48d_U ≤ Q := burnsideF48d_U_le.trans h1
  have hcard := burnsideF48d_card_inv_U (burnsideF48d_orbF_inv hUQ 6)
  obtain ⟨-, o6, o479, o15916, o26571⟩ := burnsideF48d_ol_P1
  have hnot : ∀ p : Fin 26572, burnsideF48d_ol burnsideF48d_P1 p ≠ 84 →
      p ∉ burnsideF48d_orbF Q 6 := by
    intro p hp hmem
    rw [burnsideF48d_mem_orbF] at hmem
    obtain ⟨z, hz, hzp⟩ := hmem
    exact hp ((burnsideF48d_ol_of_mem ⟨z, h2 hz, hzp⟩).trans o6)
  have hn0 : (0 : Fin 26572) ∉ burnsideF48d_orbF Q 6 := by
    intro hmem
    rw [burnsideF48d_mem_orbF] at hmem
    obtain ⟨z, hz, hz6⟩ := hmem
    have h0 := (burnsideF48d_mem_P1 z).1 (h2 hz)
    rw [← h0] at hz6
    exact absurd ((z : Equiv.Perm (Fin 26572)).injective hz6) (by decide)
  rw [if_neg hn0, if_pos (burnsideF48d_self_mem_orbF Q 6),
    if_neg (hnot 479 (by rw [o479]; norm_num)), if_neg (hnot 15916 (by rw [o15916]; norm_num)),
    if_neg (hnot 26571 (by rw [o26571]; norm_num))] at hcard
  have hQ : Nat.card ↥Q = (burnsideF48d_orbF Q 6).card * 9211644 := by
    rw [burnsideF48d_card_R Q 6, burnsideF48d_P1_6_eq Q h1 h2, burnsideF48d_card_P1_6]
  by_cases h186 : (186 : Fin 26572) ∈ burnsideF48d_orbF Q 6
  · rw [if_pos h186] at hcard
    right
    refine Subgroup.eq_of_le_of_card_ge h2 ?_
    rw [hQ, hcard, burnsideF48d_card_P1]
  · rw [if_neg h186] at hcard
    left
    refine (Subgroup.eq_of_le_of_card_ge h1 ?_).symm
    rw [hQ, hcard, burnsideF48d_card_B]

theorem burnsideF48d_P2_max :
    burnsideF48d_P1 ⊓ burnsideF48d_P2 ≤ burnsideF48d_P2 ∧
    burnsideF48d_P2 ≤ ⊤ ∧ burnsideF48d_P2 ≠ ⊤ ∧
    ∀ R : Subgroup ↥burnsideF48d_X, burnsideF48d_P2 < R → R ≤ ⊤ → R = ⊤ := by
  obtain ⟨x0, x6, -, -, -, -, y0, y6, -⟩ := burnsideF48d_xy_apt
  have hL1 : burnsideF48d_L 1 ∈ burnsideF48d_P2 := Subgroup.subset_closure ⟨1, by decide, rfl⟩
  refine ⟨inf_le_right, le_top, fun h => ?_, fun R hR _ => ?_⟩
  · have h1 : burnsideF48d_L 0 ∈ burnsideF48d_P2 := h ▸ Subgroup.mem_top _
    have := (burnsideF48d_mem_P2 _).1 h1 6 (by decide)
    rw [x6] at this
    exact absurd this (by decide)
  · suffices hx : burnsideF48d_L 0 ∈ R by
      rw [eq_top_iff, ← burnsideF48d_closure_L, Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      by_cases hj : j = 0
      · subst hj
        exact hx
      · exact hR.le (Subgroup.subset_closure ⟨j, hj, rfl⟩)
    have hB : burnsideF48d_P1 ⊓ burnsideF48d_P2 ≤ R ⊓ burnsideF48d_P1 :=
      le_inf (inf_le_right.trans hR.le) inf_le_left
    rcases burnsideF48d_B_max hB inf_le_right with hRB | hRP
    ·
      have hcard := burnsideF48d_card_inv_P2 (burnsideF48d_orbF_inv hR.le 0)
      rw [if_pos (burnsideF48d_self_mem_orbF R 0)] at hcard
      have hRS : Nat.card ↥R = (burnsideF48d_orbF R 0).card * 27634932 := by
        rw [burnsideF48d_card_R R 0, burnsideF48d_stab0, hRB, burnsideF48d_card_B]
      have hdvd : (burnsideF48d_orbF R 0).card ∣ 744016 := by
        have h := Subgroup.card_subgroup_dvd_card R
        rw [hRS, burnsideF48d_card_X, show (20560831566912 : ℕ) = 744016 * 27634932 by norm_num] at h
        exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h
      have h186 : (186 : Fin 26572) ∈ burnsideF48d_orbF R 0 := by
        by_contra h186
        rw [if_neg h186] at hcard
        by_cases h26571 : (26571 : Fin 26572) ∈ burnsideF48d_orbF R 0
        · rw [if_pos h26571] at hcard
          rw [hcard] at hdvd
          norm_num at hdvd
        · rw [if_neg h26571] at hcard
          have hle : Nat.card ↥R ≤ Nat.card ↥burnsideF48d_P2 := by
            rw [hRS, hcard, burnsideF48d_card_P2]
          exact hR.ne (Subgroup.eq_of_le_of_card_ge hR.le hle)
      obtain ⟨r, hr, hr0⟩ := burnsideF48d_mem_orbF.1 h186
      have hTR : burnsideF48d_T ≤ R := (burnsideF48d_T_le.trans inf_le_right).trans hR.le
      set K'' := burnsideF48d_T.map (MulAut.conj r⁻¹).toMonoidHom with hK''
      have hK''B : K'' ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2 := by
        intro z hz
        rw [hK'', burnsideAut_mem_map_conj, inv_inv] at hz
        have hzR : z ∈ R := by
          have e : z = r⁻¹ * (r * z * r⁻¹) * r := by group
          rw [e]
          exact R.mul_mem (R.mul_mem (R.inv_mem hr) (hTR hz)) hr
        have hz0 : ((z : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = 0 := by
          have h1 := (burnsideF48d_mem_T _).1 hz 186 (by decide)
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
            Equiv.Perm.mul_apply] at h1
          have hr' : ((r : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572))⁻¹ 186 = 0 :=
            Equiv.Perm.inv_eq_iff_eq.2 hr0.symm
          rw [hr', ← hr0] at h1
          exact (r : Equiv.Perm (Fin 26572)).injective h1
        have : z ∈ R ⊓ burnsideF48d_P1 := ⟨hzR, (burnsideF48d_mem_P1 z).2 hz0⟩
        rwa [hRB] at this
      have hK''card : Nat.card ↥K'' = 52 := by
        rw [hK'', Subgroup.card_map_of_injective (MulAut.conj r⁻¹).injective, burnsideF48d_card_T]
      obtain ⟨t, htB, ht⟩ := burnsideF48d_hconj K'' hK''B hK''card
      set n := r * t⁻¹ with hn
      have hnR : n ∈ R := R.mul_mem hr (R.inv_mem (hR.le htB.2))
      have hn0 : ((n : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = 186 := by
        have ht0 := (burnsideF48d_mem_P1 t).1 htB.1
        have ht0' : ((t : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572))⁻¹ 0 = 0 :=
          Equiv.Perm.inv_eq_iff_eq.2 ht0.symm
        rw [hn, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, ht0', hr0]
      have hnT : ∀ k ∈ burnsideF48d_T, n * k * n⁻¹ ∈ burnsideF48d_T := by
        intro k hk
        have h1 : t⁻¹ * k * t ∈ K'' := (ht _).2 (by
          have e : t * (t⁻¹ * k * t) * t⁻¹ = k := by group
          rw [e]; exact hk)
        rw [hK'', burnsideAut_mem_map_conj, inv_inv] at h1
        have e : n * k * n⁻¹ = r * (t⁻¹ * k * t) * r⁻¹ := by rw [hn]; group
        rw [e]
        exact h1
      set c := (burnsideF48d_L 0 * burnsideF48d_L 1)⁻¹ * n with hc
      have hc0 : ((c : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = 0 := by
        rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hn0,
          Equiv.Perm.inv_eq_iff_eq, Subgroup.coe_mul, Equiv.Perm.mul_apply, y0, x6]
      have hcP1 : c ∈ burnsideF48d_P1 := (burnsideF48d_mem_P1 c).2 hc0
      have hcT : ∀ k ∈ burnsideF48d_T, c * k * c⁻¹ ∈ burnsideF48d_T :=
        burnsideF48d_normT_mul (burnsideF48d_normT_inv
          (burnsideF48d_normT_mul burnsideF48d_L0_normT burnsideF48d_L1_normT)) hnT
      by_cases hcP2 : c ∈ burnsideF48d_P2
      · have hcTm : c ∈ burnsideF48d_T := burnsideF48d_normalizer_T ⟨hcP1, hcP2⟩ hcT
        rw [burnsideF48d_key1 hc]
        exact R.mul_mem (R.mul_mem hnR (R.inv_mem (hTR hcTm))) (R.inv_mem (hR.le hL1))
      · have htc := burnsideF48d_xred hcP1 hcP2 hcT
        have hw : burnsideF48d_L 0 * burnsideF48d_L 1 * burnsideF48d_L 0 ∈ R := by
          rw [burnsideF48d_key2 hc]
          exact R.mul_mem hnR (R.inv_mem (hTR htc))
        have hW2 : burnsideF48s_ev burnsideF48d_L burnsideF48d_W2 = 1 :=
          burnsideF48d_rels _ (List.mem_append_right _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        have hL5 : burnsideF48d_L 5 ∈ R := hR.le (Subgroup.subset_closure ⟨5, by decide, rfl⟩)
        have hL12 : burnsideF48d_L 12 ∈ R := hR.le (Subgroup.subset_closure ⟨12, by decide, rfl⟩)
        rw [burnsideF48d_W2_eq burnsideF48d_L hW2]
        exact R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem hL5 hw) hL12) (R.inv_mem hw)) hL5
    · exact (inf_eq_right.1 hRP) (Subgroup.subset_closure ⟨0, by decide, rfl⟩)

theorem burnsideF48d_sup : burnsideF48d_P1 ⊔ burnsideF48d_P2 = ⊤ := by
  obtain ⟨-, -, -, hmax⟩ := burnsideF48d_P1_max
  refine hmax _ (lt_of_le_of_ne le_sup_left fun h => ?_) le_top
  have h1 : burnsideF48d_L 1 ∈ burnsideF48d_P1 := by
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨1, by decide, rfl⟩)
  rw [burnsideF48d_mem_P1, burnsideF48d_xy_apt.2.2.2.2.2.2.1] at h1
  exact absurd h1 (by decide)

end Model

end CFSG.ASVolI

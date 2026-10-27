module

public import CFSG.Quasithin.H13.GoldschmidtI51Cnt

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

omit [Finite G] in
theorem seven_dvd_G2 (hD : IsDSystem .C3 Gs) : 7 ∣ Nat.card ↥(Gs 2) := by
  obtain ⟨φ, hφ, -⟩ := hD.d2two
  have h := Subgroup.card_dvd_of_surjective (f := φ) hφ
  rw [CFSG.Quasithin.H13.A6.SL3.card_S] at h
  exact dvd_trans (by norm_num) h

theorem not_seven_dvd_G0 (hD : IsDSystem .C3 Gs) : ¬ 7 ∣ Nat.card ↥(Gs 0) := by
  obtain ⟨b, o, ⟨M⟩⟩ := model0_bo hD
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M.ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange M.ψ).toEquiv, M.range] at h1
  have h2 : Nat.card ↥(sgR b) ∣ 720 := by
    have := Subgroup.card_subgroup_dvd_card (sgR b)
    rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin,
      show Nat.factorial 6 = 720 by decide] at this
  have h3 : IsPGroup 2 M.ψ.ker := by
    have h := CFSG.pCore_isPGroup (p := 2) (G := ↥(Gs 0))
    rwa [M.ker]
  obtain ⟨n, hn⟩ := h3.exists_card_eq
  intro h7
  rw [h1] at h7
  have hp : Nat.Prime 7 := by norm_num
  rcases hp.dvd_mul.1 h7 with h | h
  · have := dvd_trans h h2
    omega
  · rw [hn] at h
    have := hp.dvd_of_dvd_pow h
    omega

theorem far_col_all (hD : IsDSystem .C3 Gs) {s0 f0 t0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hf0 : f0 ∈ Gs 0) (hnf0 : ¬ Nr Gs f0) (ht0 : t0 ∈ Gs 1) (ht00 : t0 ∉ Gs 0)
    (hcol : s0⁻¹ * (f0 * t0) ∈ Nbd Gs) : ∀ h ∈ Gs 0, ∀ t ∈ Gs 1, s0⁻¹ * h * t ∈ Nbd Gs := by
  intro h hh t ht
  by_cases hnr : Nr Gs h
  · exact near_collinear hD hnr hs0 ht
  by_cases htG0 : t ∈ Gs 0
  · exact ⟨1, (Gs 0).one_mem, s0⁻¹, (Gs 1).inv_mem hs0, h * t, (Gs 0).mul_mem hh htG0, by group⟩
  obtain ⟨g, hg, hk, hc⟩ := T16 hD hs0 hs00 hh hnr ht htG0 hf0 hnf0 ht0 ht00
  have e : s0⁻¹ * h * t = (s0⁻¹ * g * s0)⁻¹ * (s0⁻¹ * (f0 * t0)) *
      ((f0 * t0)⁻¹ * (g * h * t)) := by group
  rw [e]
  exact Nbd_mul_G0 hc (G0_mul_Nbd ((Gs 0).inv_mem hk) hcol)

theorem far_col_all' (hD : IsDSystem .C3 Gs) {s0 f0 t0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hf0 : f0 ∈ Gs 0) (hnf0 : ¬ Nr Gs f0) (ht0 : t0 ∈ Gs 1) (ht00 : t0 ∉ Gs 0)
    (hcol : s0⁻¹ * (f0 * t0) ∈ Nbd Gs) :
    ∀ s ∈ Gs 1, s ∉ Gs 0 → ∀ h ∈ Gs 0, ∀ t ∈ Gs 1, s⁻¹ * h * t ∈ Nbd Gs := by
  intro s hs hs0' h hh t ht
  obtain ⟨q0, hq0, hq01⟩ := exists_q0 hD
  have hq0G : q0 ∈ Gs 0 := TT_le 0 (QQ_le_TT hD 0 hq0)
  have key := far_col_all hD hs0 hs00 hf0 hnf0 ht0 ht00 hcol
  rcases line_pts hD hs0 hs00 hq0 hq01 hs with h1 | h1 | h1
  · exact absurd h1 hs0'
  · have e : s⁻¹ * h * t = (s0⁻¹ * s)⁻¹ * (s0⁻¹ * h * t) := by group
    rw [e]; exact G0_mul_Nbd ((Gs 0).inv_mem h1) (key h hh t ht)
  · have e : s⁻¹ * h * t = ((q0 * s0)⁻¹ * s)⁻¹ * (s0⁻¹ * (q0⁻¹ * h) * t) := by group
    rw [e]
    exact G0_mul_Nbd ((Gs 0).inv_mem h1)
      (key (q0⁻¹ * h) ((Gs 0).mul_mem ((Gs 0).inv_mem hq0G) hh) t ht)

theorem Nbd_mul (hD : IsDSystem .C3 Gs) {s0 f0 t0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hf0 : f0 ∈ Gs 0) (hnf0 : ¬ Nr Gs f0) (ht0 : t0 ∈ Gs 1) (ht00 : t0 ∉ Gs 0)
    (hcol : s0⁻¹ * (f0 * t0) ∈ Nbd Gs) {n m : G} (hn : n ∈ Nbd Gs) (hm : m ∈ Nbd Gs) :
    n * m ∈ Nbd Gs := by
  obtain ⟨a, ha, s, hs, c, hc, rfl⟩ := hn
  obtain ⟨a', ha', s', hs', c', hc', rfl⟩ := hm
  by_cases hsG0 : s ∈ Gs 0
  · have e : a * s * c * (a' * s' * c') = (a * s * c * a') * s' * c' := by group
    exact ⟨a * s * c * a', (Gs 0).mul_mem ((Gs 0).mul_mem ((Gs 0).mul_mem ha hsG0) hc) ha', s', hs',
      c', hc', e⟩
  · have h1 := far_col_all' hD hs0 hs00 hf0 hnf0 ht0 ht00 hcol s⁻¹ ((Gs 1).inv_mem hs)
      (fun h => hsG0 (by simpa using (Gs 0).inv_mem h)) (c * a') ((Gs 0).mul_mem hc ha') s' hs'
    rw [inv_inv] at h1
    have e : a * s * c * (a' * s' * c') = a * (s * (c * a') * s') * c' := by group
    rw [e]
    exact Nbd_mul_G0 hc' (G0_mul_Nbd ha h1)

theorem Nbd_univ (hD : IsDSystem .C3 Gs) {s0 f0 t0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hf0 : f0 ∈ Gs 0) (hnf0 : ¬ Nr Gs f0) (ht0 : t0 ∈ Gs 1) (ht00 : t0 ∉ Gs 0)
    (hcol : s0⁻¹ * (f0 * t0) ∈ Nbd Gs) (g : G) : g ∈ Nbd Gs := by
  let N : Subgroup G :=
    { carrier := Nbd Gs
      mul_mem' := fun {n m} hn hm => Nbd_mul hD hs0 hs00 hf0 hnf0 ht0 ht00 hcol hn hm
      one_mem' := G0_sub_Nbd (Gs 0).one_mem
      inv_mem' := fun {n} hn => Nbd_inv hn }
  have h0 : Gs 0 ≤ N := fun x hx => G0_sub_Nbd hx
  have h1 : Gs 1 ≤ N := fun x hx => G1_sub_Nbd hx
  have h2 : Gs 2 ≤ N := fun x hx => G2_sub_Nbd hD hx
  have : (⊤ : Subgroup G) ≤ N := by
    rw [← hD.d4gen]; exact sup_le (sup_le h0 h1) h2
  exact this (Subgroup.mem_top g)

theorem card_Omega_of_univ (hD : IsDSystem .C3 Gs) (h : ∀ g : G, g ∈ Nbd Gs) :
    Nat.card (G ⧸ Gs 0) = 31 := by
  have hu : (Set.univ : Set (G ⧸ Gs 0)) = insert (oPt Gs) (Dlt Gs) := by
    ext p
    induction p using QuotientGroup.induction_on with | _ a => ?_
    simp only [Set.mem_univ, Set.mem_insert_iff, true_iff]
    by_cases hp : (a : G ⧸ Gs 0) = oPt Gs
    · exact Or.inl hp
    · exact Or.inr ⟨hp, col_oPt.2 (h a)⟩
  have := Set.ncard_insert_of_notMem (a := oPt Gs) (s := Dlt Gs) (by simp [Dlt])
    (Set.toFinite _)
  rw [← hu, Set.ncard_univ, ncard_Dlt hD] at this
  omega

theorem no_Nbd_univ (hD : IsDSystem .C3 Gs) (h : ∀ g : G, g ∈ Nbd Gs) : False := by
  have h31 := card_Omega_of_univ hD h
  have hG := Subgroup.card_eq_card_quotient_mul_card_subgroup (Gs 0)
  rw [h31] at hG
  have h7 : 7 ∣ Nat.card G :=
    dvd_trans (seven_dvd_G2 hD) (Subgroup.card_subgroup_dvd_card (Gs 2))
  rw [hG] at h7
  have hp : Nat.Prime 7 := by norm_num
  rcases hp.dvd_mul.1 h7 with h' | h'
  · omega
  · exact not_seven_dvd_G0 hD h'

theorem far_not_col (hD : IsDSystem .C3 Gs) {s f t : G} (hs : s ∈ Gs 1) (hs0 : s ∉ Gs 0)
    (hf : f ∈ Gs 0) (hnf : ¬ Nr Gs f) (ht : t ∈ Gs 1) (ht0 : t ∉ Gs 0) :
    s⁻¹ * (f * t) ∉ Nbd Gs :=
  fun hcol => no_Nbd_univ hD (Nbd_univ hD hs hs0 hf hnf ht ht0 hcol)

end CFSG.Quasithin.H13.I51

module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoRuPGroup

public section

namespace CFSG.Quasithin.H13.K1262Two.RuP

open CFSG.Quasithin.H13.Cover

variable {Γ : Type} [Group Γ]

@[expose] def Good (R T : Subgroup Γ) (y : Γ) : Prop :=
  ∃ z ∈ T, z ∉ R ∧ z ∈ R ⊔ Subgroup.zpowers y

theorem mem_sup_zpowers (R : Subgroup Γ) (y : Γ) : y ∈ R ⊔ Subgroup.zpowers y :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

theorem good_of_mem {R T : Subgroup Γ} {x y : Γ} (hx : x ∈ R ⊔ Subgroup.zpowers y)
    (h : Good R T x) : Good R T y := by
  obtain ⟨z, hzT, hzR, hz⟩ := h
  exact ⟨z, hzT, hzR, sup_le le_sup_left ((Subgroup.zpowers_le).2 hx) hz⟩

section Two

variable [Finite Γ] {R T : Subgroup Γ}

theorem conj_mem_two (hRT : R ≤ T) (hcard : Nat.card T = 2 * Nat.card R) {g r : Γ} (hg : g ∈ T)
    (hr : r ∈ R) : g * r * g⁻¹ ∈ R := by
  by_cases hgR : g ∈ R
  · exact R.mul_mem (R.mul_mem hgR hr) (R.inv_mem hgR)
  · have h1 : g * r ∉ R := fun h => hgR (by simpa using R.mul_mem h (R.inv_mem hr))
    have h2 : g⁻¹ ∉ R := fun h => hgR (by simpa using R.inv_mem h)
    exact mul_mem_of_not_mem hRT hcard (T.mul_mem hg (hRT hr)) (T.inv_mem hg) h1 h2

theorem T_le (hRT : R ≤ T) (hcard : Nat.card T = 2 * Nat.card R) {Y : Subgroup Γ} (hRY : R ≤ Y)
    {z : Γ} (hzT : z ∈ T) (hzR : z ∉ R) (hzY : z ∈ Y) : T ≤ Y := by
  intro t ht
  by_cases htR : t ∈ R
  · exact hRY htR
  · have h2 : z⁻¹ ∉ R := fun h => hzR (by simpa using R.inv_mem h)
    have h := mul_mem_of_not_mem hRT hcard (T.inv_mem hzT) ht h2 htR
    simpa using Y.mul_mem hzY (hRY h)

theorem two_dvd_index (hRT : R ≤ T) (hcard : Nat.card T = 2 * Nat.card R) {Y : Subgroup Γ}
    (hTY : T ≤ Y) : 2 ∣ (R.subgroupOf Y).index := by
  have h := Subgroup.relIndex_mul_relIndex (H := R) (K := T) (L := Y) hRT hTY
  have h2 : R.relIndex T = 2 := by
    have h3 := Subgroup.relIndex_mul_card R T
    rw [inf_of_le_left hRT, hcard] at h3
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3
  rw [h2] at h
  change 2 ∣ R.relIndex Y
  rw [← h]
  exact dvd_mul_right _ _

theorem not_good (hRT : R ≤ T) (hcard : Nat.card T = 2 * Nat.card R) {Y : Subgroup Γ}
    (hRY : R ≤ Y) (hodd : ¬ 2 ∣ (R.subgroupOf Y).index) {y : Γ} (hy : y ∈ Y) :
    ¬ Good R T y := by
  rintro ⟨z, hzT, hzR, hz⟩
  have hzY : z ∈ Y := sup_le hRY ((Subgroup.zpowers_le).2 hy) hz
  exact hodd (two_dvd_index hRT hcard (T_le hRT hcard hRY hzT hzR hzY))

theorem good_conj (hRT : R ≤ T) (hcard : Nat.card T = 2 * Nat.card R) {g y : Γ} (hg : g ∈ T)
    (h : Good R T y) : Good R T (g * y * g⁻¹) := by
  obtain ⟨z, hzT, hzR, hz⟩ := h
  refine ⟨g * z * g⁻¹, T.mul_mem (T.mul_mem hg hzT) (T.inv_mem hg), fun h => hzR ?_, ?_⟩
  · have h1 := conj_mem_two hRT hcard (T.inv_mem hg) h
    have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    rwa [e] at h1
  · have hle : R ⊔ Subgroup.zpowers y ≤
        (R ⊔ Subgroup.zpowers (g * y * g⁻¹)).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun r hr => Subgroup.mem_comap.2 (Subgroup.mem_sup_left ?_))
        ((Subgroup.zpowers_le).2 (Subgroup.mem_comap.2 ?_))
      · simpa using conj_mem_two hRT hcard hg hr
      · simpa using mem_sup_zpowers R (g * y * g⁻¹)
    simpa using Subgroup.mem_comap.1 (hle hz)

theorem dc_form (hRT : R ≤ T) (hcard : Nat.card T = 2 * Nat.card R) {τ : Γ} (hτT : τ ∈ T)
    (hτR : τ ∉ R) {s t : Γ} (hs : s ∈ T) (ht : t ∈ T) (x : Γ) :
    ∃ r1 ∈ R, ∃ r2 ∈ R, (s * x * t = r1 * x * r2 ∨ s * x * t = r1 * (τ * x) * r2 ∨
      s * x * t = r1 * (x * τ) * r2 ∨ s * x * t = r1 * (τ * x * τ⁻¹) * r2) := by
  have hτi : τ⁻¹ ∉ R := fun h => hτR (by simpa using R.inv_mem h)
  by_cases hsR : s ∈ R <;> by_cases htR : t ∈ R
  · exact ⟨s, hsR, t, htR, Or.inl rfl⟩
  · have h2 := mul_mem_of_not_mem hRT hcard (T.inv_mem hτT) ht hτi htR
    exact ⟨s, hsR, τ⁻¹ * t, h2, Or.inr (Or.inr (Or.inl (by group)))⟩
  · have h1 := mul_mem_of_not_mem hRT hcard hs (T.inv_mem hτT) hsR hτi
    exact ⟨s * τ⁻¹, h1, t, htR, Or.inr (Or.inl (by group))⟩
  · have h1 := mul_mem_of_not_mem hRT hcard hs (T.inv_mem hτT) hsR hτi
    have h2 := mul_mem_of_not_mem hRT hcard hτT ht hτR htR
    exact ⟨s * τ⁻¹, h1, τ * t, h2, Or.inr (Or.inr (Or.inr (by group)))⟩

theorem false_of_form (hRT : R ≤ T) (hcard : Nat.card T = 2 * Nat.card R) {Y : Subgroup Γ}
    (hRY : R ≤ Y) (hodd : ¬ 2 ∣ (R.subgroupOf Y).index) {g y r1 r2 : Γ} (hr1 : r1 ∈ R)
    (hr2 : r2 ∈ R) (hg : g ∈ Y) (e : g = r1 * y * r2) (hy : Good R T y) : False := by
  refine not_good hRT hcard hRY hodd ?_ hy
  have h : y = r1⁻¹ * g * r2⁻¹ := by rw [e]; group
  rw [h]
  exact Y.mul_mem (Y.mul_mem (Y.inv_mem (hRY hr1)) hg) (Y.inv_mem (hRY hr2))

theorem good_mul_tau (hRT : R ≤ T) (hcard : Nat.card T = 2 * Nat.card R) {τ x : Γ}
    (hτT : τ ∈ T) (h : Good R T (τ * x)) : Good R T (x * τ) := by
  have h1 := good_conj hRT hcard (T.inv_mem hτT) h
  have e : τ⁻¹ * (τ * x) * τ⁻¹⁻¹ = x * τ := by group
  rwa [e] at h1

theorem false_of_dc (hRT : R ≤ T) (hcard : Nat.card T = 2 * Nat.card R) {τ : Γ} (hτT : τ ∈ T)
    (hτR : τ ∉ R) {Y : Subgroup Γ} (hRY : R ≤ Y) (hodd : ¬ 2 ∣ (R.subgroupOf Y).index)
    {s t x : Γ} (hs : s ∈ T) (ht : t ∈ T) (hg : s * x * t ∈ Y) (g1 : Good R T x)
    (g2 : Good R T (τ * x)) : False := by
  obtain ⟨r1, hr1, r2, hr2, e | e | e | e⟩ := dc_form hRT hcard hτT hτR hs ht x
  · exact false_of_form hRT hcard hRY hodd hr1 hr2 hg e g1
  · exact false_of_form hRT hcard hRY hodd hr1 hr2 hg e g2
  · exact false_of_form hRT hcard hRY hodd hr1 hr2 hg e (good_mul_tau hRT hcard hτT g2)
  · exact false_of_form hRT hcard hRY hodd hr1 hr2 hg e (good_conj hRT hcard hτT g1)

theorem noBig_of_good_two {VA VB : Subgroup Γ} {τ : Γ} {P : Γ → Prop} (hRT : R ≤ T)
    (hcard : Nat.card T = 2 * Nat.card R) (hR : Nat.card R = 2 ^ 13) (hτT : τ ∈ T) (hτR : τ ∉ R)
    (hA : Nat.card VA ∣ 245760) (hB : Nat.card VB ∣ 344064)
    (hcov : ∀ g, g ∈ VA ∨ g ∈ VB ∨ ∃ x, P x ∧ ∃ s ∈ T, ∃ t ∈ T, g = s * x * t)
    (hgood : ∀ x, P x → Good R T x ∧ Good R T (τ * x)) : NoBig R := by
  refine ⟨hR, fun Y hRY _ hodd h9 _ => ?_⟩
  have hc : ∀ g ∈ Y, g ∈ VA ∨ g ∈ VB := by
    intro g hg
    rcases hcov g with h | h | ⟨x, hx, s, hs, t, ht, rfl⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact (false_of_dc hRT hcard hτT hτR hRY hodd hs ht hg (hgood x hx).1 (hgood x hx).2).elim
  rcases le_or_le_of_cover_two hc with h | h
  · exact absurd (h9.trans ((Subgroup.card_dvd_of_le h).trans hA)) (by decide)
  · exact absurd (h9.trans ((Subgroup.card_dvd_of_le h).trans hB)) (by decide)

theorem noBig_of_good_four {VA VB W1 W2 : Subgroup Γ} {τ : Γ} {P Q : Γ → Prop} (hRT : R ≤ T)
    (hcard : Nat.card T = 2 * Nat.card R) (hR : Nat.card R = 2 ^ 13) (hτT : τ ∈ T) (hτR : τ ∉ R)
    (hRA : R ≤ VA) (hRB : R ≤ VB) (hR1 : R ≤ W1) (hR2 : R ≤ W2)
    (hA : Nat.card VA ∣ 245760) (hB : Nat.card VB ∣ 344064) (h1 : Nat.card W1 ∣ 245760)
    (h2 : Nat.card W2 ∣ 245760) (h12 : ∀ y ∈ W1, τ * y * τ⁻¹ ∈ W2)
    (h21 : ∀ y ∈ W2, τ * y * τ⁻¹ ∈ W1)
    (hcov : ∀ g, g ∈ VA ∨ g ∈ VB ∨ ∃ x, (P x ∨ Q x) ∧ ∃ s ∈ T, ∃ t ∈ T, g = s * x * t)
    (hgood : ∀ x, P x → Good R T x ∧ Good R T (τ * x))
    (hQ : ∀ x, Q x → (x ∈ W1 ∨ x ∈ W2) ∧ Good R T (τ * x)) : NoBig R := by
  refine ⟨hR, fun Y hRY hY hodd h9 h5 => ?_⟩
  have hc : ∀ g ∈ Y, g ∈ VB ∨ g ∈ VA ∨ g ∈ W1 ∨ g ∈ W2 := by
    intro g hg
    rcases hcov g with h | h | ⟨x, hx | hx, s, hs, t, ht, rfl⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact (false_of_dc hRT hcard hτT hτR hRY hodd hs ht hg (hgood x hx).1 (hgood x hx).2).elim
    · obtain ⟨hW, g2⟩ := hQ x hx
      obtain ⟨r1, hr1, r2, hr2, e | e | e | e⟩ := dc_form hRT hcard hτT hτR hs ht x
      · rw [e]
        rcases hW with hW | hW
        · exact Or.inr (Or.inr (Or.inl (W1.mul_mem (W1.mul_mem (hR1 hr1) hW) (hR1 hr2))))
        · exact Or.inr (Or.inr (Or.inr (W2.mul_mem (W2.mul_mem (hR2 hr1) hW) (hR2 hr2))))
      · exact (false_of_form hRT hcard hRY hodd hr1 hr2 hg e g2).elim
      · exact (false_of_form hRT hcard hRY hodd hr1 hr2 hg e (good_mul_tau hRT hcard hτT g2)).elim
      · rw [e]
        rcases hW with hW | hW
        · exact Or.inr (Or.inr (Or.inr
            (W2.mul_mem (W2.mul_mem (hR2 hr1) (h12 x hW)) (hR2 hr2))))
        · exact Or.inr (Or.inr (Or.inl
            (W1.mul_mem (W1.mul_mem (hR1 hr1) (h21 x hW)) (hR1 hr2))))
  let V : Fin 4 → Subgroup Γ := ![VB, VA, W1, W2]
  have hRV : ∀ i, R ≤ V i := by
    intro i
    fin_cases i
    exacts [hRB, hRA, hR1, hR2]
  have hN : ∀ i, ∃ N, Nat.card (V i) ∣ N ∧ ¬ 9 ∣ N := by
    intro i
    fin_cases i
    exacts [⟨344064, hB, by decide⟩, ⟨245760, hA, by decide⟩, ⟨245760, h1, by decide⟩,
      ⟨245760, h2, by decide⟩]
  refine not_cover_four (Y := ↥Y) (R.subgroupOf Y) hodd (fun i => (V i).subgroupOf Y)
    (fun i => Subgroup.comap_mono (hRV i)) (fun i hi => ?_) (fun i => ?_) ?_ ?_
  · rw [Subgroup.subgroupOf_eq_top] at hi
    obtain ⟨N, hN, hn9⟩ := hN i
    exact hn9 (h9.trans ((Subgroup.card_dvd_of_le hi).trans hN))
  · obtain ⟨N, hN, hn9⟩ := hN i
    exact dvd_index_of_dvd_card Y (V i) Nat.prime_three (k := 2) h9 hN hn9
  · exact dvd_index_of_dvd_card Y VB Nat.prime_five (k := 1) (by simpa using h5) hB (by decide)
  · rintro ⟨y, hy⟩
    rcases hc y hy with h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]

end Two

theorem f_mul {S : List Γ} {f : Γ → ZMod 2} (f1 : f 1 = 0)
    (hS : ∀ s ∈ S, s * s = 1 ∧ ∃ v : ZMod 2, ∀ g ∈ Subgroup.closure {x | x ∈ S},
      f (s * g) = f g + v) :
    ∀ g ∈ Subgroup.closure {x | x ∈ S}, ∀ h ∈ Subgroup.closure {x | x ∈ S},
      f (g * h) = f g + f h := by
  intro g hg
  refine Subgroup.closure_induction_left
    (p := fun g _ => ∀ h ∈ Subgroup.closure {x | x ∈ S}, f (g * h) = f g + f h) ?_ ?_ ?_ hg
  · intro h _
    rw [one_mul, f1, zero_add]
  · intro s hs y hy ih h hh
    obtain ⟨-, v, hv⟩ := hS s hs
    rw [mul_assoc, hv _ (Subgroup.mul_mem _ hy hh), ih h hh, hv _ hy]
    ring
  · intro s hs y hy ih h hh
    obtain ⟨hss, v, hv⟩ := hS s hs
    rw [inv_eq_of_mul_eq_one_right hss, mul_assoc, hv _ (Subgroup.mul_mem _ hy hh), ih h hh,
      hv _ hy]
    ring

theorem idx2 [Finite Γ] {S : List Γ} {T R : Subgroup Γ} (hT : T = Subgroup.closure {x | x ∈ S})
    {f : Γ → ZMod 2} (f1 : f 1 = 0)
    (hS : ∀ s ∈ S, s * s = 1 ∧ ∃ v : ZMod 2, ∀ g ∈ T, f (s * g) = f g + v)
    {τ : Γ} (hτT : τ ∈ T) (hτ : f τ = 1) (hτi : τ * τ = 1) (hRT : R ≤ T)
    (hRf : ∀ r ∈ R, f r = 0)
    (hc : ∀ s ∈ S, (s ∈ R ∧ τ * s * τ ∈ R) ∨ (τ * s ∈ R ∧ s * τ ∈ R)) :
    (∀ g ∈ T, g ∈ R ↔ f g = 0) ∧ Nat.card T = 2 * Nat.card R := by
  subst hT
  have hmul := f_mul f1 hS
  have hor : ∀ g ∈ Subgroup.closure {x | x ∈ S}, g ∈ R ∨ τ * g ∈ R := by
    have step : ∀ s ∈ S, ∀ y, y ∈ R ∨ τ * y ∈ R → s * y ∈ R ∨ τ * (s * y) ∈ R := by
      intro s hs y hy
      rcases hc s hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hy with hy | hy
        · exact Or.inl (R.mul_mem h1 hy)
        · right
          have e1 : τ * s * τ * (τ * y) = τ * s * (τ * τ) * y := by group
          have e : τ * (s * y) = τ * s * τ * (τ * y) := by rw [e1, hτi, mul_one, mul_assoc]
          rw [e]
          exact R.mul_mem h2 hy
      · rcases hy with hy | hy
        · right
          rw [← mul_assoc]
          exact R.mul_mem h1 hy
        · left
          have e1 : s * τ * (τ * y) = s * (τ * τ) * y := by group
          have e : s * y = s * τ * (τ * y) := by rw [e1, hτi, mul_one]
          rw [e]
          exact R.mul_mem h2 hy
    intro g hg
    refine Subgroup.closure_induction_left (p := fun g _ => g ∈ R ∨ τ * g ∈ R)
      (Or.inl R.one_mem) ?_ ?_ hg
    · intro s hs y _ ih
      exact step s hs y ih
    · intro s hs y _ ih
      rw [inv_eq_of_mul_eq_one_right (hS s hs).1]
      exact step s hs y ih
  have hiff : ∀ g ∈ Subgroup.closure {x | x ∈ S}, g ∈ R ↔ f g = 0 := by
    intro g hg
    refine ⟨hRf g, fun h0 => ?_⟩
    rcases hor g hg with h | h
    · exact h
    · have h1 := hRf _ h
      rw [hmul _ hτT _ hg, hτ, h0] at h1
      exact absurd h1 (by decide)
  refine ⟨hiff, ?_⟩
  have hidx : (R.subgroupOf (Subgroup.closure {x | x ∈ S})).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨τ, hτT⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      hiff _ (Subgroup.mul_mem _ b.2 hτT), hiff _ b.2, hmul _ b.2 _ hτT, hτ]
    generalize f b = z
    revert z
    decide
  have h3 := Subgroup.relIndex_mul_card R (Subgroup.closure {x | x ∈ S})
  rw [inf_of_le_left hRT] at h3
  change (R.subgroupOf _).index * _ = _ at h3
  rw [hidx] at h3
  exact h3.symm

end CFSG.Quasithin.H13.K1262Two.RuP

end

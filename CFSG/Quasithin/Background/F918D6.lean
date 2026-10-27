module

public import CFSG.Quasithin.Background.B4L3Fin
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin

private def ctr (g : L3.Γ) : L3.Vec := ∑ x ∈ L3.cim g, x

private def e₁ : L3.Vec := ![1, 0, 0]

private def e₂ : L3.Vec := ![0, 1, 0]

private def a₀ : L3.Γ := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

private def b₀ : L3.Γ := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

set_option maxRecDepth 100000 in
private theorem a₀_b₀ : L3.IsInvol a₀ ∧ L3.IsInvol b₀ ∧ L3.IsInvol (a₀ * b₀) ∧ a₀ * b₀ = b₀ * a₀ ∧
    ctr a₀ = e₁ ∧ ctr b₀ = e₂ ∧ ctr (a₀ * b₀) = e₁ + e₂ := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem ctr_a₀_mul : ∀ b : L3.Γ, L3.IsInvol b → a₀ * b = b * a₀ → ctr a₀ ≠ ctr b →
    ctr (a₀ * b) = ctr a₀ + ctr b := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem stab_trans : ∀ q : L3.Vec, q ≠ 0 → q ≠ e₁ →
    ∃ g : L3.Γ, L3.act g e₁ = e₁ ∧ L3.act g e₂ = q := by
  decide +kernel

private theorem ctr_one : ctr 1 = 0 := by decide +kernel

private theorem vec_add_self : ∀ z : L3.Vec, z + z = 0 := by decide

private theorem act_inj (g : L3.Γ) : Function.Injective (L3.act g) := fun x y h => by
  have := congrArg (L3.act g⁻¹) h
  rwa [L3.act_inv_act, L3.act_inv_act] at this

private theorem two_trans {p q : L3.Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) :
    ∃ g : L3.Γ, L3.act g e₁ = p ∧ L3.act g e₂ = q := by
  obtain ⟨h, hh⟩ := L3.act_trans e₁ p (by decide) hp
  have hq0 : L3.act h⁻¹ q ≠ 0 := fun h0 => hq (by rw [← L3.act_act_inv h q, h0, L3.act_zero])
  have hq1 : L3.act h⁻¹ q ≠ e₁ := fun h1 => hpq (by rw [← hh, ← h1, L3.act_act_inv])
  obtain ⟨g, hg1, hg2⟩ := stab_trans _ hq0 hq1
  exact ⟨h * g, by rw [L3.act_mul, hg1, hh], by rw [L3.act_mul, hg2, L3.act_act_inv]⟩

private theorem act_conj_sub (g a : L3.Γ) (v : L3.Vec) :
    L3.act (g * a * g⁻¹) v - v = L3.act g (L3.act a (L3.act g⁻¹ v) - L3.act g⁻¹ v) := by
  rw [L3.act_sub, L3.act_mul, L3.act_mul, L3.act_act_inv]

private theorem cim_conj (g a : L3.Γ) : L3.cim (g * a * g⁻¹) = (L3.cim a).image (L3.act g) := by
  unfold L3.cim
  rw [Finset.image_image]
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨L3.act g⁻¹ v, (act_conj_sub g a v).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨L3.act g w, ?_⟩
    rw [act_conj_sub, L3.act_inv_act]

private theorem ctr_conj (g a : L3.Γ) : ctr (g * a * g⁻¹) = L3.act g (ctr a) := by
  unfold ctr
  rw [cim_conj, Finset.sum_image fun x _ y _ h => act_inj g h]
  unfold L3.act
  exact (Matrix.mulVec_sum _ _ _).symm

private theorem ctr_eq_of_cim {g : L3.Γ} {c : L3.Vec} (hc0 : c ≠ 0) (h : L3.cim g = {0, c}) :
    ctr g = c := by
  unfold ctr
  rw [h, Finset.sum_pair (Ne.symm hc0), zero_add]

private theorem cim_eq_ctr {g : L3.Γ} (hg : L3.IsInvol g) : L3.cim g = {0, ctr g} ∧ ctr g ≠ 0 := by
  obtain ⟨c, hc0, hc⟩ := L3.invol_center g hg
  rw [ctr_eq_of_cim hc0 hc]
  exact ⟨hc, hc0⟩

private theorem mem_AS_ctr {a : L3.Γ} (ha : L3.IsInvol a) : a ∈ L3.AS {0, ctr a} := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v => ?_⟩
  rw [← (cim_eq_ctr ha).1]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

private theorem eq_of_mul_eq_one {a b : L3.Γ} (hb : L3.IsInvol b) (h : a * b = 1) : a = b :=
  calc a = a * b * b := by rw [mul_assoc, hb.1, mul_one]
    _ = b := by rw [h, one_mul]

private theorem ctr_same_mul {a b : L3.Γ} (ha : L3.IsInvol a) (hb : L3.IsInvol b) (hab : a ≠ b)
    (hc : ctr a = ctr b) : ctr (a * b) = ctr a := by
  have hc0 := (cim_eq_ctr ha).2
  have hbA : b ∈ L3.AS {0, ctr a} := by rw [hc]; exact mem_AS_ctr hb
  have hm := L3.AS_mul _ hc0 a (mem_AS_ctr ha) b hbA
  exact ctr_eq_of_cim hc0 (L3.AS_cim _ hc0 _ hm fun h => hab (eq_of_mul_eq_one hb h))

private theorem ctr_same_eq {a b s : L3.Γ} (ha : L3.IsInvol a) (hb : L3.IsInvol b) (hab : a ≠ b)
    (hc : ctr a = ctr b) (hs : L3.IsInvol s) (hsc : ctr s = ctr a) :
    s = a ∨ s = b ∨ s = a * b := by
  have hc0 := (cim_eq_ctr ha).2
  have haA := mem_AS_ctr ha
  have hbA : b ∈ L3.AS {0, ctr a} := by rw [hc]; exact mem_AS_ctr hb
  have hsA : s ∈ L3.AS {0, ctr a} := by rw [← hsc]; exact mem_AS_ctr hs
  have h1A : (1 : L3.Γ) ∈ L3.AS {0, ctr a} := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v => ?_⟩
    simp [L3.act_one]
  have habA := L3.AS_mul _ hc0 a haA b hbA
  have hab1 : a * b ≠ 1 := fun h => hab (eq_of_mul_eq_one hb h)
  have ha1 : a ≠ a * b := fun h => hb.2 (mul_left_cancel (h.symm.trans (mul_one a).symm))
  have hb1 : b ≠ a * b := fun h => ha.2 (mul_right_cancel ((one_mul b).trans h)).symm
  have hsub : ({1, a, b, a * b} : Finset L3.Γ) ⊆ L3.AS {0, ctr a} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h <;> rw [h] <;> assumption
  have hn1 : (1 : L3.Γ) ∉ ({a, b, a * b} : Finset L3.Γ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha.2, Ne.symm hb.2, Ne.symm hab1⟩
  have hna : a ∉ ({b, a * b} : Finset L3.Γ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, ha1⟩
  have hcard : ({1, a, b, a * b} : Finset L3.Γ).card = 4 := by
    rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hna, Finset.card_pair hb1]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, L3.AS_card _ hc0])
  rw [← heq] at hsA
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsA
  rcases hsA with h | h | h | h
  · exact absurd h hs.2
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private theorem invol_conj {a : L3.Γ} (g : L3.Γ) (ha : L3.IsInvol a) :
    L3.IsInvol (g * a * g⁻¹) := by
  refine ⟨?_, fun h => ha.2 ?_⟩
  · calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha.1, mul_one, mul_inv_cancel]
  · calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]

private theorem ctr_comm_mul {a b : L3.Γ} (ha : L3.IsInvol a) (hb : L3.IsInvol b)
    (hab : a * b = b * a) (hc : ctr a ≠ ctr b) : ctr (a * b) = ctr a + ctr b := by
  obtain ⟨x, rfl⟩ := L3.conj_invol a₀_b₀.1 ha
  obtain ⟨b', rfl⟩ : ∃ b', b = x * b' * x⁻¹ := ⟨x⁻¹ * b * x, by group⟩
  have hb' : L3.IsInvol b' := by
    have h := invol_conj x⁻¹ hb
    rwa [show x⁻¹ * (x * b' * x⁻¹) * x⁻¹⁻¹ = b' by group] at h
  have hab' : a₀ * b' = b' * a₀ := by
    have h : x * (a₀ * b') * x⁻¹ = x * (b' * a₀) * x⁻¹ := by
      rw [show x * (a₀ * b') * x⁻¹ = x * a₀ * x⁻¹ * (x * b' * x⁻¹) by group, hab]
      group
    exact mul_left_cancel (mul_right_cancel h)
  rw [ctr_conj, ctr_conj] at hc
  have hc' : ctr a₀ ≠ ctr b' := fun h => hc (by rw [h])
  rw [show x * a₀ * x⁻¹ * (x * b' * x⁻¹) = x * (a₀ * b') * x⁻¹ by group, ctr_conj, ctr_conj,
    ctr_conj, ctr_a₀_mul b' hb' hab' hc', L3.act_add]

private theorem invol_map (θ : L3.Γ ≃* L3.Γ) {a : L3.Γ} (ha : L3.IsInvol a) :
    L3.IsInvol (θ a) :=
  ⟨by rw [← map_mul, ha.1, map_one], fun h => ha.2 (θ.injective (by rw [h, map_one]))⟩

private theorem eq_of_basis {f g : L3.Vec → L3.Vec} (hf : ∀ a b, f (a + b) = f a + f b)
    (hg : ∀ a b, g (a + b) = g a + g b) (h : ∀ j : Fin 3, f (Pi.single j 1) = g (Pi.single j 1))
    (v : L3.Vec) : f v = g v := by
  have hf0 : f 0 = 0 := by
    have := hf 0 0
    rw [add_zero] at this
    exact (add_eq_left.mp this.symm)
  have hg0 : g 0 = 0 := by
    have := hg 0 0
    rw [add_zero] at this
    exact (add_eq_left.mp this.symm)
  have hs : ∀ j : Fin 3, ∀ a : ZMod 2, f (Pi.single j a) = g (Pi.single j a) := by
    intro j a
    have ha : a = 0 ∨ a = 1 := by revert a; decide
    rcases ha with rfl | rfl
    · rw [Pi.single_zero, hf0, hg0]
    · exact h j
  have hv : v = (Pi.single (0 : Fin 3) (v 0) : L3.Vec) + (Pi.single (1 : Fin 3) (v 1) : L3.Vec) +
      (Pi.single (2 : Fin 3) (v 2) : L3.Vec) := by
    funext i
    fin_cases i <;> simp
  rw [hv, hf, hf, hg, hg, hs, hs, hs]

private theorem exists_act_eq {f : L3.Vec → L3.Vec} (hf : ∀ a b, f (a + b) = f a + f b)
    (hinj : Function.Injective f) : ∃ δ : L3.Γ, ∀ v, L3.act δ v = f v := by
  have hf0 : f 0 = 0 := by
    have := hf 0 0
    rw [add_zero] at this
    exact (add_eq_left.mp this.symm)
  set M : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun i j => f (Pi.single j 1) i with hM
  have hMv : ∀ v, M.mulVec v = f v := by
    refine eq_of_basis (fun a b => Matrix.mulVec_add M a b) hf fun j => ?_
    funext i
    simp [hM, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdet : M.det = 1 := by
    have hne : M.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0
      apply hinj
      rw [← hMv, hv, hf0]
    generalize M.det = d at hne ⊢
    revert d
    decide
  exact ⟨⟨M, hdet⟩, fun v => hMv v⟩

theorem outer_swaps_same_center (θ : L3.Γ ≃* L3.Γ)
    (hθ : ¬ ∃ g : L3.Γ, ∀ x : L3.Γ, θ x = g * x * g⁻¹)
    {t t' : L3.Γ} (ht : L3.IsInvol t) (ht' : L3.IsInvol t') (hne : t ≠ t')
    (hcomm : t * t' = t' * t) (hsame : L3.cim t = L3.cim t') :
    L3.cim (θ t) ≠ L3.cim (θ t') := by
  intro hcon
  apply hθ
  have hsame' : ctr t = ctr t' := congrArg (fun S => ∑ x ∈ S, x) hsame
  have hcon' : ctr (θ t) = ctr (θ t') := congrArg (fun S => ∑ x ∈ S, x) hcon
  have hθt := invol_map θ ht
  have hθt' := invol_map θ ht'
  have hθne : θ t ≠ θ t' := fun h => hne (θ.injective h)
  have hbase : ∀ s, L3.IsInvol s → ctr s = ctr t → ctr (θ s) = ctr (θ t) := by
    intro s hs hst
    rcases ctr_same_eq ht ht' hne hsame' hs hst with h | h | h
    · rw [h]
    · rw [h, hcon']
    · rw [h, hcomm, map_mul, ctr_same_mul hθt' hθt hθne.symm hcon'.symm, hcon']
  have ht0 := (cim_eq_ctr ht).2
  have htrans : ∀ a, L3.IsInvol a → ∀ g, L3.act g (ctr t) = ctr a →
      ctr (θ a) = L3.act (θ g) (ctr (θ t)) := by
    intro a ha g hg
    have h1 : ctr (g⁻¹ * a * g⁻¹⁻¹) = ctr t := by
      rw [ctr_conj, ← hg, L3.act_inv_act]
    have h2 := hbase _ (invol_conj g⁻¹ ha) h1
    have h3 : a = g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ := by group
    rw [h3, map_mul, map_mul, map_inv, ctr_conj, h2]
  have hwd : ∀ a b, L3.IsInvol a → L3.IsInvol b → ctr a = ctr b → ctr (θ a) = ctr (θ b) := by
    intro a b ha hb hab
    obtain ⟨g, hg⟩ := L3.act_trans _ _ ht0 (cim_eq_ctr ha).2
    rw [htrans a ha g hg, htrans b hb g (hg.trans hab)]
  have hsex : ∀ v : L3.Vec, ∃ s : L3.Γ, (v = 0 → s = 1) ∧ (v ≠ 0 → L3.IsInvol s ∧ ctr s = v) := by
    intro v
    by_cases hv : v = 0
    · exact ⟨1, fun _ => rfl, fun h => absurd hv h⟩
    · obtain ⟨g, hg⟩ := L3.act_trans _ _ ht0 hv
      exact ⟨g * t * g⁻¹, fun h => absurd h hv, fun _ => ⟨invol_conj g ht, by rw [ctr_conj, hg]⟩⟩
  choose s hs0 hs using hsex
  obtain ⟨f, hf⟩ : ∃ f : L3.Vec → L3.Vec, ∀ v, f v = ctr (θ (s v)) := ⟨_, fun _ => rfl⟩
  have hf0 : f 0 = 0 := by rw [hf, hs0 0 rfl, map_one, ctr_one]
  have hfa : ∀ a, L3.IsInvol a → f (ctr a) = ctr (θ a) := by
    intro a ha
    have h0 := (cim_eq_ctr ha).2
    rw [hf]
    exact hwd _ _ (hs _ h0).1 ha (hs _ h0).2
  have hsurj : Function.Surjective f := by
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by rw [hf0, hw]⟩
    · obtain ⟨hsw, hcw⟩ := hs w hw
      refine ⟨ctr (θ.symm (s w)), ?_⟩
      rw [hfa _ (invol_map θ.symm hsw), MulEquiv.apply_symm_apply, hcw]
  have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hsurj
  have hadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    by_cases hx : x = 0
    · rw [hx, zero_add, hf0, zero_add]
    by_cases hy : y = 0
    · rw [hy, add_zero, hf0, add_zero]
    by_cases hxy : x = y
    · rw [hxy, vec_add_self, hf0, vec_add_self]
    obtain ⟨g, hg1, hg2⟩ := two_trans hx hy hxy
    obtain ⟨ha0, hb0, hab0, hcomm0, hca0, hcb0, hcab0⟩ := a₀_b₀
    have ha := invol_conj g ha0
    have hb := invol_conj g hb0
    have hab := invol_conj g hab0
    have hca : ctr (g * a₀ * g⁻¹) = x := by rw [ctr_conj, hca0, hg1]
    have hcb : ctr (g * b₀ * g⁻¹) = y := by rw [ctr_conj, hcb0, hg2]
    have hcab : ctr (g * (a₀ * b₀) * g⁻¹) = x + y := by
      rw [ctr_conj, hcab0, L3.act_add, hg1, hg2]
    have hprod : g * (a₀ * b₀) * g⁻¹ = g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) := by group
    have hc : g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * b₀ * g⁻¹ * (g * a₀ * g⁻¹) :=
      calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * (a₀ * b₀) * g⁻¹ := by group
        _ = g * (b₀ * a₀) * g⁻¹ := by rw [hcomm0]
        _ = g * b₀ * g⁻¹ * (g * a₀ * g⁻¹) := by group
    have hcθ : θ (g * a₀ * g⁻¹) * θ (g * b₀ * g⁻¹) = θ (g * b₀ * g⁻¹) * θ (g * a₀ * g⁻¹) := by
      rw [← map_mul, ← map_mul, hc]
    have hne' : ctr (θ (g * a₀ * g⁻¹)) ≠ ctr (θ (g * b₀ * g⁻¹)) := by
      rw [← hfa _ ha, ← hfa _ hb, hca, hcb]
      exact fun h => hxy (hinj h)
    calc f (x + y) = f (ctr (g * (a₀ * b₀) * g⁻¹)) := by rw [hcab]
      _ = ctr (θ (g * (a₀ * b₀) * g⁻¹)) := hfa _ hab
      _ = ctr (θ (g * a₀ * g⁻¹) * θ (g * b₀ * g⁻¹)) := by rw [hprod, map_mul]
      _ = ctr (θ (g * a₀ * g⁻¹)) + ctr (θ (g * b₀ * g⁻¹)) :=
        ctr_comm_mul (invol_map θ ha) (invol_map θ hb) hcθ hne'
      _ = f x + f y := by rw [← hfa _ ha, ← hfa _ hb, hca, hcb]
  obtain ⟨δ, hδ⟩ := exists_act_eq hadd hinj
  have hequiv : ∀ γ w, f (L3.act γ w) = L3.act (θ γ) (f w) := by
    intro γ w
    by_cases hw : w = 0
    · rw [hw, L3.act_zero, hf0, L3.act_zero]
    obtain ⟨hsw, hcw⟩ := hs w hw
    have h1 : ctr (γ * s w * γ⁻¹) = L3.act γ w := by rw [ctr_conj, hcw]
    rw [← h1, hfa _ (invol_conj γ hsw), map_mul, map_mul, map_inv, ctr_conj, ← hfa _ hsw, hcw]
  refine ⟨δ, fun x => L3.act_ext fun v => ?_⟩
  obtain ⟨w, rfl⟩ : ∃ w, L3.act δ w = v := ⟨L3.act δ⁻¹ v, L3.act_act_inv δ v⟩
  rw [L3.act_mul, L3.act_mul, L3.act_inv_act, hδ, hδ, hequiv]

end CFSG.Quasithin

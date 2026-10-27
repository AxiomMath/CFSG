module

public import CFSG.Quasithin.Background.B4L3Fin
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.L3Split

open CFSG.Quasithin L3

@[expose] def invs : Finset Γ := Finset.univ.filter fun τ => τ * τ = 1 ∧ τ ≠ 1

theorem mem_invs {τ : Γ} : τ ∈ invs ↔ IsInvol τ := by
  simp [invs, IsInvol]

@[expose] def invC (c : Vec) : Finset Γ :=
  Finset.univ.filter fun τ => (τ * τ = 1 ∧ τ ≠ 1) ∧ ∃ v : Vec, act τ v - v = c

theorem sc_check : ∀ τ ∈ invs, ∀ τ' ∈ invs, τ ≠ τ' → cim τ = cim τ' →
    (τ * τ' = τ' * τ ∧ τ * τ' ∈ invs ∧ cim (τ * τ') = cim τ ∧
      ∃ w : Vec, act τ' w = w ∧ act τ w ≠ w) := by
  unfold invs cim act
  decide +kernel

theorem sa_check : ∀ τ₁ ∈ invs, ∀ τ₂ ∈ invs, fixS τ₁ = fixS τ₂ → cim τ₁ ≠ cim τ₂ →
    τ₁ * τ₂ ∈ invs ∧ fixS (τ₁ * τ₂) = fixS τ₁ := by
  unfold invs fixS cim act
  decide +kernel

@[expose] def esaB (c₁ c₂ : Vec) : Bool :=
  decide (∃ τ₁ ∈ invC c₁, ∃ τ₂ ∈ invC c₂, fixS τ₁ = fixS τ₂ ∧
    ∃ v : Vec, act τ₁ v ≠ v ∧ act τ₁ v - v = c₁ ∧ act τ₂ v - v = c₂)

theorem esaB_check : ∀ c₁ c₂ : Vec, c₁ ≠ 0 → c₂ ≠ 0 → c₁ ≠ c₂ → esaB c₁ c₂ = true := by
  unfold esaB invC fixS act
  decide +kernel

theorem esa_check (c₁ c₂ : Vec) (h1 : c₁ ≠ 0) (h2 : c₂ ≠ 0) (h12 : c₁ ≠ c₂) :
    ∃ τ₁ ∈ invC c₁, ∃ τ₂ ∈ invC c₂, fixS τ₁ = fixS τ₂ ∧
      ∃ v : Vec, act τ₁ v ≠ v ∧ act τ₁ v - v = c₁ ∧ act τ₂ v - v = c₂ :=
  of_decide_eq_true (esaB_check c₁ c₂ h1 h2 h12)

theorem center_check : ∀ c : Vec, c ≠ 0 → (invC c).Nonempty := by
  unfold invC act
  decide +kernel

theorem vec_neg : ∀ v : Vec, -v = v := by decide

theorem vec_sub : ∀ v w : Vec, v - w = v + w := by decide

theorem vec_add_self : ∀ v : Vec, v + v = 0 := by decide

theorem vec_swap : ∀ a b c d : Vec, a + b = c + d → a + c = b + d := by decide

theorem moved_check : ∀ τ ∈ invs, ∀ v w : Vec, act τ v ≠ v → act τ w ≠ w →
    act τ v - v = act τ w - w := by
  unfold invs act
  decide +kernel

theorem cim_check : ∀ τ ∈ invs, ∀ τ' ∈ invs, ∀ v w : Vec, act τ v ≠ v → act τ' w ≠ w →
    act τ v - v = act τ' w - w → cim τ = cim τ' := by
  unfold invs cim act
  decide +kernel

theorem ctr_fixed : ∀ τ ∈ invs, ∀ v : Vec, act τ (act τ v - v) = act τ v - v := by
  unfold invs act
  decide +kernel

theorem cim_ne_check : ∀ τ ∈ invs, ∀ τ' ∈ invs, ∀ v : Vec, act τ v ≠ v → act τ' v ≠ v →
    act τ v - v ≠ act τ' v - v → cim τ ≠ cim τ' := by
  unfold invs cim act
  decide +kernel

theorem fix_card : ∀ τ ∈ invs, (Finset.univ.filter fun v => act τ v = v).card = 4 := by
  unfold invs act
  decide +kernel

variable {A : Type*} [CommGroup A] [Finite A]

theorem card_eq_eight (ρ : Γ →* MulAut A) (β : A →* Multiplicative Vec)
    (hβs : Function.Surjective β)
    (hβ : ∀ γ x, β (ρ γ x) = Multiplicative.ofAdd (act γ (Multiplicative.toAdd (β x))))
    {a₀ : Γ} (ha₀ : IsInvol a₀) {E : Subgroup (Multiplicative Vec)} (hE : Nat.card E = 4)
    (hfixE : ∀ x, β x ∈ E → ρ a₀ x = x)
    (hgen : Subgroup.closure {x | ∃ γ y, ρ γ y * y⁻¹ = x} = ⊤) : Nat.card A = 8 := by
  classical
  set bv : A → Vec := fun x => Multiplicative.toAdd (β x) with hbv
  have hbvρ : ∀ γ x, bv (ρ γ x) = act γ (bv x) := by
    intro γ x
    simp only [hbv, hβ]
    rfl
  have hbvmul : ∀ x y, bv (x * y) = bv x + bv y := by
    intro x y
    simp only [hbv, map_mul]
    rfl
  have hbvinv : ∀ x, bv x⁻¹ = bv x := by
    intro x
    show Multiplicative.toAdd (β x⁻¹) = Multiplicative.toAdd (β x)
    rw [map_inv, toAdd_inv, vec_neg]
  have hbvs : ∀ v : Vec, ∃ x, bv x = v := by
    intro v
    obtain ⟨x, hx⟩ := hβs (Multiplicative.ofAdd v)
    exact ⟨x, by simp only [hbv, hx]; rfl⟩
  have ha₀i : a₀ ∈ invs := mem_invs.mpr ha₀
  have hfix0 : ∀ x, act a₀ (bv x) = bv x → ρ a₀ x = x := by
    let F : Subgroup (Multiplicative Vec) :=
      { carrier := {m | act a₀ (Multiplicative.toAdd m) = Multiplicative.toAdd m}
        one_mem' := by
          show act a₀ 0 = 0
          exact act_zero a₀
        mul_mem' := by
          intro a b ha hb
          show act a₀ (Multiplicative.toAdd a + Multiplicative.toAdd b) = _
          rw [act_add, ha, hb]
          rfl
        inv_mem' := by
          intro a ha
          show act a₀ (Multiplicative.toAdd a⁻¹) = Multiplicative.toAdd a⁻¹
          rw [toAdd_inv, vec_neg]
          exact ha }
    have hEF : E ≤ F := by
      intro m hm
      obtain ⟨x, rfl⟩ := hβs m
      have h1 := hfixE x hm
      show act a₀ (bv x) = bv x
      rw [← hbvρ, h1]
    have hF4 : Nat.card F = 4 := by
      rw [← fix_card a₀ ha₀i, ← Nat.card_eq_finsetCard]
      refine Nat.card_congr
        { toFun := fun m =>
            ⟨Multiplicative.toAdd m.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, m.2⟩⟩
          invFun := fun v => ⟨Multiplicative.ofAdd v.1, by
            have := v.2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
            exact this⟩
          left_inv := fun m => rfl
          right_inv := fun v => rfl }
    have hEF' : E = F := Subgroup.eq_of_le_of_card_ge hEF (by rw [hE, hF4])
    intro x hx
    exact hfixE x (hEF' ▸ (show β x ∈ F from hx))
  have hfixτ : ∀ τ ∈ invs, ∀ x, act τ (bv x) = bv x → ρ τ x = x := by
    intro τ hτ x hx
    obtain ⟨g, hg⟩ := conj_invol ha₀ (mem_invs.mp hτ)
    have h1 : act a₀ (bv (ρ g⁻¹ x)) = bv (ρ g⁻¹ x) := by
      rw [hbvρ, ← act_mul]
      have e1 : a₀ * g⁻¹ = g⁻¹ * τ := by rw [← hg]; group
      rw [e1, act_mul, hx]
    have h2 := hfix0 _ h1
    rw [← hg, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, h2, ← MulAut.mul_apply,
      ← map_mul, mul_inv_cancel, map_one]
    rfl
  set Y : Γ → A → A := fun γ x => ρ γ x * x⁻¹ with hY
  have hbvY : ∀ γ x, bv (Y γ x) = act γ (bv x) - bv x := by
    intro γ x
    simp only [hY, hbvmul, hbvinv, hbvρ, vec_sub]
  have hYmul : ∀ γ δ x, Y (γ * δ) x = ρ γ (Y δ x) * Y γ x := by
    intro γ δ x
    simp only [hY]
    rw [map_mul, MulAut.mul_apply, map_mul (ρ γ), map_inv (ρ γ)]
    group
  have hP0 : ∀ τ ∈ invs, ∀ x, act τ (bv x) = bv x → Y τ x = 1 := by
    intro τ hτ x hx
    simp only [hY, hfixτ τ hτ x hx, mul_inv_cancel]
  have hP1 : ∀ τ ∈ invs, ∀ x x', act τ (bv x) ≠ bv x → act τ (bv x') ≠ bv x' →
      Y τ x = Y τ x' := by
    intro τ hτ x x' hx hx'
    have hm := moved_check τ hτ _ _ hx hx'
    have hh : act τ (bv (x⁻¹ * x')) = bv (x⁻¹ * x') := by
      rw [hbvmul, hbvinv, act_add]
      rw [vec_sub, vec_sub] at hm
      exact vec_swap _ _ _ _ hm
    have h1 := hfixτ τ hτ _ hh
    have e3 : x' = x * (x⁻¹ * x') := by group
    simp only [hY]
    rw [e3, map_mul, h1]
    group
  have hP3 : ∀ τ ∈ invs, ∀ x, ρ τ (Y τ x) = Y τ x := by
    intro τ hτ x
    refine hfixτ τ hτ _ ?_
    rw [hbvY]
    exact ctr_fixed τ hτ _
  have hY2 : ∀ τ ∈ invs, ∀ x, Y τ x * Y τ x = 1 := by
    intro τ hτ x
    have hτ2 : τ * τ = 1 := (mem_invs.mp hτ).1
    have h1 : ρ τ (ρ τ x) = x := by
      rw [← MulAut.mul_apply, ← map_mul, hτ2, map_one]
      rfl
    have h2 : ρ τ x = Y τ x * x := by simp only [hY]; group
    have h3 : ρ τ (ρ τ x) = Y τ x * (Y τ x * x) := by rw [h2, map_mul, hP3 τ hτ x, h2]
    have h4 : (Y τ x * Y τ x) * x = 1 * x := by rw [one_mul, mul_assoc, ← h3, h1]
    exact mul_right_cancel h4
  have ha : ∀ τ ∈ invs, ∀ τ' ∈ invs, cim τ = cim τ' → ∀ x x',
      act τ (bv x) ≠ bv x → act τ' (bv x') ≠ bv x' → Y τ x = Y τ' x' := by
    intro τ hτ τ' hτ' hc x x' hx hx'
    by_cases hττ : τ = τ'
    · subst hττ
      exact hP1 τ hτ x x' hx hx'
    obtain ⟨hcomm, hσ, hσc, w, hw', hw⟩ := sc_check τ hτ τ' hτ' hττ hc
    obtain ⟨-, -, -, w₂, hw₂, hw₂'⟩ := sc_check τ' hτ' τ hτ (Ne.symm hττ) hc.symm
    obtain ⟨xw, hxw⟩ := hbvs w
    obtain ⟨xw₂, hxw₂⟩ := hbvs w₂
    have h1 : Y (τ * τ') xw = Y τ xw := by
      simp only [hY]
      rw [map_mul, MulAut.mul_apply, hfixτ τ' hτ' xw (by rw [hxw]; exact hw')]
    have h2 : Y (τ * τ') xw₂ = Y τ' xw₂ := by
      simp only [hY]
      rw [hcomm, map_mul, MulAut.mul_apply, hfixτ τ hτ xw₂ (by rw [hxw₂]; exact hw₂)]
    have hmv1 : act (τ * τ') (bv xw) ≠ bv xw := by
      intro h0
      have h3 := hP0 _ hσ xw h0
      rw [h1] at h3
      apply hw
      have := congrArg bv h3
      rw [hbvY] at this
      rw [← hxw]
      have h4 : act τ (bv xw) - bv xw = 0 := by simpa [hbv] using this
      exact sub_eq_zero.mp h4
    have hmv2 : act (τ * τ') (bv xw₂) ≠ bv xw₂ := by
      intro h0
      have h3 := hP0 _ hσ xw₂ h0
      rw [h2] at h3
      apply hw₂'
      have := congrArg bv h3
      rw [hbvY] at this
      rw [← hxw₂]
      have h4 : act τ' (bv xw₂) - bv xw₂ = 0 := by simpa [hbv] using this
      exact sub_eq_zero.mp h4
    calc Y τ x = Y τ xw := hP1 τ hτ x xw hx (by rw [hxw]; exact hw)
      _ = Y (τ * τ') xw := h1.symm
      _ = Y (τ * τ') xw₂ := hP1 _ hσ xw xw₂ hmv1 hmv2
      _ = Y τ' xw₂ := h2
      _ = Y τ' x' := hP1 τ' hτ' xw₂ x' (by rw [hxw₂]; exact hw₂') hx'
  have hb : ∀ τ₁ ∈ invs, ∀ τ₂ ∈ invs, fixS τ₁ = fixS τ₂ → ∀ x,
      Y (τ₁ * τ₂) x = Y τ₁ x * Y τ₂ x := by
    intro τ₁ hτ₁ τ₂ hτ₂ hfs x
    have h1 : ρ τ₁ (Y τ₂ x) = Y τ₂ x := by
      refine hfixτ τ₁ hτ₁ _ ?_
      have h2 : bv (Y τ₂ x) ∈ fixS τ₂ := by
        simp only [fixS, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hbvY]
        exact ctr_fixed τ₂ hτ₂ _
      rw [← hfs] at h2
      simpa [fixS] using h2
    rw [hYmul, h1, mul_comm]
  have hcho : ∀ c : Vec, c ≠ 0 → ∃ τ ∈ invs, ∃ w : Vec, act τ w ≠ w ∧ act τ w - w = c := by
    intro c hc
    obtain ⟨τ, hτ⟩ := center_check c hc
    simp only [invC, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨hτi, w, hw⟩ := hτ
    refine ⟨τ, mem_invs.mpr hτi, w, fun h0 => hc ?_, hw⟩
    rw [← hw, h0, sub_self]
  choose! τc hτc wc hwc hwc' using hcho
  choose xs hxs using hbvs
  set s : Vec → A := fun c => if c = 0 then 1 else Y (τc c) (xs (wc c)) with hs
  have hs0 : s 0 = 1 := by simp [hs]
  have hsne : ∀ c, c ≠ 0 → s c = Y (τc c) (xs (wc c)) := by
    intro c hc
    simp [hs, hc]
  have hK : ∀ τ ∈ invs, ∀ x, act τ (bv x) ≠ bv x → Y τ x = s (act τ (bv x) - bv x) := by
    intro τ hτ x hx
    have hc0 : act τ (bv x) - bv x ≠ 0 := fun h0 => hx (sub_eq_zero.mp h0)
    rw [hsne _ hc0]
    have hcim : cim τ = cim (τc (act τ (bv x) - bv x)) :=
      cim_check τ hτ _ (hτc _ hc0) (bv x) (wc _) hx (hwc _ hc0) (hwc' _ hc0).symm
    exact ha τ hτ _ (hτc _ hc0) hcim x (xs (wc _)) hx (by rw [hxs]; exact hwc _ hc0)
  have hsadd : ∀ c₁ c₂ : Vec, s (c₁ + c₂) = s c₁ * s c₂ := by
    intro c₁ c₂
    by_cases h1 : c₁ = 0
    · rw [h1, zero_add, hs0, one_mul]
    by_cases h2 : c₂ = 0
    · rw [h2, add_zero, hs0, mul_one]
    by_cases h12 : c₁ = c₂
    · rw [← h12, vec_add_self, hs0, hsne c₁ h1, hY2 _ (hτc c₁ h1)]
    obtain ⟨τ₁, hτ₁, τ₂, hτ₂, hfs, v, hv, hv1, hv2⟩ := esa_check c₁ c₂ h1 h2 h12
    simp only [invC, Finset.mem_filter, Finset.mem_univ, true_and] at hτ₁ hτ₂
    have hτ₁i : τ₁ ∈ invs := mem_invs.mpr hτ₁.1
    have hτ₂i : τ₂ ∈ invs := mem_invs.mpr hτ₂.1
    obtain ⟨x, hx⟩ : ∃ x, bv x = v := ⟨xs v, hxs v⟩
    have hv' : act τ₂ v ≠ v := fun h0 => h2 (by rw [← hv2, h0, sub_self])
    have hσi : τ₁ * τ₂ ∈ invs := by
      have hne : cim τ₁ ≠ cim τ₂ :=
        cim_ne_check τ₁ hτ₁i τ₂ hτ₂i v hv hv' (by rw [hv1, hv2]; exact h12)
      exact (sa_check τ₁ hτ₁i τ₂ hτ₂i hfs hne).1
    have hc₂fix : act τ₁ c₂ = c₂ := by
      have h3 : c₂ ∈ fixS τ₂ := by
        simp only [fixS, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hv2]
        exact ctr_fixed τ₂ hτ₂i v
      rw [← hfs] at h3
      simpa [fixS] using h3
    have hσv : act (τ₁ * τ₂) v - v = c₁ + c₂ := by
      rw [act_mul]
      have e1 : act τ₂ v = v + c₂ := by rw [← hv2]; abel
      rw [e1, act_add, hc₂fix, ← hv1]
      abel
    have hσmv : act (τ₁ * τ₂) v ≠ v := by
      intro h0
      apply h12
      have := hσv
      rw [h0, sub_self] at this
      have h4 : c₁ + c₂ = 0 := this.symm
      rw [← vec_sub] at h4
      exact sub_eq_zero.mp h4
    rw [← hx] at hv hv' hσmv hσv hv1 hv2
    rw [← hσv, ← hK _ hσi x hσmv, hb τ₁ hτ₁i τ₂ hτ₂i hfs x, ← hv1, ← hv2,
      ← hK τ₁ hτ₁i x hv, ← hK τ₂ hτ₂i x hv']
  let sH : Multiplicative Vec →* A :=
    { toFun := fun m => s (Multiplicative.toAdd m)
      map_one' := hs0
      map_mul' := fun a b => hsadd _ _ }
  have hseq : ∀ γ c, ρ γ (s c) = s (act γ c) := by
    intro γ c
    by_cases hc : c = 0
    · rw [hc, hs0, map_one, act_zero, hs0]
    rw [hsne c hc]
    set τ := τc c with hτdef
    set x := xs (wc c) with hxdef
    have hτi : τ ∈ invs := hτc c hc
    have hxm : act τ (bv x) ≠ bv x := by rw [hxdef, hxs]; exact hwc c hc
    have hxc : act τ (bv x) - bv x = c := by rw [hxdef, hxs]; exact hwc' c hc
    have hσi : γ * τ * γ⁻¹ ∈ invs := by
      rw [mem_invs] at hτi ⊢
      refine ⟨?_, fun h0 => hτi.2 ?_⟩
      · have e1 : γ * τ * γ⁻¹ * (γ * τ * γ⁻¹) = γ * (τ * τ) * γ⁻¹ := by group
        rw [e1, hτi.1, mul_one, mul_inv_cancel]
      · calc τ = γ⁻¹ * (γ * τ * γ⁻¹) * γ := by group
          _ = 1 := by rw [h0]; group
    have hρY : ρ γ (Y τ x) = Y (γ * τ * γ⁻¹) (ρ γ x) := by
      have e1 : ρ (γ * τ * γ⁻¹) (ρ γ x) = ρ γ (ρ τ x) := by
        have e2 : ρ γ⁻¹ (ρ γ x) = x := by
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
        rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, e2]
      simp only [hY]
      rw [e1, map_mul, map_inv]
    have hmv : act (γ * τ * γ⁻¹) (bv (ρ γ x)) ≠ bv (ρ γ x) := by
      rw [hbvρ, act_mul, act_mul, act_inv_act]
      intro h0
      apply hxm
      have := congrArg (act γ⁻¹) h0
      rwa [act_inv_act, act_inv_act] at this
    rw [hρY, hK _ hσi _ hmv, hbvρ, act_mul, act_mul, act_inv_act, ← act_sub, hxc]
  have hrange : ∀ γ x, Y γ x ∈ sH.range := by
    intro γ
    have hγ : γ ∈ Subgroup.closure ({x12, x23, x31} : Set Γ) := by
      rw [closure_gens]
      exact Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem τ hτ =>
      intro x
      have hτi : τ ∈ invs := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
        rcases hτ with rfl | rfl | rfl
        · exact mem_invs.mpr x12_invol
        · exact mem_invs.mpr x23_invol
        · exact mem_invs.mpr x31_invol
      by_cases hx : act τ (bv x) = bv x
      · rw [hP0 τ hτi x hx]
        exact Subgroup.one_mem _
      · rw [hK τ hτi x hx]
        exact ⟨Multiplicative.ofAdd _, rfl⟩
    | one =>
      intro x
      simp only [hY, map_one, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    | mul γ δ _ _ ihγ ihδ =>
      intro x
      rw [hYmul]
      refine Subgroup.mul_mem _ ?_ (ihγ x)
      obtain ⟨m, hm⟩ := ihδ x
      rw [← hm]
      exact ⟨Multiplicative.ofAdd (act γ (Multiplicative.toAdd m)), (hseq γ _).symm⟩
    | inv γ _ ihγ =>
      intro x
      have e1 : Y γ⁻¹ x = (Y γ (ρ γ⁻¹ x))⁻¹ := by
        simp only [hY]
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
        group
      rw [e1]
      exact Subgroup.inv_mem _ (ihγ _)
  have htop : sH.range = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨γ, y, rfl⟩
    exact hrange γ y
  have hle : Nat.card A ≤ 8 := by
    have h1 : Nat.card sH.range ≤ Nat.card (Multiplicative Vec) :=
      Nat.card_le_card_of_surjective _ sH.rangeRestrict_surjective
    rw [htop, Subgroup.card_top] at h1
    have h8 : Nat.card (Multiplicative Vec) = 8 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    omega
  have hge : 8 ≤ Nat.card A := by
    have h1 : Nat.card (Multiplicative Vec) ≤ Nat.card A := Nat.card_le_card_of_surjective _ hβs
    have h8 : Nat.card (Multiplicative Vec) = 8 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    omega
  omega

end CFSG.Quasithin.L3Split

module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PA
public import CFSG.Quasithin.Vol2.Ch3E213MG41PB
public import CFSG.Quasithin.Vol2.Ch3E213MG41PC

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)} {F₁ : Subfield k}
  {e e' : Fin 4 → k}

theorem CaseB.exists_ne (hB : CaseB G₀ F₁ e e') : ∃ μ : F₁, μ ≠ 0 ∧ μ ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun x : F₁ => decide (x = 0)) := by
    intro x y hxy
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · rw [hx, hy]
    · simp [hx, hy] at hxy
    · simp [hx, hy] at hxy
    · rw [hcon x hx, hcon y hy]
  have h := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card Bool = 2 := by simp
  have := hB.four
  omega

theorem CaseB.exists_act_frame (hB : CaseB G₀ F₁ e e') {z : Fin 4 → k} (hz : z ∈ Refl.normC G₀)
    (hz2 : z 2 = 0) (hp0 : proj z ≠ 0) {a b : k} (ha : a ∈ F₁) (hb : b ∈ F₁)
    (hab : a ≠ 0 ∨ b ≠ 0) : ∃ g ∈ G₀, natAct g (eOne k) = eOne k ∧
      ∃ l : k, natAct g z = a • e + b • e' + l • eOne k := by
  obtain ⟨g, hg, hgρ, hgp⟩ := hB.trans z hz hz2 hp0 a ha b hb hab
  refine ⟨g, hg, hgρ, natAct g z 1, ?_⟩
  rw [← hgp]
  exact eq_proj_add (by rw [act_two (mem_stabE.mpr hgρ), hz2])

theorem CaseB.eq_of_proj_eq (hone : Refl.OnePerCentre G₀) (hB : CaseB G₀ F₁ e e')
    {z w : Fin 4 → k} (hz : z ∈ Refl.normC G₀) (hw : w ∈ Refl.normC G₀) (hz2 : z 2 = 0)
    (hw2 : w 2 = 0) (hp : proj z = proj w) (hp0 : proj z ≠ 0) : z = w := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hwz : w = z + (w 1 - z 1) • eOne k := by
    have e1 := eq_proj_add hz2
    have e2 := eq_proj_add hw2
    rw [hp] at e1
    funext i
    have f1 := congrFun e1 i
    have f2 := congrFun e2 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at f1 f2 ⊢
    linear_combination f2 - f1
  by_contra hne
  have hc : w 1 - z 1 ≠ 0 := by
    intro h0
    apply hne
    rw [hwz, h0, zero_smul, add_zero]
  have hzρ : spBil z (eOne k) = 0 := by rw [bil_eOne]; exact hz2
  have hw' : trv (z + (w 1 - z 1) • eOne k) 1 ∈ G₀ := by rw [← hwz]; exact hw.2
  have key : ∀ ν : k, ν ∈ F₁ → ν ≠ 0 → (w 1 - z 1) ^ 2 * (ν + 1) ∈ Lam G₀ (eOne k) := by
    intro ν hν hν0
    obtain ⟨g₁, hg₁, hρ₁, l₁, h₁⟩ :=
      hB.exists_act_frame hz hz2 hp0 F₁.one_mem F₁.zero_mem (Or.inl one_ne_zero)
    obtain ⟨g₂, hg₂, hρ₂, l₂, h₂⟩ :=
      hB.exists_act_frame hz hz2 hp0 F₁.zero_mem hν (Or.inr hν0)
    obtain ⟨g₃, hg₃, hρ₃, l₃, h₃⟩ := hB.exists_act_frame hz hz2 hp0 F₁.one_mem
      (F₁.add_mem hν F₁.one_mem) (Or.inl one_ne_zero)
    obtain ⟨g₄, hg₄, hρ₄, l₄, h₄⟩ :=
      hB.exists_act_frame hz hz2 hp0 F₁.zero_mem F₁.one_mem (Or.inr one_ne_zero)
    have hsum : natAct g₁ z + natAct g₂ z =
        natAct g₃ z + natAct g₄ z + (l₁ + l₂ + l₃ + l₄) • eOne k := by
      rw [h₁, h₂, h₃, h₄]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-e' i - (l₃ + l₄) * eOne k i) * h2
    have hL := mem_Lam_of_fibre hzρ hz.2 hw' hg₁ hg₂ hg₃ hg₄ hρ₁ hρ₂ hρ₃ hρ₄ hsum
    rw [h₁, h₂, h₃, h₄, hB.bil_frame, hB.bil_frame] at hL
    simpa using hL
  obtain ⟨μ, hμ0, hμ1⟩ := hB.exists_ne
  have hμk0 : (μ : k) ≠ 0 := fun h => hμ0 (Subtype.ext h)
  have hμk1 : (μ : k) ≠ 1 := fun h => hμ1 (Subtype.ext h)
  have hμ10 : (μ : k) + 1 ≠ 0 := fun h => hμk1 (by linear_combination h - h2)
  have hμ11 : (μ : k) + 1 + 1 = μ := by linear_combination h2
  have hc2 : (w 1 - z 1) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hρ0 : eOne k ≠ 0 := fun h => by simpa [eOne] using congrFun h 1
  have h₁ := key μ μ.2 hμk0
  have h₂ := key ((μ : k) + 1) (F₁.add_mem μ.2 F₁.one_mem) hμ10
  rw [hμ11] at h₂
  have heq := eq_of_mem_Lam hone hρ0 h₁ h₂ (mul_ne_zero hc2 hμ10) (mul_ne_zero hc2 hμk0)
  exact hc2 (by linear_combination heq)

theorem CaseB.eq_of_mem (hone : Refl.OnePerCentre G₀) (hB : CaseB G₀ F₁ e e') {a b l l' : k}
    (hab : a ≠ 0 ∨ b ≠ 0) (h : a • e + b • e' + l • eOne k ∈ Refl.normC G₀)
    (h' : a • e + b • e' + l' • eOne k ∈ Refl.normC G₀) : l = l' := by
  obtain ⟨h1, h2, hp⟩ := hB.frame_apply a b l
  obtain ⟨h1', h2', hp'⟩ := hB.frame_apply a b l'
  have he := hB.eq_of_proj_eq hone h h' h2 h2' (by rw [hp, hp'])
    (by rw [hp]; exact hB.frame_ne_zero hab)
  have := congrFun he 1
  rwa [h1, h1'] at this

omit [CharP k 2] in
theorem coe_ne_zero_or {x : F₁ × F₁} (hx : x ≠ 0) : (x.1 : k) ≠ 0 ∨ (x.2 : k) ≠ 0 := by
  by_contra h
  push Not at h
  exact hx (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2))

theorem CaseB.exists_lift (hone : Refl.OnePerCentre G₀) (hB : CaseB G₀ F₁ e e') :
    ∃ L : F₁ × F₁ → k, IsCocycle2 L ∧ ∀ x : F₁ × F₁, x ≠ 0 →
      (x.1 : k) • e + (x.2 : k) • e' + L x • eOne k ∈ Refl.normC G₀ := by
  have hlift : ∀ x : F₁ × F₁, ∃ l : k, x ≠ 0 →
      (x.1 : k) • e + (x.2 : k) • e' + l • eOne k ∈ Refl.normC G₀ := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, fun h => absurd hx h⟩
    · obtain ⟨z, hz, hz2, hzp⟩ := hB.cover x.1 x.1.2 x.2 x.2.2 (coe_ne_zero_or hx)
      refine ⟨z 1, fun _ => ?_⟩
      rw [← hzp, ← eq_proj_add hz2]
      exact hz
  choose L hL using hlift
  refine ⟨L, fun x y hxy => ?_, hL⟩
  have h2F : (2 : F₁) = 0 := CharTwo.two_eq_zero
  have hx : x ≠ 0 := by
    rintro rfl
    exact hxy (by simp [bil2])
  have hy : y ≠ 0 := by
    rintro rfl
    exact hxy (by simp [bil2])
  set c := bil2 x y with hc
  have hxcy : x + c • y ≠ 0 := by
    intro h0
    have e1 : bil2 (x + c • y) y = c := by
      simp only [hc, bil2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination ((x.1 * y.2 + x.2 * y.1) * y.1 * y.2) * h2F
    rw [h0] at e1
    exact hxy (by simpa [bil2] using e1.symm)
  have hbxy : spBil ((x.1 : k) • e + (x.2 : k) • e' + L x • eOne k)
      ((y.1 : k) • e + (y.2 : k) • e' + L y • eOne k) = (c : k) := by
    rw [hB.bil_frame, hc]
    simp [bil2]
  have hmove := Refl.act_mem_normC (hL x hx) (hL y hy).2
  rw [act_trv, one_mul, hbxy] at hmove
  have e3 : (x.1 : k) • e + (x.2 : k) • e' + L x • eOne k +
      (c : k) • ((y.1 : k) • e + (y.2 : k) • e' + L y • eOne k) =
      (((x + c • y).1 : F₁) : k) • e + (((x + c • y).2 : F₁) : k) • e' +
        (L x + (c : k) * L y) • eOne k := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, Subfield.coe_add, Subfield.coe_mul]
    ring
  rw [e3] at hmove
  exact (hB.eq_of_mem hone (coe_ne_zero_or hxcy) hmove (hL _ hxcy)).symm

end CFSG.Quasithin.Ch3E213M.G41.Big

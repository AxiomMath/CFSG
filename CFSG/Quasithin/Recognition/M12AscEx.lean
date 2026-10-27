module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

variable {G : Type*} [Group G]

private theorem f_zpow_comm {f r : G} (hf : f * f = 1) (hr : f * r * f = r⁻¹) (i : ℤ) :
    f * r ^ i = r ^ (-i) * f := by
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  have h1 : f * r * f⁻¹ = r⁻¹ := by rw [hfi]; exact hr
  have h2 : f * r ^ i * f⁻¹ = (r⁻¹) ^ i := by rw [← conj_zpow, h1]
  calc f * r ^ i = (f * r ^ i * f⁻¹) * f := by rw [hfi, mul_assoc, hf, mul_one]
    _ = (r⁻¹) ^ i * f := by rw [h2]
    _ = r ^ (-i) * f := by rw [inv_zpow']

private theorem dihedral_conj_f {f r : G} (hf : f * f = 1) (hr : f * r * f = r⁻¹) (j : ℤ) :
    r ^ j * f * (r ^ j)⁻¹ = r ^ (2 * j) * f := by
  have h := f_zpow_comm hf hr (-j)
  rw [neg_neg] at h
  calc r ^ j * f * (r ^ j)⁻¹ = r ^ j * (f * r ^ (-j)) := by rw [zpow_neg]; group
    _ = r ^ j * (r ^ j * f) := by rw [h]
    _ = r ^ (2 * j) * f := by rw [← mul_assoc, ← zpow_add, two_mul]

private theorem dihedral_conj_a {a f r : G} (hf : f * f = 1) (hr : f * r * f = r⁻¹)
    (har : a = r * f) (j : ℤ) : r ^ j * a * (r ^ j)⁻¹ = r ^ (2 * j + 1) * f := by
  have h := f_zpow_comm hf hr (-j)
  rw [neg_neg] at h
  calc r ^ j * a * (r ^ j)⁻¹ = r ^ j * (r * f) * (r ^ j)⁻¹ := by rw [← har]
    _ = r ^ (j + 1) * (f * r ^ (-j)) := by rw [zpow_neg, zpow_add_one]; group
    _ = r ^ (j + 1) * (r ^ j * f) := by rw [h]
    _ = r ^ (2 * j + 1) * f := by rw [← mul_assoc, ← zpow_add]; congr 2; ring

theorem transitive_of_TI_strongly_closed [Finite G] (E : Subgroup G)
    (hinv : ∀ e ∈ E, e ≠ 1 → e * e = 1)
    (hTI : ∀ x : G, ∀ w ∈ E, w ≠ 1 → x * w * x⁻¹ ∈ E → x ∈ Subgroup.normalizer (E : Set G))
    (hsc : ∀ e ∈ E, e ≠ 1 → ∀ x : G, x * e * x⁻¹ ∈ Subgroup.normalizer (E : Set G) → x * e * x⁻¹ ∈ E)
    (hne : Subgroup.normalizer (E : Set G) ≠ ⊤) :
    ∀ e ∈ E, e ≠ 1 → ∀ f ∈ E, f ≠ 1 → ∃ m ∈ Subgroup.normalizer (E : Set G), m * e * m⁻¹ = f := by
  intro e he he1 f hf hf1
  have hCG : ∀ w ∈ E, w ≠ 1 → ∀ x : G, x * w * x⁻¹ = w → x ∈ Subgroup.normalizer (E : Set G) :=
    fun w hw hw1 x hx => hTI x w hw hw1 (by rw [hx]; exact hw)
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ Subgroup.normalizer (E : Set G) := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  have he2 := hinv e he he1
  have hf2 := hinv f hf hf1
  set a := g * e * g⁻¹ with ha_def
  have ha2 : a * a = 1 := by
    calc a * a = g * (e * e) * g⁻¹ := by rw [ha_def]; group
      _ = 1 := by rw [he2]; group
  have ha1 : a ≠ 1 := by
    intro h
    apply he1
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [ha_def, mul_assoc] using this
  have haE : a ∉ E := by
    intro haE
    apply hg
    have : g⁻¹ ∈ Subgroup.normalizer (E : Set G) := hTI g⁻¹ a haE ha1 (by simpa [ha_def, mul_assoc] using he)
    exact (Subgroup.inv_mem_iff _).1 this
  have haM : a ∉ Subgroup.normalizer (E : Set G) := fun haM => haE (hsc e he he1 g haM)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  set r := a * f with hr_def
  have hra : a * r * a = r⁻¹ := by
    rw [hr_def, mul_inv_rev, hai, hfi]
    calc a * (a * f) * a = (a * a) * f * a := by group
      _ = f * a := by rw [ha2, one_mul]
  have hrf : f * r * f = r⁻¹ := by
    rw [hr_def, mul_inv_rev, hai, hfi]
    calc f * (a * f) * f = f * a * (f * f) := by group
      _ = f * a := by rw [hf2, mul_one]
  have har : a = r * f := by
    rw [hr_def]
    calc a = a * (f * f) := by rw [hf2, mul_one]
      _ = a * f * f := by group
  rcases Nat.even_or_odd (orderOf r) with ⟨m, hm⟩ | ⟨k, hk⟩
  ·
    exfalso
    set z' := r ^ m with hz'_def
    have hrn : r ^ (m + m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one r
    have hz'2 : z' * z' = 1 := by rw [hz'_def, ← pow_add]; exact hrn
    have hpos : 0 < orderOf r := orderOf_pos r
    have hz'1 : z' ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have hz'i : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
    have hza : a * z' = z' * a := by
      have h := f_zpow_comm ha2 hra (m : ℤ)
      rw [zpow_natCast] at h
      rw [zpow_neg, zpow_natCast, ← hz'_def, hz'i] at h
      exact h
    have hzf : f * z' = z' * f := by
      have h := f_zpow_comm hf2 hrf (m : ℤ)
      rw [zpow_natCast] at h
      rw [zpow_neg, zpow_natCast, ← hz'_def, hz'i] at h
      exact h
    have hxM : f * z' ∈ Subgroup.normalizer (E : Set G) := by
      apply hCG f hf hf1
      calc f * z' * f * (f * z')⁻¹ = f * (z' * f * z'⁻¹) * f⁻¹ := by group
        _ = f * f * f⁻¹ := by
          rw [show z' * f * z'⁻¹ = f from by rw [← hzf]; group]
        _ = f := by group
    have hxE : f * z' ∈ E := by
      rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hx : f * z' = r ^ (-(j : ℤ)) * f * (r ^ (-(j : ℤ)))⁻¹ := by
          rw [dihedral_conj_f hf2 hrf (-(j : ℤ))]
          have h := f_zpow_comm hf2 hrf (m : ℤ)
          rw [zpow_natCast] at h
          rw [hz'_def, h]
          congr 2
          rw [hj]; push_cast; ring
        have := hsc f hf hf1 (r ^ (-(j : ℤ))) (by rw [← hx]; exact hxM)
        rwa [← hx] at this
      · have hx : f * z' = r ^ (-(j : ℤ) - 1) * a * (r ^ (-(j : ℤ) - 1))⁻¹ := by
          rw [dihedral_conj_a hf2 hrf har (-(j : ℤ) - 1)]
          have h := f_zpow_comm hf2 hrf (m : ℤ)
          rw [zpow_natCast] at h
          rw [hz'_def, h]
          congr 2
          rw [hj]; push_cast; ring
        have hc : (r ^ (-(j : ℤ) - 1) * g) * e * (r ^ (-(j : ℤ) - 1) * g)⁻¹ = f * z' := by
          rw [hx, ha_def]; group
        have := hsc e he he1 (r ^ (-(j : ℤ) - 1) * g) (by rw [hc]; exact hxM)
        rwa [hc] at this
    have hz'E : z' ∈ E := by
      have := E.mul_mem hf hxE
      rwa [← mul_assoc, hf2, one_mul] at this
    exact haM (hCG z' hz'E hz'1 a (by rw [hza]; group))
  ·
    have hrk : r ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one r
    have hfa : r ^ (k : ℤ) * a * (r ^ (k : ℤ))⁻¹ = f := by
      rw [dihedral_conj_a hf2 hrf har (k : ℤ)]
      have : r ^ (2 * (k : ℤ) + 1) = 1 := by
        have h : (2 * (k : ℤ) + 1) = ((2 * k + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h, zpow_natCast]; exact hrk
      rw [this, one_mul]
    have hmul : ((r ^ (k : ℤ)) * g)⁻¹ * f * (((r ^ (k : ℤ)) * g)⁻¹)⁻¹ = e := by
      rw [← hfa, ha_def]; group
    refine ⟨(r ^ (k : ℤ)) * g, ?_, ?_⟩
    · have := hTI ((r ^ (k : ℤ)) * g)⁻¹ f hf hf1 (by rw [hmul]; exact he)
      exact (Subgroup.inv_mem_iff _).1 this
    · rw [← hfa, ha_def]; group

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 Subgroup

private theorem s16c1c_mem_commV_zpowers {W : Type} [CommGroup W] {a : MulAut W}
    (ha : a * a = 1) (u : W) :
    u ∈ CFSG.Quasithin.commV (Subgroup.zpowers a) ↔ ∃ v : W, a v * v⁻¹ = u := by
  let φ : W →* W :=
    { toFun := fun v => a v * v⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  let S : Subgroup W :=
    { carrier := Set.range φ
      one_mem' := ⟨1, map_one φ⟩
      mul_mem' := by
        rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
        exact ⟨v * w, map_mul φ v w⟩
      inv_mem' := by
        rintro _ ⟨v, rfl⟩
        exact ⟨v⁻¹, map_inv φ v⟩ }
  have hgen : {w : W | ∃ x ∈ Subgroup.zpowers a, ∃ v : W, x v * v⁻¹ = w} =
      (S : Set W) := by
    ext w
    constructor
    · rintro ⟨x, hx, v, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      have ha2 : a ^ (2 : ℤ) = 1 := by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
        exact ha
      have hk2 : a ^ k = 1 ∨ a ^ k = a := by
        have h := zpow_eq_zpow_emod k (x := a) (n := (2 : ℤ)) ha2
        rcases Int.emod_two_eq_zero_or_one k with h0 | h1
        · left; rw [h, h0]; simp
        · right; rw [h, h1]; simp
      rw [← hk]
      rcases hk2 with h1 | h1
      · rw [h1]
        refine ⟨1, ?_⟩
        simp [φ]
      · rw [h1]
        refine ⟨v, ?_⟩
        simp [φ]
    · rintro ⟨v, rfl⟩
      exact ⟨a, Subgroup.mem_zpowers a, v, by simp [φ]⟩
  rw [CFSG.Quasithin.commV, hgen, Subgroup.closure_eq]
  rfl

private theorem s16c1c_mem_fixV_zpowers {W : Type} [CommGroup W] (a : MulAut W) (w : W) :
    w ∈ CFSG.Quasithin.fixV (Subgroup.zpowers a) ↔ a w = w := by
  rw [CFSG.Quasithin.mem_fixV]
  constructor
  · intro h
    exact h a (Subgroup.mem_zpowers a)
  · intro h x hx
    have hs : a • w = w := by simpa [MulAut.smul_def] using h
    have hxw : x • w = w := smul_eq_self_of_mem_zpowers hx hs
    simpa [MulAut.smul_def] using hxw

theorem s16c1c_card_commV_kappa {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀)
    {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ^ 2 = 1) {w₀ : V₀} (hw₀ : w₀ ≠ 0)
    (h1 : ∀ u, g u - u = 0 ∨ g u - u = w₀) (h2 : ∃ u, g u - u = w₀) :
    Nat.card (CFSG.Quasithin.commV (Subgroup.zpowers (s16c1G_kappa β g))) = 2 := by
  set a := s16c1G_kappa β g with ha_def
  have ha : a * a = 1 := by
    rw [ha_def, ← map_mul, ← pow_two, hg, map_one]
  let w₁ : W := β.symm (Multiplicative.ofAdd w₀)
  have hw₁β : β w₁ = Multiplicative.ofAdd w₀ := by simp [w₁]
  have hw₁_ne : w₁ ≠ 1 := by
    intro hcon
    apply hw₀
    have h' := congrArg (fun x => Multiplicative.toAdd (β x)) hcon
    simpa [w₁] using h'
  have hw₁_pow : w₁ ^ 2 = 1 := by
    apply β.injective
    rw [map_pow, map_one, pow_two, hw₁β, ← ofAdd_add,
      CFSG.RankThree.OrthogonalInvolutions.add_self_vec (ZMod 2)]
    rfl
  have hval : ∀ v : W, a v * v⁻¹ = 1 ∨ a v * v⁻¹ = w₁ := by
    intro v
    have hβ : β (a v * v⁻¹) = Multiplicative.ofAdd
        (g (Multiplicative.toAdd (β v)) - Multiplicative.toAdd (β v)) := by
      rw [← ofAdd_toAdd (β (a v * v⁻¹))]
      congr 1
      rw [ha_def, map_mul, map_inv, toAdd_mul, toAdd_inv, s16c1G_kappa_apply]
      simp [sub_eq_add_neg]
    rcases h1 (Multiplicative.toAdd (β v)) with h0 | h0
    · left
      apply β.injective
      rw [hβ, h0, map_one]
      rfl
    · right
      apply β.injective
      rw [hβ, h0]
      simp [w₁]
  obtain ⟨u₀, hu₀⟩ := h2
  have hw₁_mem : w₁ ∈ CFSG.Quasithin.commV (Subgroup.zpowers a) := by
    rw [s16c1c_mem_commV_zpowers ha]
    refine ⟨β.symm (Multiplicative.ofAdd u₀), ?_⟩
    apply β.injective
    have hβ : β (a (β.symm (Multiplicative.ofAdd u₀)) *
        (β.symm (Multiplicative.ofAdd u₀))⁻¹) =
        Multiplicative.ofAdd (g u₀ - u₀) := by
      rw [← ofAdd_toAdd (β (a (β.symm (Multiplicative.ofAdd u₀)) *
        (β.symm (Multiplicative.ofAdd u₀))⁻¹))]
      congr 1
      rw [ha_def, map_mul, map_inv, toAdd_mul, toAdd_inv, s16c1G_kappa_apply]
      simp [sub_eq_add_neg]
    rw [hβ, hu₀]
    simp [w₁]
  have hcomm : CFSG.Quasithin.commV (Subgroup.zpowers a) = Subgroup.zpowers w₁ := by
    apply le_antisymm
    · intro u hu
      rw [s16c1c_mem_commV_zpowers ha u] at hu
      obtain ⟨v, hv⟩ := hu
      rcases hval v with h | h
      · rw [← hv, h]; exact Subgroup.one_mem _
      · rw [← hv, h]; exact Subgroup.mem_zpowers w₁
    · intro u hu
      exact Subgroup.zpowers_le.mpr hw₁_mem hu
  rw [hcomm, Nat.card_zpowers, orderOf_eq_prime hw₁_pow hw₁_ne]

theorem s16c1c_fixV_sup_kappa {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀)
    {g₁ g₂ : V₀ ≃ₗ[ZMod 2] V₀} (h : ∀ u, ∃ u₁, g₁ u₁ = u₁ ∧ g₂ (u - u₁) = u - u₁) :
    CFSG.Quasithin.fixV (Subgroup.zpowers (s16c1G_kappa β g₁)) ⊔
      CFSG.Quasithin.fixV (Subgroup.zpowers (s16c1G_kappa β g₂)) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  rw [Subgroup.mem_sup]
  obtain ⟨u₁, hu₁, hu₂⟩ := h (Multiplicative.toAdd (β w))
  refine ⟨β.symm (Multiplicative.ofAdd u₁), ?_,
    β.symm (Multiplicative.ofAdd (Multiplicative.toAdd (β w) - u₁)), ?_, ?_⟩
  · rw [s16c1c_mem_fixV_zpowers]
    apply β.injective
    rw [s16c1G_kappa_apply]
    simp [hu₁]
  · rw [s16c1c_mem_fixV_zpowers]
    apply β.injective
    rw [s16c1G_kappa_apply]
    simp [hu₂]
  · apply β.injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      ← ofAdd_add]
    have hsum : u₁ + (Multiplicative.toAdd (β w) - u₁) = Multiplicative.toAdd (β w) := by
      abel
    rw [hsum, ofAdd_toAdd]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

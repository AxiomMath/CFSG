module

public import CFSG.Quasithin.Background.F918Z6Symm
public import CFSG.Quasithin.Background.F918Z4d
public import CFSG.Quasithin.Background.F918Z3Cg2Fix

public section

namespace CFSG.Quasithin

namespace Z7b

variable {V : Type} [CommGroup V]

theorem forall_map_conj_eq_iff {A H : Subgroup (MulAut V)} :
    (∀ a ∈ A, H.map (MulAut.conj a).toMonoidHom = H) ↔ ∀ a ∈ A, ∀ y ∈ H, a * y * a⁻¹ ∈ H := by
  constructor
  · intro h a ha y hy
    have := Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hy
    rw [h a ha] at this
    exact this
  · intro h a ha
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact h a ha y hy
    · intro y hy
      refine ⟨a⁻¹ * y * a, ?_, ?_⟩
      · simpa using h a⁻¹ (A.inv_mem ha) y hy
      · show a * (a⁻¹ * y * a) * a⁻¹ = y
        group

variable [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}

theorem normalizes_X_of_normalizes_D (hZ : Z37 D X G T' s) {a : MulAut V} (haG : a ∈ G)
    (ha' : ∀ y ∈ D, a⁻¹ * y * a ∈ D) {x : MulAut V} (hx : x ∈ X) : a * x * a⁻¹ ∈ X := by
  have hg : a * x * a⁻¹ ∈ D ⊔ X := hZ.DX_norm a haG x (Subgroup.mem_sup_right hx)
  obtain ⟨y, hy, x', hx', hyx⟩ := Z3Cg2.exists_mul_of_mem_sup hZ.comm hg
  have hcent : ∀ z ∈ D, (a * x * a⁻¹) * z = z * (a * x * a⁻¹) := by
    intro z hz
    have h1 := hZ.comm _ (ha' z hz) x hx
    calc (a * x * a⁻¹) * z = a * (x * (a⁻¹ * z * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * z * a) * x) * a⁻¹ := by rw [h1]
      _ = z * (a * x * a⁻¹) := by group
  have hyc : ∀ z ∈ D, y * z = z * y := by
    intro z hz
    have h2 := hcent z hz
    rw [hyx] at h2
    have h3 := hZ.comm z hz x' hx'
    have h4 : y * z * x' = z * y * x' :=
      calc y * z * x' = y * (z * x') := by group
        _ = y * (x' * z) := by rw [h3]
        _ = y * x' * z := by group
        _ = z * (y * x') := h2
        _ = z * y * x' := by group
    exact mul_right_cancel h4
  have hy1 : y = 1 := by
    have : IsSimpleGroup ↥D := hZ.simple
    obtain ⟨p, hp, q, hq, hpq⟩ := hZ.nonab
    have hpq' : (⟨p, hp⟩ : ↥D) * ⟨q, hq⟩ ≠ ⟨q, hq⟩ * ⟨p, hp⟩ := fun h =>
      hpq (congrArg Subtype.val h)
    have hmem : (⟨y, hy⟩ : ↥D) ∈ Subgroup.center ↥D := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hyc g g.2).symm
    rw [Z3Cg2.center_eq_bot_of_simple hpq', Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  rw [hyx, hy1, one_mul]
  exact hx'

theorem map_conj_X_of_map_conj_D (hZ : Z37 D X G T' s) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hAD : ∀ a ∈ A, D.map (MulAut.conj a).toMonoidHom = D) :
    ∀ a ∈ A, X.map (MulAut.conj a).toMonoidHom = X := by
  rw [forall_map_conj_eq_iff] at hAD ⊢
  intro a ha x hx
  exact normalizes_X_of_normalizes_D hZ (hAG ha)
    (fun y hy => by simpa using hAD a⁻¹ (A.inv_mem ha) y hy) hx

end Z7b

theorem Z37Concl.symm {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)}
    {s : MulAut V} (hZ : Z37 D X G T' s) (h : Z37Concl X D) : Z37Concl D X := by
  have e : ↥X ≃* ↥D := (conjEquivOfEq hZ.swapDX).symm
  rcases h with ⟨n, hn, hΩ⟩ | ⟨h3, hT⟩
  · rw [sup_comm] at hΩ
    exact Or.inl ⟨n, isPSL_congr e hn, hΩ⟩
  · rw [sup_comm] at hT
    exact Or.inr ⟨isPSL_congr e h3, hT⟩

theorem caseII_concl_of_core {V : Type} [CommGroup V] [Finite V]
    {D X G T' : Subgroup (MulAut V)} {s : MulAut V}
    (core : ∀ {D₁ X₁ : Subgroup (MulAut V)}, Z37 D₁ X₁ G T' s → ∀ {A : Subgroup (MulAut V)},
      A ∈ QhatStar G → A ≤ T' → (∀ a ∈ A, D₁.map (MulAut.conj a).toMonoidHom = D₁) →
        (∃ a ∈ A, ∃ y ∈ D₁, a * y ≠ y * a) → Z37Concl D₁ X₁)
    (hZ : Z37 D X G T' s) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G) (hAT : A ≤ T')
    (hAD : ∀ a ∈ A, D.map (MulAut.conj a).toMonoidHom = D) : Z37Concl D X := by
  obtain ⟨r, -, -, hAr, -⟩ := QhatStar_spec hA
  have hA2 : IsA2 G A := hAr.1.1
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA2.ne_bot
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha2 : a * a = 1 := by
    have := hA2.isElemAbelian2.2 a haA
    rwa [pow_two] at this
  by_cases hD : ∀ y ∈ D, a * y = y * a
  · by_cases hXc : ∀ x ∈ X, a * x = x * a
    · exact (ha1' (Z4d.eq_one_of_commutes hZ ha2 hD hXc)).elim
    · push Not at hXc
      obtain ⟨x, hx, hax⟩ := hXc
      have hAX := Z7b.map_conj_X_of_map_conj_D hZ hA2.le hAD
      exact Z37Concl.symm hZ (core hZ.symm hA hAT hAX ⟨a, haA, x, hx, hax⟩)
  · push Not at hD
    obtain ⟨y, hy, hay⟩ := hD
    exact core hZ hA hAT hAD ⟨a, haA, y, hy, hay⟩

end CFSG.Quasithin

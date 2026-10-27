module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModSylB

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

theorem iff_of_forall_mem' {H : Subgroup W} {g : MulAut W} (h : ∀ w ∈ H, g w ∈ H) :
    ∀ w : W, w ∈ H ↔ g w ∈ H := by
  intro w
  refine ⟨h w, fun hw => ?_⟩
  have hinj : Function.Injective (fun x : H => (⟨g x, h x x.2⟩ : H)) := fun a b hab =>
    Subtype.ext (g.injective (congrArg Subtype.val hab))
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hinj ⟨g w, hw⟩
  have hx' : g x = g w := congrArg Subtype.val hx
  rw [← g.injective hx']
  exact x.2

omit [Finite W] in
theorem vEMod_inf_W₁ (x₁ x₂ : MulAut W) :
    S.vEMod x₁ x₂ ⊓ S.W₁ = S.W₁ ⊓ fixV (Subgroup.zpowers x₁) := by
  apply le_antisymm
  · rintro w ⟨hwV, hw1⟩
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Subgroup.mem_sup.mp hwV
    have hl₂1 : l₂ ∈ S.W₁ := by
      have : l₂ = l₁⁻¹ * (l₁ * l₂) := by group
      rw [this]
      exact S.W₁.mul_mem (S.W₁.inv_mem hl₁.1) hw1
    have h3 : l₂ ∈ S.W₁ ⊓ S.W₂ := ⟨hl₂1, hl₂.1⟩
    rw [S.winf, Subgroup.mem_bot] at h3
    rw [h3, mul_one]
    exact hl₁
  · intro w hw
    exact ⟨Subgroup.mem_sup_left hw, hw.1⟩

omit [Finite W] in
theorem fixV_closure_pair {x₁ x₂ : MulAut W} (hx₁ : x₁ ∈ S.A₁) (hx₂ : x₂ ∈ S.A₂) :
    fixV (Subgroup.closure {x₁, x₂}) = S.vEMod x₁ x₂ := by
  apply le_antisymm
  · intro w hw
    have h1 : x₁ w = w := mem_fixV.mp hw x₁ (Subgroup.subset_closure (by simp))
    have h2 : x₂ w = w := mem_fixV.mp hw x₂ (Subgroup.subset_closure (by simp))
    have hw' : w ∈ S.W₁ ⊔ S.W₂ := by rw [S.wsup]; exact Subgroup.mem_top w
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hw'
    have e1 : x₁ u₁ = u₁ := by
      have h : x₁ u₁ * u₂ = u₁ * u₂ := by
        have := h1
        rwa [map_mul, S.fix_W₂_of_mem_A₁ hx₁ hu₂] at this
      exact mul_right_cancel h
    have e2 : x₂ u₂ = u₂ := by
      have h : u₁ * x₂ u₂ = u₁ * u₂ := by
        have := h2
        rwa [map_mul, S.fix_W₁_of_mem_A₂ hx₂ hu₁] at this
      exact mul_left_cancel h
    exact Subgroup.mul_mem_sup ⟨hu₁, mem_fixV_zpowers_iff.mpr e1⟩
      ⟨hu₂, mem_fixV_zpowers_iff.mpr e2⟩
  · intro w hw
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Subgroup.mem_sup.mp hw
    have e1 : x₁ l₁ = l₁ := mem_fixV_zpowers_iff.mp hl₁.2
    have e2 : x₂ l₂ = l₂ := mem_fixV_zpowers_iff.mp hl₂.2
    have hfix : ∀ y ∈ Subgroup.closure {x₁, x₂}, y (l₁ * l₂) = l₁ * l₂ := by
      intro y hy
      refine Subgroup.closure_induction (p := fun y _ => y (l₁ * l₂) = l₁ * l₂) ?_ ?_ ?_ ?_ hy
      · rintro y (rfl | rfl)
        · rw [map_mul, e1, S.fix_W₂_of_mem_A₁ hx₁ hl₂.1]
        · rw [map_mul, e2, S.fix_W₁_of_mem_A₂ hx₂ hl₁.1]
      · rfl
      · intro a b _ _ ha hb
        show a (b (l₁ * l₂)) = l₁ * l₂
        rw [hb, ha]
      · intro a _ ha
        calc a⁻¹ (l₁ * l₂) = a⁻¹ (a (l₁ * l₂)) := by rw [ha]
          _ = l₁ * l₂ := MulAut.inv_apply_self W a _
    exact mem_fixV.mpr hfix

omit [Finite W] in
theorem maps_vEMod_of_comm {x₁ x₂ ε : MulAut W} (hε₁ : ∀ w ∈ S.W₁, ε w = w)
    (hεW₂ : ∀ w ∈ S.W₂, ε w ∈ S.W₂) (hc : ε * x₂ = x₂ * ε) :
    ∀ w ∈ S.vEMod x₁ x₂, ε w ∈ S.vEMod x₁ x₂ := by
  intro w hw
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Subgroup.mem_sup.mp hw
  have h2 : ε l₂ ∈ S.W₂ ⊓ fixV (Subgroup.zpowers x₂) := by
    refine ⟨hεW₂ l₂ hl₂.1, mem_fixV_zpowers_iff.mpr ?_⟩
    have e2 : x₂ l₂ = l₂ := mem_fixV_zpowers_iff.mp hl₂.2
    calc x₂ (ε l₂) = (x₂ * ε) l₂ := rfl
      _ = (ε * x₂) l₂ := by rw [hc]
      _ = ε l₂ := by show ε (x₂ l₂) = ε l₂; rw [e2]
  rw [map_mul, hε₁ l₁ hl₁.1]
  exact Subgroup.mul_mem_sup hl₁ h2

omit [Finite W] in
theorem maps_vEMod_of_comm₁ {x₁ x₂ ε : MulAut W} (hε₂ : ∀ w ∈ S.W₂, ε w = w)
    (hεW₁ : ∀ w ∈ S.W₁, ε w ∈ S.W₁) (hc : ε * x₁ = x₁ * ε) :
    ∀ w ∈ S.vEMod x₁ x₂, ε w ∈ S.vEMod x₁ x₂ := by
  intro w hw
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Subgroup.mem_sup.mp hw
  have h1 : ε l₁ ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁) := by
    refine ⟨hεW₁ l₁ hl₁.1, mem_fixV_zpowers_iff.mpr ?_⟩
    have e1 : x₁ l₁ = l₁ := mem_fixV_zpowers_iff.mp hl₁.2
    calc x₁ (ε l₁) = (x₁ * ε) l₁ := rfl
      _ = (ε * x₁) l₁ := by rw [hc]
      _ = ε l₁ := by show ε (x₁ l₁) = ε l₁; rw [e1]
  rw [map_mul, hε₂ l₂ hl₂.1]
  exact Subgroup.mul_mem_sup h1 hl₂

end CFSG.Quasithin.SixData151b

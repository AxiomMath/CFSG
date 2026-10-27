module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.Background.B4Models

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.M338

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem gen_mem_commV {H : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ H) (v : V) :
    x v * v⁻¹ ∈ commV H :=
  Subgroup.subset_closure ⟨x, hx, v, rfl⟩

theorem commV_le_of_le {A B : Subgroup (MulAut V)} (h : A ≤ B) : commV A ≤ commV B :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, e⟩ => ⟨x, h hx, v, e⟩

theorem apply_mem_commV {H : Subgroup (MulAut V)} {y : MulAut V}
    (hy : y ∈ Subgroup.normalizer (H : Set (MulAut V))) {v : V} (hv : v ∈ commV H) :
    y v ∈ commV H :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hy hv

theorem apply_mem_fixV {H : Subgroup (MulAut V)} {y : MulAut V}
    (hy : y ∈ Subgroup.normalizer (H : Set (MulAut V))) {v : V} (hv : v ∈ fixV H) :
    y v ∈ fixV H :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hy hv

theorem commV_sup (A B : Subgroup (MulAut V)) : commV (A ⊔ B) = commV A ⊔ commV B := by
  refine le_antisymm ?_ (sup_le (commV_le_of_le le_sup_left) (commV_le_of_le le_sup_right))
  have key : ∀ x ∈ A ⊔ B, ∀ v : V, x v * v⁻¹ ∈ commV A ⊔ commV B := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro v
      rcases hx with hx | hx
      · exact Subgroup.mem_sup_left (gen_mem_commV hx v)
      · exact Subgroup.mem_sup_right (gen_mem_commV hx v)
    | one => intro v; simp
    | mul x y _ _ hx hy =>
      intro v
      have e : (x * y) v * v⁻¹ = (x (y v) * (y v)⁻¹) * (y v * v⁻¹) := by
        simp [MulAut.mul_apply]
      rw [e]
      exact (commV A ⊔ commV B).mul_mem (hx _) (hy _)
    | inv x _ hx =>
      intro v
      have h1 := hx (x⁻¹ v)
      have e : x⁻¹ v * v⁻¹ = (x (x⁻¹ v) * (x⁻¹ v)⁻¹)⁻¹ := by
        simp
      rw [e]
      exact (commV A ⊔ commV B).inv_mem h1
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  exact key x hx v

section Realize

variable {D : FFModel} {H : Subgroup (MulAut V)} {W C : Subgroup V} {π : D.Gam →* ↥H}

theorem mem_of_forall_mul_inv_mem (h : D.RealizesVia H W C π)
    (hF : ∀ m ∈ D.sec, (∀ γ : D.Gam, D.act γ m * m⁻¹ ∈ D.ker) → m ∈ D.ker)
    {w : V} (hw : w ∈ W) (hfix : ∀ g ∈ H, g w * w⁻¹ ∈ C) : w ∈ C := by
  obtain ⟨-, -, -, hWinv, -, hsec, -, β, -, hβk, hβe⟩ := h
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, hw⟩)
  have hker : (m : D.Amb) ∈ D.ker := by
    refine hF m m.2 fun γ => ?_
    have hπw : ((π γ : ↥H) : MulAut V) w ∈ W := hWinv (π γ) w hw
    have h1 := hβe γ ⟨w, hw⟩ m hπw (hsec γ m m.2) hm.symm
    have h2 : β ⟨_, hπw⟩ = β ⟨w, hw⟩ := by
      have h3 : (((⟨_, hπw⟩ : ↥W) * (⟨w, hw⟩ : ↥W)⁻¹ : ↥W) : V) ∈ C := hfix _ (π γ).2
      have h4 := (hβk (⟨_, hπw⟩ * (⟨w, hw⟩ : ↥W)⁻¹)).mpr h3
      rw [map_mul, map_inv, mul_inv_eq_one] at h4
      exact h4
    rw [h2, ← hm, QuotientGroup.eq] at h1
    have h5 := Subgroup.mem_subgroupOf.mp h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
    rwa [mul_comm] at h5
  have h1 : β ⟨w, hw⟩ = 1 := by
    rw [← hm, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hker
  exact (hβk _).mp h1

theorem le_commV_sup (h : D.RealizesVia H W C π)
    (hG : D.sec ≤ Subgroup.closure {x | ∃ γ : D.Gam, ∃ y ∈ D.sec, D.act γ y * y⁻¹ = x} ⊔ D.ker) :
    W ≤ commV H ⊔ C := by
  obtain ⟨-, -, hks, hWinv, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have key : ∀ x ∈ Subgroup.closure {x | ∃ γ : D.Gam, ∃ y ∈ D.sec, D.act γ y * y⁻¹ = x} ⊔ D.ker,
      ∃ hx : x ∈ D.sec, ∃ c : ↥W, (c : V) ∈ commV H ∧ β c = QuotientGroup.mk ⟨x, hx⟩ := by
    intro x hx
    rw [← Subgroup.closure_eq D.ker, ← Subgroup.closure_union] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨γ, y, hy, rfl⟩ | hx
      · obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨y, hy⟩)
        have hπu : ((π γ : ↥H) : MulAut V) u ∈ W := hWinv (π γ) u u.2
        have hy' : D.act γ y ∈ D.sec := hsec γ y hy
        refine ⟨D.sec.mul_mem hy' (D.sec.inv_mem hy), ⟨_, hπu⟩ * u⁻¹,
          gen_mem_commV (π γ).2 _, ?_⟩
        rw [map_mul, map_inv, hβe γ u ⟨y, hy⟩ hπu hy' hu, hu]
        rfl
      · refine ⟨hks hx, 1, (commV H).one_mem, ?_⟩
        rw [map_one, eq_comm, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hx
    | one => exact ⟨D.sec.one_mem, 1, (commV H).one_mem, by rw [map_one]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hx, c, hc, hcx⟩ := hx
      obtain ⟨hy, d, hd, hdy⟩ := hy
      exact ⟨D.sec.mul_mem hx hy, c * d, (commV H).mul_mem hc hd, by rw [map_mul, hcx, hdy]; rfl⟩
    | inv x _ hx =>
      obtain ⟨hx, c, hc, hcx⟩ := hx
      exact ⟨D.sec.inv_mem hx, c⁻¹, (commV H).inv_mem hc, by rw [map_inv, hcx]; rfl⟩
  intro w hw
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, hw⟩)
  obtain ⟨hmx, c, hc, hcm⟩ := key m (hG m.2)
  have h1 : β (⟨w, hw⟩ * c⁻¹) = 1 := by
    rw [map_mul, map_inv, hcm, ← hm]
    exact mul_inv_cancel _
  have h2 := (hβk _).mp h1
  have e : w = (w * (c : V)⁻¹) * c := by group
  rw [e]
  exact (commV H ⊔ C).mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hc)

end Realize

end CFSG.Quasithin.H13.M338

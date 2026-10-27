module

public import CFSG.Quasithin.EmptyFaithful.S153EN8J

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t} {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

section VPart

variable (B : BarModel cx)

include B in
theorem vOf_mem : B.a₁.val ∈ V₁ := by
  have hV := cx.c.hyp.elemAbelian
  have h := (mem_map_inclMod_iff hV (U := commV B.L₁) (v := B.a₁.val)).2
    ⟨B.a₁, B.hF.sylow.a₁_mem, rfl⟩
  rwa [B.hV₁] at h

include B in
theorem vOf_ne_one : B.a₁.val ≠ 1 := fun h => B.hF.sylow.a₁_ne (IntMod.val_injective h)

include B in
theorem barM_mem_S' {x : G} (hxT : x ∈ T) (hxN : x ∈ Subgroup.normalizer (V₁ : Set G)) :
    barM cx (S153E.T_le_M cx hxT) ∈ autI cx.c.hyp.elemAbelian T ⊓ (B.L₁ ⊔ B.L₂) := by
  have hV := cx.c.hyp.elemAbelian
  have hxM : x ∈ M := S153E.T_le_M cx hxT
  refine Subgroup.mem_inf.2 ⟨convI_mem_autI _ hxT _, ?_⟩
  rw [B.hS.mem_sup_iff (barM_mem_autI hxM)]
  intro u hu
  have hxN' : x ∈ Subgroup.normalizer (((commV B.L₁).map (inclMod hV) : Subgroup G) : Set G) := by
    rw [B.hV₁]
    exact hxN
  have hst := (mem_normalizer_map_inclMod_iff hV (cx.c.hyp.le_normalizer hxM) (commV B.L₁)).1 hxN'
  exact (mem_stabSub.1 hst u).2 hu

include B in
theorem exists_of_mem_S' {y' : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)}
    (hy : y' ∈ autI cx.c.hyp.elemAbelian T ⊓ (B.L₁ ⊔ B.L₂)) :
    ∃ (x : G) (hxT : x ∈ T), x ∈ Subgroup.normalizer (V₁ : Set G) ∧
      barM cx (S153E.T_le_M cx hxT) = y' := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨x, hxT, hxy⟩ := (mem_autI _).1 (Subgroup.mem_inf.1 hy).1
  have hxM : (x : G) ∈ M := S153E.T_le_M cx hxT
  refine ⟨x, hxT, ?_, hxy⟩
  have hst : convI hV ⟨(x : G), x.2⟩ ∈ stabSub (commV B.L₁) := by
    rw [show convI hV ⟨(x : G), x.2⟩ = y' from hxy]
    exact B.hS.sup_le_stab₁ (Subgroup.mem_inf.1 hy).2
  have := (mem_normalizer_map_inclMod_iff hV x.2 (commV B.L₁)).2 hst
  rwa [B.hV₁] at this

include B in
theorem ZS_inf_V₁_eq : ZS153 T M V₁ ⊓ V₁ = Subgroup.zpowers B.a₁.val := by
  have hV := cx.c.hyp.elemAbelian
  apply le_antisymm
  · intro w hw
    obtain ⟨hwZ, hwV₁⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨u, hu, rfl⟩ := exists_mem_commV₁ B hwV₁
    have hfix : ∀ y' ∈ autI hV T ⊓ (B.L₁ ⊔ B.L₂), y' u = u := by
      intro y' hy'
      obtain ⟨x, hxT, hxN, hxy⟩ := exists_of_mem_S' B hy'
      have hxS : x ∈ Sgp153 T V₁ := Subgroup.mem_inf.2 ⟨hxT, hxN⟩
      have hcomm := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hwZ).2 x hxS
      refine IntMod.val_injective ?_
      rw [← hxy, barM_apply_val]
      calc x * u.val * x⁻¹ = (u.val * x) * x⁻¹ := by rw [← hcomm]
        _ = u.val := by group
    have hcases := (B.hF.sylow.fixS u).1 hfix
    have hinf := B.hS.inf
    have hnot : ∀ a : IntMod (VZ T M) hV, a ∈ commV B.L₂ → a ≠ 1 → a ∉ commV B.L₁ := by
      intro a ha ha1 ha'
      have : a ∈ commV B.L₁ ⊓ commV B.L₂ := ⟨ha', ha⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact ha1 this
    rcases hcases with h | h | h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
    · exact absurd (h ▸ hu) (hnot _ B.hF.sylow.a₂_mem B.hF.sylow.a₂_ne)
    · exfalso
      refine hnot _ B.hF.sylow.a₂_mem B.hF.sylow.a₂_ne ?_
      have h1 : B.a₂ = B.a₁⁻¹ * u := by rw [h]; group
      rw [h1]
      exact (commV B.L₁).mul_mem ((commV B.L₁).inv_mem B.hF.sylow.a₁_mem) hu
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨B.a₁.val_mem, ?_⟩, vOf_mem B⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxS := Subgroup.mem_inf.1 hx
    have hxM : x ∈ M := S153E.T_le_M cx hxS.1
    have hmem := barM_mem_S' B hxS.1 hxS.2
    have hfix := (B.hF.sylow.fixS B.a₁).2 (Or.inr (Or.inl rfl)) _ hmem
    have h1 : x * B.a₁.val * x⁻¹ = B.a₁.val := by
      have := congrArg IntMod.val hfix
      rwa [barM_apply_val] at this
    calc x * B.a₁.val = (x * B.a₁.val * x⁻¹) * x := by group
      _ = B.a₁.val * x := by rw [h1]

end VPart

end S153EN8

end CFSG.Quasithin

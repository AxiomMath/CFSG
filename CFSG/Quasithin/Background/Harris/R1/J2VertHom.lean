module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.CosetTable

variable {m : ℕ} {ws : List (List (Fin m × Bool))} {G : Type*} [Group G] {g : Fin m → G}

theorem lift_eq_one_of_prod
    (hp : ∀ r ∈ ws, (r.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod = 1) :
    ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}, FreeGroup.lift g r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [FreeGroup.lift_mk]
  simpa [Bool.cond_eq_ite] using hp w hw

@[expose] noncomputable def pgHom
    (hp : ∀ r ∈ ws, (r.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod = 1) :
    PG m ws →* G :=
  PresentedGroup.toGroup (lift_eq_one_of_prod hp)

theorem pgHom_of (hp : ∀ r ∈ ws, (r.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod = 1)
    (i : Fin m) : pgHom hp (PresentedGroup.of i) = g i :=
  PresentedGroup.toGroup.of (lift_eq_one_of_prod hp)

theorem range_pgHom (hp : ∀ r ∈ ws, (r.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod = 1) :
    (pgHom hp).range = Subgroup.closure (Set.range g) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}, MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext i
  exact pgHom_of hp i

theorem card_range_pgHom (hp : ∀ r ∈ ws, (r.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod = 1)
    {N : ℕ} (hfin : Finite (PG m ws)) (hle : Nat.card (PG m ws) ≤ N)
    (hge : N ≤ Nat.card (Subgroup.closure (Set.range g))) :
    Nat.card (pgHom hp).range = N := by
  rw [range_pgHom hp]
  refine le_antisymm ?_ hge
  have := Nat.card_le_card_of_surjective _ (pgHom hp).rangeRestrict_surjective
  rw [range_pgHom hp] at this
  exact this.trans hle

theorem pgHom_injective (hp : ∀ r ∈ ws, (r.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod = 1)
    {N : ℕ} (hfin : Finite (PG m ws)) (hle : Nat.card (PG m ws) ≤ N)
    (hge : N ≤ Nat.card (Subgroup.closure (Set.range g))) :
    Function.Injective (pgHom hp) := by
  have hc := card_range_pgHom hp hfin hle hge
  have hb := (pgHom hp).rangeRestrict_surjective.bijective_of_nat_card_le (by rw [hc]; exact hle)
  intro a b h
  exact hb.1 (Subtype.ext h)

end CFSG.Quasithin.Background.Harris.R1.J2Vert

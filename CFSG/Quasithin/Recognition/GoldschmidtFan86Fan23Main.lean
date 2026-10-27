module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Fan23Lift
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Fan23Inj

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ

universe u v

@[expose] def Fan23 {V : Type v} (Γ : SimpleGraph V) (G : Type u) [Group G] [MulAction G V] :
    Prop :=
  ∀ α β : V, Γ.Adj α β → ∀ P1 P2 : Subgroup G, P1 ≤ MulAction.stabilizer G α →
    P2 ≤ MulAction.stabilizer G β →
    P1 ⊓ MulAction.stabilizer G β = P2 ⊓ MulAction.stabilizer G α →
    Subgroup.closure ((P1 : Set G) ∪ (P2 : Set G)) ⊓ MulAction.stabilizer G α = P1 ∧
    Subgroup.closure ((P1 : Set G) ∪ (P2 : Set G)) ⊓ MulAction.stabilizer G β = P2

namespace Fan23

variable {V : Type v} {G : Type u} [Group G] [MulAction G V] {P1 P2 : Subgroup G} {α β : V}

theorem mem_stab {g : G} {v : V} : g ∈ MulAction.stabilizer G v ↔ g • v = v :=
  MulAction.mem_stabilizer_iff

theorem locInj (h1 : P1 ≤ MulAction.stabilizer G α) (h2 : P2 ≤ MulAction.stabilizer G β)
    (hB : P1 ⊓ MulAction.stabilizer G β = P2 ⊓ MulAction.stabilizer G α)
    (u a b : Vtx (amal P1 P2)) (ha : (amal P1 P2).treeGraph.Adj u a)
    (hb : (amal P1 P2).treeGraph.Adj u b) (hab : vmap h1 h2 a = vmap h1 h2 b) : a = b := by
  rcases u with q | q
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y₁, ⟨c₁, rfl⟩, rfl⟩ := ((amal P1 P2).adj_vtx_iff true g a).1 ha
    obtain ⟨y₂, ⟨c₂, rfl⟩, rfl⟩ := ((amal P1 P2).adj_vtx_iff true g b).1 hb
    have hab' : liftHom P1 P2 (g * (amal P1 P2).ofA c₁) • β =
        liftHom P1 P2 (g * (amal P1 P2).ofA c₂) • β := hab
    rw [map_mul, map_mul, liftHom_ofA, liftHom_ofA, mul_smul, mul_smul] at hab'
    have h12 : (c₁ : G) • β = (c₂ : G) • β := MulAction.injective (liftHom P1 P2 g) hab'
    have hmem : ((c₁ : G)⁻¹ * c₂) ∈ P1 ⊓ P2 := by
      have hst : ((c₁ : G)⁻¹ * c₂) ∈ P1 ⊓ MulAction.stabilizer G β :=
        Subgroup.mem_inf.2 ⟨P1.mul_mem (P1.inv_mem c₁.2) c₂.2, mem_stab.2 (by
          rw [mul_smul, ← h12, inv_smul_smul])⟩
      have hst' : ((c₁ : G)⁻¹ * c₂) ∈ P2 ⊓ MulAction.stabilizer G α := hB ▸ hst
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hst).1, (Subgroup.mem_inf.1 hst').1⟩
    refine ((amal P1 P2).vtx_eq_iff _ _ _ _).2 ⟨rfl, ?_⟩
    have e : (g * (amal P1 P2).ofA c₁)⁻¹ * (g * (amal P1 P2).ofA c₂) =
        (amal P1 P2).ofA (c₁⁻¹ * c₂) := by
      rw [map_mul, map_inv]
      group
    show _ ∈ (amal P1 P2).ofB.range
    rw [e, ofA_mem_ofB_range_iff]
    exact ⟨⟨(c₁ : G)⁻¹ * c₂, hmem⟩, Subtype.ext rfl⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y₁, ⟨c₁, rfl⟩, rfl⟩ := ((amal P1 P2).adj_vtx_iff false g a).1 ha
    obtain ⟨y₂, ⟨c₂, rfl⟩, rfl⟩ := ((amal P1 P2).adj_vtx_iff false g b).1 hb
    have hab' : liftHom P1 P2 (g * (amal P1 P2).ofB c₁) • α =
        liftHom P1 P2 (g * (amal P1 P2).ofB c₂) • α := hab
    rw [map_mul, map_mul, liftHom_ofB, liftHom_ofB, mul_smul, mul_smul] at hab'
    have h12 : (c₁ : G) • α = (c₂ : G) • α := MulAction.injective (liftHom P1 P2 g) hab'
    have hmem : ((c₁ : G)⁻¹ * c₂) ∈ P1 ⊓ P2 := by
      have hst : ((c₁ : G)⁻¹ * c₂) ∈ P2 ⊓ MulAction.stabilizer G α :=
        Subgroup.mem_inf.2 ⟨P2.mul_mem (P2.inv_mem c₁.2) c₂.2, mem_stab.2 (by
          rw [mul_smul, ← h12, inv_smul_smul])⟩
      have hst' : ((c₁ : G)⁻¹ * c₂) ∈ P1 ⊓ MulAction.stabilizer G β := hB.symm ▸ hst
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hst').1, (Subgroup.mem_inf.1 hst).1⟩
    refine ((amal P1 P2).vtx_eq_iff _ _ _ _).2 ⟨rfl, ?_⟩
    have e : (g * (amal P1 P2).ofB c₁)⁻¹ * (g * (amal P1 P2).ofB c₂) =
        (amal P1 P2).ofB (c₁⁻¹ * c₂) := by
      rw [map_mul, map_inv]
      group
    show _ ∈ (amal P1 P2).ofA.range
    rw [e, ofB_mem_ofA_range_iff]
    exact ⟨⟨(c₁ : G)⁻¹ * c₂, hmem⟩, Subtype.ext rfl⟩

variable {Γ : SimpleGraph V}

theorem vmap_injective (hT : Γ.IsTree) (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔
    Γ.Adj u v) (hαβ : Γ.Adj α β) (h1 : P1 ≤ MulAction.stabilizer G α)
    (h2 : P2 ≤ MulAction.stabilizer G β)
    (hB : P1 ⊓ MulAction.stabilizer G β = P2 ⊓ MulAction.stabilizer G α) :
    Function.Injective (vmap h1 h2) :=
  injective_of_locInj (amal P1 P2).universalCompletion.cosetGraph_connected hT (vmap h1 h2)
    (fun _ _ h => vmap_adj hadj hαβ h1 h2 h)
    (fun u a b ha hb hab => locInj h1 h2 hB u a b ha hb hab)

end Fan23

theorem fan23 {V : Type v} {Γ : SimpleGraph V} {G : Type u} [Group G] [MulAction G V]
    (hT : Γ.IsTree) (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) :
    Fan23 Γ G := by
  intro α β hαβ P1 P2 h1 h2 hB
  have hinj := Fan23.vmap_injective hT hadj hαβ h1 h2 hB
  have hcl : Subgroup.closure ((P1 : Set G) ∪ (P2 : Set G)) = (Fan23.liftHom P1 P2).range := by
    rw [Fan23.range_liftHom, Subgroup.sup_eq_closure]
  have hl1 : P1 ≤ Subgroup.closure ((P1 : Set G) ∪ (P2 : Set G)) := fun x hx =>
    Subgroup.subset_closure (Set.mem_union_left _ hx)
  have hl2 : P2 ≤ Subgroup.closure ((P1 : Set G) ∪ (P2 : Set G)) := fun x hx =>
    Subgroup.subset_closure (Set.mem_union_right _ hx)
  refine ⟨le_antisymm ?_ (le_inf hl1 h1), le_antisymm ?_ (le_inf hl2 h2)⟩
  · rintro x ⟨hx, hxα⟩
    rw [hcl] at hx
    obtain ⟨g, rfl⟩ := hx
    have h := hinj (a₁ := (Fan23.amal P1 P2).vtx true g) (a₂ := (Fan23.amal P1 P2).vtx true 1)
      (by
        rw [Fan23.vmap_vtx_true, Fan23.vmap_vtx_true, map_one, one_smul]
        exact MulAction.mem_stabilizer_iff.1 hxα)
    obtain ⟨-, c, hc⟩ := ((Fan23.amal P1 P2).vtx_eq_iff true true g 1).1 h
    have hg : g = ((Fan23.amal P1 P2).ofA c)⁻¹ := by
      rw [hc]
      group
    rw [hg, map_inv, Fan23.liftHom_ofA]
    exact P1.inv_mem c.2
  · rintro x ⟨hx, hxβ⟩
    rw [hcl] at hx
    obtain ⟨g, rfl⟩ := hx
    have h := hinj (a₁ := (Fan23.amal P1 P2).vtx false g) (a₂ := (Fan23.amal P1 P2).vtx false 1)
      (by
        rw [Fan23.vmap_vtx_false, Fan23.vmap_vtx_false, map_one, one_smul]
        exact MulAction.mem_stabilizer_iff.1 hxβ)
    obtain ⟨-, c, hc⟩ := ((Fan23.amal P1 P2).vtx_eq_iff false false g 1).1 h
    have hg : g = ((Fan23.amal P1 P2).ofB c)⁻¹ := by
      rw [hc]
      group
    rw [hg, map_inv, Fan23.liftHom_ofB]
    exact P2.inv_mem c.2

end CFSG.Quasithin.Fan86

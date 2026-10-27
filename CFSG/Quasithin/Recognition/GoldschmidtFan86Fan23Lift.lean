module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAct
public import CFSG.Quasithin.Recognition.GoldschmidtStatement

public section

namespace CFSG.Quasithin.Fan86.Fan23

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ

universe u v

variable {V : Type v} {G : Type u} [Group G] [MulAction G V] (P1 P2 : Subgroup G)

abbrev amal : GoldAmalgam P1 (P1 ⊓ P2 : Subgroup G) P2 := GoldAmalgam.ofSubgroupPair P1 P2

@[expose] noncomputable def liftHom : (amal P1 P2).Universal →* G :=
  Monoid.PushoutI.lift (φ := (amal P1 P2).diagram)
    (fun i => match i with | true => P1.subtype | false => P2.subtype) (P1 ⊓ P2).subtype
    (fun i => by cases i <;> rfl)

theorem liftHom_ofA (a : P1) : liftHom P1 P2 ((amal P1 P2).ofA a) = (a : G) :=
  Monoid.PushoutI.lift_of (φ := (amal P1 P2).diagram) (i := true) _ _ _ a

theorem liftHom_ofB (b : P2) : liftHom P1 P2 ((amal P1 P2).ofB b) = (b : G) :=
  Monoid.PushoutI.lift_of (φ := (amal P1 P2).diagram) (i := false) _ _ _ b

theorem range_liftHom : (liftHom P1 P2).range = P1 ⊔ P2 := by
  have h1 : (amal P1 P2).ofA.range.map (liftHom P1 P2) = P1 := by
    rw [← MonoidHom.range_comp]
    have : (liftHom P1 P2).comp (amal P1 P2).ofA = P1.subtype := MonoidHom.ext (liftHom_ofA P1 P2)
    rw [this, Subgroup.range_subtype]
  have h2 : (amal P1 P2).ofB.range.map (liftHom P1 P2) = P2 := by
    rw [← MonoidHom.range_comp]
    have : (liftHom P1 P2).comp (amal P1 P2).ofB = P2.subtype := MonoidHom.ext (liftHom_ofB P1 P2)
    rw [this, Subgroup.range_subtype]
  rw [MonoidHom.range_eq_map, ← (amal P1 P2).ofA_range_sup_ofB_range, Subgroup.map_sup, h1, h2]

variable {P1 P2} {α β : V}

@[expose] noncomputable def vmapA (h1 : P1 ≤ MulAction.stabilizer G α) :
    (amal P1 P2).Universal ⧸ (amal P1 P2).ofA.range → V :=
  Quotient.lift (fun g => liftHom P1 P2 g • α) (by
    intro a b hab
    obtain ⟨c, hc⟩ := (QuotientGroup.leftRel_apply.mp hab : a⁻¹ * b ∈ (amal P1 P2).ofA.range)
    have hb : b = a * (amal P1 P2).ofA c := by rw [hc]; group
    show liftHom P1 P2 a • α = liftHom P1 P2 b • α
    rw [hb, map_mul, mul_smul, liftHom_ofA, MulAction.mem_stabilizer_iff.mp (h1 c.2)])

@[expose] noncomputable def vmapB (h2 : P2 ≤ MulAction.stabilizer G β) :
    (amal P1 P2).Universal ⧸ (amal P1 P2).ofB.range → V :=
  Quotient.lift (fun g => liftHom P1 P2 g • β) (by
    intro a b hab
    obtain ⟨c, hc⟩ := (QuotientGroup.leftRel_apply.mp hab : a⁻¹ * b ∈ (amal P1 P2).ofB.range)
    have hb : b = a * (amal P1 P2).ofB c := by rw [hc]; group
    show liftHom P1 P2 a • β = liftHom P1 P2 b • β
    rw [hb, map_mul, mul_smul, liftHom_ofB, MulAction.mem_stabilizer_iff.mp (h2 c.2)])

@[expose] noncomputable def vmap (h1 : P1 ≤ MulAction.stabilizer G α)
    (h2 : P2 ≤ MulAction.stabilizer G β) : Vtx (amal P1 P2) → V :=
  Sum.elim (vmapA h1) (vmapB h2)

theorem vmap_vtx_true (h1 : P1 ≤ MulAction.stabilizer G α) (h2 : P2 ≤ MulAction.stabilizer G β)
    (g : (amal P1 P2).Universal) : vmap h1 h2 ((amal P1 P2).vtx true g) = liftHom P1 P2 g • α :=
  rfl

theorem vmap_vtx_false (h1 : P1 ≤ MulAction.stabilizer G α) (h2 : P2 ≤ MulAction.stabilizer G β)
    (g : (amal P1 P2).Universal) : vmap h1 h2 ((amal P1 P2).vtx false g) = liftHom P1 P2 g • β :=
  rfl

variable {Γ : SimpleGraph V}

theorem vmap_adj (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hab : Γ.Adj α β) (h1 : P1 ≤ MulAction.stabilizer G α) (h2 : P2 ≤ MulAction.stabilizer G β)
    {u w : Vtx (amal P1 P2)} (h : (amal P1 P2).treeGraph.Adj u w) :
    Γ.Adj (vmap h1 h2 u) (vmap h1 h2 w) := by
  rcases u with x | x <;> rcases w with y | y
  · simp [GoldAmalgam.treeGraph, goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel] at h
  · obtain ⟨z, rfl, rfl⟩ := (goldCosetGraph_adj_inl_inr _ _ x y).1 h
    exact (hadj (liftHom P1 P2 z) α β).2 hab
  · obtain ⟨z, rfl, rfl⟩ := (goldCosetGraph_adj_inl_inr _ _ y x).1 h.symm
    exact ((hadj (liftHom P1 P2 z) α β).2 hab).symm
  · simp [GoldAmalgam.treeGraph, goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel] at h

end CFSG.Quasithin.Fan86.Fan23

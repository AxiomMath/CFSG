module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86OrbitTreeDef

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {H : Subgroup G} {α : V}

theorem orbitGraph_adj_smul (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (h : ↥H) (u v : ↥(MulAction.orbit ↥H α)) :
    (orbitGraph Γ (MulAction.orbit ↥H α)).Adj (h • u) (h • v) ↔
      (orbitGraph Γ (MulAction.orbit ↥H α)).Adj u v := by
  have key : ∀ (h : ↥H) (u v : ↥(MulAction.orbit ↥H α)),
      (orbitGraph Γ (MulAction.orbit ↥H α)).Adj u v →
        (orbitGraph Γ (MulAction.orbit ↥H α)).Adj (h • u) (h • v) := by
    rintro h u v ⟨hne, w, hu, hv⟩
    exact ⟨fun e => hne (MulAction.injective h e), (h : G) • w, (hadj h u.1 w).2 hu,
      (hadj h v.1 w).2 hv⟩
  refine ⟨fun hh => ?_, key h u v⟩
  simpa using key h⁻¹ _ _ hh

theorem orbit_transitive (u v : ↥(MulAction.orbit ↥H α)) : ∃ h : ↥H, h • u = v := by
  obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.1 u.2
  obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.1 v.2
  refine ⟨y * x⁻¹, Subtype.ext ?_⟩
  show (y * x⁻¹) • u.1 = v.1
  rw [← hx, ← hy, mul_smul, inv_smul_smul]

theorem orbit_finite_stabilizer (hfin : ∀ v : V, Finite (MulAction.stabilizer G v))
    (w : ↥(MulAction.orbit ↥H α)) : Finite (MulAction.stabilizer ↥H w) := by
  have := hfin w.1
  refine Finite.of_injective
    (fun s : MulAction.stabilizer ↥H w => (⟨((s : ↥H) : G), MulAction.mem_stabilizer_iff.2
      (congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 s.2))⟩ :
        MulAction.stabilizer G w.1)) ?_
  intro s t hst
  exact Subtype.ext (Subtype.ext (congrArg (fun x : MulAction.stabilizer G w.1 => x.1) hst))

theorem orbitGraph_loc (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : OrbitLoc Γ H (MulAction.orbit ↥H α)) (hP : OrbitPartner Γ (MulAction.orbit ↥H α))
    (w u v : ↥(MulAction.orbit ↥H α)) (hu : (orbitGraph Γ (MulAction.orbit ↥H α)).Adj w u)
    (hv : (orbitGraph Γ (MulAction.orbit ↥H α)).Adj w v) :
    ∃ h ∈ MulAction.stabilizer ↥H w, h • u = v := by
  obtain ⟨hwu, x, hwx, hux⟩ := hu
  obtain ⟨hwv, y, hwy, hvy⟩ := hv
  obtain ⟨h, hh, hhw, hhx⟩ := hloc w.1 w.2 x y hwx hwy
  refine ⟨⟨h, hh⟩, MulAction.mem_stabilizer_iff.2 (Subtype.ext hhw), Subtype.ext ?_⟩
  have hmem : h • u.1 ∈ MulAction.orbit ↥H α :=
    ((⟨h, hh⟩ : ↥H) • u).2
  have e1 : h • u.1 ∈ MulAction.orbit ↥H α ∧ h • u.1 ≠ w.1 ∧ Γ.Adj (h • u.1) y := by
    refine ⟨hmem, fun e => hwu (MulAction.injective h (e.trans hhw.symm)).symm, ?_⟩
    rw [← hhx]
    exact (hadj h u.1 x).2 hux
  have e2 : v.1 ∈ MulAction.orbit ↥H α ∧ v.1 ≠ w.1 ∧ Γ.Adj v.1 y := ⟨v.2, hwv.symm, hvy⟩
  exact (hP w.1 w.2 y hwy).unique e1 e2

theorem card_neighborSet_smul (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (g : G) (v : V) : Nat.card (Γ.neighborSet (g • v)) = Nat.card (Γ.neighborSet v) :=
  (Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g) (fun w => by
    simp only [mem_neighborSet, MulAction.toPerm_apply]
    exact (hadj g v w).symm))).symm

theorem card_neighborSet_orbit (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {n : ℕ} (hα : Nat.card (Γ.neighborSet α) = n) (u : ↥(MulAction.orbit ↥H α)) :
    Nat.card (Γ.neighborSet u.1) = n := by
  obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.1 u.2
  rw [← hx, ← hα]
  exact card_neighborSet_smul hadj (x : G) α

theorem orbitPartner_of_orbit (h : ∀ u ∈ MulAction.orbit ↥H α, ∀ w, Γ.Adj u w →
    ∃ u', (u' ∈ MulAction.orbit ↥H u ∧ u' ≠ u ∧ Γ.Adj u' w) ∧
      ∀ u'', (u'' ∈ MulAction.orbit ↥H u ∧ u'' ≠ u ∧ Γ.Adj u'' w) → u'' = u') :
    OrbitPartner Γ (MulAction.orbit ↥H α) := by
  intro u hu w hw
  have e : MulAction.orbit ↥H u = MulAction.orbit ↥H α := MulAction.orbit_eq_iff.2 hu
  obtain ⟨u', hu', huniq⟩ := h u hu w hw
  rw [e] at hu' huniq
  exact ⟨u', hu', huniq⟩

end CFSG.Quasithin.Fan86

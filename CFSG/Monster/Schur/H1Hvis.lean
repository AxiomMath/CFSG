module

public import CFSG.Monster.Schur.FixedNvis
public import CFSG.Monster.Schur.Restriction
public import CFSG.Monster.VisQuot.Simple
public import CFSG.Monster.Visible.Irreducible

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel CFSG.Monster.VisCert
  CFSG.Monster.Visible CFSG.Monster.VisQuot

@[expose] noncomputable def hvisRep : Representation (ZMod 2) Hvis L2 :=
  (Units.coeHom (Module.End (ZMod 2) L2)).comp Hvis.subtype

theorem hvisRep_apply (g : Hvis) (v : L2) : hvisRep g v = (g : GLV) • v := rfl

theorem perfect_Hvis :
    Group.IsPerfect Hvis := Group.isPerfect_def.2 commutator_Hvis_eq_top

theorem odd_index_Nvis_subgroupOf :
    Odd (Nvis.subgroupOf Hvis).index := by
  rw [← stabilizer_fDelta, MulAction.index_stabilizer_of_transitive, natCard_deltaSub]
  decide

theorem irreducible_Hvis_L2 (W : Submodule (ZMod 2) L2)
    (hW : ∀ g : Hvis, ∀ w ∈ W, hvisRep g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  refine visible_quotient_irreducible_action.2.2 W fun p w hw => ?_
  have hp : p.1.2 ∈ PvisLat := ⟨p.1, p.2, rfl⟩
  exact hW ⟨modTwoUnit p.1.2, modTwoUnit_mem_Hvis hp⟩ w hw

theorem twoΩCls_ne_zero : twoΩCls ≠ 0 := by
  intro h
  rw [← dec_seed, ← dec_zero] at h
  exact absurd (dec_injective (by norm_num) (by norm_num) h) (by norm_num)

theorem end_Hvis_L2 (ψ : Module.End (ZMod 2) L2)
    (hψ : ∀ (g : Hvis) v, ψ (hvisRep g v) = hvisRep g (ψ v)) : ψ = 0 ∨ ψ = 1 := by
  have hw : ∀ g ∈ Nvis, (g : GLV) • twoΩCls = twoΩCls := fun g hg =>
    (Hvis_stab_iff g (Nvis_le_Hvis hg)).2 hg
  have hψw : ∀ g ∈ Nvis, (g : GLV) • ψ twoΩCls = ψ twoΩCls := fun g hg => by
    have h := hψ ⟨g, Nvis_le_Hvis hg⟩ twoΩCls
    rw [hvisRep_apply, hvisRep_apply, hw g hg] at h
    exact h.symm
  rcases fixed_Nvis_L2 _ hψw with h | h
  · left
    have hker : LinearMap.ker ψ = ⊤ := by
      have hinv : ∀ g : Hvis, ∀ w ∈ LinearMap.ker ψ, hvisRep g w ∈ LinearMap.ker ψ := by
        intro g w hw
        rw [LinearMap.mem_ker, hψ, LinearMap.mem_ker.1 hw, map_zero]
      rcases irreducible_Hvis_L2 _ hinv with h1 | h1
      · exfalso
        have h2 : twoΩCls ∈ LinearMap.ker ψ := LinearMap.mem_ker.2 h
        rw [h1, Submodule.mem_bot] at h2
        exact twoΩCls_ne_zero h2
      · exact h1
    exact LinearMap.ext fun v => LinearMap.mem_ker.1 (by rw [hker]; trivial)
  · right
    have hker : LinearMap.ker (ψ - 1) = ⊤ := by
      have hinv : ∀ g : Hvis, ∀ w ∈ LinearMap.ker (ψ - 1),
          hvisRep g w ∈ LinearMap.ker (ψ - 1) := by
        intro g w hw
        have hw' : ψ w = w := by
          have := LinearMap.mem_ker.1 hw
          rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hψ, hw', sub_self]
      rcases irreducible_Hvis_L2 _ hinv with h1 | h1
      · exfalso
        have h2 : twoΩCls ∈ LinearMap.ker (ψ - 1) := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, h, sub_self]
        rw [h1, Submodule.mem_bot] at h2
        exact twoΩCls_ne_zero h2
      · exact h1
    refine LinearMap.ext fun v => ?_
    have := LinearMap.mem_ker.1 (by rw [hker]; trivial : v ∈ LinearMap.ker (ψ - 1))
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
    exact this

theorem h1_Hvis_dual
    (f : Hvis → Module.Dual (ZMod 2) L2)
    (hf : ∀ g h v, f (g * h) v = f g (hvisRep h v) + f h v) :
    ∃ φ : Module.Dual (ZMod 2) L2, ∀ (g : Hvis) v, f g v = φ (hvisRep g v) - φ v := by
  refine principal_of_odd_index_dual hvisRep odd_index_Nvis_subgroupOf f hf ?_
  obtain ⟨φ, hφ⟩ := h1_Nvis_dual (fun g => f ⟨g, Nvis_le_Hvis g.2⟩)
    (fun g h v => hf ⟨g, Nvis_le_Hvis g.2⟩ ⟨h, Nvis_le_Hvis h.2⟩ v)
  exact ⟨φ, fun p hp v => hφ ⟨p, hp⟩ v⟩

end CFSG.Monster.Schur

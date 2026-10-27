module

public import CFSG.Monster.VisCert.CyclicSpan
public import CFSG.Monster.Visible.SignCompat.Compat

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisCert

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.Lifts

@[expose] def PvisLat : Subgroup latticeO := Pvis.map (MonoidHom.snd (GL SpinIdx ℚ) latticeO)

theorem mem_PvisLat {g : latticeO} : g ∈ PvisLat ↔ ∃ s, (s, g) ∈ Pvis := by
  constructor
  · rintro ⟨⟨s, g'⟩, h, rfl⟩
    exact ⟨s, h⟩
  · rintro ⟨s, h⟩
    exact ⟨(s, g), h, rfl⟩

theorem xiO_mem_PvisLat : xiO ∈ PvisLat := mem_PvisLat.2 ⟨xiPair.1.1, xiPair.2⟩

theorem PO_mem_PvisLat (p : AutPerm) : PO p ∈ PvisLat := mem_PvisLat.2 ⟨sU p, sU_PO_mem_Pvis p⟩

theorem gO_mem_PvisLat (a : C) : gO a ∈ PvisLat :=
  mem_PvisLat.2 ⟨YU ⟨a, 0⟩, YU_gO_mem_Pvis ⟨a, 0⟩⟩

theorem cycGen_mem_PvisLat (g : Fin 14) : cycGen g ∈ PvisLat := by
  unfold cycGen
  split_ifs
  · exact xiO_mem_PvisLat
  · exact PO_mem_PvisLat pAut
  · exact gO_mem_PvisLat _

theorem cycWordElt_mem_PvisLat (w : List ℕ) : cycWordElt w ∈ PvisLat := by
  induction w with
  | nil => exact PvisLat.one_mem
  | cons g w ih =>
    rw [cycWordElt, List.map_cons, List.prod_cons]
    refine PvisLat.mul_mem ?_ ih
    unfold cycGenN
    split_ifs
    · exact cycGen_mem_PvisLat _
    · exact PvisLat.one_mem

theorem orbitCls_mem_orbit (t : Fin 24) :
    ∃ p : Pvis, modTwoEnd p.1.2 twoΩCls = orbitCls t := by
  obtain ⟨s, hs⟩ := mem_PvisLat.1 (cycWordElt_mem_PvisLat orbitWords[(t : ℕ)]!)
  exact ⟨⟨_, hs⟩, (dec_orbitVecs t).symm⟩

theorem span_orbit_twoΩCls :
    Submodule.span (ZMod 2) {x : L2 | ∃ p : Pvis, modTwoEnd p.1.2 twoΩCls = x} = ⊤ := by
  refine eq_top_iff.2 (span_orbitCls ▸ Submodule.span_mono ?_)
  rintro _ ⟨t, rfl⟩
  exact orbitCls_mem_orbit t

theorem visible_lattice_cyclic_span :
    pCyc ∈ AutPerm ∧
    (∀ j : Fin 12, permWord pCyc (B j) =
      ∑ k : Fin 12, (if (pCoeff.getD j 0).testBit k then 1 else 0) • B k) ∧
    (∀ j k : Fin 24, QuadraticMap.polarBilin qL (ellCls j) (ellCls k) = bvec 24 (gramRow j) k) ∧
    LinearIndependent (ZMod 2) ellCls ∧ Submodule.span (ZMod 2) (Set.range ellCls) = ⊤ ∧
    (∀ (g : Fin 14) (i : Fin 24), modTwoEnd (cycGen g) (ellCls i) =
      ∑ j : Fin 24, bvec 24 (cycRows[(g : ℕ)]!)[(i : ℕ)]! j • ellCls j) ∧
    twoΩCls = ∑ j : Fin 24, bvec 24 seedVec j • ellCls j ∧
    (∀ t : Fin 24, ∑ j : Fin 24, bvec 24 orbitVecs[(t : ℕ)]! j • ellCls j =
      modTwoEnd (cycWordElt orbitWords[(t : ℕ)]!) twoΩCls) ∧
    LinearIndependent (ZMod 2)
      (fun t : Fin 24 => ∑ j : Fin 24, bvec 24 orbitVecs[(t : ℕ)]! j • ellCls j) ∧
    (∀ g : Fin 14, ∃ s, (s, cycGen g) ∈ Pvis) ∧
    Submodule.span (ZMod 2) {x : L2 | ∃ p : Pvis, modTwoEnd p.1.2 twoΩCls = x} = ⊤ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := cyclic_span_certificate
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun g => mem_PvisLat.1 (cycGen_mem_PvisLat g),
    span_orbit_twoΩCls⟩

end CFSG.Monster.VisCert

module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
import CFSG.LocalAnalysis.StandardType.GGKacCompsSpec

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG.Assembly CFSG.StandardType

theorem k0LabelOf_lab_n (fam : LargeEvenLieTag) (r tw nEff : ℕ) :
    (k0LabelOf fam r tw nEff).lab.n = nEff := by
  cases fam <;> simp only [k0LabelOf] <;> split_ifs <;> simp_all

theorem orbitDescriptorOf_lab_n (D : K0Diag) (rho : List ℕ) (d n : ℕ) (orb : List (List ℕ)) :
    (orbitDescriptorOf D rho d n orb).lab.n = orb.length * n :=
  k0LabelOf_lab_n _ _ _ _

theorem KacRow.exists_perm_orbits {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) :
    ∃ M : List (List (List ℕ)), M.Perm row.rawComponentOrbits ∧
      row.D.orbits = M.map row.orbitDescriptor := by
  have h : row.D.orbits = k0SortBy (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
      (row.rawComponentOrbits.map row.orbitDescriptor) := by
    rw [row.D_eq]
    rfl
  have hp : row.D.orbits.Perm (row.rawComponentOrbits.map row.orbitDescriptor) := by
    rw [h, k0SortBy_eq_insertionSort]
    exact List.perm_insertionSort _ _
  have hc : Relation.Comp (fun a b => a = List.map row.orbitDescriptor b)
      (fun a b => List.Perm a b) row.D.orbits row.rawComponentOrbits := by
    rw [List.eq_map_comp_perm]
    exact hp
  obtain ⟨M, hM, hMp⟩ := hc
  exact ⟨M, hMp, hM⟩

end CFSG.StandardType.GGK0MarkedKacIface1587

end

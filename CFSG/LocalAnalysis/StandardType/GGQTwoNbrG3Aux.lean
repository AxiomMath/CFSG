module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryDatum
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Open CFSG.ClassicalGroups.UnitaryFlag

theorem qTwoNbrG3_weyl_normalizer_of_cover
    {G : Type} [Group G] [Finite G] {d : ℕ}
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) (hd : 5 ≤ d)
    {Bs X : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 1 F d) →* X} (hM : UnitTB.Model ψ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (σ : Equiv.Perm (Fin d)) :
    (ψ (LineU.permSU hM.field σ) : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
  obtain ⟨_, _, _, _, _, _, _, _, hπ, _, _, _, _, _, _, _⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (p := 3) (r := r) (f := 1) (F := F) hF
      le_rfl (by norm_num) (by norm_num) (by omega) hBs hSC hN hM hdiag
  exact hπ σ

end CFSG.StandardType.QTwo

end

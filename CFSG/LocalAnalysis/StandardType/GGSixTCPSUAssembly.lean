module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUNotDvdLeaf
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDvd

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

theorem false_of_dvd_PSU_of_models
    {X : Type} [Group X] [Finite X] {n p : ℕ} {G₀ B D J L : Subgroup X} {x : X} {g : ℕ}
    {ψ : (ggU .PSU n (g + 1)).K →* X} (h : GGTCHyp .PSU n (g + 1) ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .PSU (g + 1)) (hp : p ∣ 2 ^ (g + 1) + 1)
    (hM1 : ∀ {S : Set (GL (Fin n) (PSUF g))} {ε e : Matrix (Fin n) (Fin n) (PSUF g)}
      {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}, PSUBlock ψ B S ε e → e ≠ ε →
      IsComponentOf J'
        ⁅glBlockCentralizer (PSUj n g) S ε, glBlockCentralizer (PSUj n g) S ε⁆ →
      J'.map ψ = J → 2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e) : False := by
  classical
  have hH := PSULiftHyp.of_ggTCHyp h
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [h.range]
    exact h.j_comp
  obtain ⟨S, ε, e, J', -, hb, -, hJ'g, hJ'm⟩ := hH.exists_block h.d_le hJ
  have hd : 2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e := by
    by_cases hself : e = ε
    · exact hb.two_le_blockDegree_of_selfDual hH hself h.d_card h.j_cent hJ'g hJ'm hF
    · exact hM1 hb hself hJ'g hJ'm
  exact hb.false_of_dvd hH hp hd

end CFSG.StandardType.TableCRes

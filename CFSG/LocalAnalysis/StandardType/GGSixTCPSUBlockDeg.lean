module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUSelfDual
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUTypeDet

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

variable {X : Type} [Group X] {n g p : ℕ} {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X}

theorem PSUBlock.two_le_blockDegree_of_selfDual
    [Finite X] (hH : PSULiftHyp n g ψ p B)
    {S : Set (GL (Fin n) (PSUF g))} {ε e : Matrix (Fin n) (Fin n) (PSUF g)}
    (hb : PSUBlock ψ B S ε e) (hself : e = ε) {D J : Subgroup X} (hDcard : Nat.card D = p ^ 2)
    (hjc : B ⊓ Subgroup.centralizer (J : Set X) = D)
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJ'g : IsComponentOf J'
      ⁅glBlockCentralizer (PSUj n g) S ε, glBlockCentralizer (PSUj n g) S ε⁆)
    (hJ'm : J'.map ψ = J) (hF : GGSixLSevenFieldExtCase J .PSU (g + 1)) :
    2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e := by
  rw [← hself] at hb hJ'g
  by_contra hlt
  have hpos := (exists_blockDegree_mul_eq_rank (hb.S_comm hH) (hb.S_odd hH) hb.e_prim).1
  have hd1 : blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e = 1 := by omega
  obtain ⟨hr3, hmodel⟩ := hb.exists_model_of_selfDual_one hH hd1 hDcard hjc hJ'g hJ'm
  exact false_of_fieldExt_of_model_PSU hr3 hmodel hF

end CFSG.StandardType.TableCRes

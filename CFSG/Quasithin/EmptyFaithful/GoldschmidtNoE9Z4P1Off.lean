module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Dict
public import CFSG.Quasithin.EmptyFaithful.S14612GB0
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Rho

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem exists_involution_of_autOn_Qset (hcls : ClassAutShapeStmt) (h35 : Lemma1435)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    (h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {B : Subgroup G} (hBH : B ≤ H)
    (hB : autOn (tildeOf (quasithinOmegaOneCenter T) B)
      (tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H)) ∈
        @Qset ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H))
          (commGroupOfElemAbelian h98.toHypF91.isElemAbelian_tilde)
          (autOn (tildeOf (quasithinOmegaOneCenter T) H)
            (tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H)))) :
    ∃ x : ↥H, (x : G) ∈ B ∧ orderOf (rhoH h98.toHypF91 x) = 2 ∧
      ∀ y : ↥H, (y : G) ∈ B →
        rhoH h98.toHypF91 y = 1 ∨ rhoH h98.toHypF91 y = rhoH h98.toHypF91 x := by
  obtain ⟨hsplit, hinf, -⟩ := shape_splitting h35 S hred h98
  have hstr := e9z4Str_of_shape hcls h35 S hred hshape h98
  have hB' := map_rhoH_mem_Qset h98.toHypF91 hBH hB
  obtain ⟨x, hxB, hx2, -, hall⟩ := exists_of_map_mem_Qset hsplit hinf hstr hB'
  exact ⟨x, Subgroup.mem_subgroupOf.mp hxB, hx2,
    fun y hy => hall y (Subgroup.mem_subgroupOf.mpr hy)⟩

end CFSG.Quasithin

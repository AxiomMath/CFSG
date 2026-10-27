module

public import CFSG.Quasithin.Background.HMathieuStd
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.Quasithin.H.Mathieu

@[expose] def octAdd (O : Finset (Fin 24)) : (Fin 11 → ZMod 2) →+ ZMod 2 where
  toFun v := ∑ i ∈ O, liftE v i
  map_zero' := by simp
  map_add' v v' := by simp [Finset.sum_add_distrib]

@[expose] def octFun (O : Finset (Fin 24)) (w : W11) : ZMod 2 := octAdd O (Multiplicative.toAdd w)

theorem octFun_def (O : Finset (Fin 24)) (w : W11) :
    octFun O w = ∑ i ∈ O, liftE (Multiplicative.toAdd w) i := rfl

@[expose] def annOf (S : Finset (Finset (Fin 24))) : Subgroup W11 :=
  ⨅ O ∈ S, (AddMonoidHom.toMultiplicative (octAdd O)).ker

theorem mem_annOf {S : Finset (Finset (Fin 24))} {w : W11} :
    w ∈ annOf S ↔ ∀ O ∈ S, octFun O w = 0 := by
  simp only [annOf, Subgroup.mem_iInf, MonoidHom.mem_ker, AddMonoidHom.toMultiplicative_apply_apply,
    ofAdd_eq_one, octFun]

end CFSG.Quasithin.H13.AS91.M24G

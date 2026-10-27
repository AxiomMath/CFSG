module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

structure s16h_E3Frame {W : Type} [CommGroup W] (X L L' T : Subgroup (MulAut W))
    (U U' : Subgroup W) : Prop where
  exp2 : ∀ w : W, w ^ 2 = 1
  inf_eq : U ⊓ U' = ⊥
  sup_eq : U ⊔ U' = ⊤
  le_x : L ≤ X
  le_x' : L' ≤ X
  t_le : T ≤ X
  t_two : IsPGroup 2 ↥T
  t_syl : ¬ 2 ∣ T.relIndex X
  comm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  fix_u : ∀ b ∈ L', ∀ w ∈ U, b w = w
  fix_u' : ∀ a ∈ L, ∀ w ∈ U', a w = w
  u_eq : U = commSub ⊤ L
  u'_eq : U' = commSub ⊤ L'
  perm : ∀ x ∈ X,
    (L.map (MulAut.conj x).toMonoidHom = L ∧ L'.map (MulAut.conj x).toMonoidHom = L' ∧
        U.map x.toMonoidHom = U ∧ U'.map x.toMonoidHom = U') ∨
      (L.map (MulAut.conj x).toMonoidHom = L' ∧ L'.map (MulAut.conj x).toMonoidHom = L ∧
        U.map x.toMonoidHom = U' ∧ U'.map x.toMonoidHom = U)
  swap : ∃ t ∈ T, L.map (MulAut.conj t).toMonoidHom = L' ∧ U.map t.toMonoidHom = U'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

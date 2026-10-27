module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPmWDatum
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] def GGQ2LDatum.toWDatum {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) : GGQ2WDatum p where
  Λ := M.Λ
  coxeter := M.coxeter
  cartan := M.cartan
  V := M.V
  coroot := M.coroot
  root := M.root
  isWeyl := M.isWeyl
  isCartan := M.isCartan
  pairing := M.pairing

theorem GGQ2LDatum.weyl_eq_map {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) :
    M.toWDatum.weyl = (ggAutomizer L Bs).map (ggLin (p := p) M.model) := by
  have hsimple : ∀ i : M.Λ, ggLin (p := p) M.model (M.simple i) = M.toWDatum.simpleRefl i := by
    intro i
    refine LinearEquiv.ext fun v => ?_
    rw [M.simple_apply]
    exact (Module.reflection_apply v (M.toWDatum.root_coroot_self i)).symm
  have hrange : Set.range M.toWDatum.simpleRefl
      = ggLin (p := p) M.model '' Set.range M.simple := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨M.simple i, ⟨i, rfl⟩, hsimple i⟩
    · rintro ⟨φ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hsimple i).symm⟩
  rw [show M.toWDatum.weyl = Subgroup.closure (Set.range M.toWDatum.simpleRefl) from rfl]
  rw [hrange, M.automizer_L, MonoidHom.map_closure]
  rfl

end CFSG.StandardType

end

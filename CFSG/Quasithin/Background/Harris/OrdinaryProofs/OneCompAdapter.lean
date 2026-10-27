module

public import CFSG.Quasithin.Background.Harris.Interfaces

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem OneCompSetting.toG93Hyp {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (h : OneCompSetting Γ A L m) : G93Hyp Γ A L L m where
  quotient := h.quotient
  A_le := h.A_le
  A_elem := h.A_elem
  A_card := h.A_card
  bound := h.bound
  L_comp := h.L_comp
  L_comm := h.L_comm
  H_le := h.L_comp.1
  H_normal := h.L_normal
  H_irr := h.L_irr
  H_eq := Or.inl rfl

theorem oneCompFor_of_g93Hyp_concl {P Q : ∀ (X : Type) [Group X], Prop}
    (hconcl : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (Γ A L : Subgroup (GLV V)) (m : ℕ),
      G93Hyp Γ A L L m → P (↥L ⧸ Subgroup.center ↥L) → G93Concl Γ L m)
    (hPQ : ∀ (X : Type) [Group X], Q X → P (X ⧸ Subgroup.center X)) :
    OneCompFor Q :=
  fun V _ _ _ Γ A L m hs hQ => hconcl V Γ A L m (OneCompSetting.toG93Hyp hs) (hPQ ↥L hQ)

theorem oneCompFor_of_false {P Q : ∀ (X : Type) [Group X], Prop}
    (hfalse : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (Γ A L : Subgroup (GLV V)) (m : ℕ),
      G93Hyp Γ A L L m → P (↥L ⧸ Subgroup.center ↥L) → False)
    (hPQ : ∀ (X : Type) [Group X], Q X → P (X ⧸ Subgroup.center X)) :
    OneCompFor Q :=
  oneCompFor_of_g93Hyp_concl
    (fun V _ _ _ Γ A L m hG hP => (hfalse V Γ A L m hG hP).elim) hPQ

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end

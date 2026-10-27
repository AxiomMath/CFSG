module

public import CFSG.Quasithin.MS93.S45IV

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

@[expose] def S45Q2a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Ctx M T L φ), Fintype.card F = 2 → c.HZV

@[expose] def Ctx.HQ2b {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ) :
    Prop :=
  ∀ (p p' : ℕ → Vtx (puAmalgam c.hyp.le)) (N : ℕ), IsGoodPath _ p N → IsGoodPath _ p' N →
    ∀ a : ℕ, Even a → 34 ≤ a → a + 30 ≤ N → (∀ i, i ≤ a + 2 → p' i = p i) →
    Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)) →
    Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) →
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        Subgroup.centralizer (Ltil c.hyp.le L (p a) : Set (puAmalgam c.hyp.le).Universal) ≤
      Hloc c.hyp.le L (p a) ∧
    centerOf ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤
      Uloc c.hyp.le L (p a) ⊔ Hloc c.hyp.le L (p a) ∧
    frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ = Vcirc c.hyp.le L (p a) ∧
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        Subgroup.centralizer (Vcirc c.hyp.le L (p a) : Set (puAmalgam c.hyp.le).Universal) ≤
      whv c.hyp (p a) (p (a + 2)) ∧
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤
      (conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2))) ⊔
        (conjCl (stab (puAmalgam c.hyp.le) (p a))
            (Vcirc c.hyp.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2)))

end CFSG.Quasithin.MS93.S45

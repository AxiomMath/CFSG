module

public import CFSG.Quasithin.MS93.S5Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5C56

@[expose] def C56g : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
      ∀ l : Submodule F (MSP.V4 F),
        S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
      ∀ g ∈ stab _ (baseA (puAmalgam h.le)), ∀ x ∈ puTrans h.le L (baseA _),
        S5.Concl56 h (2 ^ k) a α' l g x →
        ZM _ (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓
            ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ stabCenter _ (baseA (puAmalgam h.le))

@[expose] def C56x : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
      ∀ l : Submodule F (MSP.V4 F),
        S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
      ∀ g ∈ stab _ (baseA (puAmalgam h.le)), ∀ x ∈ puTrans h.le L (baseA _),
        S5.Concl56 h (2 ^ k) a α' l g x →
        ZM _ (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓
            ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ stabCenter _ (baseA (puAmalgam h.le)) ∧
          ((Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
            ZM _ (x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ⊓
                ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
              stabCenter _ (baseA (puAmalgam h.le)))

theorem c56g_of_c56x (h : C56x) : C56g := by
  intro G _ _ M T L hp hmin hb k F _ _ a hd α' hc hαβ l hl g hg x hx hconc
  exact (h G M T L hp hmin hb k F _ _ a hd α' hc hαβ l hl g hg x hx hconc).1

end S5C56

end CFSG.Quasithin.MS93

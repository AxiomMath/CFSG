module

public import CFSG.Quasithin.MS93.S4A43Stmt

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

@[expose] def S441EndB5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2)) →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ IsC1 h.le L (Fintype.card F) (g • geo (puAmalgam h.le) α α' 2)
          (conjCl (stab (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))
            (ZM (puAmalgam h.le) (g • α)))
          (ZM (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))) →
      ¬ ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Bloc h.le L α →
      ∀ μ lam δ : Vtx (puAmalgam h.le),
        (∃ g : (puAmalgam h.le).Universal,
          g • μ = α ∧ g • α = geo (puAmalgam h.le) α α' 2) →
        IsCritical (puAmalgam h.le) μ (geo (puAmalgam h.le) α' α 2) →
        geo (puAmalgam h.le) μ (geo (puAmalgam h.le) α' α 2) 2 = α →
        ⁅⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆, ZM (puAmalgam h.le) α'⁆ ≠ ⊥ →
        (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) α' α 2) lam = 2 →
        ¬ ZM (puAmalgam h.le) μ ≤ Subgroup.normalizer
          ((⁅ZM (puAmalgam h.le) lam, Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)⁆ ⊔
              ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) →
        IsCritical (puAmalgam h.le) lam α →
        ¬ Uloc h.le L μ ⊓ Subgroup.centralizer
            (Qv (puAmalgam h.le) (geo (puAmalgam h.le) μ α 1) :
              Set (puAmalgam h.le).Universal) ≤ Dloc h.le L α →
        (∃ l ∈ stab (puAmalgam h.le) α, l • μ = δ) →
        ¬ ZM (puAmalgam h.le) lam ≤ Subgroup.normalizer
          ((Uloc h.le L δ ⊓ Subgroup.centralizer
              (Qv (puAmalgam h.le) (geo (puAmalgam h.le) δ α 1) :
                Set (puAmalgam h.le).Universal) :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) →
        ¬ ZM (puAmalgam h.le) lam ≤ Subgroup.normalizer
          ((ZM (puAmalgam h.le) δ ⊔ ZM (puAmalgam h.le) α :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) →
        IsCritical (puAmalgam h.le) δ (geo (puAmalgam h.le) α' α 2) →
        stab (puAmalgam h.le) α ≤ Subgroup.normalizer
          ((⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) →
        Usup (puAmalgam h.le) δ (geo (puAmalgam h.le) δ α 1) ≤ Subgroup.centralizer
          (ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) : Set (puAmalgam h.le).Universal) →
        Nat.card ↥⁅ZM (puAmalgam h.le) δ, ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)⁆ =
          Fintype.card F →
        Uloc h.le L δ ⊓ Subgroup.centralizer
            (Qv (puAmalgam h.le) (geo (puAmalgam h.le) δ α 1) :
              Set (puAmalgam h.le).Universal) ≤
          ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)

@[expose] def S441EndB6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2)) →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ IsC1 h.le L (Fintype.card F) (g • geo (puAmalgam h.le) α α' 2)
          (conjCl (stab (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))
            (ZM (puAmalgam h.le) (g • α)))
          (ZM (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))) →
      ¬ ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Bloc h.le L α →
      ∀ μ lam γ δ : Vtx (puAmalgam h.le),
        (∃ g : (puAmalgam h.le).Universal,
          g • μ = α ∧ g • α = geo (puAmalgam h.le) α α' 2) →
        IsCritical (puAmalgam h.le) μ (geo (puAmalgam h.le) α' α 2) →
        geo (puAmalgam h.le) μ (geo (puAmalgam h.le) α' α 2) 2 = α →
        ⁅⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆, ZM (puAmalgam h.le) α'⁆ ≠ ⊥ →
        (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) α' α 2) lam = 2 →
        ¬ ZM (puAmalgam h.le) μ ≤ Subgroup.normalizer
          ((⁅ZM (puAmalgam h.le) lam, Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)⁆ ⊔
              ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) →
        IsCritical (puAmalgam h.le) lam α →
        Uloc h.le L μ ⊓ Subgroup.centralizer
            (Qv (puAmalgam h.le) (geo (puAmalgam h.le) μ α 1) :
              Set (puAmalgam h.le).Universal) ≤ Dloc h.le L α →
        (puAmalgam h.le).treeGraph.Adj α γ → (puAmalgam h.le).treeGraph.Adj γ δ →
        (∃ g : (puAmalgam h.le).Universal, g • α = δ ∧
          g • geo (puAmalgam h.le) μ α 1 = γ ∧ g • μ = α) →
        ¬ ZM (puAmalgam h.le) lam ≤ Subgroup.normalizer
          ((Uloc h.le L α ⊓ Subgroup.centralizer
              (Qv (puAmalgam h.le) γ : Set (puAmalgam h.le).Universal) :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) →
        ¬ ZM (puAmalgam h.le) lam ≤ Subgroup.normalizer
          ((ZM (puAmalgam h.le) δ ⊔ ZM (puAmalgam h.le) α :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) →
        IsCritical (puAmalgam h.le) δ (geo (puAmalgam h.le) α' α 2) →
        ∀ k ∈ stab (puAmalgam h.le) δ,
          ¬ ZM (puAmalgam h.le) (k • α) ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 4) →
          Usup (puAmalgam h.le) (k • α) (k • γ) ≤ Subgroup.centralizer
            (ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 4) : Set (puAmalgam h.le).Universal) →
          Nat.card ↥⁅ZM (puAmalgam h.le) (k • α),
              ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 4)⁆ = Fintype.card F →
          Uloc h.le L α ⊓ Subgroup.centralizer
              (Qv (puAmalgam h.le) γ : Set (puAmalgam h.le).Universal) ≤
            ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 4)

end CFSG.Quasithin.MS93.S4A

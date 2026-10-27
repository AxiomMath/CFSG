module

public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section ConjClosure

variable {G : Type*} [Group G]

@[expose] def conjCl (H K : Subgroup G) : Subgroup G :=
  ⨆ g ∈ H, K.map (MulAut.conj g).toMonoidHom

end ConjClosure

section AmalgamNotation

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def Usup (δ ρ : Vtx X) : Subgroup X.Universal := ⁅Zv X δ, Qv X ρ⁆

@[expose] def Gab (α β : Vtx X) : Subgroup X.Universal :=
  stab X α ⊓ Subgroup.normalizer (Qv X β : Set X.Universal)

@[expose] def IsStraight (α α' : Vtx X) : Prop :=
  ∀ i : ℕ, 0 < i → 2 * i < X.treeGraph.dist α α' →
    ∃ g ∈ stab X (geo X α α' (2 * i)), g • geo X α α' (2 * i + 2) = geo X α α' (2 * i - 2)

end AmalgamNotation

section SL3Via

variable {G : Type} [Group G]

@[expose] def IsSL3FullVia (M T L : Subgroup G) {F : Type} [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) : Prop :=
  (∃ n : ℕ, Fintype.card F = 2 ^ n) ∧ Function.Surjective φ ∧
    Xq M = Zq M L ⊔ Uq M T L ∧ Zq M L ⊓ Uq M T L = ⊥ ∧
    IsSumOfNaturalModulesVia M (Uq M T L) ⊥ φ false 1

theorem isSL3Full_iff_exists_via {M T L : Subgroup G} :
    IsSL3Full M T L ↔ ∃ (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)),
      IsSL3FullVia M T L φ := by
  constructor
  · rintro ⟨hX, hZU, n, F, _, _, φ, hF, hφ, hnat⟩
    exact ⟨F, inferInstance, inferInstance, φ, ⟨n, hF⟩, hφ, hX, hZU, hnat⟩
  · rintro ⟨F, _, _, φ, ⟨n, hF⟩, hφ, hX, hZU, hnat⟩
    exact ⟨hX, hZU, n, F, inferInstance, inferInstance, φ, hF, hφ, hnat⟩

end SL3Via

section PUNotation

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M) (L : Subgroup G)

noncomputable abbrev Ltil (δ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  puTrans hTM L δ

noncomputable abbrev Uloc (δ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  puTrans hTM (Uq M T L) δ

noncomputable abbrev Dloc (δ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  puTrans hTM (Dq M L) δ

@[expose] noncomputable def Bloc (δ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  Subgroup.closure {x | x ∈ Vv (puAmalgam hTM) δ ∧
    ∀ l ∈ puTrans hTM L δ, ⁅x, l⁆ ∈ Zv (puAmalgam hTM) δ}

@[expose] noncomputable def Vcirc (δ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  ⁅Vv (puAmalgam hTM) δ, puTrans hTM L δ⁆

@[expose] noncomputable def Hloc (δ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  ⁅Vcirc hTM L δ, Qv (puAmalgam hTM) δ⁆

@[expose] def nablaSet (δ : Vtx (puAmalgam hTM)) : Set (Vtx (puAmalgam hTM)) :=
  {μ | (puAmalgam hTM).treeGraph.dist δ μ = 2 ∧ ¬ Zv (puAmalgam hTM) μ ≤ Bloc hTM L δ}

@[expose] def IsC1 (q : ℕ) (δ : Vtx (puAmalgam hTM)) (A B : Subgroup (puAmalgam hTM).Universal) :
    Prop :=
  ⁅⁅A, Qv (puAmalgam hTM) δ⁆, puTrans hTM L δ⁆ ≤ B ∧
    ∃ C : Subgroup (puAmalgam hTM).Universal, ⁅A, Qv (puAmalgam hTM) δ⁆ ⊔ B ≤ C ∧ C ≤ A ∧
      ⁅C, stab (puAmalgam hTM) δ⁆ ≤ ⁅A, Qv (puAmalgam hTM) δ⁆ ⊔ B ∧
      (⁅A, stab (puAmalgam hTM) δ⁆ ⊔ B) ⊔ C = A ∧
      (⁅A, stab (puAmalgam hTM) δ⁆ ⊔ B) ⊓ C = ⁅A, Qv (puAmalgam hTM) δ⁆ ⊔ B ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (ψ : ↥(stab (puAmalgam hTM) δ) →* ↥(StatedSL 3 F)),
        Fintype.card F = q ∧ Function.Surjective ψ ∧
        IsSumOfNaturalModulesVia (stab (puAmalgam hTM) δ) (⁅A, stab (puAmalgam hTM) δ⁆ ⊔ B)
          (⁅A, Qv (puAmalgam hTM) δ⁆ ⊔ B) ψ false 1

@[expose] def Concl441 (α γ : Vtx (puAmalgam hTM)) : Prop :=
  ¬ ⁅ZM (puAmalgam hTM) α, Qv (puAmalgam hTM) γ⁆ ≤ Dloc hTM L γ →
    ⁅conjCl (stab (puAmalgam hTM) γ) (ZM (puAmalgam hTM) α),
        Qv (puAmalgam hTM) α ⊓ Qv (puAmalgam hTM) γ⁆ ≤ Dloc hTM L γ ∧
      ∀ x ∈ Qv (puAmalgam hTM) γ,
        ¬ ⁅conjCl (stab (puAmalgam hTM) γ) (ZM (puAmalgam hTM) α), Subgroup.zpowers x⁆ ≤
          Dloc hTM L γ →
        ZM (puAmalgam hTM) γ ≤
          ⁅Subgroup.zpowers x, conjCl (stab (puAmalgam hTM) γ) (ZM (puAmalgam hTM) α)⁆ ⊔
            Dloc hTM L γ

@[expose] def Concl444 (α α' : Vtx (puAmalgam hTM)) : Prop :=
  ∀ γ : Vtx (puAmalgam hTM), (puAmalgam hTM).treeGraph.Adj α γ →
    ¬ ZM (puAmalgam hTM) α' ≤
        Subgroup.normalizer (Usup (puAmalgam hTM) α γ : Set (puAmalgam hTM).Universal) →
      ∃ t ∈ stab (puAmalgam hTM) α,
        (Usup (puAmalgam hTM) α (geo (puAmalgam hTM) α α' 1)).map (MulAut.conj t).toMonoidHom =
            Usup (puAmalgam hTM) α γ ∧
          ¬ (ZM (puAmalgam hTM) (geo (puAmalgam hTM) α α' 2)).map (MulAut.conj t).toMonoidHom ≤
            Qv (puAmalgam hTM) (geo (puAmalgam hTM) α' α 2)

end PUNotation

section Items

@[expose] def S39 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    critDist (puAmalgam h.le) = 4 → IsSL3Full M T L →
    ∀ α : Vtx (puAmalgam h.le), IsMVtx _ α → ⁅Vv _ α, Vv _ α⁆ ≤ centerOf (Vv _ α)

@[expose] def S41 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G), PUHyp M T L → IsSL3Full M T L →
    M = L ⊔ pCoreOf 2 M ∧ Zq M L ≤ Subgroup.centralizer (M : Set G) ∧ Xq M = Z0q M T ∧
      ⁅Z0q M T, M⁆ = Uq M T L

@[expose] def S42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) →
    ∀ (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)),
    IsSL3FullVia M T L φ →
    ∀ α β : Vtx (puAmalgam h.le), IsMVtx _ α → (puAmalgam h.le).treeGraph.Adj α β →
      ((∀ δ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj β δ →
            Usup _ δ β ≤ Bloc h.le L α) →
          Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ^ 2 →
          Usup (puAmalgam h.le) α β ≤ ZH _ β) ∧
        ∀ Y : Subgroup (puAmalgam h.le).Universal,
          stab _ α ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal) → Y ≤ Qv _ α →
          ⁅Vcirc h.le L α, Y⁆ ≤ Dloc h.le L α → ⁅Vv _ α, Y⁆ ≤ Dloc h.le L α

@[expose] def S43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) → IsSL3Full M T L →
    ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      ¬ Vv _ α ≤ Qv _ (geo _ α' α 2)

@[expose] def S44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    4 < critDist (puAmalgam h.le) →
    ∀ (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)),
    IsSL3FullVia M T L φ →
      critDist (puAmalgam h.le) = 8 ∧
      (∀ α β : Vtx (puAmalgam h.le), IsMVtx _ α → (puAmalgam h.le).treeGraph.Adj α β →
        IsC1 h.le L (Fintype.card F) α (Vv _ α) (ZM _ α) ∧
          ⁅Vv _ α, Qv _ α⁆ ≤ stabCenter _ α ∧
          (ZH _ β).relIndex (ZM _ α) = Fintype.card F ∧
          (Qv _ α).relIndex (Qv _ β) = Fintype.card F ^ 2) ∧
      (∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
        Concl441 h.le L α (geo _ α α' 2)) ∧
      (∃ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' ∧
        IsStraight (puAmalgam h.le) α α') ∧
      ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
        IsStraight (puAmalgam h.le) α α' → Concl444 h.le α α'

end Items

end CFSG.Quasithin.MS93

module

public import CFSG.Quasithin.MS93.SkItems
public import CFSG.Quasithin.MS93.MSPBasic

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S5

section General

variable {Γ : Type*} [Group Γ]

@[expose] def rconj (g : Γ) (K : Subgroup Γ) : Subgroup Γ := K.map (MulAut.conj g⁻¹).toMonoidHom

@[expose] def OneNoncentral (H N V Z : Subgroup Γ) : Prop :=
  ¬ ⁅V, N⁆ ≤ Z ∧ ∀ A B C : Subgroup Γ, Z ≤ A → A ≤ B → B ≤ C → C ≤ V →
    H ≤ Subgroup.normalizer (A : Set Γ) → H ≤ Subgroup.normalizer (B : Set Γ) →
    H ≤ Subgroup.normalizer (C : Set Γ) → ⁅B, N⁆ ≤ A ∨ ⁅C, N⁆ ≤ B

end General

section Vertex

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def nclStab (δ : Vtx X) (K : Subgroup X.Universal) : Subgroup X.Universal :=
  ⨆ g : ↥(stab X δ), K.map (MulAut.conj (g : X.Universal)).toMonoidHom

@[expose] def IsHatTriple (α α' : Vtx X) (t₁ t₂ t₃ : X.Universal) : Prop :=
  t₁ ∈ Qv X (geo X α' α 1) ∧ t₂ ∈ Qv X (geo X α' α 1) ∧ t₃ ∈ Qv X (geo X α' α 1) ∧
    (Subgroup.centralizer ({t₁} : Set X.Universal)).relIndex (ZM X α') = 2 ∧
    (Subgroup.centralizer ({t₂} : Set X.Universal)).relIndex (ZM X α') = 2 ∧
    (Subgroup.centralizer ({t₃} : Set X.Universal)).relIndex (ZM X α') = 2 ∧
    t₁ * t₂⁻¹ ∉ Qv X α' ∧
    ZM X α ⊔ Qv X α' = Subgroup.closure ({t₁, t₂} : Set X.Universal) ⊔ Qv X α' ∧
    Qv X (geo X α' α 1) ⊓ Subgroup.centralizer (critR X α α' : Set X.Universal) ⊔ Qv X α' =
      Subgroup.closure ({t₁, t₂, t₃} : Set X.Universal) ⊔ Qv X α'

@[expose] def zHat (α α' : Vtx X) : Subgroup X.Universal :=
  ZM X α' ⊓ ⨅ (t : X.Universal × X.Universal × X.Universal)
    (_ : IsHatTriple X α α' t.1 t.2.1 t.2.2)
    (_ : t.2.2 ∉ Subgroup.closure ({t.1, t.2.1} : Set X.Universal) ⊔ Qv X α'),
    Subgroup.centralizer ({t.2.2} : Set X.Universal)

variable {X} in
theorem zHat_le_centralizer {α α' : Vtx X} {t₁ t₂ t₃ : X.Universal}
    (ht : IsHatTriple X α α' t₁ t₂ t₃)
    (hn : t₃ ∉ Subgroup.closure ({t₁, t₂} : Set X.Universal) ⊔ Qv X α') :
    zHat X α α' ≤ Subgroup.centralizer ({t₃} : Set X.Universal) :=
  inf_le_right.trans ((iInf₂_le (⟨t₁, t₂, t₃⟩ : _ × _ × _) ht).trans (iInf_le _ hn))

variable {X} in
theorem IsHatTriple.not_mem_of_not_le {α α' : Vtx X} {t₁ t₂ t₃ : X.Universal}
    (ht : IsHatTriple X α α' t₁ t₂ t₃) {Y : Subgroup X.Universal}
    (hY : Y ≤ Qv X (geo X α' α 1) ⊓ Subgroup.centralizer (critR X α α' : Set X.Universal))
    (hYn : ¬ Y ≤ Subgroup.closure ({t₁, t₂} : Set X.Universal) ⊔ Qv X α') :
    t₃ ∉ Subgroup.closure ({t₁, t₂} : Set X.Universal) ⊔ Qv X α' := by
  intro h3
  refine hYn (hY.trans (le_sup_left.trans (ht.2.2.2.2.2.2.2.2.le.trans (sup_le ?_ le_sup_right))))
  rw [Subgroup.closure_le]
  rintro t (rfl | rfl | rfl)
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  · exact h3

end Vertex

section PU

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

@[expose] def vPre {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F))
    (Y : Subgroup ↥(StatedSp 2 F)) : Subgroup (puAmalgam hTM).Universal :=
  (Y.comap a).map (puAmalgam hTM).ofA

@[expose] def vIm {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F))
    (K : Subgroup (puAmalgam hTM).Universal) : Subgroup ↥(StatedSp 2 F) :=
  (K.comap (puAmalgam hTM).ofA).map a

variable (L : Subgroup G)

@[expose] def uSub (δ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  ⁅ZM (puAmalgam hTM) δ, puTrans hTM L δ⁆

@[expose] def dSub (δ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  Qv (puAmalgam hTM) δ ⊓
    Subgroup.centralizer (puTrans hTM L δ : Set (puAmalgam hTM).Universal)

@[expose] def voSub (δ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  ⁅Vv (puAmalgam hTM) δ, puTrans hTM L δ⁆

@[expose] def bSub (δ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  Subgroup.closure {v | v ∈ Vv (puAmalgam hTM) δ ∧
    ∀ y ∈ puTrans hTM L δ, ⁅v, y⁆ ∈ ZM (puAmalgam hTM) δ}

@[expose] def IsOffCand (q : ℕ) (γ ε : Vtx (puAmalgam hTM))
    (E : Subgroup (puAmalgam hTM).Universal) : Prop :=
  E ≤ Qv (puAmalgam hTM) ε ∧
    (Subgroup.centralizer (E : Set (puAmalgam hTM).Universal)).relIndex (uSub hTM L γ) ≤
      (Qv (puAmalgam hTM) γ).relIndex E ∧
    (Subgroup.centralizer (E : Set (puAmalgam hTM).Universal)).relIndex (uSub hTM L γ) ≤ q ^ 2

@[expose] def offSet (q : ℕ) (γ ε : Vtx (puAmalgam hTM)) :
    Set (Subgroup (puAmalgam hTM).Universal) :=
  {E | IsOffCand hTM L q γ ε E ∧
    ∀ E' : Subgroup (puAmalgam hTM).Universal, IsOffCand hTM L q γ ε E' →
      Nat.card E' ≤ Nat.card E}

@[expose] def jOff (q : ℕ) (γ ε : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  ⨆ E ∈ offSet hTM L q γ ε, E

end PU

section Data

variable {G : Type} [Group G]

@[expose] def IsSp4Data (M T L : Subgroup G) (k : ℕ) (F : Type) [Field F] [Fintype F]
    (a : ↥M →* ↥(StatedSp 2 F)) : Prop :=
  1 ≤ k ∧ Fintype.card F = 2 ^ k ∧ Function.Surjective a ∧
    IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a false 1

theorem isSp4Full_iff {M T L : Subgroup G} :
    IsSp4Full M T L ↔ ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
      (a : ↥M →* ↥(StatedSp 2 F)), IsSp4Data M T L k F a := by
  constructor
  · rintro ⟨k, F, _, _, a, hk, hF, ha, hnat⟩
    exact ⟨k, F, _, _, a, hk, hF, ha, hnat⟩
  · rintro ⟨k, F, _, _, a, hk, hF, ha, hnat⟩
    exact ⟨k, F, _, _, a, hk, hF, ha, hnat⟩

@[expose] def Sp4Lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G), PUHyp M T L →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      IsSp4Data M T L k F a →
      Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 ^ k ∧
      Uq M T L ⊓ Subgroup.centralizer (L : Set G) =
        Uq M T L ⊓ Subgroup.centralizer (M : Set G) ∧
      ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
        m * u * m⁻¹ = u

end Data

section Lambda

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] def Concl55 (h : PUHyp M T L) (q : ℕ) (α' δ : Vtx (puAmalgam h.le))
    (g x : (puAmalgam h.le).Universal) : Prop :=
  (Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ⊔ S5.zHat _ (baseA _) α' = stab _ (baseA _) ∧
      S5.rconj x (Qv _ (g⁻¹ • baseB (puAmalgam h.le))) ⊔ ZM _ α' = stab _ (baseA _)) ∧
    (ZH _ (baseB _) ⊓ Subgroup.centralizer
        (S5.jOff h.le L q (baseA _) (g⁻¹ • baseB (puAmalgam h.le)) :
          Set (puAmalgam h.le).Universal) ≤
        stabCenter _ (baseA _) ∧
      ZH _ (baseB _) ⊓ Subgroup.centralizer
        (S5.rconj x (S5.jOff h.le L q (baseA _) (g⁻¹ • baseB (puAmalgam h.le))) :
          Set (puAmalgam h.le).Universal) ≤
        stabCenter _ (baseA _)) ∧
    (puTrans h.le L (baseA _) ≤
        (S5.jOff h.le L q (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) ⊔ S5.zHat _ (baseA _) α') ⊓
        (S5.rconj x (S5.jOff h.le L q (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le))) ⊔
          S5.zHat _ (baseA _) α') ∨
      (Qv _ (baseA _) ≤ S5.jOff h.le L q δ (baseB _) ∧
        (Qv _ (baseA _)).relIndex
            (S5.jOff h.le L q δ (baseB _) ⊓ S5.jOff h.le L q (baseA _) (baseB _)) ≤ q ^ 2 ∧
        XM _ (baseA _) ≠
          S5.uSub h.le L (baseA _) ⊔ XM _ (baseA _) ⊓
            Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal)))

@[expose] def Concl56 (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F))
    (α' : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F)) (g x : (puAmalgam h.le).Universal) :
    Prop :=
  (∀ E₁ E₂ : Subgroup (puAmalgam h.le).Universal, IsPGroup 2 E₁ → IsPGroup 2 E₂ →
      E₁ ≤ S5.rconj g (S5.vPre h.le a (MSP.qLine l)) → E₂ ≤ S5.vPre h.le a (MSP.qLine l) →
      q ^ 2 < (Qv _ (baseA _)).relIndex E₁ → q ^ 2 < (Qv _ (baseA _)).relIndex E₂ →
      E₁ ⊔ E₂ ⊔ Qv _ (baseA _) = stab _ (baseA _)) ∧
    ZM _ (baseA _) ⊓
        Subgroup.centralizer (S5.rconj g (S5.vPre h.le a (MSP.qLine l)) :
          Set (puAmalgam h.le).Universal) ⊓
        Subgroup.centralizer (S5.rconj (g * x) (S5.vPre h.le a (MSP.qLine l)) :
          Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (baseA _) ∧
    puTrans h.le L (baseA _) ≤
      S5.rconj g (S5.jOff h.le L q (baseA _) (baseB _)) ⊔ S5.zHat _ (baseA _) α' ⊔
        S5.rconj x⁻¹ (S5.zHat _ (baseA _) α') ∧
    ((Qv _ α').relIndex (ZM _ (baseA _)) = q → x ∈ S5.vPre h.le a (MSP.stab l))

@[expose] def Case56 (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F))
    (δ : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F)) : Prop :=
  S5.jOff h.le L q δ (baseB _) = S5.jOff h.le L q (baseA _) (baseB _) ∧ MSP.IsLine l ∧
    Qv _ (baseB _) ≤ S5.vPre h.le a (MSP.stab l) ∧
    S5.jOff h.le L q (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)

@[expose] def lam (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F))
    (α' δ : Vtx (puAmalgam h.le)) : Set (Vtx (puAmalgam h.le)) :=
  {μ | ∃ g x : (puAmalgam h.le).Universal, g ∈ stab _ (baseA _) ∧
    x ∈ puTrans h.le L (baseA _) ∧
    (((∀ l, ¬ Case56 h q a δ l) ∧ Concl55 h q α' δ g x) ∨
      (∃ l, Case56 h q a δ l ∧ Concl56 h q a α' l g x)) ∧
    (μ = g⁻¹ • δ ∨ μ = x⁻¹ • (g⁻¹ • δ))}

@[expose] def lamAll (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F))
    (α' : Vtx (puAmalgam h.le)) : Set (Vtx (puAmalgam h.le)) :=
  {μ | ∃ δ, (puAmalgam h.le).treeGraph.Adj (baseB _) δ ∧
    ¬ S5.uSub h.le L δ ≤ S5.bSub h.le L (baseA _) ∧ μ ∈ lam h q a α' δ}

end Lambda

end S5

section Items

@[expose] def S51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ E₁ E₂ : Subgroup (puAmalgam h.le).Universal,
        E₁ ≤ Qv _ (baseB _) → E₂ ≤ Qv _ (baseB _) →
        (Qv _ (baseA _)).relIndex E₁ = 2 ^ k →
        (Subgroup.centralizer (E₁ : Set (puAmalgam h.le).Universal)).relIndex
          (S5.uSub h.le L (baseA _)) = 2 ^ k →
        (Qv _ (baseA _)).relIndex E₂ = 2 ^ k →
        (Subgroup.centralizer (E₂ : Set (puAmalgam h.le).Universal)).relIndex
          (S5.uSub h.le L (baseA _)) = 2 ^ k →
        S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≠ E₁ ⊔ E₂

@[expose] def S52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
        ((2 ^ k) ^ 2 ≤ (Qv _ α').relIndex (ZM _ (baseA _)) →
          S5.OneNoncentral (stab _ (baseA _)) (puTrans h.le L (baseA _)) (Vv _ (baseA _))
            (ZM _ (baseA _))) ∧
        ⁅Vv (puAmalgam h.le) (baseA _), Qv (puAmalgam h.le) (baseA _)⁆ ≤
          centerOf (Vv (puAmalgam h.le) (baseA _)) ∧
        ⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆ ≤
          XM (puAmalgam h.le) (baseA _) ∧
        ⁅⁅XM (puAmalgam h.le) α' ⊓ Qv (puAmalgam h.le) (baseA _),
            Vv (puAmalgam h.le) (baseA _) ⊓ Qv (puAmalgam h.le) (geo _ α' (baseA _) 2)⁆,
          Vv (puAmalgam h.le) (baseA _) ⊓ Qv (puAmalgam h.le) (geo _ α' (baseA _) 2)⁆ = ⊥

@[expose] def S53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      XM _ (baseA _) ⊓
          Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) :
            Set (puAmalgam h.le).Universal) ≤
        S5.uSub h.le L (baseA _) ⊔ S5.dSub h.le L (baseA _)

@[expose] def S54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      (Nat.card (S5.offSet h.le L (2 ^ k) (baseA _) (baseB _)) = 1 ∧
          (∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
            Qv _ (baseB _) ≤ S5.vPre h.le a (MSP.stab l) ∧
            S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)) ∧
          (2 ^ k) ^ 2 ≤ (Qv _ (baseA _)).relIndex (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _))) ∨
        (Nat.card (S5.offSet h.le L (2 ^ k) (baseA _) (baseB _)) = 2 ^ k + 1 ∧
          S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) = Qv _ (baseB _) ∧
          ∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧
            S5.vIm h.le a (Qv _ (baseB _)) = MSP.qPoint p)

@[expose] def S55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
        geo _ (baseA _) α' 1 = baseB _ →
        ∀ δ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
          (S5.jOff h.le L (2 ^ k) δ (baseB _) ≠ S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ∨
            ∀ l : Submodule F (MSP.V4 F), MSP.IsLine l →
              Qv _ (baseB _) ≤ S5.vPre h.le a (MSP.stab l) →
              ¬ S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)) →
          ∃ g ∈ stab _ (baseA _), ∃ x ∈ puTrans h.le L (baseA _),
            S5.Concl55 h (2 ^ k) α' δ g x

@[expose] def S56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
        geo _ (baseA _) α' 1 = baseB _ →
        ∀ l : Submodule F (MSP.V4 F), MSP.IsLine l →
          Qv _ (baseB _) ≤ S5.vPre h.le a (MSP.stab l) →
          S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l) →
          ∃ g ∈ stab _ (baseA _), ∃ x ∈ puTrans h.le L (baseA _),
            S5.Concl56 h (2 ^ k) a α' l g x

end Items

end CFSG.Quasithin.MS93

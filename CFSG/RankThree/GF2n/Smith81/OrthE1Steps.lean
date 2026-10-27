module

public import CFSG.RankThree.GF2n.Smith81.OrthLaneA
public import CFSG.RankThree.GF2n.Smith81.OrthNoA2E1

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

structure QSpace (K : Type) [Field K] where
  E : Type
  [acg : AddCommGroup E]
  [mod : Module K E]
  [fin : Module.Finite K E]
  B : LinearMap.BilinForm K E
  Qf : E → K
  alt : ∀ e, B e e = 0
  nondeg : ∀ e, (∀ f, B e f = 0) → e = 0
  Qf_smul : ∀ (a : K) e, Qf (a • e) = a ^ 2 * Qf e
  Qf_add : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f

attribute [instance] QSpace.acg QSpace.mod QSpace.fin

abbrev QSpace.ofModel {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) : QSpace K where
  E := M₀.E
  B := M₀.B
  Qf := M₀.Qf
  alt := M₀.alt
  nondeg := M₀.nondeg
  Qf_smul := M₀.Qf_smul
  Qf_add := M₀.Qf_add

section QSpaceDefs

variable {K : Type} [Field K] (S : QSpace K)

@[expose] def QSpace.O : Subgroup (S.E ≃ₗ[K] S.E) where
  carrier := {g | ∀ e, S.Qf (g e) = S.Qf e}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb e => by
    change S.Qf (a (b e)) = S.Qf e
    rw [ha, hb]
  inv_mem' := fun {a} ha e => by
    have h := ha (a.symm e)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

@[expose] def QSpace.Ω : Subgroup (S.E ≃ₗ[K] S.E) := ⁅S.O, S.O⁆

@[expose] def QSpace.IsTS (V : Submodule K S.E) : Prop := ∀ e ∈ V, S.Qf e = 0

@[expose] def QSpace.IsHyp : Prop :=
  ∃ S₁ S₂ : Submodule K S.E, IsCompl S₁ S₂ ∧ S.IsTS S₁ ∧ S.IsTS S₂

@[expose] def QSpace.P (V : Submodule K S.E) : Subgroup (S.E ≃ₗ[K] S.E) where
  carrier := {g | g ∈ S.O ∧ ∀ v, v ∈ V ↔ g v ∈ V}
  one_mem' := ⟨S.O.one_mem, fun _ => Iff.rfl⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨S.O.mul_mem ha.1 hb.1, fun v => (hb.2 v).trans (ha.2 (b v))⟩
  inv_mem' := fun {a} ha =>
    ⟨S.O.inv_mem ha.1, fun v => by
      have h := ha.2 (a.symm v)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm⟩

@[expose] def QSpace.U (V : Submodule K S.E) : Subgroup (S.E ≃ₗ[K] S.E) where
  carrier := {g | g ∈ S.O ∧ ∀ v ∈ V, g v = v}
  one_mem' := ⟨S.O.one_mem, fun _ _ => rfl⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨S.O.mul_mem ha.1 hb.1, fun v hv => by
      change a (b v) = v
      rw [hb.2 v hv, ha.2 v hv]⟩
  inv_mem' := fun {a} ha =>
    ⟨S.O.inv_mem ha.1, fun v hv => by
      change a.symm v = v
      rw [LinearEquiv.symm_apply_eq]
      exact (ha.2 v hv).symm⟩

@[expose] def QSpace.Cent (X : Set (S.E ≃ₗ[K] S.E)) : Subgroup (S.E ≃ₗ[K] S.E) :=
  S.O ⊓ Subgroup.centralizer X

end QSpaceDefs

section ModelDefs

variable {G : Type} [Group G]

structure ActionModel (M Q Z : Subgroup G) where
  K : Type
  [field : Field K]
  [fin : Finite K]
  [charTwo : CharP K 2]
  γ : G → K
  M₀ : Tim79.QuadModel Q Z K γ
  glob : GlobalModelData M Q Z γ M₀
  φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)
  φ_π : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
    M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)
  φ_ker : ∀ m : ↥(H0 M Z), φ m = 1 ↔ (m : G) ∈ Q
  φ_Qf : ∀ (m : ↥(H0 M Z)) e, M₀.Qf (φ m e) = M₀.Qf e

attribute [instance] ActionModel.field ActionModel.fin ActionModel.charTwo

structure E1Hyp (M Q Z B : Subgroup G) (t : G) : Prop where
  ctx : Ctx M Q Z B
  mem : t ∈ LB M Q B
  notQ : t ∉ Q
  cent : CentTrivial M Q Z (Lgen M (LB M Q B))
  case : CaseE1 M Q Z B t
  noA2 : NoA2 Q Z (LB M Q B)
  gen : GenByB M Q B

@[expose] def E1Xpre (M Q B : Subgroup G) (t : G) : Subgroup G :=
  ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ ⊔ Q

end ModelDefs

section ModelAPI

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {t : G}

theorem E1Hyp.sec (h : E1Hyp M Q Z B t) : Sec5Hyp h.ctx 4 t :=
  ⟨h.case.width, by norm_num, h.noA2, h.gen, h.mem, h.notQ⟩

theorem ActionModel.nonempty (H : StrothHyp M Q Z) : Nonempty (ActionModel M Q Z) := by
  obtain ⟨K, _, _, _, γ, M₀, h⟩ := stroth_globalModelData H
  obtain ⟨φ, h1, h2, h3⟩ := exists_actionHom_H0 H h
  exact ⟨⟨K, γ, M₀, h, φ, h1, h2, h3⟩⟩

namespace ActionModel

variable (AM : ActionModel M Q Z)

abbrev S : QSpace AM.K := QSpace.ofModel AM.M₀

@[expose] def Vsp (hc : Ctx M Q Z B) (t : G) : Submodule AM.K AM.M₀.E :=
  imgSub AM.M₀ (Vt M (LB M Q B) B Z t) (fun c _ he => hc.smul_mem_img_Vt AM.glob t c he)

@[expose] def actImage (S : Subgroup G) : Subgroup (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) :=
  (S.subgroupOf (H0 M Z)).map AM.φ

end ActionModel

end ModelAPI

section KFacts

@[expose] def polarFn {V K : Type} [Add V] [Sub K] [Add K] (f : V → K) (x y : V) : K := f (x + y) - f x - f y

@[expose] def polarGram {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (f : (ι → K) → K) :
    Matrix ι ι K :=
  Matrix.of fun i j => polarFn f (Pi.single i 1) (Pi.single j 1)

structure BetaProps {K : Type} [Field K] (S : QSpace K) (V : Submodule K S.E)
    (β : S.E →ₗ[K] S.E) : Prop where
  range : ∀ e, β e ∈ V
  ker : ∀ e, β e = 0 → e ∈ V
  kills : ∀ v ∈ V, β v = 0
  alt : ∀ e, S.B e (β e) = 0

@[expose] def ParabolicStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
  ∀ (S : QSpace K), Module.finrank K S.E = 8 → S.IsHyp →
  ∀ (V : Submodule K S.E), S.IsTS V → Module.finrank K V = 4 →
    (∀ e, (∀ v ∈ V, S.B e v = 0) → e ∈ V) ∧
    (∃ V' : Submodule K S.E, IsCompl V V' ∧ S.IsTS V') ∧
    (∀ g : S.E ≃ₗ[K] S.E, g ∈ S.U V ↔
      ∃ β : S.E →ₗ[K] S.E, (∀ e, β e ∈ V) ∧ (∀ v ∈ V, β v = 0) ∧ (∀ e, S.B e (β e) = 0) ∧
        ∀ e, g e = e + β e) ∧
    (∀ β : S.E →ₗ[K] S.E, (∀ e, β e ∈ V) → (∀ v ∈ V, β v = 0) → (∀ e, S.B e (β e) = 0) →
      ∃ g ∈ S.U V, ∀ e, g e = e + β e)

@[expose] def ActsAsNatural {K : Type} [Field K] (S : QSpace K) (V : Submodule K S.E)
    (Xg : Subgroup (S.E ≃ₗ[K] S.E)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ↥V ≃ₗ[K] (ι → K)) (f : (ι → K) → K) : Prop :=
  ∃ hX : ∀ g ∈ Xg, ∀ v ∈ V, g v ∈ V,
    (∀ (g : S.E ≃ₗ[K] S.E) (hg : g ∈ Xg), ∃ A ∈ StatedOmega f, ∀ (v : S.E) (hv : v ∈ V),
      c ⟨g v, hX g hg v hv⟩ = (A : Matrix ι ι K) *ᵥ c ⟨v, hv⟩) ∧
    (∀ A ∈ StatedOmega f, ∃ (g : S.E ≃ₗ[K] S.E) (hg : g ∈ Xg), ∀ (v : S.E) (hv : v ∈ V),
      c ⟨g v, hX g hg v hv⟩ = (A : Matrix ι ι K) *ᵥ c ⟨v, hv⟩) ∧
    (∀ g ∈ Xg, (∀ v ∈ V, g v = v) → g = 1)

@[expose] def NatIrredFor {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (f : (ι → K) → K) : Prop :=
  (∀ A : Matrix ι ι K, (∀ g ∈ StatedOmega f, A * (g : Matrix ι ι K) = (g : Matrix ι ι K) * A) →
      ∃ c : K, A = c • (1 : Matrix ι ι K)) ∧
  (∀ b : Matrix ι ι K, (∀ g ∈ StatedOmega f, (g : Matrix ι ι K)ᵀ * b * (g : Matrix ι ι K) = b) →
      ∃ c : K, b = c • polarGram f)

@[expose] def ForBothSigns (P : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K],
    ((ι → K) → K) → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    P (Fin 2 ⊕ Fin 2) K (StatedQuadPlus 2 K) ∧
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        P (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K (StatedQuadMinus 2 K b c)

@[expose] def NatIrredStatement : Prop := ForBothSigns fun _ _ _ K _ f => NatIrredFor K f

@[expose] def NormalizerOmegaFor {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (f : (ι → K) → K) : Prop :=
  ∀ A : GL ι K, (∀ g ∈ StatedOmega f, A * g * A⁻¹ ∈ StatedOmega f) →
    ∃ c : K, c ≠ 0 ∧ ∀ v, f (c • ((A : Matrix ι ι K) *ᵥ v)) = f v

@[expose] def NormalizerOmegaStatement : Prop :=
  ForBothSigns fun _ _ _ K _ f => NormalizerOmegaFor K f

@[expose] def DicksonNatFor {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (f : (ι → K) → K) : Prop :=
  ∀ A : GL ι K, (∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v) → A * A = 1 →
    (A ∈ StatedOmega f ↔ Even ((A : Matrix ι ι K) - 1).rank)

@[expose] def DicksonNatStatement : Prop := ForBothSigns fun _ _ _ K _ f => DicksonNatFor K f

@[expose] def DicksonSpaceStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
  ∀ (S : QSpace K), Module.finrank K S.E = 8 → S.IsHyp →
  ∀ (V : Submodule K S.E), S.IsTS V → Module.finrank K V = 4 →
    S.P V ≤ S.Ω ∧
    ∀ g ∈ S.Ω, Even (Module.finrank K ↥(V ⊓ V.map (g : S.E →ₗ[K] S.E)))

@[expose] def SL2RootStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (P₁ P₂ : Sylow 2 ↥(StatedSL 2 K)),
    P₁ ≠ P₂ → (P₁ : Subgroup ↥(StatedSL 2 K)) ⊔ (P₂ : Subgroup ↥(StatedSL 2 K)) = ⊤

@[expose] def ListNoPerfectOutStatement : Prop :=
  ∀ (D : Type) [Group D] [Finite D], ListGroup D → IsSimpleGroup D →
    ∀ P : Subgroup (MulAut D), ⁅P, P⁆ = P → P ≤ (MulAut.conj : D →* MulAut D).range

@[expose] def H1TensorStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ c : ↥(StatedSL 2 K) → Matrix (Fin 2) (Fin 2) K,
      (∀ g h : ↥(StatedSL 2 K), c (g * h) =
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * c h +
          c g * ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) →
      ∃ m : Matrix (Fin 2) (Fin 2) K, ∀ g : ↥(StatedSL 2 K),
        c g = ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * m -
          m * ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

@[expose] def sympPair (n : ℕ) (K : Type) [Field K] (v w : Fin n ⊕ Fin n → K) : K :=
  v ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w)

@[expose] def leviSL2 (K : Type) [Field K] : Subgroup ↥(StatedSp 2 K) :=
  Subgroup.closure {g | ∃ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 ∧
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ}

@[expose] def Sp4InvolutionStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ g : ↥(StatedSp 2 K), g * g = 1 →
      (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1).rank = 2 →
      (∃ v : Fin 2 ⊕ Fin 2 → K,
        sympPair 2 K v
          (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) ≠ 0) →
      IsPGroup 2 ↥(Subgroup.centralizer ({g} : Set ↥(StatedSp 2 K)))

@[expose] def WalterList (D : Type) [Group D] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel D .PSL 2 2 f) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧
    StatedClassicalModel D .PSL 2 p f) ∨
  (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel D .twistedG2 3 f) ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic D .J1

@[expose] def Omega4BasicFor {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (f : (ι → K) → K) : Prop :=
  ⁅StatedOmega f, StatedOmega f⁆ = StatedOmega f ∧ Subgroup.center ↥(StatedOmega f) = ⊥ ∧
    ∀ P : Sylow 2 ↥(StatedOmega f), Nat.card P = Nat.card K ^ 2

@[expose] def Omega4BasicStatement : Prop := ForBothSigns fun _ _ _ K _ f => Omega4BasicFor K f

@[expose] def OmegaLineStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    (∃ F₁ F₂ : Subgroup (GL (Fin 2 ⊕ Fin 2) K),
      F₁ ⊔ F₂ = StatedOmega (StatedQuadPlus 2 K) ∧ F₁ ⊓ F₂ = ⊥ ∧
      (∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a) ∧
      IsSLModel 2 (Nat.card K) ↥F₁ ∧ IsSLModel 2 (Nat.card K) ↥F₂ ∧
      ∀ A : Subgroup (GL (Fin 2 ⊕ Fin 2) K), A ≤ StatedOmega (StatedQuadPlus 2 K) →
        IsPGroup 2 A → Nat.card A = Nat.card K →
        (∃ Γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, Γ ≠ 0 ∧
          ∀ c : K, ∃ a ∈ A, ((a : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) - 1 = c • Γ) →
        A ≤ F₁ ∨ A ≤ F₂) ∧
    ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ A : Subgroup (GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K),
        A ≤ StatedOmega (StatedQuadMinus 2 K b c) → IsPGroup 2 A → Nat.card A = Nat.card K →
        (∃ Γ : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K,
          Γ ≠ 0 ∧ ∀ c' : K, ∃ a ∈ A,
            ((a : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) : Matrix _ _ K) - 1 = c' • Γ) → False

end KFacts

section LemmaC

@[expose] def LemmaCConclusion {K : Type} [Field K] (S : QSpace K) (V : Submodule K S.E)
    (Xg : Subgroup (S.E ≃ₗ[K] S.E)) : Prop :=
  ∃ β : S.E →ₗ[K] S.E, BetaProps S V β ∧ (∀ x ∈ Xg, ∀ e, x (β e) = β (x e)) ∧
    (∀ c : K, ∃ g ∈ S.Cent (Xg : Set (S.E ≃ₗ[K] S.E)), ∀ e, g e = e + c • β e) ∧
    ((∀ g ∈ S.Cent (Xg : Set (S.E ≃ₗ[K] S.E)), ∃ c : K, ∀ e, g e = e + c • β e) ∨
      Nonempty (↥(StatedSL 2 K) ≃* ↥(S.Cent (Xg : Set (S.E ≃ₗ[K] S.E)))))

@[expose] def LemmaCStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
  ∀ (S : QSpace K), Module.finrank K S.E = 8 → S.IsHyp →
  ∀ (V : Submodule K S.E), S.IsTS V → Module.finrank K V = 4 →
  ∀ (Xg : Subgroup (S.E ≃ₗ[K] S.E)), Xg ≤ S.O →
    (∀ c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K), ActsAsNatural S V Xg c (StatedQuadPlus 2 K) →
      LemmaCConclusion S V Xg) ∧
    (∀ (b c' : K), (∀ s : K, s ^ 2 + b * s + c' ≠ 0) →
      ∀ c : ↥V ≃ₗ[K] (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
        ActsAsNatural S V Xg c (StatedQuadMinus 2 K b c') → LemmaCConclusion S V Xg)

end LemmaC

section Steps

@[expose] def E1Ct {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) (t : G) :
    Subgroup G :=
  CommQ hc.hyp.Q_normal.2 t ⊓ H0 M Z

@[expose] def Step1Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G) (hH : E1Hyp M Q Z B t)
    (AM : ActionModel M Q Z),
    Module.finrank AM.K AM.M₀.E = 8 ∧ AM.S.IsHyp ∧ AM.S.IsTS (AM.Vsp hH.ctx t) ∧
      Module.finrank AM.K (AM.Vsp hH.ctx t) = 4

@[expose] def NtCentralStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ r ∈ Rt M (LB M Q B) t, ∀ n ∈ Nt M (LB M Q B) t, ⁅r, n⁆ ∈ Q

@[expose] def NtLineStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G) (hH : E1Hyp M Q Z B t)
    (AM : ActionModel M Q Z),
    ∃ β : AM.M₀.E →ₗ[AM.K] AM.M₀.E, BetaProps AM.S (AM.Vsp hH.ctx t) β ∧
      (∀ r : ↥(H0 M Z), (r : G) ∈ Rt M (LB M Q B) t → ∀ e, AM.φ r (β e) = β (AM.φ r e)) ∧
      (∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t → ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e) ∧
      (∀ c : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧
        ∀ e, AM.φ x e = e + c • β e)

@[expose] def NtTIStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ g ∈ H0 M Z, Nt M (LB M Q B) t ⊓ conjSubgroup g (Nt M (LB M Q B) t) = Q ∨
      conjSubgroup g (Nt M (LB M Q B) t) = Nt M (LB M Q B) t

@[expose] def TMemNtStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    t ∈ Nt M (LB M Q B) t

@[expose] def RtSplitStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    Nt M (LB M Q B) t ≤ LB M Q B ∧
    Nt M (LB M Q B) t ⊓ E1Xpre M Q B t = Q ∧
    Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t ∧
    (∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t, r * x * r⁻¹ ∈ E1Xpre M Q B t) ∧
    ⁅E1Xpre M Q B t, E1Xpre M Q B t⁆ ⊔ Q = E1Xpre M Q B t ∧
    LB M Q B = Nt M (LB M Q B) t ⊔ (LB M Q B ⊓ E1Xpre M Q B t) ∧
    Nat.card ↥(LB M Q B ⊓ E1Xpre M Q B t) = Nat.card Q * Nat.card Z ^ 2 ∧
    (CaseE1Plus M Q Z B t → QuotSat (E1Xpre M Q B t) Q (IsOmegaPlus 2 (Nat.card Z))) ∧
    (CaseE1Minus M Q Z B t → QuotSat (E1Xpre M Q B t) Q (IsOmegaMinus 2 (Nat.card Z)))

@[expose] def CtNormalizesStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ c ∈ M, ⁅c, t⁆ ∈ Q →
      conjSubgroup c (Rt M (LB M Q B) t) = Rt M (LB M Q B) t ∧
      conjSubgroup c (Nt M (LB M Q B) t) = Nt M (LB M Q B) t ∧
      conjSubgroup c (E1Xpre M Q B t) = E1Xpre M Q B t

@[expose] def CtStructureStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G) (hH : E1Hyp M Q Z B t),
    Rt M (LB M Q B) t ≤ E1Ct hH.ctx t ∧
    (Rt M (LB M Q B) t).relIndex (E1Ct hH.ctx t) ≤ 2 ∧
    ∀ P : Subgroup G, Q ≤ P → P ≤ E1Ct hH.ctx t → ⁅P, P⁆ ⊔ Q = P → P ≤ E1Xpre M Q B t

@[expose] def NtConjLBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ g ∈ Lgen M (LB M Q B), conjSubgroup g (Nt M (LB M Q B) t) ≤ LB M Q B →
      ∃ h ∈ Lgen M (LB M Q B), h ∈ Subgroup.normalizer (LB M Q B : Set G) ∧
        conjSubgroup g (Nt M (LB M Q B) t) = conjSubgroup h (Nt M (LB M Q B) t)

@[expose] def TheoremRStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    (∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ E1Xpre M Q B t, s * x * s⁻¹ ∈ E1Xpre M Q B t) →
    ∃ Y : Subgroup G, Q ≤ Y ∧ Y ≤ Lgen M (LB M Q B) ∧
      (∀ s ∈ Lgen M (LB M Q B), ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) ∧
      Y ⊓ E1Xpre M Q B t = Q ∧ Y ⊔ E1Xpre M Q B t = Lgen M (LB M Q B) ∧
      (∀ y ∈ Y, ∀ x ∈ E1Xpre M Q B t, ⁅y, x⁆ ∈ Q) ∧ QuotSat Y Q (IsSLModel 2 (Nat.card Z))

@[expose] def XNormalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ E1Xpre M Q B t, s * x * s⁻¹ ∈ E1Xpre M Q B t

end Steps

section P1Defs

variable {G : Type} [Group G]

@[expose] def E1CaseA (M Q B : Subgroup G) (t : G) : Prop :=
  ∀ g ∈ Lgen M (LB M Q B), conjSubgroup g (Nt M (LB M Q B) t) ≤ LB M Q B →
    conjSubgroup g (Nt M (LB M Q B) t) = Nt M (LB M Q B) t

@[expose] def E1Dpre (M Q B : Subgroup G) (t : G) : Subgroup G :=
  ⨆ g ∈ Lgen M (LB M Q B), conjSubgroup g (Nt M (LB M Q B) t)

@[expose] def E1CaseBHyp (M Q B : Subgroup G) (t g : G) : Prop :=
  g ∈ Lgen M (LB M Q B) ∧ g ∈ Subgroup.normalizer (LB M Q B : Set G) ∧
    conjSubgroup g (Nt M (LB M Q B) t) ≤ LB M Q B ∧
    conjSubgroup g (Nt M (LB M Q B) t) ≠ Nt M (LB M Q B) t

@[expose] def TwoFactors (Q X F₁ F₂ : Subgroup G) (q : ℕ) : Prop :=
  Q ≤ F₁ ∧ Q ≤ F₂ ∧ F₁ ≤ X ∧ F₂ ≤ X ∧ F₁ ⊔ F₂ = X ∧ F₁ ⊓ F₂ = Q ∧
    (∀ a ∈ F₁, ∀ b ∈ F₂, ⁅a, b⁆ ∈ Q) ∧ QuotSat F₁ Q (IsSLModel 2 q) ∧ QuotSat F₂ Q (IsSLModel 2 q)

@[expose] def Syl2Pre (M Q B S₁ : Subgroup G) : Prop :=
  Q ≤ S₁ ∧ S₁ ≤ Lgen M (LB M Q B) ∧ QuotSat S₁ Q (fun W _ => IsPGroup 2 W) ∧
    ¬ 2 ∣ S₁.relIndex (Lgen M (LB M Q B))

structure E1CaseBData (M Q Z B : Subgroup G) (t : G) where
  g : G
  hg : E1CaseBHyp M Q B t g
  Fb : Subgroup G
  Fc : Subgroup G
  Y : Subgroup G
  two : TwoFactors Q (E1Xpre M Q B t) Fb Fc (Nat.card Z)
  two' : TwoFactors Q (conjSubgroup g (E1Xpre M Q B t)) Y Fc (Nat.card Z)
  N_le_Y : Nt M (LB M Q B) t ≤ Y
  N'_le_Fb : conjSubgroup g (Nt M (LB M Q B) t) ≤ Fb
  YFb : Y ⊓ Fb = Q ∧ ∀ a ∈ Y, ∀ b ∈ Fb, ⁅a, b⁆ ∈ Q

end P1Defs

section Tensor3

abbrev Tensor3 (K : Type) := Fin 2 → Fin 2 → Fin 2 → K

variable {K : Type} [Field K]

@[expose] def tensor3Form (T : Tensor3 K) : K :=
  T 0 0 0 * T 1 1 1 + T 0 0 1 * T 1 1 0 + T 0 1 0 * T 1 0 1 + T 0 1 1 * T 1 0 0

@[expose] def tensor3Act0 (A : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) : Tensor3 K :=
  fun a b c => ∑ a', A a a' * T a' b c

@[expose] def tensor3Act1 (A : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) : Tensor3 K :=
  fun a b c => ∑ b', A b b' * T a b' c

@[expose] def tensor3Act2 (A : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) : Tensor3 K :=
  fun a b c => ∑ c', A c c' * T a b c'

end Tensor3

section P1Statements

@[expose] def FactorAct {G : Type} [Group G] {M Q Z : Subgroup G} (AM : ActionModel M Q Z)
    (θ : AM.M₀.E ≃ₗ[AM.K] Tensor3 AM.K) (F : Subgroup G)
    (act : Matrix (Fin 2) (Fin 2) AM.K → Tensor3 AM.K → Tensor3 AM.K) : Prop :=
  (∀ x : ↥(H0 M Z), (x : G) ∈ F → ∃ A : Matrix (Fin 2) (Fin 2) AM.K, A.det = 1 ∧
      ∀ e, θ (AM.φ x e) = act A (θ e)) ∧
  (∀ A : Matrix (Fin 2) (Fin 2) AM.K, A.det = 1 → ∃ x : ↥(H0 M Z), (x : G) ∈ F ∧
      ∀ e, θ (AM.φ x e) = act A (θ e))

@[expose] def M1FittingTrivialStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ A : Subgroup G, Q ≤ A → A ≤ Lgen M (LB M Q B) →
      (∀ s ∈ Lgen M (LB M Q B), conjSubgroup s A = A) →
      QuotSat A Q (fun W _ => Group.IsNilpotent W) → A = Q

@[expose] def NtElemAbelianStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    (∀ x ∈ Nt M (LB M Q B) t, ∀ y ∈ Nt M (LB M Q B) t, ⁅x, y⁆ ∈ Q) ∧
      ∀ x ∈ Nt M (LB M Q B) t, x ^ 2 ∈ Q

@[expose] def CaseA1Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    E1CaseA M Q B t → ∀ g ∈ Lgen M (LB M Q B),
      ((∀ x ∈ Nt M (LB M Q B) t, ∀ y ∈ conjSubgroup g (Nt M (LB M Q B) t), ⁅x, y⁆ ∈ Q) ↔
        conjSubgroup g (Nt M (LB M Q B) t) = Nt M (LB M Q B) t)

@[expose] def CaseA2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    E1CaseA M Q B t → QuotSat (E1Dpre M Q B t) Q (fun W _ => IsSimpleGroup W ∧ ListGroup W)

@[expose] def CaseA3Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    E1CaseA M Q B t → ∀ d ∈ E1Dpre M Q B t, ∀ x ∈ E1Xpre M Q B t, ⁅d, x⁆ ∈ Q

@[expose] def CaseA4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    (∀ d ∈ E1Dpre M Q B t, ∀ x ∈ E1Xpre M Q B t, ⁅d, x⁆ ∈ Q) →
      ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ E1Xpre M Q B t, s * x * s⁻¹ ∈ E1Xpre M Q B t

@[expose] def B1Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ g : G, E1CaseBHyp M Q B t g →
      (CaseE1Minus M Q Z B t → False) ∧
      (CaseE1Plus M Q Z B t → ∃ Fb Fc : Subgroup G,
        TwoFactors Q (E1Xpre M Q B t) Fb Fc (Nat.card Z) ∧
          conjSubgroup g (Nt M (LB M Q B) t) ≤ Nt M (LB M Q B) t ⊔ Fb)

@[expose] def B2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ g : G, E1CaseBHyp M Q B t g → CaseE1Plus M Q Z B t →
      ∀ Fb Fc : Subgroup G, TwoFactors Q (E1Xpre M Q B t) Fb Fc (Nat.card Z) →
        conjSubgroup g (Nt M (LB M Q B) t) ≤ Nt M (LB M Q B) t ⊔ Fb →
        ∃ Y : Subgroup G, TwoFactors Q (conjSubgroup g (E1Xpre M Q B t)) Y Fc (Nat.card Z)

@[expose] def TripleStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ AM : ActionModel M Q Z, ∀ g : G, E1CaseBHyp M Q B t g → CaseE1Plus M Q Z B t →
      ∀ Fb Fc Y : Subgroup G, TwoFactors Q (E1Xpre M Q B t) Fb Fc (Nat.card Z) →
        conjSubgroup g (Nt M (LB M Q B) t) ≤ Nt M (LB M Q B) t ⊔ Fb →
        TwoFactors Q (conjSubgroup g (E1Xpre M Q B t)) Y Fc (Nat.card Z) →
        (∃ θ : AM.M₀.E ≃ₗ[AM.K] Tensor3 AM.K, (∀ e, AM.M₀.Qf e = tensor3Form (θ e)) ∧
          FactorAct AM θ Y tensor3Act0 ∧ FactorAct AM θ Fb tensor3Act1 ∧
          FactorAct AM θ Fc tensor3Act2) ∧
        Nt M (LB M Q B) t ≤ Y ∧ conjSubgroup g (Nt M (LB M Q B) t) ≤ Fb ∧ Y ⊓ Fb = Q ∧
          ∀ a ∈ Y, ∀ b ∈ Fb, ⁅a, b⁆ ∈ Q

@[expose] def CaseBDataStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    (∃ g : G, E1CaseBHyp M Q B t g) → Nonempty (E1CaseBData M Q Z B t)

@[expose] def B6Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ D : E1CaseBData M Q Z B t,
      LB M Q B ≤ D.Y ⊔ D.Fb ⊔ D.Fc ∧ D.Y ⊔ D.Fb ⊔ D.Fc ≤ Lgen M (LB M Q B) ∧
      (∀ n ∈ Lgen M (LB M Q B), n ∈ Subgroup.normalizer (LB M Q B : Set G) →
        conjSubgroup n (D.Y ⊔ D.Fb ⊔ D.Fc) = D.Y ⊔ D.Fb ⊔ D.Fc) ∧
      ∃ S₁ : Subgroup G, Syl2Pre M Q B S₁ ∧ LB M Q B ≤ S₁ ∧ (LB M Q B).relIndex S₁ ≤ 2

@[expose] def B7aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    Nonempty (E1CaseBData M Q Z B t) →
      ⁅Lgen M (LB M Q B), Lgen M (LB M Q B)⁆ ⊔ Q = Lgen M (LB M Q B)

@[expose] def B7bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ _D : E1CaseBData M Q Z B t, ∀ S₁ : Subgroup G, Syl2Pre M Q B S₁ → LB M Q B ≤ S₁ →
      (LB M Q B).relIndex S₁ ≤ 2 → S₁ ≠ LB M Q B →
      ∃ j ∈ S₁, j ∉ LB M Q B ∧ j * j ∈ Q ∧ ∀ h ∈ Lgen M (LB M Q B), h * j * h⁻¹ ∉ LB M Q B

@[expose] def B7cStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ⁅Lgen M (LB M Q B), Lgen M (LB M Q B)⁆ ⊔ Q = Lgen M (LB M Q B) →
    ∀ S₁ : Subgroup G, Syl2Pre M Q B S₁ → LB M Q B ≤ S₁ → (LB M Q B).relIndex S₁ ≤ 2 →
      (∃ j ∈ S₁, j ∉ LB M Q B ∧ j * j ∈ Q ∧
        ∀ h ∈ Lgen M (LB M Q B), h * j * h⁻¹ ∉ LB M Q B) → False

@[expose] def B8Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    E1CaseBData M Q Z B t → Syl2Pre M Q B (LB M Q B) → False

@[expose] def CaseBFalseStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    ∀ g : G, E1CaseBHyp M Q B t g → False

end P1Statements

section Glue

theorem E1Xpre_le_Lgen {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) : E1Xpre M Q B t ≤ Lgen M (LB M Q B) := by
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  refine (sup_le (Subgroup.commutator_le.mpr fun a ha b hb => ?_) hQR).trans
    (Rt_le_Lgen M (LB M Q B) t)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem caseA_holds (hN : NtConjLBStatement) (hB : CaseBFalseStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
      E1CaseA M Q B t := by
  intro G _ _ M Q Z B t hH g hg hle
  by_contra hne
  obtain ⟨h, hh, hhn, hgh⟩ := hN G M Q Z B t hH g hg hle
  exact hB G M Q Z B t hH h ⟨hh, hhn, by rw [← hgh]; exact hle, by rw [← hgh]; exact hne⟩

theorem xNormal_of (hN : NtConjLBStatement) (hB : CaseBFalseStatement)
    (hA3 : CaseA3Statement) (hA4 : CaseA4Statement) : XNormalStatement := by
  intro G _ _ M Q Z B t hH
  exact hA4 G M Q Z B t hH (hA3 G M Q Z B t hH (caseA_holds hN hB G M Q Z B t hH))

theorem caseBData_of_steps (hB1 : B1Statement) (hB2 : B2Statement) (hT : TripleStatement) :
    CaseBDataStatement := by
  intro G _ _ M Q Z B t hH ⟨g, hg⟩
  have h1 := hB1 G M Q Z B t hH g hg
  have hplus : CaseE1Plus M Q Z B t := by
    rcases (caseE1_iff M Q Z B t).mp hH.case with h | h
    · exact h
    · exact (h1.1 h).elim
  obtain ⟨Fb, Fc, hFF, hN'⟩ := h1.2 hplus
  obtain ⟨Y, hY⟩ := hB2 G M Q Z B t hH g hg hplus Fb Fc hFF hN'
  obtain ⟨AM⟩ := ActionModel.nonempty hH.ctx.hyp
  obtain ⟨-, hNY, hN'Fb, hYFb1, hYFb2⟩ :=
    hT G M Q Z B t hH AM g hg hplus Fb Fc Y hFF hN' hY
  exact ⟨⟨g, hg, Fb, Fc, Y, hFF, hY, hNY, hN'Fb, hYFb1, hYFb2⟩⟩

theorem caseBFalse_of_steps (hD : CaseBDataStatement) (hB6 : B6Statement) (hB7a : B7aStatement)
    (hB7b : B7bStatement) (hB7c : B7cStatement) (hB8 : B8Statement) : CaseBFalseStatement := by
  intro G _ _ M Q Z B t hH g hg
  obtain ⟨D⟩ := hD G M Q Z B t hH ⟨g, hg⟩
  obtain ⟨-, -, -, S₁, hS, hLS, hidx⟩ := hB6 G M Q Z B t hH D
  have hperf := hB7a G M Q Z B t hH ⟨D⟩
  by_cases hEq : S₁ = LB M Q B
  · subst hEq
    exact hB8 G M Q Z B t hH D hS
  · exact hB7c G M Q Z B t hH hperf S₁ hS hLS hidx
      (hB7b G M Q Z B t hH D S₁ hS hLS hidx hEq)

end Glue

section Assembly

theorem exists_mul_of_sup_of_le_normalizer' {G : Type} [Group G] {Y X : Subgroup G}
    (h : Y ≤ Subgroup.normalizer (X : Set G)) {s : G} (hs : s ∈ Y ⊔ X) :
    ∃ y ∈ Y, ∃ x ∈ X, s = y * x := by
  let T : Subgroup G :=
    { carrier := {s | ∃ y ∈ Y, ∃ x ∈ X, s = y * x}
      one_mem' := ⟨1, Y.one_mem, 1, X.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨y, hy, x, hx, rfl⟩ ⟨y', hy', x', hx', rfl⟩
        refine ⟨y * y', Y.mul_mem hy hy', (y'⁻¹ * x * y') * x', ?_, by group⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp (h (Y.inv_mem hy')) x).mp hx
        simp only [inv_inv] at h1
        exact X.mul_mem h1 hx'
      inv_mem' := by
        rintro _ ⟨y, hy, x, hx, rfl⟩
        refine ⟨y⁻¹, Y.inv_mem hy, y * x⁻¹ * y⁻¹, ?_, by group⟩
        exact (Subgroup.mem_normalizer_iff.mp (h hy) x⁻¹).mp (X.inv_mem hx) }
  have hYT : Y ≤ T := fun y hy => ⟨y, hy, 1, X.one_mem, (mul_one y).symm⟩
  have hXT : X ≤ T := fun x hx => ⟨1, Y.one_mem, x, hx, (one_mul x).symm⟩
  exact (sup_le hYT hXT) hs

theorem internalProd_holds :
    ∀ (G : Type) [Group G] (S Y X Q : Subgroup G) (P₁ P₂ : ∀ (W : Type) [Group W], Prop),
      S ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Y → Q ≤ X → Y ≤ S → X ≤ S → Y ⊓ X = Q →
      Y ⊔ X = S → (∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ Q) → QuotSat Y Q P₁ → QuotSat X Q P₂ →
        QuotSat S Q (IsProdOf P₁ P₂) := by
  intro G _ S Y X Q P₁ P₂ hQS hQY hQX hYS hXS hYX hsup hcomm hY hX
  obtain ⟨hNY, hP₁⟩ := hY
  obtain ⟨hNX, hP₂⟩ := hX
  haveI hNS : (Q.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQS
  haveI := hNY
  haveI := hNX
  refine ⟨hNS, ↥Y ⧸ Q.subgroupOf Y, ↥X ⧸ Q.subgroupOf X, inferInstance, inferInstance, hP₁, hP₂,
    ?_⟩
  let iY : (↥Y ⧸ Q.subgroupOf Y) →* (↥S ⧸ Q.subgroupOf S) :=
    QuotientGroup.map (Q.subgroupOf Y) (Q.subgroupOf S) (Subgroup.inclusion hYS)
      (fun y hy => by simpa [Subgroup.mem_subgroupOf] using hy)
  let iX : (↥X ⧸ Q.subgroupOf X) →* (↥S ⧸ Q.subgroupOf S) :=
    QuotientGroup.map (Q.subgroupOf X) (Q.subgroupOf S) (Subgroup.inclusion hXS)
      (fun x hx => by simpa [Subgroup.mem_subgroupOf] using hx)
  have hc : ∀ (a : ↥Y ⧸ Q.subgroupOf Y) (b : ↥X ⧸ Q.subgroupOf X), Commute (iY a) (iX b) := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H y =>
      induction b using QuotientGroup.induction_on with
      | H x =>
        show iY (↑y) * iX (↑x) = iX (↑x) * iY (↑y)
        simp only [iY, iX, QuotientGroup.map_mk]
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have h1 := hcomm (y : G)⁻¹ (Y.inv_mem y.2) (x : G)⁻¹ (X.inv_mem x.2)
        have h2 := Q.inv_mem h1
        have e : ((y : G) * x)⁻¹ * ((x : G) * y) = (⁅(y : G)⁻¹, (x : G)⁻¹⁆)⁻¹ := by
          simp only [commutatorElement_def]
          group
        show ((y : G) * (x : G))⁻¹ * ((x : G) * (y : G)) ∈ Q
        rw [e]
        exact h2
  let Φ : (↥Y ⧸ Q.subgroupOf Y) × (↥X ⧸ Q.subgroupOf X) →* (↥S ⧸ Q.subgroupOf S) :=
    MonoidHom.noncommCoprod iY iX hc
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    induction a using QuotientGroup.induction_on with
    | H y =>
      induction b using QuotientGroup.induction_on with
      | H x =>
        have h1 : iY ↑y * iX ↑x = 1 := hab
        simp only [iY, iX, QuotientGroup.map_mk] at h1
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
        have h2 : ((y : G) * (x : G)) ∈ Q := h1
        have hyX : (y : G) ∈ X := by
          have := X.mul_mem (hQX h2) (X.inv_mem x.2)
          simpa using this
        have hyQ : (y : G) ∈ Q := by
          have : (y : G) ∈ Y ⊓ X := ⟨y.2, hyX⟩
          rwa [hYX] at this
        have hxQ : (x : G) ∈ Q := by
          have := Q.mul_mem (Q.inv_mem hyQ) h2
          simpa using this
        refine Prod.ext ?_ ?_
        · exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr hyQ)
        · exact (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hxQ)
  have hYX' : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X := by
    intro y hy x hx
    have h3 := hcomm y hy x hx
    have : y * x * y⁻¹ = ⁅y, x⁆ * x := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact X.mul_mem (hQX h3) hx
  have hYn : Y ≤ Subgroup.normalizer (X : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hYX' y hy x hx, fun hx => ?_⟩
    have := hYX' y⁻¹ (Y.inv_mem hy) _ hx
    simpa [mul_assoc] using this
  have hsurj : Function.Surjective Φ := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H s =>
      have hs : (s : G) ∈ Y ⊔ X := by rw [hsup]; exact s.2
      obtain ⟨y, hy, x, hx, hyx⟩ := exists_mul_of_sup_of_le_normalizer' hYn hs
      refine ⟨(↑(⟨y, hy⟩ : ↥Y), ↑(⟨x, hx⟩ : ↥X)), ?_⟩
      show iY ↑(⟨y, hy⟩ : ↥Y) * iX ↑(⟨x, hx⟩ : ↥X) = ↑s
      simp only [iY, iX, QuotientGroup.map_mk]
      rw [← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hyx.symm
  exact ⟨(MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm⟩

theorem smith23E1Lgen_of_steps (hT : OrthNoA2E1Statement) (hG : StrothGenByBStatement)
    (hS6 : RtSplitStatement) (hR : TheoremRStatement) (hP1 : XNormalStatement) :
    Smith23E1LgenStatement := by
  intro G _ _ M Q Z B t hcfg hd4
  have mk : CaseE1 M Q Z B t → E1Hyp M Q Z B t := fun hE =>
    have hno : NoA2 Q Z (LB M Q B) :=
      hT G M Q Z B t hcfg hd4 hE B hcfg.ctx.conj hcfg.ctx.le hcfg.ctx.ne
    ⟨hcfg.ctx, hd4.2.1, hd4.2.2.1, hd4.2.2.2, hE, hno,
      hG G M Q Z B hcfg.ctx 4 hE.width (by norm_num) hno⟩
  have hQN : Lgen M (LB M Q B) ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
    hcfg.ctx.hyp.Q_normal.2 (Lgen_le_H0 hcfg.ctx hs).1
  have core : ∀ (hE : CaseE1 M Q Z B t) (P₂ : ∀ (W : Type) [Group W], Prop),
      QuotSat (E1Xpre M Q B t) Q P₂ →
        QuotSat (Lgen M (LB M Q B)) Q (IsProdOf (IsSLModel 2 (Nat.card Z)) P₂) := by
    intro hE P₂ hX
    have hH := mk hE
    obtain ⟨Y, hQY, hYL, -, hYX, hsup, hcomm, hY⟩ := hR G M Q Z B t hH (hP1 G M Q Z B t hH)
    exact internalProd_holds G _ Y (E1Xpre M Q B t) Q _ P₂ hQN hQY le_sup_right hYL
      (E1Xpre_le_Lgen hcfg.ctx hd4.2.1) hYX hsup hcomm hY hX
  refine ⟨fun hE => ?_, fun hE => ?_⟩
  · have hE1 := (caseE1_iff M Q Z B t).mpr (Or.inl hE)
    obtain ⟨-, -, -, -, -, -, -, hXp, -⟩ := hS6 G M Q Z B t (mk hE1)
    exact core hE1 _ (hXp hE)
  · have hE1 := (caseE1_iff M Q Z B t).mpr (Or.inr hE)
    obtain ⟨-, -, -, -, -, -, -, -, hXm⟩ := hS6 G M Q Z B t (mk hE1)
    exact core hE1 _ (hXm hE)

end Assembly

section DAG

@[expose] def E1NaturalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G) (hH : E1Hyp M Q Z B t),
    (CaseE1Plus M Q Z B t → OmegaPlusNat hH.ctx t 2) ∧
    (CaseE1Minus M Q Z B t → OmegaMinusNat hH.ctx t 2)

@[expose] def E1NaturalKStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G) (hH : E1Hyp M Q Z B t)
    (AM : ActionModel M Q Z),
    (CaseE1Plus M Q Z B t → ∃ c : ↥(AM.Vsp hH.ctx t) ≃ₗ[AM.K] (Fin 2 ⊕ Fin 2 → AM.K),
      ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) c
        (StatedQuadPlus 2 AM.K)) ∧
    (CaseE1Minus M Q Z B t → ∃ (b c' : AM.K), (∀ s : AM.K, s ^ 2 + b * s + c' ≠ 0) ∧
      ∃ c : ↥(AM.Vsp hH.ctx t) ≃ₗ[AM.K] (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → AM.K),
        ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) c
          (StatedQuadMinus 2 AM.K b c'))

theorem phi_mul_apply {K E : Type*} [Field K] [AddCommGroup E] [Module K E] (β : E →ₗ[K] E)
    (hββ : ∀ e, β (β e) = 0) (a b : E → E) (c d : K) (ha : ∀ e, a e = e + c • β e)
    (hb : ∀ e, b e = e + d • β e) (e : E) : a (b e) = e + (c + d) • β e := by
  rw [ha, hb, map_add, map_smul, hββ]
  simp only [smul_zero, add_zero, add_smul]
  abel

theorem ntElemAbelian_of (hLine : NtLineStatement) : NtElemAbelianStatement := by
  intro G _ _ M Q Z B t hH
  obtain ⟨AM⟩ := ActionModel.nonempty hH.ctx.hyp
  obtain ⟨β, hβ, -, hN, -⟩ := hLine G M Q Z B t hH AM
  have hc := hH.ctx
  have hNH : Nt M (LB M Q B) t ≤ H0 M Z :=
    (orthE1_Nt_le_Rt M (LB M Q B) t).trans (hc.Rt_le_H0 t)
  have hββ : ∀ e, β (β e) = 0 := fun e => hβ.kills _ (hβ.range e)
  constructor
  · intro x hx y hy
    obtain ⟨c, hc'⟩ := hN ⟨x, hNH hx⟩ hx
    obtain ⟨d, hd'⟩ := hN ⟨y, hNH hy⟩ hy
    have hcomm : AM.φ ⟨x, hNH hx⟩ * AM.φ ⟨y, hNH hy⟩ = AM.φ ⟨y, hNH hy⟩ * AM.φ ⟨x, hNH hx⟩ := by
      refine LinearEquiv.ext fun e => ?_
      simp only [LinearEquiv.mul_apply]
      rw [phi_mul_apply β hββ _ _ c d hc' hd' e, phi_mul_apply β hββ _ _ d c hd' hc' e,
        add_comm c d]
    have h1 : AM.φ ⁅(⟨x, hNH hx⟩ : ↥(H0 M Z)), ⟨y, hNH hy⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    have h3 := (AM.φ_ker _).mp h1
    simpa [commutatorElement_def] using h3
  · intro x hx
    obtain ⟨c, hc'⟩ := hN ⟨x, hNH hx⟩ hx
    have h1 : AM.φ ((⟨x, hNH hx⟩ : ↥(H0 M Z)) ^ 2) = 1 := by
      rw [map_pow, pow_two]
      refine LinearEquiv.ext fun e => ?_
      rw [LinearEquiv.mul_apply, phi_mul_apply β hββ _ _ c c hc' hc' e, CharTwo.add_self_eq_zero,
        zero_smul, add_zero]
      rfl
    have h3 := (AM.φ_ker _).mp h1
    simpa using h3

theorem caseA4_of (hCt : CtStructureStatement) (hSplit : RtSplitStatement)
    (hT : TMemNtStatement) : CaseA4Statement := by
  intro G _ _ M Q Z B t hH hD s hs x hx
  have hc := hH.ctx
  have hsH : s ∈ H0 M Z := Lgen_le_H0 hc hs
  have hsM : s ∈ M := hsH.1
  have hXL : E1Xpre M Q B t ≤ Lgen M (LB M Q B) := E1Xpre_le_Lgen hc hH.mem
  obtain ⟨-, -, -, -, hperf, -⟩ := hSplit G M Q Z B t hH
  obtain ⟨-, -, hperfle⟩ := hCt G M Q Z B t hH
  have hQ : conjSubgroup s Q = Q := hc.conj_Q_eq hsM
  have hQN : ∀ q ∈ Q, s * q * s⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) q).mp hq
  have hQX : Q ≤ E1Xpre M Q B t := le_sup_right
  have hQP : Q ≤ conjSubgroup s (E1Xpre M Q B t) :=
    calc Q = conjSubgroup s Q := hQ.symm
      _ ≤ conjSubgroup s (E1Xpre M Q B t) := Subgroup.map_mono hQX
  have hPL : conjSubgroup s (E1Xpre M Q B t) ≤ Lgen M (LB M Q B) := by
    intro p hp
    have h1 : s⁻¹ * p * s ∈ E1Xpre M Q B t := mem_conjSubgroup.mp hp
    have e : p = s * (s⁻¹ * p * s) * s⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hs (hXL h1)) (inv_mem hs)
  have hdD : s⁻¹ * t * s ∈ E1Dpre M Q B t := by
    have h1 : s⁻¹ * t * s ∈ conjSubgroup s⁻¹ (Nt M (LB M Q B) t) := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hT G M Q Z B t hH
    exact (le_iSup₂_of_le s⁻¹ (inv_mem hs) le_rfl : conjSubgroup s⁻¹ (Nt M (LB M Q B) t) ≤
      E1Dpre M Q B t) h1
  have hPC : conjSubgroup s (E1Xpre M Q B t) ≤ E1Ct hc t := by
    intro p hp
    have hpL := hPL hp
    refine ⟨⟨(Lgen_le_H0 hc hpL).1, ?_⟩, Lgen_le_H0 hc hpL⟩
    have hx' : s⁻¹ * p * s ∈ E1Xpre M Q B t := mem_conjSubgroup.mp hp
    have h1 := hD _ hdD _ hx'
    have h2 := Q.inv_mem h1
    have h3 := hQN _ h2
    convert h3 using 1
    rw [← commutatorElement_inv]
    simp only [commutatorElement_def]
    group
  have hPperf : ⁅conjSubgroup s (E1Xpre M Q B t), conjSubgroup s (E1Xpre M Q B t)⁆ ⊔ Q =
      conjSubgroup s (E1Xpre M Q B t) := by
    have e : conjSubgroup s (⁅E1Xpre M Q B t, E1Xpre M Q B t⁆ ⊔ Q) =
        ⁅conjSubgroup s (E1Xpre M Q B t), conjSubgroup s (E1Xpre M Q B t)⁆ ⊔ Q := by
      unfold conjSubgroup at hQ ⊢
      rw [Subgroup.map_sup, Subgroup.map_commutator, hQ]
    rw [← e, hperf]
  have hPX := hperfle _ hQP hPC hPperf
  have hmem : s * x * s⁻¹ ∈ conjSubgroup s (E1Xpre M Q B t) := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hx
  exact hPX hmem

end DAG

end CFSG.RankThree.GF2n.Smith81.Smith23E1

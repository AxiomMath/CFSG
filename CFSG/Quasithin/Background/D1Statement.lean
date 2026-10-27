module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Internal

variable {G : Type*} [Group G]

@[expose] noncomputable def qInt [Finite G] (G₁ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    WithTop ℚ :=
  @qOf ↥V (commGroupOfElemAbelian hV) inferInstance (autOn G₁ V)

@[expose] def IsFFInt (G₁ V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  @IsFFModule ↥V (commGroupOfElemAbelian hV) (autOn G₁ V)

end Internal

@[expose] noncomputable def dualAct (W : Type*) [CommGroup W] :
    MulAut W →* MulAut (W →* Multiplicative (ZMod 2)) where
  toFun g :=
    { toFun := fun φ => φ.comp (g⁻¹ : MulAut W).toMonoidHom
      invFun := fun φ => φ.comp g.toMonoidHom
      left_inv := fun φ => by ext w; simp
      right_inv := fun φ => by ext w; simp
      map_mul' := fun φ ψ => by ext w; simp }
  map_one' := by ext φ w; simp
  map_mul' g h := by
    ext φ w
    simp [MulAut.mul_apply]

section Internal2

variable {G : Type*} [Group G]

@[expose] def IsDualFFInt (G₁ V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  @IsFFModule (↥V →* Multiplicative (ZMod 2))
    MonoidHom.instCommGroup
    ((@autOn G _ G₁ V).map (@dualAct ↥V (commGroupOfElemAbelian hV)))

@[expose] def IsNormalIn (G₂ U N : Subgroup G) : Prop :=
  N ≤ U ∧ ∀ g ∈ G₂, ∀ x ∈ N, g * x * g⁻¹ ∈ N

@[expose] def IsChiefStep (G₂ U L N : Subgroup G) : Prop :=
  IsNormalIn G₂ U N ∧ IsNormalIn G₂ U L ∧ L < N ∧
    ∀ K : Subgroup G, IsNormalIn G₂ U K → L ≤ K → K ≤ N → K = L ∨ K = N

@[expose] def IsCentralStep (G₂ L N : Subgroup G) : Prop :=
  ∀ g ∈ G₂, ∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ L

inductive IsChiefSeriesFrom (G₂ U : Subgroup G) : Subgroup G → ℕ → Prop
  | bot : IsChiefSeriesFrom G₂ U ⊥ 0
  | central {N L : Subgroup G} {n : ℕ} : IsChiefStep G₂ U L N → IsCentralStep G₂ L N →
      IsChiefSeriesFrom G₂ U L n → IsChiefSeriesFrom G₂ U N n
  | noncentral {N L : Subgroup G} {n : ℕ} : IsChiefStep G₂ U L N → ¬ IsCentralStep G₂ L N →
      IsChiefSeriesFrom G₂ U L n → IsChiefSeriesFrom G₂ U N (n + 1)

structure D11Hyp (G₁ G₂ T V M₂ : Subgroup G) : Prop where
  sylow₁ : IsSylowTwoOf T G₁
  sylow₂ : IsSylowTwoOf T G₂
  reduced : IsTwoReducedIn G₁ V
  nontrivial : V ≠ ⊥
  unique_max : IsUniqueMaxOver G₂ T M₂
  centralizer : pCoreOf 2 G₁ = T ⊓ Subgroup.centralizer (V : Set G)
  no_normal : ∀ N : Subgroup G, N ≤ pCoreOf 2 G₁ → (N.subgroupOf (G₁ ⊔ G₂)).Normal → N = ⊥

@[expose] def D15Concl [Finite G] (G₁ G₂ T V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ¬ V ≤ pCoreOf 2 G₂ ∨
  (qInt G₁ V hV ≤ 1 ∧ IsFFInt G₁ V hV) ∨
  IsDualFFInt G₁ V hV ∨
  (qInt G₁ V hV ≤ 2 ∧ (∀ x ∈ conjClosure V G₂, ∀ y ∈ conjClosure V G₂, x * y = y * x) ∧
    ∃ c : ℕ, 2 ≤ c ∧ IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) ∨
  (((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).subgroupOf G₂).Normal ∧ IsElemAbelian 2 (conjClosure V G₂) ∧
    IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1 ∧
    ⁅conjClosure V G₂, pCoreOf 2 G₂⁆ ≤ centerOf (pCoreOf 2 G₂) ∧
    pCoreOf 2 G₂ = ⁅pCoreOf 2 G₂, thompsonJ (pCoreOf 2 G₁)⁆ ∧
    thompsonJ (pCoreOf 2 G₁) = thompsonJ T)

universe u in
@[expose] def D15 : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (G₁ G₂ T V M₂ : Subgroup G) (h : D11Hyp G₁ G₂ T V M₂),
    D15Concl G₁ G₂ T V h.reduced.2.2.1

end Internal2

end CFSG.Quasithin

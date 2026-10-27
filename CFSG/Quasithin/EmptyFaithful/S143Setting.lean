module

public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S143A6Nat
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143

variable {G : Type} [Group G] [Finite G]

@[expose] def qOf (T : Subgroup G) : Subgroup G := pCoreOf 2 (mcOf T)

@[expose] def wOf (T M : Subgroup G) : Subgroup G :=
  uOfL22 T M ⊓ Subgroup.centralizer (VZ T M : Set G)

@[expose] def iTwo (T M : Subgroup G) : Subgroup G := conjClosure (uOfL22 T M) (yOfL22 T M)

@[expose] def rOf (T M : Subgroup G) : Subgroup G := pCoreOf 2 (iTwo T M)

@[expose] def kOf (T M A : Subgroup G) : Subgroup G :=
  oTwoUpper (mcOf T ⊓ Subgroup.normalizer (A : Set G)) ⊔ yOfL22 T M

@[expose] def dOf (T M : Subgroup G) : Subgroup G :=
  qOf T ⊓ Subgroup.centralizer (uOfL22 T M : Set G)

@[expose] def IsA6Block (K A : Subgroup G) : Prop :=
  oTwoUpper K = K ∧ A = pCoreOf 2 K ∧
    ∃ (φ : OTwoQuot K ≃* ↥(alternatingGroup (Fin 6))) (ψ : ↥A ≃* N6),
      ∀ (k : ↥K) (a : ↥A) (h : (k : G) * (a : G) * (k : G)⁻¹ ∈ A),
        ψ ⟨(k : G) * (a : G) * (k : G)⁻¹, h⟩ =
          n6Act ((φ (QuotientGroup.mk k) : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))
            (ψ a)

structure Concl14315 (T M : Subgroup G) : Prop where
  q8sq : IsQ8Sq ↥(uOfL22 T M)
  orth : ∃ q : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) → ZMod 2,
    IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧ IsPlusType q ∧
      Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) = 16 ∧
      (∀ (x : SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T))
        (hx : x ∈ tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)),
        ∀ u : Subgroup.normalizer (quasithinOmegaOneCenter T : Set G),
          (u : G) ∈ uOfL22 T M → secMk _ _ u = x → (q ⟨x, hx⟩ = 0 ↔ (u : G) ^ 2 = 1)) ∧
      autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
        (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) = orthogonalGroupOf q
  eSing : ∀ g ∈ yOfL22 T M, g ∉ mcOf T →
    ∀ e ∈ wOf T M ⊓ conjSubgroup (wOf T M) g, e ^ 2 = 1

@[expose] def Lemma14315 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → Concl14315 T M

structure Counter (T M : Subgroup G) (g : G) : Prop where
  hyp : Hyp1421 G T M
  h1281 : Hyp1281Two G T M (yOfL22 T M)
  notSix : ¬ SixModels G
  nonab : ¬ IsMulCommutative ↥(uOfL22 T M)
  g_mem : g ∈ yOfL22 T M
  g_nmem : g ∉ mcOf T
  c15 : Concl14315 T M

structure Concl18a (T M : Subgroup G) (g : G) : Prop where
  v_eq : VZ T M = qOf T ⊓ conjSubgroup (uOfL22 T M) g
  r_eq : rOf T M = pCoreOf 2 (yOfL22 T M)
  i2_cent : iTwo T M ⊓ Subgroup.centralizer (VZ T M : Set G) = rOf T M
  i2_sThree : Nonempty (OTwoQuot (iTwo T M) ≃* Equiv.Perm (Fin 3))
  r_fpf : ∀ x ∈ iTwo T M, orderOf x = 3 → ∀ r ∈ rOf T M, x * r * x⁻¹ = r → r = 1
  rq_index : (rOf T M ⊔ qOf T).relIndex T = 2
  rstar_card : Nat.card ↥(imageOTwoQuot (mcOf T) (rOf T M)) = 4
  u_eq : uOfL22 T M = pCoreOf 2 (oTwoUpper (mcOf T))

structure Concl18b (T M A : Subgroup G) (t : G) : Prop where
  t_mem : t ∈ T
  t_nmem : t ∉ rOf T M ⊔ qOf T
  A_elem : IsElemAbelian 2 A
  A_card : Nat.card A = 16
  A_le : A ≤ rOf T M
  r_eq_AAt : rOf T M = A ⊔ conjSubgroup A t
  card_R : Nat.card (rOf T M) = 64
  v_eq_inf : VZ T M = A ⊓ conjSubgroup A t
  maximal : ∀ B : Subgroup G, B ≤ rOf T M → IsElemAbelian 2 B → B ≤ A ∨ B ≤ conjSubgroup A t
  normal_A : iTwo T M ⊔ qOf T ≤ Subgroup.normalizer (A : Set G)

structure Concl18c (T A : Subgroup G) : Prop where
  nh_star : imageOTwoQuot (mcOf T) (mcOf T ⊓ Subgroup.normalizer (A : Set G)) =
    Subgroup.centralizer (imageOTwoQuot (mcOf T) A : Set (OTwoQuot (mcOf T)))
  nh_iso : Nonempty (↥(imageOTwoQuot (mcOf T) (mcOf T ⊓ Subgroup.normalizer (A : Set G))) ≃*
    Multiplicative (ZMod 2) × Equiv.Perm (Fin 3))

structure Concl14318 (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G) : Prop where
  a : Concl18a T M g
  b : Concl18b T M A t
  c : Concl18c T A

@[expose] def Lemma14318a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G), Counter T M g → Concl18a T M g

@[expose] def Lemma14318b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G), Counter T M g →
    Concl18a T M g → ∃ (A : Subgroup G) (t : G), Concl18b T M A t

@[expose] def Lemma14318c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl18a T M g → Concl18b T M A t → Concl18c T A

structure Concl19a (T M : Subgroup G) : Prop where
  q_eq : qOf T = uOfL22 T M ⊔ dOf T M

structure Concl19b (T M A : Subgroup G) : Prop where
  block : IsA6Block (kOf T M A) A
  centralizer_K : Subgroup.centralizer (kOf T M A : Set G) = ⊥
  normalizer_K : Subgroup.normalizer (kOf T M A : Set G) = kOf T M A ⊔ dOf T M
  D_le_D8 : ∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X)
  D_D8_iff : Nonempty (↥(dOf T M) ≃* DihedralGroup 4) ↔
    ((kOf T M A).relIndex (Subgroup.normalizer (kOf T M A : Set G)) = 4 ∧
      A < Subgroup.centralizer (A : Set G))
  normalizer_A : Subgroup.normalizer (A : Set G) = Subgroup.normalizer (kOf T M A : Set G)
  sylow_RU : IsSylowTwoOf (rOf T M ⊔ uOfL22 T M) (kOf T M A)
  splits : ∃ C : Subgroup G, C ≤ kOf T M A ∧ A ⊓ C = ⊥ ∧ A ⊔ C = kOf T M A

structure Concl14319 (T M A : Subgroup G) : Prop where
  a : Concl19a T M
  b : Concl19b T M A

@[expose] def Lemma14319Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl19a T M → Concl19b T M A

@[expose] def Lemma14320 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl14319 T M A →
      Subgroup.centralizer (A : Set G) = A

structure Concl14321 (T M : Subgroup G) : Prop where
  exists_invol : (rOf T M ⊔ uOfL22 T M).relIndex T = 2 →
    ∃ t ∈ T, t ∉ rOf T M ⊔ uOfL22 T M ∧ orderOf t = 2
  not_fused : ∀ t ∈ T, t ∉ rOf T M ⊔ qOf T → orderOf t = 2 →
    ∀ y : G, ∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 → y * z * y⁻¹ ≠ t
  fused : ∀ r ∈ rOf T M ⊔ uOfL22 T M, orderOf r = 2 →
    ∃ y : G, ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ y * z * y⁻¹ = r

@[expose] def Lemma14321Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl14319 T M A →
      Subgroup.centralizer (A : Set G) = A →
        ∀ t ∈ T, t ∉ rOf T M ⊔ qOf T → orderOf t = 2 →
          ∀ y : G, ∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 → y * z * y⁻¹ ≠ t

@[expose] def Lemma14322 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl14319 T M A →
      Subgroup.centralizer (A : Set G) = A → Concl14321 T M →
        dOf T M = quasithinOmegaOneCenter T ∧ uOfL22 T M = qOf T

end S143

end CFSG.Quasithin

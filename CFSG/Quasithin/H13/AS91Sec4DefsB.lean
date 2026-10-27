module

public import CFSG.Quasithin.H13.AS91Sec4Defs
public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin

@[expose, instance_reducible] def commGroupOfElem {G : Type*} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : CommGroup ↥E :=
  { (inferInstance : Group ↥E) with mul_comm := fun a b => hE.1.is_comm.comm a b }

@[expose] def conjNormalizer {G : Type*} [Group G] (E : Subgroup G) :
    ↥(normalizer (E : Set G)) →* MulAut ↥E where
  toFun n :=
    { toFun e := ⟨n * e * n⁻¹, (mem_normalizer_iff.mp n.2 e).mp e.2⟩
      invFun e := ⟨n⁻¹ * e * n, by
        have h := (mem_normalizer_iff.mp (inv_mem n.2) e).mp e.2
        simpa using h⟩
      left_inv e := Subtype.ext (by simp [mul_assoc])
      right_inv e := Subtype.ext (by simp [mul_assoc])
      map_mul' e f := Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext e
    simp
  map_mul' m n := by
    ext e
    simp [mul_assoc]

theorem conjNormalizer_apply {G : Type*} [Group G] (E : Subgroup G) (n : ↥(normalizer (E : Set G)))
    (e : ↥E) : ((conjNormalizer E n e : ↥E) : G) = n * e * n⁻¹ := rfl

structure Loc44 (G : Type) [Group G] [Finite G] (z : G) extends Loc43 G z where
  K : Subgroup G
  K_eq : K = ⨆ (g : G) (_ : g * z * g⁻¹ ∈ Z), (Q z).map (MulAut.conj g).toMonoidHom
  R : Subgroup G
  normalizer_eq : normalizer (Z : Set G) = K ⊔ centralizer (Z : Set G)
  K_normal : ∀ n ∈ normalizer (Z : Set G), ∀ k ∈ K, n * k * n⁻¹ ∈ K
  K_inf : K ⊓ centralizer (Z : Set G) = R
  R_eq_K : R = pCoreOf 2 K
  R_eq_S : R = pCoreOf 2 (centralizer (Z : Set G))
  K_quot : ∃ φ : ↥K →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2), Function.Surjective φ ∧
    φ.ker = R.subgroupOf K
  S_quot : ∃ φ : ↥(centralizer (Z : Set G)) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
    φ.ker = R.subgroupOf (centralizer (Z : Set G))
  card_R : Nat.card R = 2 ^ 15
  center_R : (center R).map R.subtype = Z
  comm_R : ⁅R, R⁆ = Z
  sq_R : ∀ x ∈ R, x * x ∈ Z

@[expose] def Stmt4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HypJ4 G z → Nonempty (Loc44 G z)

structure Loc46 (G : Type) [Group G] [Finite G] (z : G) extends Loc44 G z, Loc45 G z where
  E : Subgroup G
  E_eq : E = Open.thompsonSubgroup (T : Subgroup G)
  E_elem : IsElemAbelian 2 E
  card_E : Nat.card E = 2 ^ 11
  E_le : E ≤ G13
  E_normal : ∀ g ∈ G13, ∀ e ∈ E, g * e * g⁻¹ ∈ E
  card_QE : Nat.card (Q z ⊔ E : Subgroup G) = 2 ^ 17
  QE_elem : ∀ x ∈ Q z ⊔ E, ∀ y ∈ Q z ⊔ E, x * y * x⁻¹ * y⁻¹ ∈ E ∧ x * x ∈ E

@[expose] def Stmt4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HypJ4 G z → Nonempty (Loc46 G z)

structure Loc47 (G : Type) [Group G] [Finite G] (z : G) extends Loc46 G z where
  G12 : Subgroup G
  G12_eq : G12 = normalizer (Z : Set G) ⊓ normalizer (E : Set G)
  K_le : K ≤ G12
  relIndex_G12 : G12.relIndex (normalizer (Z : Set G)) = 5
  card_RE : Nat.card (R ⊔ E : Subgroup G) = 2 ^ 17
  G12_quot : ∃ φ : ↥G12 →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3),
    Function.Surjective φ ∧ φ.ker = (R ⊔ E).subgroupOf G12

@[expose] def Stmt4_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HypJ4 G z → Nonempty (Loc47 G z)

structure Loc48 (G : Type) [Group G] [Finite G] (z : G) extends Loc47 G z where
  todd : @MathieuCocode24 ↥E (commGroupOfElem E_elem) (conjNormalizer E).range ⊤ ⊥
  centralizer_E : ∀ m ∈ normalizer (E : Set G), (∀ e ∈ E, m * e = e * m) → m ∈ E
  split : ∃ C : Subgroup G, C ≤ normalizer (E : Set G) ∧ C ⊓ E = ⊥ ∧
    C ⊔ E = normalizer (E : Set G)

@[expose] def Stmt4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HypJ4 G z → Nonempty (Loc48 G z)

structure Loc49 (G : Type) [Group G] [Finite G] (z : G) extends Loc48 G z where
  quasisimple : CFSG.IsQuasisimple ↥(H z ⊓ centralizer (X : Set G))
  inv_X : ∃ t ∈ H z, t * t = 1 ∧ ∀ x ∈ X, t * x * t⁻¹ = x⁻¹

@[expose] def Stmt4_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HypJ4 G z → Nonempty (Loc49 G z)

end CFSG.Quasithin.H13.AS91

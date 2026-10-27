module

public import CFSG.RankThree.PartTwo.Sec21.Item21LateProof2119

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

section Aut

variable {G : Type} [Group G]

@[expose] def trivOnQuot (A B : Subgroup G) : Subgroup (MulAut A) where
  carrier := {φ | ∀ x : A, ((x⁻¹ * φ x : A) : G) ∈ B}
  mul_mem' := by
    intro φ ψ hφ hψ x
    have h : x⁻¹ * (φ * ψ) x = (x⁻¹ * ψ x) * ((ψ x)⁻¹ * φ (ψ x)) := by
      rw [MulAut.mul_apply]
      group
    rw [h, Subgroup.coe_mul]
    exact B.mul_mem (hψ x) (hφ (ψ x))
  one_mem' := by
    intro x
    simp
  inv_mem' := by
    intro φ hφ x
    have h : x⁻¹ * φ⁻¹ x = ((φ⁻¹ x)⁻¹ * φ (φ⁻¹ x))⁻¹ := by
      rw [MulAut.apply_inv_self]
      group
    rw [h, Subgroup.coe_inv]
    exact B.inv_mem (hφ _)

@[expose] def fixOn (A B : Subgroup G) : Subgroup (MulAut A) where
  carrier := {φ | ∀ x : A, (x : G) ∈ B → φ x = x}
  mul_mem' := by
    intro φ ψ hφ hψ x hx
    rw [MulAut.mul_apply, hψ x hx, hφ x hx]
  one_mem' := fun _ _ => rfl
  inv_mem' := by
    intro φ hφ x hx
    calc φ⁻¹ x = φ⁻¹ (φ x) := by rw [hφ x hx]
      _ = x := MulAut.inv_apply_self _ _ _

theorem mem_trivOnQuot_iff {A B : Subgroup G} {φ : MulAut A} :
    φ ∈ trivOnQuot A B ↔ ∀ x : A, ((x⁻¹ * φ x : A) : G) ∈ B :=
  Iff.rfl

theorem mem_fixOn_iff {A B : Subgroup G} {φ : MulAut A} :
    φ ∈ fixOn A B ↔ ∀ x : A, (x : G) ∈ B → φ x = x :=
  Iff.rfl

end Aut

structure Config2119End (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G)
    (L : Subgroup G) (d : G) (U₀ : Subgroup G) (a : G) (X : Subgroup G) : Prop where
  cfg : Config2119 G A E U c L
  mem_d : d ∈ A ⊓ L
  ne_one_d : d ≠ 1
  type_d : Sec4.InducesTypeOn L d 1
  normal_d : ∀ g ∈ Subgroup.normalizer (A : Set G), g * d * g⁻¹ ∈ Subgroup.zpowers d
  mem_U₀ : U₀ ∈ fourGroupsMinus E
  le_U₀ : U₀ ≤ L
  mem_a : a ∈ E ⊓ Subgroup.centralizer (U₀ : Set G)
  not_mem_a : a ∉ Subgroup.zpowers c
  mem_pair : (a, X) ∈ lThreeStarPairs A E U₀

section Conclusions

variable {G : Type} [Group G] [Finite G]

@[expose] def Concl2123 (L X : Subgroup G) (c d : G) : Prop :=
  Nonempty (lBar X ≃* lBar L) ∧ d ∈ X ∧ Sec4.InducesTypeOn X d 1 ∧ Sec4.InducesTypeOn X c 2

@[expose] def Concl2124 (A L X : Subgroup G) (d : G) : Prop :=
  starOf A X ⊔ starOf A L = trivOnQuot A (Subgroup.zpowers d)

@[expose] def IsLOf2125 (L : Subgroup G) (c d e : G) (Le : Subgroup G) : Prop :=
  Le ∈ thetaComponentsAt 3 e ∧ 3 ∣ Nat.card Le ∧
    (∀ K ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card K → K = Le) ∧ Nonempty (lBar Le ≃* lBar L) ∧
    d ∈ Le ∧ Sec4.InducesTypeOn Le d 1 ∧
    (e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d → Sec4.InducesTypeOn Le c 2)

@[expose] def IsFOf2127 (A Le F : Subgroup G) : Prop :=
  IsElemAbelian 3 F ∧ Nat.card F = 27 ∧ F ≤ A ⊔ Le ∧ A ≤ Subgroup.normalizer (F : Set G) ∧
    Nonempty (Sec4.autIn Le F ≃* QuaternionGroup 2)

@[expose] def q2127Of (A : Subgroup G) (d : G) (F : G → Subgroup G) : Subgroup G :=
  ⨆ e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}, A ⊔ F e

@[expose] def IsQOf2127 (A : Subgroup G) (d : G) (F : G → Subgroup G) : Prop :=
  CFSG.ABGLocalTools.IsSylowOf 3 (q2127Of A d F) (Subgroup.normalizer (A : Set G)) ∧
    q2127Of A d F ⊓ Subgroup.centralizer (A : Set G) = A ∧
    starOf A (q2127Of A d F) =
      trivOnQuot A (Subgroup.zpowers d) ⊓ fixOn A (Subgroup.zpowers d) ∧
    (∀ x ∈ q2127Of A d F, ∃ e ∈ A, e ∉ Subgroup.zpowers d ∧ x ∈ A ⊔ F e) ∧
    ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      Nat.card (A ⊔ F e : Subgroup G) = 81 ∧ ∀ x ∈ A ⊔ F e, x ^ 3 = 1

@[expose] def IsExtra2127 (Q : Subgroup G) : Prop :=
  IsExtraspecialPGroup 3 Q ∧ Nat.card Q = 3 ^ 5 ∧ Monoid.exponent Q = 3

@[expose] def y2128Of (Le F Q : Subgroup G) : Subgroup G :=
  (Le ⊓ Subgroup.normalizer (F : Set G)) ⊔ Q

@[expose] def Concl2128 (Le F Q : Subgroup G) : Prop :=
  y2128Of Le F Q ≤ Subgroup.normalizer (F : Set G) ∧
    Sec4.autIn (y2128Of Le F Q) F ≤ trivOnQuot F Le ∧
    Nat.card (Sec4.autIn (y2128Of Le F Q) F) = 216

end Conclusions

@[expose] def Item2123 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d

@[expose] def Item2123Field : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Config2119 G A E U₀ a X → d ∈ X →
      Sec4.InducesTypeOn X d 1 → a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d →
      Sec4.InducesTypeOn X c 2 → Nonempty (lBar X ≃* lBar L)

@[expose] def Item2124 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d

@[expose] def Item2125 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∃ Le : Subgroup G, IsLOf2125 L c d e Le

@[expose] def Item2126 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2))

@[expose] def Item2127 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ F : Subgroup G, IsFOf2127 A (Lf e) F →
          CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F) (Subgroup.centralizer ({e} : Set G))

@[expose] def Item2127Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        (∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ F : Subgroup G, IsFOf2127 A (Lf e) F →
          CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F) (Subgroup.centralizer ({e} : Set G))) →
        ∃ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) ∧
          IsQOf2127 A d F

@[expose] def Item2127QExtra : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
          IsQOf2127 A d F → IsExtra2127 (q2127Of A d F)

@[expose] def Item2128 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d →
            CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))) →
          IsQOf2127 A d F → IsExtra2127 (q2127Of A d F) →
          ∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F)

end CFSG.RankThree.PartTwo.Sec21

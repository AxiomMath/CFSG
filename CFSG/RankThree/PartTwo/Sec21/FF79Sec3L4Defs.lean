module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4In
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAFin1

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)

structure FF79Sec34UFacts {G : Type} [Group G] [Finite G] (b a : G) (J A : Subgroup G) : Prop where
  elemU : IsElemAb 3 2 (U34 b a J A)
  U_le_A : U34 b a J A ≤ A
  a_mem : a ∈ U34 b a J A
  b_nor : b ∈ Nor (U34 b a J A)
  cenU_b : U34 b a J A ⊓ Cen b = Subgroup.zpowers a
  K_cen_U : Lay (J ⊓ Cen a) ≤ CenS (U34 b a J A)
  K_cen_b : Lay (J ⊓ Cen a) ≤ Cen b
  K_nor : ∀ w : G, w ∈ Cen a ⊓ Cen b → w ∈ Nor (Lay (J ⊓ Cen a))

section GSide

variable {G : Type} [Group G]

abbrev CQ (U : Subgroup G) : Type := ↥(CenS U) ⧸ pPrimeCore 3 ↥(CenS U)

@[expose] noncomputable def cqβ (U : Subgroup G) (b : G) (hb : b ∈ Nor U) : MulAut (CQ U) :=
  pPrimeQuotMulAut ↥(CenS U) (conjAut (CenS U) b (nor_cenS_of_nor hb))

@[expose] def cqImg (U X : Subgroup G) : Subgroup (CQ U) :=
  (X.subgroupOf (CenS U)).map (QuotientGroup.mk' (pPrimeCore 3 ↥(CenS U)))

end GSide

section AP

variable {H : Type} [Group H] [Finite H]

structure FF79APData (β : MulAut H) (Z K : Subgroup H) (z₀ : H) : Prop where
  beta3 : β ^ 3 = 1
  core : pPrimeCore 3 H = ⊥
  absyl : ∃ S : Subgroup H, IsSylowOf 3 S ⊤ ∧ IsMulCommutative S
  Z_central : Z ≤ Subgroup.center H
  Z_card : Nat.card Z = 9
  z₀_mem : z₀ ∈ Z
  z₀_ord : orderOf z₀ = 3
  z₀_fix : β z₀ = z₀
  A4 : ∃ A' : Subgroup H, IsElemAb 3 4 A' ∧ Z ≤ A'
  K_a5 : Nonempty (K ≃* alternatingGroup (Fin 5))
  K_fix : ∀ k ∈ K, β k = k
  K_cen_R : ∀ y ∈ pCore 3 H, ∀ k ∈ K, y * k = k * y
  K_nor : ∀ y : H, β y = y → ∀ k ∈ K, y * k * y⁻¹ ∈ K
  no27 : ∀ T : Subgroup H, (∀ t ∈ T, β t = t) → ¬ IsElemAb 3 3 T
  no_rank2 : ∀ P T : Subgroup H, IsPGroup 2 P → P ≠ ⊥ → IsElemAb 3 2 T → T ⊓ Z = ⊥ →
    T ≤ Nor P → False
  exp3 : ∀ S : Subgroup H, IsMulCommutative S → IsPGroup 3 S → (∀ s ∈ S, β s ∈ S) →
    ∀ s ∈ S, β (β s * s⁻¹) = β s * s⁻¹ → s ^ 3 = 1
  catalog : ∀ L : Subgroup H, IsComponent L → IsSimpleGroup ↥L → InCatalog ↥L

def apFix (β : MulAut H) (L : Subgroup H) : Subgroup H :=
  L ⊓ β.toMonoidHom.eqLocus (MonoidHom.id H)

structure FF79APStruct (β : MulAut H) (K L : Subgroup H) : Prop where
  layer_eq : layer H = L
  simple : IsSimpleGroup ↥L
  nonab : ∃ x y : ↥L, x * y ≠ y * x
  β_mem : ∀ x : H, x ∈ L → β x ∈ L
  K_le : K ≤ L
  absyl : ∃ S : Subgroup H, S ≤ L ∧ IsSylowOf 3 S L ∧ IsMulCommutative S
  inv3 : ∀ t u v : H, t ∈ L → orderOf t = 2 → u ∈ L → v ∈ L → orderOf u = 3 → orderOf v = 3 →
    u * t = t * u → v * t = t * v → u * v = v * u → v ∈ Subgroup.zpowers u
  outer : ∀ e : H, e ∈ L → ¬ ∀ l ∈ L, β l = e * l * e⁻¹
  K_comp : IsComponent (K.subgroupOf (apFix β L))
  others : ∀ K' : Subgroup H, K' ≤ apFix β L → IsComponent (K'.subgroupOf (apFix β L)) →
    K' ≠ K → Nat.Coprime 3 (Nat.card K')
  catalog : InCatalog ↥L
  exp3 : ∀ S : Subgroup H, IsMulCommutative S → IsPGroup 3 S → (∀ s ∈ S, β s ∈ S) →
    ∀ s ∈ S, β (β s * s⁻¹) = β s * s⁻¹ → s ^ 3 = 1

end AP

end CFSG.RankThree.PartTwo.Sec21.FF79

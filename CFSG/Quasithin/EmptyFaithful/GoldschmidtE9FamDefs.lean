module

public import CFSG.Quasithin.EmptyFaithful.T1521SJ
public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def NrmE9Prop (S L H : Subgroup G) : Prop :=
  H ≤ Subgroup.normalizer (thompsonJ S : Set G) ∧ Odd (Nat.card H) ∧
    ∀ H₀ : Subgroup G, H₀ ≤ H → H₀.relIndex H ∣ 3 →
      (∀ v ∈ S, v ∈ Subgroup.normalizer (L : Set G) → (∀ x ∈ S ⊓ L, v * x = x * v) →
        (∀ h ∈ H₀, v * h = h * v) → ∀ l ∈ L, v * l = l * v) ∧
      (∀ x ∈ centerOf (S ⊓ L), (∀ h ∈ H₀, x * h = h * x) → x ∈ centerOf L)

@[expose] def NrmE9 (S L : Subgroup G) : Prop :=
  ∃ H : Subgroup G, H ≤ borelJoin1521 S L ∧ NrmE9Prop S L H

@[expose] def Exc5 (X S L : Subgroup G) : Prop :=
  ∀ Y : Subgroup G, Y ≤ X → Y ≤ Subgroup.normalizer (thompsonJ S : Set G) →
    Y ≤ Subgroup.normalizer (conjJoin S L : Set G) → IsPGroup 5 ↥Y →
    ((S : Set G) * (Y : Set G) = (Y : Set G) * (S : Set G)) → ⁅L, Y⁆ = ⊥

@[expose] def NoE16 (S L : Subgroup G) : Prop :=
  ∀ V Y : Subgroup G, V ≤ S → V ≤ Subgroup.normalizer (L : Set G) → IsElemAbelian 2 V →
    Nat.card ↥V = 16 → Y ≤ Subgroup.normalizer (L : Set G) → Y ≤ Subgroup.normalizer (V : Set G) →
    IsPGroup 5 ↥Y → ⁅V, Y⁆ = V → ⁅L, V⁆ ≠ ⊥ → False

@[expose] def FamE9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    ((CharTwo L ∧ ⁅L, thompsonJ S⁆ = L ∧ IsBlock2 X L ∧
        (IsAltType L 5 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)) ∨
      (IsComponentOf L X ∧ IsPGroup 2 ↥(Subgroup.center ↥L) ∧ CentralMoving1521 S L ∧
        (CompTypeA15120 L ∨ CompTypeB15120 L))) →
    NrmE9 S L ∨ Exc5 X S L ∨ NoE16 S L

@[expose] def DichE9BlockL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    ⁅L, thompsonJ S⁆ = L → CharTwo L → IsBlock2 X L → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
    NrmE9 S L ∨ Exc5 X S L

@[expose] def DichE9BlockA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    ⁅L, thompsonJ S⁆ = L → CharTwo L → IsBlock2 X L → IsAltType L 5 → Exc5 X S L

@[expose] def DichE9L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    (∃ n : ℕ, 2 ≤ n ∧ IsPSL 2 2 n ↥L) → NrmE9 S L ∨ Exc5 X S L

@[expose] def DichE9Sz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    ((∃ e : ℕ, IsSz e ↥L) ∨ IsSz 3 (↥L ⧸ CFSG.pCore 2 ↥L)) → NrmE9 S L

@[expose] def DichE9U3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    (∃ n : ℕ, 2 ≤ n ∧ IsPSU 3 2 n ↥L) → NrmE9 S L ∨ NoE16 S L

@[expose] def DichE9L3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L → CentralMoving1521 S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    ((∃ n : ℕ, 1 < n ∧ IsPSL 3 2 n ↥L) ∨ IsPSL 3 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)) →
    NrmE9 S L ∨ Exc5 X S L

@[expose] def DichE9Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    (∃ n : ℕ, 1 < n ∧ IsPSp4 2 n ↥L) → NrmE9 S L ∨ Exc5 X S L

theorem nrmE9_of_inner {S L H : Subgroup G} (hJ : thompsonJ S ≤ innerPart1521 S L)
    (hH : H ≤ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G))
    (hodd : Odd (Nat.card H))
    (hA : ∀ H₀ : Subgroup G, H₀ ≤ H → H₀.relIndex H ∣ 3 →
      (∀ v ∈ S, v ∈ Subgroup.normalizer (L : Set G) → (∀ x ∈ S ⊓ L, v * x = x * v) →
        (∀ h ∈ H₀, v * h = h * v) → ∀ l ∈ L, v * l = l * v) ∧
      (∀ x ∈ centerOf (S ⊓ L), (∀ h ∈ H₀, x * h = h * x) → x ∈ centerOf L)) :
    NrmE9 S L :=
  ⟨H, hH.trans le_conjJoin, hH.trans (borel_le_normalizer_thompsonJ_of_le hJ), hodd, hA⟩

omit [Finite G] in
theorem pow_three_mem_of_relIndex_dvd_three {H H₀ : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hidx : H₀.relIndex H ∣ 3) :
    ∀ h ∈ H, h ^ 3 ∈ H₀ := by
  intro h hh
  let _ : CommGroup ↥H := { (inferInstance : Group ↥H) with
    mul_comm := fun a b => Subtype.ext (hcomm _ a.2 _ b.2) }
  have hN : (H₀.subgroupOf H).Normal := Subgroup.normal_of_isMulCommutative _
  have hcard : Nat.card (↥H ⧸ H₀.subgroupOf H) ∣ 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  obtain ⟨k, hk⟩ := hcard
  have h1 : (QuotientGroup.mk (⟨h, hh⟩ : ↥H) : ↥H ⧸ H₀.subgroupOf H) ^ 3 = 1 := by
    rw [hk, pow_mul, pow_card_eq_one', one_pow]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

end CFSG.Quasithin.E9

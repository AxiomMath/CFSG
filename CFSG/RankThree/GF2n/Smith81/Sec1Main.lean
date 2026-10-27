module

public import CFSG.RankThree.GF2n.Smith81.Sec1Four
public import CFSG.RankThree.GF2n.Smith81.Sec1Width1

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Proved

variable [Finite G] {M Q Z X B : Subgroup G} {x : G}

theorem smith_1_12 (hs : Sit M Q Z X x) : Post12 M Q Z X := by
  rcases lt_or_eq_of_le hs.hyp.q4 with h | h
  · exact smith_1_12_of_gt4 hs h
  · exact smith_1_12_four hs h.symm

theorem smith_1_13 (hs : Sit M Q Z X x) :
    ⁅Kx Q X, Lx M X⁆ ≤ Q ⊓ QB X ∧
    Kx Q X ≤ Subgroup.centralizer ((Q ⊓ QB X : Subgroup G) : Set G) ∧
    Lx M X ≤ Subgroup.centralizer ((Q ⊓ QB X : Subgroup G) : Set G) ∧
    Q ⊓ QB X ≤ Q ⊓ Subgroup.centralizer ({x} : Set G) ∧
    ∀ d ∈ Q ⊓ QB X, ∀ y ∈ Q ⊓ Subgroup.centralizer ({x} : Set G), d * y = y * d :=
  smith_1_13_of_post12 hs (smith_1_12 hs)

theorem smith_1_16 (hs : Sit M Q Z X x) {b : G} (hb : b ∈ Jx Q X x) (hb1 : b ≠ 1) :
    ∃ (g z : G), z ∈ Z ∧ b = g * (x * z) * g⁻¹ :=
  smith_1_16_of_post12 hs (smith_1_12 hs) hb hb1

theorem smith_1_12_of_width_one (H : StrothHyp M Q Z) (hw : Width Q Z 1) :
    ∀ g z : G, z ∈ Z → z ≠ 1 → g * z * g⁻¹ ∈ M → g * z * g⁻¹ ∈ Q := by
  intro g z hz hz1 hM
  by_contra hQ
  have hs := Sit.of_conj H hz hz1 hM hQ
  exact smith_1_12_n1 hs (smith_1_12 hs) hw

end Proved

@[expose] def Smith117Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B → ∀ n : ℕ,
    Width Q Z n → 3 ≤ n → (∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B')) →
    (∀ B' : Subgroup G, Ctx M Q Z B' →
      CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G)) →
    ∀ a ∈ Q, a ∉ Z → ∀ b ∈ Q, b ∉ Z → ∀ g : G, g * a * g⁻¹ = b →
      ∃ m ∈ M, m * a * m⁻¹ = b

end CFSG.RankThree.GF2n.Smith81


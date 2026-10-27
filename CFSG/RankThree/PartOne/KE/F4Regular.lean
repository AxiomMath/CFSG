module

public import CFSG.RankThree.PartOne.KE.EDualStabilizer
public import CFSG.Monster.B.Geometry.F4Weyl

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem not_dvd_card_weylGroup_F4 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ p ∣ Nat.card (WeylGroup .F4) := by
  rw [CFSG.Monster.B.Geometry.card_f4WeylGroup]
  intro h
  have h1 : p ∣ 2 ^ 7 * 3 ^ 2 := by simpa using h
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · have := hp.dvd_of_dvd_pow h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · have := hp.dvd_of_dvd_pow h2
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem F4_regular_prime_toral_centralizer (M : Type) [Field M] [Finite M] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpM : p ∣ Nat.card Mˣ) {x : ModGL Tag.F4 M}
    (hxH : x ∈ torusGroup Tag.F4 M) (hxp : orderOf x = p)
    (hreg : ∀ a : Fin Tag.F4.rank → Mˣ, x = rootDiagUnit Tag.F4 a →
      ∀ α : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 α → rootChar a α ≠ 1) :
    adjointGroup Tag.F4 M ⊓ Subgroup.centralizer {x} = torusGroup Tag.F4 M :=
  regular_prime_toral_centralizer Tag.F4 M hp (not_dvd_card_weylGroup_F4 hp hp3) hpM hxH hxp hreg

end CFSG.RankThree.PartOne.KE

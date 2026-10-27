module

public import CFSG.Permutation.UnitaryThreeRecognition.Blocks
public import CFSG.Permutation.UnitaryThreeRecognition.SMapCentral
public import CFSG.Permutation.UnitaryThreeRecognition.ZCentral

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

structure StdHyp (G : Type*) {Ω : Type*} [Group G] [MulAction G Ω] (Q : Subgroup G)
    (a b : Ω) (j s : G) (p f d : ℕ) : Prop where
  root : IsRootSubgroup Q a
  hb : b ≠ a
  htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w
  hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1
  hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁
  hj : j ∈ pairStab G a b
  hj2 : j * j = 1
  hj1 : j ≠ 1
  hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j
  hpp : p.Prime
  hp : 3 ≤ p
  hf : 1 ≤ f
  hpodd : Odd p
  hd : Odd d
  hd3 : d ≤ 3
  hQcard : Nat.card Q = p ^ (3 * f)
  hΩcard : Nat.card Ω = p ^ (3 * f) + 1
  hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1
  hsa : s • a = b
  hs2 : s * s = 1

namespace StdHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} (S : StdHyp G Q a b j s p f d)
include S

theorem hsb : s • b = a := by rw [← S.hsa, ← mul_smul, S.hs2, one_smul]

theorem q_ge : 3 ≤ p ^ f := le_trans S.hp (Nat.le_self_pow (by have := S.hf; omega) p)

theorem hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, S.hTcard.symm⟩

theorem hsj : s * j = j * s :=
  IsRootSubgroup.swap_commute_involution S.hsa S.hs2 S.hj S.hj2 S.hj1 S.hsq

variable [Finite G] [Finite Ω]

theorem card_centQ : Nat.card (centQ Q j) = p ^ f :=
  S.root.card_centQ_involution_eq S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1 S.hsq S.hpp
    S.hp S.hf S.hQcard S.hΩcard S.hTdvd

theorem centQ_commute {x : G} (hx : x ∈ Q) {z : G} (hz : z ∈ centQ Q j) : x * z = z * x :=
  S.root.centQ_commute S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1 S.hsq S.hpp S.hp S.hf
    S.hpodd S.hd S.hd3 S.hQcard S.hΩcard S.hTcard S.hsa S.hs2 hx hz

theorem mem_centQ_of_commute {t : G} (ht : t ∈ pairStab G a b) (ht1 : t ≠ 1) {u : G}
    (hu : u ∈ Q) (htu : t * u = u * t) : u ∈ centQ Q j :=
  S.root.mem_centQ_of_commute_pairStab S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1 S.hsq
    S.hpp S.hp S.hf S.hpodd S.hd S.hQcard S.hΩcard S.hTcard S.hsa S.hs2 ht ht1 hu htu

theorem swapFix_commute {w : G} (hw : w ∈ swapFix G a b s) {z : G} (hz : z ∈ centQ Q j) :
    w * z = z * w :=
  S.root.swapFix_commute_centQ S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1 S.hsq S.hpp S.hp
    S.hf S.hpodd S.hd S.hQcard S.hΩcard S.hTcard S.hsa S.hs2 hw hz

theorem block {u : G} (hu : u ∈ Q) (huZ : u ∉ centQ Q j) {w : G} (hw : w ∈ swapFix G a b s)
    (hw1 : w ≠ 1) {w' : G} (hw' : w' ∈ swapFix G a b s) (hw'1 : w' ≠ 1) :
    (sLeft Q a b s (u⁻¹ * w * u * w⁻¹))⁻¹ * sLeft Q a b s (u⁻¹ * w' * u * w'⁻¹) ∈
      centQ Q j :=
  S.root.sLeft_block S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1 S.hsq S.hpp S.hp S.hf
    S.hpodd S.hd S.hQcard S.hΩcard S.hTcard S.hsa S.hs2 hu huZ hw hw1 hw' hw'1

theorem exists_centQ_ne_one : ∃ z ∈ centQ Q j, z ≠ 1 := by
  by_contra h
  push Not at h
  have : centQ Q j ≤ ⊥ := fun z hz => h z hz
  have h1 := Subgroup.card_le_of_le this
  rw [S.card_centQ, Subgroup.card_bot] at h1
  have := S.q_ge
  omega

theorem exists_mem_not_centQ : ∃ u ∈ Q, u ∉ centQ Q j := by
  by_contra h
  push Not at h
  have : Q ≤ centQ Q j := fun u hu => h u hu
  have h1 := Subgroup.card_le_of_le this
  rw [S.card_centQ, S.hQcard] at h1
  have : p ^ f < p ^ (3 * f) := Nat.pow_lt_pow_right (by have := S.hp; omega)
    (by have := S.hf; omega)
  omega

end StdHyp

end CFSG.UnitaryThreeRecognition

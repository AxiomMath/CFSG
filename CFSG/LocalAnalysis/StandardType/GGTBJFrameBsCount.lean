module

public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.FrameBs

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem finrank_le_two_of_centralizer_count
    {G : Type} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (Θ : ((Fin r → Multiplicative (ZMod p)) ×
      ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* Bs)
    (s : (Fin r → Multiplicative (ZMod p)) →* X)
    (hΘ : ∀ f c, ((Θ (f, c) : Bs) : G) = ((s f : X) : G) * c)
    (hJX : J ≤ X) (A : Submodule (ZMod p) (Fin r → ZMod p))
    (hAnn : ∀ t : A, ∀ j ∈ J,
      ((s (fun i => Multiplicative.ofAdd ((t : Fin r → ZMod p) i)) : X) : G) * j =
        j * ((s (fun i => Multiplicative.ofAdd ((t : Fin r → ZMod p) i)) : X) : G))
    (bX : Bs) (hbX1 : bX ≠ 1) (hbXC : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcount : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    Module.finrank (ZMod p) A ≤ 2 := by
  classical
  have hp : p.Prime := Fact.out
  have hmem : ∀ f, ((s f : X) : G) ∈ Bs := by
    intro f
    have he : ((Θ (f, 1) : Bs) : G) = ((s f : X) : G) := by
      rw [hΘ]; simp
    rw [← he]
    exact (Θ (f, 1)).2
  have hcard := card_centralizer_frame Θ s hΘ hmem hJX
  let Z := Bs ⊓ Subgroup.centralizer (X : Set G)
  have hbo : orderOf (bX : G) = p :=
    orderOf_eq_prime (hBs.2 _ bX.2) (fun he => hbX1 (Subtype.ext he))
  have hdiv : p ∣ Nat.card Z := by
    simpa only [hbo] using Subgroup.orderOf_dvd_natCard Z (show (bX : G) ∈ Z from ⟨bX.2, hbXC⟩)
  have hpC : p ≤ Nat.card Z := Nat.le_of_dvd Nat.card_pos hdiv
  let U := {f : Fin r → Multiplicative (ZMod p) //
    ∀ j ∈ J, ((s f : X) : G) * j = j * ((s f : X) : G)}
  let liftAnn : A → U := fun t =>
    ⟨fun i => Multiplicative.ofAdd ((t : Fin r → ZMod p) i), hAnn t⟩
  have hAnnInj : Function.Injective liftAnn := by
    intro t u h
    apply Subtype.ext
    funext i
    exact congrArg (fun f : U => Multiplicative.toAdd (f.1 i)) h
  have hAnnCard : Nat.card A ≤ Nat.card U := Nat.card_le_card_of_injective liftAnn hAnnInj
  have hbound : p * Nat.card A ≤ p ^ 3 := by
    calc p * Nat.card A ≤ Nat.card Z * Nat.card U := Nat.mul_le_mul hpC hAnnCard
      _ = Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
        rw [Nat.mul_comm]; exact hcard.2.symm
      _ ≤ p ^ 3 := hcount
  have hcardA : p ^ Module.finrank (ZMod p) A = Nat.card A :=
    FiniteField.pow_finrank_eq_natCard p A
  have hpow : p ^ (Module.finrank (ZMod p) A + 1) ≤ p ^ 3 := by
    rw [pow_succ, hcardA, Nat.mul_comm]
    exact hbound
  have hle := (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow
  omega

end CFSG.StandardType.FrameBs

end

module

public import CFSG.Permutation.FiveTransitive.UniqueOrbitStabilizer
public import CFSG.Permutation.FiveTransitive.ThreeSwapCardLower
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.OneOrbitThreeSwapLifts

open MulAction FixedNormalizerAction

theorem exists_lifts
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (e : Fin 6 ↪ Fixed (X := X) Q)
    (B : Subgroup (Normalizer Q))
    (hmap : B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ThreeSwapTwoGroup.subgroup e)
    (hker : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (x : B)
    (hone : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x.val)) ≤ 1)
    (z : NormalizerFixedComplement.Domain (X := X) Q) (hz : x.val • z = z) :
    ∃ y w : stabilizer B z,
      toPermHom (Normalizer Q) (Fixed (X := X) Q) y.val.val = Equiv.swap (e 2) (e 3) ∧
      toPermHom (Normalizer Q) (Fixed (X := X) Q) w.val.val = Equiv.swap (e 4) (e 5) ∧
      (∀ g : stabilizer B z, g ^ 2 = 1) ∧ IsMulCommutative (stabilizer B z) ∧
      8 ∣ Nat.card (stabilizer B z) := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  have hVsq := (ThreeSwapTwoGroup.isTwoGroup e).2
  have hinv (v : V) : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using hVsq v)
  have hVcomm (v w : V) : Commute v w := by
    calc
      v * w = (v * w)⁻¹ := (hinv (v * w)).symm
      _ = w⁻¹ * v⁻¹ := mul_inv_rev _ _
      _ = w * v := by rw [hinv, hinv]
  have hsq (b : B) : (f b.val) ^ 2 = 1 :=
    congrArg Subtype.val (hVsq ⟨f b.val, hmap.le ⟨b.val, b.property, rfl⟩⟩)
  have hcomm (a b : B) : Commute (f a.val) (f b.val) :=
    congrArg Subtype.val (hVcomm
      ⟨f a.val, hmap.le ⟨a.val, a.property, rfl⟩⟩
      ⟨f b.val, hmap.le ⟨b.val, b.property, rfl⟩⟩).eq
  have hbij := UniqueOrbitStabilizer.bijective_stabilizer Q f B hker hcomm hfree x hone z hz
  have hylocal : Equiv.swap (e 2) (e 3) ∈ B.map f := hmap.ge (Subgroup.subset_closure (by simp))
  have hwlocal : Equiv.swap (e 4) (e 5) ∈ B.map f := hmap.ge (Subgroup.subset_closure (by simp))
  obtain ⟨y, hy⟩ := hbij.surjective ⟨Equiv.swap (e 2) (e 3), hylocal⟩
  obtain ⟨w, hw⟩ := hbij.surjective ⟨Equiv.swap (e 4) (e 5), hwlocal⟩
  have hdata := UniqueOrbitStabilizer.square_and_commute Q f B hker hcomm hsq hfree x hone z hz
  have hcard : Nat.card (stabilizer B z) = Nat.card (B.map f) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  have hdiv : 8 ∣ Nat.card (stabilizer B z) := by
    rw [hcard, hmap]
    exact ThreeSwapCardLower.eight_dvd e
  exact ⟨y, w, congrArg Subtype.val hy, congrArg Subtype.val hw,
    hdata.1, isMulCommutative_iff.mpr (fun a b => (hdata.2 a b).eq), hdiv⟩

end FiveTransitive.OneOrbitThreeSwapLifts

end CFSG

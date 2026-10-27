module

public import CFSG.Permutation.FiveTransitive.NormalizerKernelQuotientOdd
public import CFSG.Permutation.FiveTransitive.OddQuotientCosetFusion
public import CFSG.Permutation.FiveTransitive.SixteenNormalizerFixedFour

public section

namespace CFSG

namespace FiveTransitive.SixteenNormalizerFusion

open MulAction FixedSetNormalizerHom

theorem exists_conjugator_of_equal_image
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s))
    (hcomm : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      ∀ q r : Q, q * r = r * q)
    (h2 : ∀ q : S, q * q = 1) (hcard : Nat.card S = 16)
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (a b : G)
    (haN : a ∈ Subgroup.normalizer
      ((S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype : Set G))
    (hbN : b ∈ Subgroup.normalizer
      ((S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype : Set G))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : fixedPermHom G X _ ⟨a, haN⟩ = fixedPermHom G X _ ⟨b, hbN⟩)
    (hfb : fixedPermHom G X _ ⟨b, hbN⟩ ≠ 1)
    (hsix : (fixedBy X b).ncard = 6)
    (htwo : (fixedBy X b ∩ fixedPoints S X).ncard = 2) :
    ∃ g : G, g ∈ Subgroup.normalizer
      ((S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype : Set G) ∧
      g * b * g⁻¹ = a := by
  let H := fixingSubgroup G s
  let Q : Subgroup G := (S : Subgroup H).map H.subtype
  let N := Subgroup.normalizer (Q : Set G)
  let U : Subgroup N := Q.subgroupOf N
  let rho : N →* Equiv.Perm (fixedPoints Q X) := fixedPermHom G X Q
  have hU : U ≤ rho.ker := by
    intro u hu
    apply (mem_ker_iff G X Q u).mpr
    intro x hx
    exact mem_fixedPoints.mp hx ⟨u.val, hu⟩
  have hodd : Odd (Nat.card (rho.ker.map (QuotientGroup.mk' U))) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact NormalizerKernelQuotientOdd.prime_not_dvd_kernel_quotient G X s S
  let aN : N := ⟨a, haN⟩
  let bN : N := ⟨b, hbN⟩
  obtain ⟨k, _, hk⟩ := OddQuotientCosetFusion.exists_ker_conjugator_mod_subgroup rho U hU hodd
    aN bN (Subtype.ext ha) (Subtype.ext hb) hab hfb
  have hkQ : ((k : G) * a * (k : G)⁻¹) * b⁻¹ ∈ Q := hk
  let e : S ≃* Q := Subgroup.equivMapOfInjective (S : Subgroup H) H.subtype H.subtype_injective
  have he (q : S) : (e q : G) = ((q : H) : G) := rfl
  have hF : fixedPoints Q X = fixedPoints S X := by
    ext x
    rw [mem_fixedPoints, mem_fixedPoints]
    constructor
    · intro h q
      exact h (e q)
    · intro h q
      obtain ⟨r, rfl⟩ := e.surjective q
      exact h r
  have hQ2 : ∀ q : Q, q * q = 1 := by
    intro q
    obtain ⟨r, rfl⟩ := e.surjective q
    rw [← map_mul, h2, map_one]
  have hQcard : Nat.card Q = 16 := (Nat.card_congr e.toEquiv).symm.trans hcard
  have hQfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1 := by
    intro q x hx hqx
    obtain ⟨r, rfl⟩ := e.surjective q
    have hr : r = 1 := hfree r x (hF ▸ hx) hqx
    rw [hr, map_one]
  have ha' : ((k : G) * a * (k : G)⁻¹) * ((k : G) * a * (k : G)⁻¹) = 1 := by
    calc
      _ = (k : G) * (a * a) * (k : G)⁻¹ := by group
      _ = 1 := by rw [← pow_two, ha]; group
  obtain ⟨q, hq⟩ := SixteenNormalizerFixedFour.coset_conjugate_of_fixed_six G X Q hcomm hQ2
    hQcard b hbN (by simpa only [pow_two] using hb) hQfree hsix (hF.symm ▸ htwo)
    ((k : G) * a * (k : G)⁻¹) ha' hkQ
  refine ⟨(k : G)⁻¹ * q.val, N.mul_mem (N.inv_mem k.property) (Q.le_normalizer q.property), ?_⟩
  calc
    _ = (k : G)⁻¹ * (q.val * b * q.val⁻¹) * (k : G) := by group
    _ = a := by rw [hq]; group

end FiveTransitive.SixteenNormalizerFusion

end CFSG

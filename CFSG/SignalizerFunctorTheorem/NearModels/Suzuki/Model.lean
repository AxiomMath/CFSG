module

public import CFSG.SignalizerFunctorTheorem.NearModels.Conjugacy
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Fixed
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic

public section

namespace CFSG.SignalizerFunctorTheorem.NearModels.Suzuki

open CFSG.Blueprint CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)
open CFSG.LieType.Ree (suzuki_frobenius_exponents)

def fixedEquivOfMulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (f : MulAut X) :
    signalizerFixedSubgroup f ≃* signalizerFixedSubgroup (MulAut.congr e f) where
  toFun x := ⟨e x, by
    change e (f (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, x.2]⟩
  invFun y := ⟨e.symm y, by
    have h : e (f (e.symm y)) = y := y.2
    change f (e.symm y) = e.symm y
    exact e.injective (by rw [h, MulEquiv.apply_symm_apply])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : X) y)

theorem card_pSubgroup_dvd_of_card_outer {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card G)) (hout : Nat.card (Outer G) ∣ p)
    (P : Subgroup (MulAut G)) (hP : IsPGroup p P) : Nat.card P ∣ p := by
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have h1 : Nat.card (inner G) * Nat.card (Outer G) = Nat.card (MulAut G) := by
    rw [← (inner G).card_mul_index, Subgroup.index_eq_card]
  have hI : Nat.card (inner G) ∣ Nat.card G :=
    Subgroup.card_dvd_of_surjective (f := (MulAut.conj : G →* MulAut G).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  have hcopI : Nat.Coprime p (Nat.card (inner G)) := Nat.Coprime.coprime_dvd_right hI hcop
  have hdvd : Nat.card P ∣ Nat.card (MulAut G) := Subgroup.card_subgroup_dvd_card P
  rw [hk] at hdvd ⊢
  rw [← h1] at hdvd
  exact ((Nat.Coprime.pow_left k hcopI).dvd_of_dvd_mul_left hdvd).trans hout

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzukiGroup_card_pSubgroup_dvd
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hp : (2 * a + 1).Prime) (hcop : Nat.Coprime (2 * a + 1) (Nat.card (suzukiGroup a K)))
    (P : Subgroup (MulAut (suzukiGroup a K))) (hP : IsPGroup (2 * a + 1) P) :
    Nat.card P ∣ 2 * a + 1 :=
  card_pSubgroup_dvd_of_card_outer hp hcop
    (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).2 P hP

theorem nonempty_fixedSubgroup_suzukiGroup
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hp : (2 * a + 1).Prime) (hcop : Nat.Coprime (2 * a + 1) (Nat.card (suzukiGroup a K)))
    (f : MulAut (suzukiGroup a K)) (hf : orderOf f = 2 * a + 1) :
    Nonempty (signalizerFixedSubgroup f ≃* suzukiGroup 0 (ZMod 2)) := by
  have : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  obtain ⟨σ, hσ, hord, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  have hφ : orderOf (szFieldAut a K σ) = 2 * a + 1 := by
    rw [orderOf_injective _ szFieldAut_injective, hord]
  have := Fact.mk hp
  obtain ⟨e⟩ := signalizerFixedSubgroup_mulEquiv_of_orderOf_eq
    (suzukiGroup_card_pSubgroup_dvd ha hK hp hcop) hf hφ
  obtain ⟨e'⟩ := nonempty_fixed_szFieldAut_equiv hK hσ
  exact ⟨e.trans e'⟩

end CFSG.SignalizerFunctorTheorem.NearModels.Suzuki

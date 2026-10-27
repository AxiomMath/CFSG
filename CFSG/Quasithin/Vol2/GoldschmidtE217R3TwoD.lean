module

public import CFSG.Quasithin.Vol2.Ch3E213MOL2
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3L2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.GLS.IVK CFSG.GH74.GLS

namespace E217R3

@[expose] def KFactL3U3NotOddCube : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p →
    ((p % 4 = 1 ∧ IsPSU 3 p 1 K) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 K)) →
    ∀ z : K, orderOf z = 2 → ¬ OddCube z

variable {X : Type} [Group X] [Finite X]

theorem eq_central_involution {K T M : Subgroup X} (hX : E2P.ASHyp K T M) {v z : X}
    (hz2 : orderOf z = 2) (hzT : z ∈ T) (hzM : ∀ m ∈ M, m * z = z * m) (hv2 : v * v = 1)
    (hv1 : v ≠ 1) (hvT : v ∈ T) (hvM : ∀ m ∈ M, m * v = v * m)
    (hfalse : ∀ V1 : Subgroup X, (∀ x ∈ V1, x * x = 1) → 4 ≤ Nat.card V1 →
      V1 ≤ pCoreOf 2 M → V1 ≤ T → T ≤ Subgroup.normalizer (V1 : Set X) → False) : v = z := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := hX.minPar.le
  have hz2' : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    omega
  have hvz : v * z = z * v := (hvM z (hTM hzT)).symm
  set V1 : Subgroup X := Subgroup.closure ({v, z} : Set X) with hV1
  have hcomm : ∀ m ∈ M, ∀ x ∈ V1, m * x = x * m := fun m hm x hx =>
    commute_closure hv2 hz2' hvz (hvM m hm) (hzM m hm) x hx
  have hsq : ∀ x ∈ V1, x * x = 1 := by
    intro x hx
    rcases klein_closure hv2 hz2' hvz x hx with h | h | h | h <;> rw [h]
    · simp
    · exact hv2
    · exact hz2'
    · calc (v * z) * (v * z) = v * (z * v) * z := by group
        _ = v * (v * z) * z := by rw [← hvz]
        _ = (v * v) * (z * z) := by group
        _ = 1 := by rw [hv2, hz2', one_mul]
  have hV4 : 4 ≤ Nat.card V1 := four_le_card_closure hv2 hz2' hv1 hz1 hne
  have hVT : V1 ≤ T := (Subgroup.closure_le T).2 (by
    intro x hx
    rcases hx with rfl | rfl
    exacts [hvT, hzT])
  have hVM1 : V1 ≤ M := hVT.trans hTM
  have hVn : T ≤ Subgroup.normalizer (V1 : Set X) :=
    (show T ≤ Subgroup.centralizer (V1 : Set X) from fun t ht =>
      Subgroup.mem_centralizer_iff.2 fun x hx => (hcomm t (hTM ht) x hx).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hMn : M ≤ Subgroup.normalizer (V1 : Set X) :=
    (show M ≤ Subgroup.centralizer (V1 : Set X) from fun m hm =>
      Subgroup.mem_centralizer_iff.2 fun x hx => (hcomm m hm x hx).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hVp : IsPGroup 2 ↥V1 := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hsq x x.2)⟩
  exact hfalse V1 hsq hV4
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVM1 hMn hVp) hVT hVn

theorem eq_three_of_asHyp_L3U3 (hA : Ch3E213M.OL.KFactL3U3OuterInv)
    (hNot : KFactL3U3NotOddCube) {K T M : Subgroup X} (hX : E2P.ASHyp K T M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : (p % 4 = 1 ∧ IsPSU 3 p 1 ↥K) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥K))
    (hMK : M ⊓ K = K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set X)) {v : X}
    (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvT : v ∈ T) (hvM : ∀ m ∈ M, m * v = v * m)
    (hodd : OddCube v) : p = 3 := by
  by_contra hp3
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  obtain ⟨z, hzK, hz2, hzM⟩ := exists_central_involution hX hMK
  have hvz : v = z := eq_central_involution hX hz2 hzK.1 hzM hv2 hv1 hvT hvM
    (fun V1 hsq hV4 hVM _ _ => Ch3E213M.OL.false_of_asHyp hA hX hp hp5 hK hMK hsq hV4 hVM)
  subst hvz
  have hvK : v ∈ K := hzK.2
  have hz2' : (⟨v, hvK⟩ : ↥K) ≠ 1 ∧ orderOf (⟨v, hvK⟩ : ↥K) = 2 := by
    refine ⟨fun h => hv1 (congrArg Subtype.val h), ?_⟩
    rw [← Subgroup.orderOf_coe]
    exact hz2
  have hOK : OddCube (⟨v, hvK⟩ : ↥K) :=
    OddCube.of_subgroup hvK (fun g _ n hn h1 => hodd g n hn h1)
  exact hNot ↥K p hp hp5 hK ⟨v, hvK⟩ hz2'.2 hOK

end E217R3

end CFSG.Quasithin

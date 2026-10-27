module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Is3D4 Bar2)
open CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem exists_prime_order_le_normalizer_of_powerMap {L T : Subgroup G} {s r : ℕ}
    (hTL : T ≤ borelQuotN L) (hT2 : IsPGroup 2 T)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ T) L) (hs : Odd s) (hr : r.Prime)
    (hrdvd : r ∣ 2 ^ s - 1)
    (hdvdB : r ∣ Nat.card ↥(L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G)))
    (hpow : ∀ u ∈ borelQuotN L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G),
      ∃ j : ℕ, ∀ b ∈ L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G),
        u * b * u⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ L ⊓ T) :
    ∃ X : Subgroup G, X ≤ L ∧ Nat.card X = r ∧ X ≤ Subgroup.normalizer (T : Set G) := by
  have hTU : T ≤ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G) :=
    (le_inf hTL (Subgroup.le_normalizer (H := T))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨xB, hxBord⟩ :=
    @exists_prime_orderOf_dvd_card'
      ↥(L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G)) _ _ r ⟨hr⟩ hdvdB
  let x : G := xB
  have hxBmem : x ∈ L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G) := xB.2
  have hxr : orderOf x = r := by
    rw [show x = (xB : G) from rfl, Subgroup.orderOf_coe, hxBord]
  have hpowT : ∀ u ∈ T, ∃ e : ℕ, u ^ 2 ^ e = 1 := by
    intro u hu
    obtain ⟨e, he⟩ := hT2 ⟨u, hu⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hconj : ∀ u ∈ T, x⁻¹ * u * x ∈ T := by
    intro u hu
    have huN : u ∈ borelQuotN L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G) :=
      ⟨hTL hu, hTU hu⟩
    obtain ⟨e, he⟩ := hpowT u hu
    obtain ⟨j, hj⟩ := hpow u huN
    have hmem := inv_mul_conj_mem_of_powerMap (Y := G)
      (B := L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G))
      (U := L ⊓ T) (t := u) (x := x) huN.2 hxBmem.2 hSyl.2.1 he hj hs hr hrdvd
      hxBmem hxr
    have heq : x⁻¹ * u * x = (x⁻¹ * (u * x * u⁻¹)) * u := by group
    rw [heq]
    exact T.mul_mem (Subgroup.mem_inf.mp hmem).2 hu
  have hxT : x ∈ Subgroup.normalizer (T : Set G) := by
    have h := Subgroup.mem_normalizer_fintype (S := (T : Set G)) (x := x⁻¹) fun u hu => by
      simpa using hconj u hu
    simpa using inv_mem h
  exact ⟨Subgroup.zpowers x, Subgroup.zpowers_le.mpr hxBmem.1, by
    rw [Nat.card_zpowers, hxr], Subgroup.zpowers_le.mpr hxT⟩

theorem is3D4_LBar {L : Subgroup G} {n : ℕ} (h : Is3D4 (Bar2 L) n) :
    Is3D4 ↥(borelQuotL L) n :=
  CFSG.Blueprint.LieModel.of_mulEquiv (bar2EquivLBar L) h

theorem exists_seven_order_le_normalizer_of_is3D4_bar2 (hB : K_3D4TwoBorel)
    {L T : Subgroup G} (hTL : T ≤ borelQuotN L) (hT2 : IsPGroup 2 T)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ T) L) (h3D4 : Is3D4 (Bar2 L) 1) :
    ∃ X : Subgroup G, X ≤ L ∧ Nat.card X = 7 ∧ X ≤ Subgroup.normalizer (T : Set G) := by
  have h3D4bar : Is3D4 ↥(borelQuotL L) 1 := is3D4_LBar h3D4
  have hSylbar : CFSG.QuasithinUnique.IsSylowTwoOf (borelQuotU L (L ⊓ T))
      (borelQuotL L) :=
    isSylowTwoOf_map_borelQuotPi hSyl
  have hfacts := hB (borelQuotY L) (borelQuotL L) (borelQuotU L (L ⊓ T)) h3D4bar hSylbar
  refine exists_prime_order_le_normalizer_of_powerMap (s := 3) (r := 7) hTL hT2 hSyl
    (by decide) Nat.prime_seven (by norm_num) ?_ ?_
  · exact hfacts.1.trans (card_inf_normalizer_bar2_dvd hSyl)
  · intro u hu
    exact exists_powerMap_lift_bar2 (U := L ⊓ T) hSyl hu hfacts.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

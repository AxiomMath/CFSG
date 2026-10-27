module

public import CFSG.Quasithin.H13.KG14726LSylow
public import CFSG.Quasithin.H13.KG14726CPar
public import CFSG.Quasithin.Vol2.RootDataG2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

theorem exists_prime_commute_gX_rC
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    ∃ ℓ ∈ adjointGroup Tag.G2 K, (∀ d : K, ℓ * gX rC d = gX rC d * ℓ) ∧
      ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p := by
  obtain ⟨ρ, hρ, -, hrange⟩ := rankOne_data (K := K) i1
  obtain ⟨p, hp, hp5, A, hA⟩ := exists_prime_orderOf_sl2 hK hf
  have hK4 : 4 ≤ Nat.card K := RootData.G2.four_le_card hK hf
  have hLP : ρ.range ≤ parabolicSubgroup Tag.G2 K {i1} := by
    rw [hrange]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact parabolicLevi_le_parabolicSubgroup _
        (xUnit_mem_parabolicLevi (Set.mem_singleton i1) c)
    · exact parabolicLevi_le_parabolicSubgroup _
        (yUnit_mem_parabolicLevi (Set.mem_singleton i1) c)
  have hperf : ⁅ρ.range, ρ.range⁆ = ρ.range := by
    have := CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K)
      (CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hK4)
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ρ)
  have hcent := (CFSG.Quasithin.le_perfectCore_of_perfect hLP hperf).trans
    CFSG.Quasithin.H13.NQCat.G2Rad.perfectCore_le_centralizer
  refine ⟨ρ A, parabolicSubgroup_le_adjointGroup _ _ _ (hLP ⟨A, rfl⟩), fun d => ?_, p, hp, hp5,
    by rw [orderOf_injective ρ hρ, hA]⟩
  exact ((mem_centralizer_iff.mp (hcent ⟨A, rfl⟩)) _ (gX_c_mem_N1 d)).symm

theorem kg115G2Input_holds :
    KG115G2Input := by
  intro f X _ hf h
  obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model h
  refine kg115Excluded_of_mulEquiv e ?_
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hc : center ↥(adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2
        (CFSG.QuasithinUnique.Setup.X6.unique_Chevalley_positive_Sylow 2).1)
  obtain ⟨-, hS₀, hS₀i⟩ := hSyl
  have hS₀i' : ¬ 2 ∣ ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).index := by
    rwa [show (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).subgroupOf ⊤).index =
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).index from
      Subgroup.relIndex_top_right _] at hS₀i
  have hcU : ∀ y : ↥(adjointGroup Tag.G2 K),
      (∀ s ∈ (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K), s * y = y * s) →
      ∀ z ∈ posUnipotent Tag.G2 K, z * (y : ModGL Tag.G2 K) = y * z := by
    intro y hy z hz
    have := hy ⟨z, posUnipotent_le_adjointGroup hz⟩ (mem_subgroupOf.mpr hz)
    exact congrArg Subtype.val this
  refine kg115Excluded_of_at hc (sylowTwoNoThree_of_conj hS₀ hS₀i' fun y hy3 hyS => ?_) ?_
  · have h1 := RootData.G2.eq_one_of_centralizer_of_odd y.2 (hcU y hyS)
      (by rw [Subgroup.orderOf_coe, hy3]; decide)
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  · intro S hS hSi l hl hlc hl1
    refine kg115At_of_prime (forall_center_of_conj hS₀ hS₀i'
      (Q := fun u => ∃ ℓ : ↥(adjointGroup Tag.G2 K), ℓ * u = u * ℓ ∧
        ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) (fun g _ hu => prime_conj g hu) ?_
      S hS hSi l hl hlc hl1)
    intro u _ huc _
    obtain ⟨d, hd⟩ := RootData.G2.exists_eq_gX_rC_of_centralizer u.2 (hcU u huc)
    obtain ⟨ℓ, hℓC, hℓc, p, hp, hp5, hℓp⟩ := exists_prime_commute_gX_rC hK hf
    refine ⟨⟨ℓ, hℓC⟩, Subtype.ext ?_, p, hp, hp5, by rw [Subgroup.orderOf_mk, hℓp]⟩
    rw [coe_mul, coe_mul, hd]
    exact hℓc d

end CFSG.Quasithin.H13.KG14726

end

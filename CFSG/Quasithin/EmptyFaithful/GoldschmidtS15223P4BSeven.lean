module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BCard
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.QuasithinUnique.Vol2Native.A312L

namespace S15223P4

namespace B

theorem eq_of_card_seventy_two
    {D P₁ P₂ : Subgroup ↥Seven.A7s} (hD : IsSylowTwoOf D ⊤) (h₁ : D ≤ P₁) (h₂ : D ≤ P₂)
    (c₁ : Nat.card P₁ = 72) (c₂ : Nat.card P₂ = 72) : P₁ = P₂ := by
  obtain ⟨h, -, hT⟩ := hD.exists_conj Seven.isSylowTwoOf_T7
  have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  have key : ∀ P : Subgroup ↥Seven.A7s, D ≤ P → Nat.card P = 72 →
      (P.map (MulAut.conj h).toMonoidHom).map Seven.A7s.subtype = Seven.Z 6 := by
    intro P hDP hP
    have hTP : Seven.T7 ≤ P.map (MulAut.conj h).toMonoidHom := hT ▸ Subgroup.map_mono hDP
    obtain ⟨i, hi, hZ⟩ := Seven.overgroup_Z hTP
    have hcard : Nat.card (Seven.Z i) = 72 := by
      rw [← hZ, Seven.card_map_subtype, Subgroup.card_map_of_injective hinj, hP]
    have h6 : i = 6 := by
      have h := Seven.card_Z hi
      rw [hcard] at h
      clear hZ hcard hTP
      interval_cases i
      all_goals first | rfl | (exfalso; revert h; decide)
    rw [hZ, h6]
  have := (key P₁ h₁ c₁).trans (key P₂ h₂ c₂).symm
  exact Subgroup.map_injective hinj (Subgroup.map_injective Seven.A7s.subtype_injective this)

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem not_ExcA7
    (c : P4Ctx T Mc M H B₀ I X) (f : P4Fact T Mc M H B₀ I X) (hExc : IsExcA7Block X)
    (hidx : (M ⊓ I).relIndex X = 35) : False := by
  obtain ⟨α, hα, hk⟩ := hExc.2.1
  have hQuot : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 2520 := by
    have e : (↥X ⧸ CFSG.pCore 2 ↥X) ≃* ↥Seven.A7s :=
      (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e.toEquiv, Seven.card_A7s]
  obtain ⟨b, hb⟩ := exists_card_pCoreOf_eq_pow X
  have hX : Nat.card X = Nat.card (pCoreOf 2 X) * (2 ^ 3 * 315) := by
    rw [card_eq_pCoreOf_mul_quot, hQuot]
    norm_num
  have hA : Nat.card ↥(sOf152 T Mc M B₀ ⊓ X) = Nat.card (pCoreOf 2 X) * 2 ^ 3 :=
    card_sylow_eq f.sylow ⟨b, hb⟩ (by norm_num) hX
  have hker : ∀ U : Subgroup G, pCoreOf 2 X ≤ U → α.ker ≤ U.subgroupOf X := fun U hU x hx =>
    hU (mem_pCoreOf_of_mem_pCore (by rwa [hk] at hx))
  have hcardImg : ∀ U : Subgroup G, pCoreOf 2 X ≤ U → ∀ n : ℕ, U.relIndex X = n →
      Nat.card ((U.subgroupOf X).map α) * n = 2520 := by
    intro U hU n hrel
    have h1 : ((U.subgroupOf X).map α).index = n := by
      rw [Subgroup.index_map_eq _ hα (hker U hU)]
      exact hrel
    have h2 := Subgroup.index_mul_card (H := (U.subgroupOf X).map α)
    rw [h1, Seven.card_A7s] at h2
    rw [mul_comm]
    exact h2
  have hAA : sOf152 T Mc M B₀ ⊓ X ≤ X := inf_le_right
  have hA315 : (sOf152 T Mc M B₀ ⊓ X).relIndex X = 315 :=
    relIndex_eq_of_card hAA (by rw [hX, hA]; ring)
  have hY35 : (oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X)).relIndex X = 35 :=
    relIndex_eq_of_card (Y_le_X f) (by rw [hX, f.card_Y, hA]; ring)
  have hM35 : (MX M I X).relIndex X = 35 := by
    rw [MX, Subgroup.inf_relIndex_right]
    exact hidx
  have hQA : pCoreOf 2 X ≤ sOf152 T Mc M B₀ ⊓ X := pCoreOf_le_A f
  have hQY : pCoreOf 2 X ≤ oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X) := hQA.trans le_sup_right
  have hAcard := hcardImg _ hQA 315 hA315
  have hY72 : Nat.card ((((oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X))).subgroupOf X).map α) = 72 := by
    have := hcardImg _ hQY 35 hY35
    omega
  have hM72 : Nat.card (((MX M I X).subgroupOf X).map α) = 72 := by
    have := hcardImg _ (pCoreOf_le_MX c f) 35 hM35
    omega
  have hA8 : Nat.card (((sOf152 T Mc M B₀ ⊓ X).subgroupOf X).map α) = 8 := by omega
  have hSyl : IsSylowTwoOf (((sOf152 T Mc M B₀ ⊓ X).subgroupOf X).map α) ⊤ :=
    isSylowTwoOf_top_of_card (a := 3) (m := 315) (by rw [hA8]; norm_num)
      (by rw [Seven.card_A7s]; norm_num) (by decide)
  have hAY : ((sOf152 T Mc M B₀ ⊓ X).subgroupOf X).map α ≤
      (((oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X))).subgroupOf X).map α :=
    Subgroup.map_mono fun _ hx => (le_sup_right : sOf152 T Mc M B₀ ⊓ X ≤ _) hx
  have hAM : ((sOf152 T Mc M B₀ ⊓ X).subgroupOf X).map α ≤ ((MX M I X).subgroupOf X).map α :=
    Subgroup.map_mono fun _ hx => A_le_MX c hx
  have hEq := eq_of_card_seventy_two hSyl hAY hAM hY72 hM72
  refine not_K_le_MX c fun k hk' => ?_
  have hkY : k ∈ oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X) := Subgroup.mem_sup_left hk'
  have hkX : k ∈ X := f.K_le hk'
  have hm : α ⟨k, hkX⟩ ∈ ((MX M I X).subgroupOf X).map α := by
    rw [← hEq]
    exact ⟨⟨k, hkX⟩, hkY, rfl⟩
  obtain ⟨m, hmM, hmk⟩ := hm
  have h1 : m⁻¹ * ⟨k, hkX⟩ ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmk, inv_mul_cancel]
  have h2 : ((m⁻¹ * ⟨k, hkX⟩ : ↥X) : G) ∈ pCoreOf 2 X :=
    mem_pCoreOf_of_mem_pCore (by rwa [hk] at h1)
  have h3 := (MX M I X).mul_mem hmM (pCoreOf_le_MX c f h2)
  simpa using h3

end B

end S15223P4

end CFSG.Quasithin

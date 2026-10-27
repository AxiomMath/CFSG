module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof432
import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def K432InnerThree : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → SectionFourHyp L → 3 ∣ Nat.card L →
    ∀ σ : MulAut L, σ ^ 3 = 1 → σ ≠ 1 →
    (∀ x : L, MulAut.conj x * σ * (MulAut.conj x)⁻¹ ∈
        Subgroup.normalizer ((Subgroup.zpowers σ : Subgroup (MulAut L)) : Set (MulAut L)) →
      MulAut.conj x * σ * (MulAut.conj x)⁻¹ ∈ Subgroup.zpowers σ) →
      ∃ b t : L, σ = MulAut.conj b ∧ t * b * t⁻¹ * b ∈ Subgroup.center L

namespace Res432

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card_of_isComponent (hO : CFSG.pPrimeCore 3 G = ⊥) {L : Subgroup G}
    (hL : IsComponent L) : 3 ∣ Nat.card L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h3
  have hcop : Nat.Coprime 3 (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hle := GH74.GLS.le_pPrimeCore_of_subnormal 3 hL.2 hcop
  rw [hO] at hle
  have hsub : ∀ w : L, w = 1 := fun w => Subtype.ext (Subgroup.mem_bot.mp (hle w.2))
  obtain ⟨-, -, ⟨u, v, huv⟩⟩ := hL.1
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  exact huv (by rw [hsub u', hsub v'])

end Res432

open Item432Proof Res432

theorem item4_32Comp_of_three (hI : K432InnerThree) (hList : K432List) : Item4_32Comp := by
  intro G _ _ hcomp hO Z hZ3 hwc
  obtain ⟨z, hz, rfl⟩ := exists_zpowers_eq hZ3
  set H := Subgroup.normalClosure ((Subgroup.zpowers z : Subgroup G) : Set G) with hH
  by_cases hex : ∃ L : Subgroup G, IsComponent L ∧ L ≤ H
  · obtain ⟨L₀, hL₀, hL₀H⟩ := hex
    obtain ⟨L, hL, hLH, hZC⟩ := exists_component_not_le_centralizer hL₀ hL₀H
    have hzN := mem_normalizer_of_isComponent hO hz hwc hL
    set σ := L.normalizerMonoidHom ⟨z, hzN⟩ with hσ
    have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hσ3 : σ ^ 3 = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨z, hzN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hz3)
      rw [this, map_one]
    have hσ1 : σ ≠ 1 := by
      intro h1
      apply hZC
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro l hl
      have h2 := congrArg (fun τ : MulAut L => ((τ ⟨l, hl⟩ : L) : G)) h1
      simp only [hσ, normalizerMonoidHom_apply_coe, MulAut.one_apply] at h2
      calc l * z = z * l * z⁻¹ * z := by rw [h2]
        _ = z * l := by group
    obtain ⟨b, t, hb, ht⟩ := hI L hL.1 (hcomp L hL) (three_dvd_card_of_isComponent hO hL) σ hσ3
      hσ1 (fun x hx => mem_zpowers_of_mem_normalizer hz hwc hzN x hx)
    by_cases hzL : z ∈ L
    ·
      have hZL : Subgroup.zpowers z ≤ L := Subgroup.zpowers_le.mpr hzL
      have hLn : L.Normal := ⟨fun x hx g => by
        have := mem_normalizer_of_le hwc hL hZL hZC g
        exact (Subgroup.mem_normalizer_iff.mp this x).mp hx⟩
      have hHL : H = L := le_antisymm (Subgroup.normalClosure_le_normal hZL) hLH
      rw [hHL]
      set Z' := (Subgroup.zpowers z).subgroupOf L with hZ'
      have hZ'3 : Nat.card Z' = 3 := by
        rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv, Nat.card_zpowers, hz]
      have hwc' : ∀ g : L, Z'.map (MulAut.conj g).toMonoidHom ≤
          Subgroup.normalizer (Z' : Set L) → Z'.map (MulAut.conj g).toMonoidHom = Z' := by
        intro g hg
        have hgG : (Subgroup.zpowers z).map (MulAut.conj (g : G)).toMonoidHom ≤
            Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
          rintro _ ⟨w, hw, rfl⟩
          have hwL : w ∈ L := hZL hw
          have h1 := hg ⟨⟨w, hwL⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
          rw [Subgroup.mem_normalizer_iff] at h1 ⊢
          intro v
          by_cases hvL : v ∈ L
          · have h2 := h1 ⟨v, hvL⟩
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            exact h2
          · constructor
            · intro hv
              exact absurd (hZL hv) hvL
            · intro hv
              exfalso
              apply hvL
              have hwL' : (g : G) * w * (g : G)⁻¹ ∈ L :=
                L.mul_mem (L.mul_mem g.2 hwL) (L.inv_mem g.2)
              have h3 := hZL hv
              have e : v = ((g : G) * w * (g : G)⁻¹)⁻¹ *
                  (((g : G) * w * (g : G)⁻¹) * v * ((g : G) * w * (g : G)⁻¹)⁻¹) *
                  ((g : G) * w * (g : G)⁻¹) := by group
              rw [e]
              exact L.mul_mem (L.mul_mem (L.inv_mem hwL') h3) hwL'
        have heq := hwc _ hgG
        ext w
        constructor
        · rintro ⟨w', hw', rfl⟩
          have hw'' : (w' : G) ∈ Subgroup.zpowers z := Subgroup.mem_subgroupOf.mp hw'
          rw [Subgroup.mem_subgroupOf]
          have : (MulAut.conj (g : G)).toMonoidHom (w' : G) ∈
              (Subgroup.zpowers z).map (MulAut.conj (g : G)).toMonoidHom :=
            ⟨w', hw'', rfl⟩
          rw [heq] at this
          simpa using this
        · intro hw
          have hw : (w : G) ∈ Subgroup.zpowers z := Subgroup.mem_subgroupOf.mp hw
          have h1 : (w : G) ∈ (Subgroup.zpowers z).map (MulAut.conj (g : G)).toMonoidHom := by
            rw [heq]
            exact hw
          obtain ⟨w', hw', hw'e⟩ := h1
          refine ⟨⟨w', hZL hw'⟩, Subgroup.mem_subgroupOf.mpr hw', ?_⟩
          apply Subtype.ext
          simpa using hw'e
      have hnc : ¬ Z' ≤ Subgroup.center L := by
        intro h
        apply hZC
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro l hl
        have h1 := Subgroup.mem_center_iff.mp
          (h (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z) : (⟨z, hzL⟩ : L) ∈ Z'))
          ⟨l, hl⟩
        exact congrArg Subtype.val h1
      rcases hList L hL.1 (hcomp L hL) (isPGroup_center_of_isSubnormal hO hL.2) Z' hZ'3 hwc'
        hnc with h1 | h2 | h3
      · left
        rw [← pRank_top_eq]
        exact h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h3)
    · exact (false_of_not_mem hz hwc hzN b t hb ht hσ1 hzL).elim
  · push Not at hex
    exact Or.inl (pRank_eq_one_of_forall hO hz hwc hex)

end CFSG.RankThree.PartTwo.Sec4

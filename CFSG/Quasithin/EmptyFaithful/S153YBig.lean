module

public import CFSG.Quasithin.EmptyFaithful.S153YA5Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Input1469C61A3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz : Subgroup G) (K : Fin 2 → Subgroup G) (ρ : G),
    IsSQTKTC I → CharTwo I → MinParabolic I S Iz → IsBlockProduct I S 2 K →
    (∀ i, ¬ K i ≤ Iz) → (∀ i, IsAltType (K i) 3) →
    ρ ∈ Subgroup.normalizer (S : Set G) → ρ ∉ S → ρ ^ 2 ∈ S →
    (∀ X : Subgroup G, X ≤ S → X ≠ ⊥ → I ≤ Subgroup.normalizer (X : Set G) →
      (S ⊔ Subgroup.zpowers ρ) ⊓ Subgroup.normalizer (X : Set G) ≤ S) →
    Nat.card S ≤ 2 ^ 9

namespace YG

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_blockProduct_one {I S Iz : Subgroup G} {K : Fin 1 → Subgroup G} {ρ : G}
    (hchar : CharTwo I) (hmp : MinParabolic I S Iz) (hbp : IsBlockProduct I S 1 K)
    (h5 : IsAltType (K 0) 5) (hρN : ρ ∈ Subgroup.normalizer (S : Set G)) (hρS : ρ ∉ S) (hρ2 : ρ ^ 2 ∈ S)
    (hb : ∀ X : Subgroup G, X ≤ S → X ≠ ⊥ → I ≤ Subgroup.normalizer (X : Set G) →
      (S ⊔ Subgroup.zpowers ρ) ⊓ Subgroup.normalizer (X : Set G) ≤ S) :
    Nat.card S ≤ 2 ^ 9 := by
  obtain ⟨hI, hIN⟩ := S153U.blockProduct_one hbp
  exact card_le_a5_single hmp hchar (hbp.2.2.1 0) h5 (hmp.isSylow.1.trans hIN) hI hρN hρS hρ2 hb

end YG

theorem input1469C61Big_of_a3 (hA3 : Input1469C61A3) : Input1469C61Big := by
  intro G _ _ I S Iz r K ρ hsq hchar hmp hbp hnot hAlt hnot2 hnot1 hρN hρS hρ2 hb
  have hbp' := hbp
  have hr1 : 1 ≤ r := hbp.1
  have hr2 : r ≤ 2 := hbp.2.1
  rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
  · refine YG.card_le_of_blockProduct_one hchar hmp hbp ?_ hρN hρS hρ2 hb
    refine (hAlt 0).resolve_left fun h3 => hnot1 ⟨rfl, fun i => ?_⟩
    rw [Subsingleton.elim i 0]
    exact h3
  · obtain ⟨t, htS, htK⟩ := hbp'.2.2.2.2.2.1 0 1
    have hK1 : K 1 = (K 0).map (MulAut.conj t).toMonoidHom := htK.symm
    have h3 : ∀ i, IsAltType (K i) 3 := by
      have h0 : IsAltType (K 0) 3 := by
        refine (hAlt 0).resolve_right fun h5 => hnot2 ⟨rfl, fun i => ?_⟩
        fin_cases i
        · exact h5
        · show IsAltType (K 1) 5
          rw [hK1]
          exact AppCS2.isAltType_map_equiv h5 (MulAut.conj t)
      intro i
      fin_cases i
      · exact h0
      · show IsAltType (K 1) 3
        rw [hK1]
        exact AppCS2.isAltType_map_equiv h0 (MulAut.conj t)
    exact hA3 G I S Iz K ρ hsq hchar hmp hbp' hnot h3 hρN hρS hρ2 hb

end CFSG.Quasithin

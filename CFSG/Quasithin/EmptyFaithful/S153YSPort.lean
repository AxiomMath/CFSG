module

public import CFSG.Quasithin.EmptyFaithful.S153YSPortC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalMain

public section

namespace CFSG.Quasithin.YS

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem a3_single_O2 {G : Type} [Group G] [Finite G] {H S L M₀ : Subgroup G}
    (hmin : IsMinimalParabolic S H) (hchar : CharTwo H)
    (hblk : IsChi0Block H L) (h3 : IsAltType L 3)
    (hth : ⁅L, thompsonJ S⁆ = L) (hHLR : H = L ⊔ S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hSM : S ≤ M₀) (h2 : S.relIndex M₀ = 2)
    (hC52 : C5.NoCommonNormal S H M₀) :
    (∀ x ∈ pCoreOf 2 H, ∀ y ∈ pCoreOf 2 H, x * y = y * x) ∧ Nat.card (pCoreOf 2 H) ≤ 8 := by
  have hcs : C56W.WSet1 H S L := ⟨hchar, hblk, hth, hHLR, hSN, hmin⟩
  obtain ⟨q, -, hZ, hab, hcard, hD⟩ :=
    hcs.single_card_data naturalModuleStructure (Or.inr h3) hC52 hSM h2
  have hq : q = 2 := by
    have h4 := C56.relIndex_blockZ_isAltType3 (G := G) (L := L) h3
    have : q ^ 2 = 2 ^ 2 := hZ.symm.trans (h4.trans (by norm_num))
    exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) this
  subst hq
  refine ⟨hab, ?_⟩
  rw [hcard]
  omega

end CFSG.Quasithin.YS

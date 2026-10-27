module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.GroupTheory.PCoreSurjective
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LieModelOrders
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsThreeDvd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem n924x_I9_subgroupOf (H : Subgroup G) :
    (F09.I9 H).subgroupOf H = CFSG.pPrimeCore 3 ↥H := by
  ext x
  rw [Subgroup.mem_subgroupOf, F09.I9]
  exact Subgroup.mem_map_iff_mem H.subtype_injective

private theorem n924x_le_normalizer_I9 (H : Subgroup G) :
    H ≤ normalizer (F09.I9 H : Set G) := by
  have hle : F09.I9 H ≤ H := Subgroup.map_subtype_le (CFSG.pPrimeCore 3 ↥H)
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  rw [n924x_I9_subgroupOf H]
  exact CFSG.pPrimeCore_normal

private theorem n924x_coprime_card_I9 (H : Subgroup G) :
    Nat.Coprime 3 (Nat.card (F09.I9 H)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [show F09.I9 H = (CFSG.pPrimeCore 3 ↥H).map H.subtype from rfl,
    Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

private theorem n924x_three_dvd_card_isL2 {Y : Type} [Group Y] {m : ℕ} (h : IsL2 Y m) :
    3 ∣ Nat.card Y := by
  rw [show Nat.card Y = ordA 1 (2 ^ m) from by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordA (k := 1) (by norm_num)

private theorem n924x_subgroupOf_I9_le_pCore {H X : Subgroup G} {m : ℕ} (hXH : X ≤ H)
    (hL2 : IsL2 (Bar2 X) m) :
    (F09.I9 H).subgroupOf X ≤ CFSG.pCore 2 ↥X := by
  haveI : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have hHI : H ≤ normalizer (F09.I9 H : Set G) := n924x_le_normalizer_I9 H
  set J : Subgroup ↥X := (F09.I9 H).subgroupOf X with hJ
  set Q : Subgroup ↥X := CFSG.pCore 2 ↥X with hQ
  have hJn : J.Normal := by
    rw [hJ]
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHI (hXH g.2)) (x : G)).mp hx
    simpa using h1
  haveI : (J.map (QuotientGroup.mk' Q)).Normal :=
    hJn.map _ (QuotientGroup.mk'_surjective Q)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.map (QuotientGroup.mk' Q)) with h | h
  · intro x hx
    have h1 : QuotientGroup.mk' Q x ∈ J.map (QuotientGroup.mk' Q) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    have h1 : Nat.card (Bar2 X) ∣ Nat.card J := by
      rw [← Subgroup.card_top (G := Bar2 X), ← h]
      exact Subgroup.card_map_dvd _ _
    have h2 : Nat.card J ∣ Nat.card (F09.I9 H) := by
      rw [hJ, ← Subgroup.card_map_of_injective X.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcop : Nat.Coprime 3 (Nat.card (F09.I9 H)) := n924x_coprime_card_I9 H
    have h3 : 3 ∣ Nat.card (Bar2 X) := n924x_three_dvd_card_isL2 hL2
    exact absurd (Nat.Coprime.coprime_dvd_right (h3.trans (h1.trans h2)) hcop) (by decide)

theorem isL2_bar2_img9 {H X : Subgroup G} {m : ℕ} (hXH : X ≤ H) (hL2 : IsL2 (Bar2 X) m) :
    IsL2 (Bar2 (F09.img9 H X)) m := by
  let f : ↥X →* ↥(F09.img9 H X) :=
    ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)).comp (Subgroup.inclusion hXH)).codRestrict
      (F09.img9 H X) fun x =>
        Subgroup.mem_map.2 ⟨Subgroup.inclusion hXH x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  have hfsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, Subtype.ext rfl⟩
  have hker : f.ker = (F09.I9 H).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [← Subtype.coe_inj, Subgroup.coe_one]
    change (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) (Subgroup.inclusion hXH x) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, F09.I9]
    exact (Subgroup.mem_map_iff_mem H.subtype_injective).symm
  have hfker : IsPGroup 2 f.ker := by
    rw [hker]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).to_le
      (n924x_subgroupOf_I9_le_pCore hXH hL2)
  obtain ⟨e⟩ :=
    CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker f hfsurj hfker
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hL2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

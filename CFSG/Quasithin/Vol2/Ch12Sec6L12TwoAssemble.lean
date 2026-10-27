module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoCore

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint Subgroup

theorem mk_mem_normalizer_map {G : Type} [Group G] {K L : Subgroup G} (hLK : L ≤ K)
    (t : ↥K) (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)) :
    QuotientGroup.mk' (Subgroup.center ↥K) t ∈
      Subgroup.normalizer (((L.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) :
        Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set (↥K ⧸ Subgroup.center ↥K)) := by
  have fwd : ∀ s : ↥K, (s : G) ∈ Subgroup.normalizer (L : Set G) →
      ∀ y ∈ (L.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)),
      QuotientGroup.mk' (Subgroup.center ↥K) s * y *
        (QuotientGroup.mk' (Subgroup.center ↥K) s)⁻¹ ∈
        (L.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    intro s hs y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hc : (s : G) * (l : G) * (s : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hs (l : G)).mp hlL
    refine Subgroup.mem_map.mpr ⟨s * l * s⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · simpa using hc
    · simp only [map_mul, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact fwd t ht y hy
  · intro hy
    have ht' : ((t⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (L : Set G) := by
      rw [Subgroup.coe_inv]
      exact inv_mem ht
    have h := fwd t⁻¹ ht' _ hy
    simpa [map_inv, mul_assoc] using h

theorem Setup.two_dvd_card_center_of_le16 {G : Type} [Group G] [Finite G] {K L E : Subgroup G}
    (S : Setup K L E)
    (h : Nat.card ↥((E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) ≤ 16) :
    2 ∣ Nat.card ↥(Subgroup.center ↥K) := by
  have hdvd := Subgroup.card_dvd_of_le (S.centralizer_le_center_of_card_le h)
  rw [S.hC, Subgroup.card_map_of_injective K.subtype_injective] at hdvd
  exact hdvd

end CFSG.Quasithin.H13.K1262Two

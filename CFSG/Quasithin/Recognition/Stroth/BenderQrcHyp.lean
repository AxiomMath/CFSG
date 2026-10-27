module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {q r : ℕ}

theorem exists_pow_mem_of_sup_eq_of_normalizes {H C D : Subgroup G}
    (hCH : C ≤ H) (hCn : H ≤ Subgroup.normalizer (C : Set G))
    (hDN : H ≤ Subgroup.normalizer (D : Set G)) (htop : D ⊔ C = H)
    (hD : ∀ d ∈ D, ∃ n : ℕ, d ^ (2 ^ n) ∈ C) :
    ∀ x ∈ H, ∃ n : ℕ, x ^ (2 ^ n) ∈ C := by
  intro x hx
  have hxK : x ∈ D ⊔ C := by rw [htop]; exact hx
  obtain ⟨a, haD, b, hbC, hxab⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (H := D) (K := C)
      (hCH.trans hDN)).mp hxK
  obtain ⟨n, hn⟩ := hD a haD
  haveI : (C.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr hCn
  let φ : ↥H →* ↥H ⧸ C.subgroupOf H := QuotientGroup.mk' (C.subgroupOf H)
  have hmemA : a ∈ H := htop ▸ Subgroup.mem_sup_left haD
  have hmemH : a * b ∈ H := by
    rw [← htop]
    exact (D ⊔ C).mul_mem (Subgroup.mem_sup_left haD) (Subgroup.mem_sup_right hbC)
  have hb1 : φ (⟨b, hCH hbC⟩ : ↥H) = 1 := by
    show QuotientGroup.mk' (C.subgroupOf H) _ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hbC
  have hxsub : (⟨x, hx⟩ : ↥H) = ⟨a * b, hmemH⟩ := Subtype.ext hxab
  have key : (φ (⟨x, hx⟩ : ↥H)) ^ (2 ^ n) = 1 := by
    have hmul : (⟨a * b, hmemH⟩ : ↥H) = ⟨a, hmemA⟩ * ⟨b, hCH hbC⟩ := rfl
    rw [hxsub, hmul, map_mul, hb1, mul_one, ← map_pow, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hn
  have hmem : (⟨x, hx⟩ : ↥H) ^ (2 ^ n) ∈ C.subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff]
    show QuotientGroup.mk' (C.subgroupOf H) ((⟨x, hx⟩ : ↥H) ^ (2 ^ n)) = 1
    rw [map_pow]
    exact key
  exact ⟨n, by simpa using Subgroup.mem_subgroupOf.mp hmem⟩

end CFSG.Quasithin.Stroth

end

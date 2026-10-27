module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.CentralizerK
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.OrderDichotomy

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem mem_NY_iff {G : Type} [Group G] {y : G} (u : ↥(CK y)) :
    u ∈ NY y ↔ (u : G) ∈ Subgroup.zpowers y := by
  unfold NY
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk⟩

theorem pow_mem_zpowers_of_quotient_pow {G : Type} [Group G] {y : G} {x : G} (hx : x ∈ CK y)
    {o : ℕ} (h : ((⟨x, hx⟩ : ↥(CK y)) : ↥(CK y) ⧸ NY y) ^ o = 1) : x ^ o ∈ Subgroup.zpowers y := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_NY_iff] at h
  exact h

theorem _root_.CFSG.Quasithin.IsTypeH2.pow_dichotomy
    {G : Type} [Group G] [Finite G] {z : G} (h : IsTypeH2 G z) (hone : involutionClassCount G = 1)
    {y : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G)) (hy3 : orderOf y = 3) :
    (∀ x ∈ CK y, x ^ 3 ∈ Subgroup.zpowers y ∨ x ^ 4 ∈ Subgroup.zpowers y ∨
        x ^ 5 ∈ Subgroup.zpowers y) ∨
      (∀ x ∈ CK y, x ^ 3 ∈ Subgroup.zpowers y ∨ x ^ 4 ∈ Subgroup.zpowers y ∨
        x ^ 7 ∈ Subgroup.zpowers y) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h.exists_psl2_of_centralizer_quotient hone hy hy3
  rcases hcard with h7 | h9
  · right
    intro x hx
    rcases psl2_pow_of_card_seven F h7 (e ((⟨x, hx⟩ : ↥(CK y)) : ↥(CK y) ⧸ NY y)) with h1 | h1 | h1
    · exact Or.inl (pow_mem_zpowers_of_quotient_pow hx (e.injective (by rw [map_pow, h1, map_one])))
    · exact Or.inr (Or.inl (pow_mem_zpowers_of_quotient_pow hx
        (e.injective (by rw [map_pow, h1, map_one]))))
    · exact Or.inr (Or.inr (pow_mem_zpowers_of_quotient_pow hx
        (e.injective (by rw [map_pow, h1, map_one]))))
  · left
    intro x hx
    rcases psl2_pow_of_card_nine F h9 (e ((⟨x, hx⟩ : ↥(CK y)) : ↥(CK y) ⧸ NY y)) with h1 | h1 | h1
    · exact Or.inl (pow_mem_zpowers_of_quotient_pow hx (e.injective (by rw [map_pow, h1, map_one])))
    · exact Or.inr (Or.inl (pow_mem_zpowers_of_quotient_pow hx
        (e.injective (by rw [map_pow, h1, map_one]))))
    · exact Or.inr (Or.inr (pow_mem_zpowers_of_quotient_pow hx
        (e.injective (by rw [map_pow, h1, map_one]))))

end CFSG.Quasithin.Kleidman.ThreeLocal

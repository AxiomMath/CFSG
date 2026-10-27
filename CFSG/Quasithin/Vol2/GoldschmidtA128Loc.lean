module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.Vol2.A128

open Subgroup CFSG.SectionRank CFSG.Open

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers (t : G) :
    centralizer {t} ≤ normalizer (zpowers t : Set G) := by
  intro x hx
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  exact (Commute.zpow_left (show Commute t x from hxt.symm) k).eq

omit [Finite G] in
theorem isPGroup_two_zpowers {t : G} (ht : orderOf t = 2) :
    IsPGroup 2 (zpowers t) ∧ zpowers t ≠ ⊥ := by
  refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]), fun h => ?_⟩
  have h1 : t ∈ zpowers t := mem_zpowers t
  rw [h, Subgroup.mem_bot] at h1
  rw [h1, orderOf_one] at ht
  omega

theorem not_centralizes_core [hp : Fact p.Prime]
    (hG : ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P → pRank p (normalizer (P : Set G)) ≤ 2)
    {Q : Subgroup G} (hQ : 2 < pRank p Q) {t : G} (ht : orderOf t = 2)
    (htQ : ∀ q ∈ Q, t * q = q * t) : False := by
  obtain ⟨h2, hne⟩ := isPGroup_two_zpowers ht
  have hQN : Q ≤ normalizer (zpowers t : Set G) := fun q hq =>
    centralizer_le_normalizer_zpowers t (Subgroup.mem_centralizer_singleton_iff.mpr (htQ q hq).symm)
  have h1 := pRank_mono hp.out.one_lt hQN
  have h3 := hG _ hne h2
  omega

theorem pRank_centralizer_le [hp : Fact p.Prime]
    (hG : ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P → pRank p (normalizer (P : Set G)) ≤ 2)
    (H : Subgroup G) {t : H} (ht : orderOf t = 2) :
    pRank p (centralizer {t} : Subgroup H) ≤ 2 := by
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  obtain ⟨h2, hne⟩ := isPGroup_two_zpowers ht'
  have hle : (centralizer {t} : Subgroup H).map H.subtype ≤
      normalizer (zpowers (t : G) : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    apply centralizer_le_normalizer_zpowers (t : G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp hx
    exact congrArg Subtype.val this
  exact (pRank_le_map hp.out.one_lt H.subtype H.subtype_injective _).trans
    ((pRank_mono hp.out.one_lt hle).trans (hG _ hne h2))

end CFSG.Quasithin.Vol2.A128

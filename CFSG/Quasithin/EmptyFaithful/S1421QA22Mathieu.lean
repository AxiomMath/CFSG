module

public import CFSG.Quasithin.EmptyFaithful.S1421QA22Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Mathieu

public section

namespace CFSG.Quasithin

theorem invFiveFree_of_card_centralizer {Y : Type} [Group Y] {n : ℕ} (hn : ¬ 5 ∣ n)
    (h : ∀ t : Y, orderOf t = 2 → Nat.card (Subgroup.centralizer ({t} : Set Y)) = n) :
    InvFiveFree Y := by
  intro t g ht1 ht2 hg hc
  have ho : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hmem : g ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc.symm
  have h1 : orderOf (⟨g, hmem⟩ : Subgroup.centralizer ({t} : Set Y)) = 5 := by
    rw [← hg]
    exact (Subgroup.orderOf_coe (⟨g, hmem⟩ : Subgroup.centralizer ({t} : Set Y))).symm
  have h2 := orderOf_dvd_natCard (⟨g, hmem⟩ : Subgroup.centralizer ({t} : Set Y))
  rw [h1, h t ho] at h2
  exact hn h2

theorem m22InvFiveFree_holds :
    M22InvFiveFree := by
  rintro Y _ _ ⟨e⟩
  exact invFiveFree_of_card_centralizer (n := 384) (by norm_num) fun t ht =>
    OddStandard.Solomon75.natCard_centralizer_involution_M22 e ht

theorem m23InvFiveFree_holds :
    M23InvFiveFree := by
  rintro Y _ _ ⟨e⟩
  exact invFiveFree_of_card_centralizer (n := 2688) (by norm_num) fun t ht =>
    OddStandard.Solomon75.natCard_centralizer_involution_M23 e ht

end CFSG.Quasithin

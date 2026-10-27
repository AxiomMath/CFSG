module

public import CFSG.RankThree.PartTwo.Census.Sporadic.NotCharTwoCert

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly

theorem not_isCharTwoType_of_nc2Facts {G : Type} [Group G] [Finite G] {a : ℕ}
    (h : ∃ (t g x : G) (S : Subgroup G), orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧
      Nat.card S = 2 ^ a ∧ g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧
      Odd (orderOf x) ∧ ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x)
    (hN : 2 ^ a = 2 ^ (Nat.card G).factorization 2) : ¬ IsCharTwoType G := by
  obtain ⟨t, g, x, S, ht, hSC, hcard, hg, hx, hx1, hxo, hxc⟩ := h
  set L := Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hL : IsTwoLocal L := ⟨Subgroup.zpowers t, by rwa [Ne, Subgroup.zpowers_eq_bot],
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]), rfl⟩
  have hCL : Subgroup.centralizer ({t} : Set G) ≤ L := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨m, rfl⟩
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 hy).symm m).eq
  set S₂ := S.map (MulAut.conj g).toMonoidHom
  have hS₂C : S₂ ≤ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hSC hy)) (Subgroup.inv_mem _ hg)
  have hc₁ : Nat.card S = 2 ^ (Nat.card L).factorization 2 :=
    card_eq_two_pow_factorization_of_le (hSC.trans hCL) (hcard.trans hN)
  have hc₂ : Nat.card S₂ = 2 ^ (Nat.card L).factorization 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc₁]
  exact not_isCharTwoType_of_sylow_inf hL (hSC.trans hCL) (hS₂C.trans hCL) hc₁ hc₂ (hCL hx) hx1
    hxo hxc

theorem not_isCharTwoType_of_nc2Facts' {G : Type} [Group G] [Finite G] {a q : ℕ}
    (h : ∃ (t g x : G) (S : Subgroup G), orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧
      Nat.card S = 2 ^ a ∧ g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧
      Odd (orderOf x) ∧ (∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x) ∧
      q ∣ Nat.card (Subgroup.centralizer ({t} : Set G)))
    (hC : ∀ u : G, orderOf u = 2 → q ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) →
      2 ^ a = 2 ^ (Nat.card (Subgroup.centralizer ({u} : Set G))).factorization 2) :
    ¬ IsCharTwoType G := by
  obtain ⟨t, g, x, S, ht, hSC, hcard, hg, hx, hx1, hxo, hxc, hq⟩ := h
  set L := Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)
  have hLC : L = Subgroup.centralizer ({t} : Set G) := OpsSpec.normalizer_zpowers_eq_centralizer ht
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hL : IsTwoLocal L := ⟨Subgroup.zpowers t, by rwa [Ne, Subgroup.zpowers_eq_bot],
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]), rfl⟩
  set S₂ := S.map (MulAut.conj g).toMonoidHom
  have hS₂C : S₂ ≤ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hSC hy)) (Subgroup.inv_mem _ hg)
  have hc₁ : Nat.card S = 2 ^ (Nat.card L).factorization 2 := by
    rw [hcard, hLC]
    exact hC t ht hq
  have hc₂ : Nat.card S₂ = 2 ^ (Nat.card L).factorization 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc₁]
  exact not_isCharTwoType_of_sylow_inf hL (hSC.trans hLC.ge) (hS₂C.trans hLC.ge) hc₁ hc₂
    (hLC.ge hx) hx1 hxo hxc

end CFSG.RankThree.PartTwo.Census

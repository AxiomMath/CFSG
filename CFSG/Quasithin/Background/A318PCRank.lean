module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.Open

theorem eq_one_or_of_mem_zpowers_cube {G : Type*} [Group G] {z g : G} (hz : z ^ 3 = 1)
    (hg : g ∈ Subgroup.zpowers z) : g = 1 ∨ g = z ∨ g = z ^ 2 := by
  obtain ⟨k, rfl⟩ := hg
  change z ^ k = 1 ∨ z ^ k = z ∨ z ^ k = z ^ 2
  have h3 : z ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hz
  have e : z ^ k = z ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [_root_.zpow_add, _root_.zpow_mul, h3, one_zpow, one_mul]
  rw [e]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h1 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases (k % 3)
  · left; simp
  · right; left; simp
  · right; right; rw [zpow_ofNat]

theorem exists_elemAbelian_three {G : Type*} [Group G] {n : ℕ} (Z A : Fin n → G)
    (h3 : ∀ i, Z i ^ 3 = 1) (h1 : ∀ i, ¬ Commute (Z i) (A i))
    (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i)) (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i))
    (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) {H : Subgroup G} (hH : ∀ i, Z i ∈ H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ n := by
  have key : ∀ i, ∀ g ∈ Subgroup.zpowers (Z i), Commute g (A i) → g = 1 := by
    intro i g hg hc
    rcases eq_one_or_of_mem_zpowers_cube (h3 i) hg with h | h | h
    · exact h
    · exact absurd (h ▸ hc) (h1 i)
    · exact absurd (h ▸ hc) (h2 i)
  have hcent : ∀ i, ∀ j, i ≠ j → Subgroup.zpowers (Z j) ≤ Subgroup.centralizer {A i} := by
    intro i j hij
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (hZA i j hij).eq.symm
  let ϕ : ∀ i, Subgroup.zpowers (Z i) →* G := fun i => (Subgroup.zpowers (Z i)).subtype
  have hϕcomm : Pairwise fun i j => ∀ (x : Subgroup.zpowers (Z i)) (y : Subgroup.zpowers (Z j)),
      Commute (ϕ i x) (ϕ j y) := by
    intro i j hij x y
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    change Commute (x : G) (y : G)
    rw [← ha, ← hb]
    exact (hZZ i j hij).zpow_zpow a b
  have hϕinj : ∀ i, Function.Injective (ϕ i) := fun i => Subtype.val_injective
  have hind : iSupIndep fun i => (ϕ i).range := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro g ⟨⟨x, rfl⟩, hg⟩
    have hle : (⨆ (j : Fin n) (_ : j ≠ i), (ϕ j).range) ≤ Subgroup.centralizer {A i} := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨y, rfl⟩
      exact hcent i j (Ne.symm hj) y.2
    have hc : Commute (x : G) (A i) := (Subgroup.mem_centralizer_iff.1 (hle hg) (A i) rfl).symm
    exact (Subgroup.mem_bot).2 (by
      have := key i _ x.2 hc
      change (x : G) = 1
      exact this)
  have hΦ := MonoidHom.injective_noncommPiCoprod_of_iSupIndep ϕ (hcomm := hϕcomm) hind hϕinj
  have hord : ∀ i, Nat.card (Subgroup.zpowers (Z i)) = 3 := fun i => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h3 i) fun h => (h1 i) (h ▸ Commute.one_left _)
  set Ψ := MonoidHom.noncommPiCoprod ϕ hϕcomm with hΨ
  have hcommA : ∀ a b : (∀ i, Subgroup.zpowers (Z i)), a * b = b * a := by
    intro a b
    funext i
    obtain ⟨x, hx⟩ := (a i).2
    obtain ⟨y, hy⟩ := (b i).2
    exact Subtype.ext (by
      change (a i : G) * (b i : G) = (b i : G) * (a i : G)
      rw [← hx, ← hy]
      exact (Commute.zpow_zpow_self _ _ _).eq)
  have hpowA : ∀ a : (∀ i, Subgroup.zpowers (Z i)), a ^ 3 = 1 := by
    intro a
    funext i
    apply Subtype.ext
    change ((a i : G)) ^ 3 = 1
    obtain ⟨x, hx⟩ := (a i).2
    rw [← hx, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h3 i,
      one_zpow]
  have hcardA : Nat.card (∀ i, Subgroup.zpowers (Z i)) = 3 ^ n := by
    rw [Nat.card_pi, Finset.prod_congr rfl fun i _ => hord i, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  refine ⟨Ψ.range, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · rw [hΨ, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨y, rfl⟩
    exact (Subgroup.zpowers_le.2 (hH i)) y.2
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcommA]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hpowA, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv, hcardA]

end A318P

end CFSG.Quasithin

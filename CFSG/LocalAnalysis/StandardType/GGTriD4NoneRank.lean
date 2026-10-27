module

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem isElemAbelian_range_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {B : Subgroup G}
    (hB : IsElemAbelian p B) {M : Type*} [Group M] (f : B →* M) : IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨a', ha'⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨b', hb'⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : M) * b = b * a
    rw [← ha', ← hb', ← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (TableB.IsElemAbelian.comm hB a'.2 b'.2))
  · obtain ⟨y', rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow]
    have : y' ^ p = 1 := Subtype.ext (by simpa using hB.2 y' y'.2)
    rw [this, map_one]

section Sections

variable {G : Type} [Group G] [Finite G]

theorem ker_ggBeta_le_of_sHat {p : ℕ} {B : Subgroup G} {y : G} {K : Subgroup G}
    (hS : LargeEvenSHat p B y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    (ggBeta K θ hBN).ker ≤ (Subgroup.zpowers y).subgroupOf B := by
  intro b hb
  rw [MonoidHom.mem_ker] at hb
  rw [Subgroup.mem_subgroupOf]
  have hc : (b : G) ∈ Subgroup.centralizer (K : Set G) :=
    mem_centralizer_of_ggLAut_eq_one K θ hK hb
  refine (hS.2.2.2.2.2 b).1 ⟨b.2, hBN b.2, ?_⟩
  have h1 : (⁅K, Subgroup.zpowers (b : G)⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact Subgroup.zpowers_le.2 hc
  rw [h1]
  exact bot_le

theorem card_le_of_sHat {p : ℕ} (hp : p.Prime) {B : Subgroup G} {y : G} {K : Subgroup G}
    (hS : LargeEvenSHat p B y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hBN : B ≤ Subgroup.normalizer (K : Set G)) {c : ℕ}
    (hrank : ∀ A : Subgroup (MulAut R), IsElemAbelian p A → Nat.card A ≤ p ^ c) :
    Nat.card B ≤ p ^ (c + 1) := by
  have hBe : IsElemAbelian p B := hS.1.1
  have hyB : y ∈ B := hS.2.1
  have h1 := TableB.card_range_mul_card_ker (ggBeta K θ hBN)
  have hr : Nat.card (ggBeta K θ hBN).range ≤ p ^ c :=
    hrank _ (isElemAbelian_range_of_isElemAbelian hBe _)
  have hker : Nat.card (ggBeta K θ hBN).ker ≤ p := by
    have h2 : Nat.card (ggBeta K θ hBN).ker ≤ Nat.card ((Subgroup.zpowers y).subgroupOf B) :=
      Subgroup.card_le_of_le (ker_ggBeta_le_of_sHat hS hK θ hBN)
    have h3 : Nat.card ((Subgroup.zpowers y).subgroupOf B) = Nat.card (Subgroup.zpowers y) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hyB)).toEquiv
    have h4 : Nat.card (Subgroup.zpowers y) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hBe.2 y hyB))
    omega
  calc Nat.card B = Nat.card (ggBeta K θ hBN).range * Nat.card (ggBeta K θ hBN).ker := h1.symm
    _ ≤ p ^ c * p := Nat.mul_le_mul hr hker
    _ = p ^ (c + 1) := (pow_succ p c).symm

theorem twoLocalRank_le_of_sHat {p : ℕ} (hp : p.Prime) {B : Subgroup G} {y : G} {K : Subgroup G}
    (hS : LargeEvenSHat p B y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hBN : B ≤ Subgroup.normalizer (K : Set G)) {c : ℕ}
    (hrank : ∀ A : Subgroup (MulAut R), IsElemAbelian p A → Nat.card A ≤ p ^ c) :
    LargeEvenTwoLocalRank p G ≤ c + 1 := by
  have hcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hS.1.2.1
  have h := card_le_of_sHat hp hS hK θ hBN hrank
  rw [hcard] at h
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h

end Sections

end CFSG.StandardType

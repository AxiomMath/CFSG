module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s21r8100_card_le_of_isSz {X : Type} [Group X] [Finite X] {n p : ℕ} (hX : IsSz X n)
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup X} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
  have hk1 : k ≤ 1 :=
    (UC6S846.le_pRank' hp le_top hE hk).trans (pRank_le_one_of_isL2_or_isSz (Or.inr hX) hp hp2)
  rw [hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
    _ = p := pow_one p

theorem uc22s21r8100_exists_centralizesBar_Sz {K : Subgroup G}
    {n p : ℕ} (hSz : IsSz (Bar2 K) n) (hZ : center (Bar2 K) = ⊥) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : ¬ p ∣ n) {B : Subgroup G} (hB : IsElemAbelian p B)
    (hBN : B ≤ normalizer (K : Set G)) :
    ∃ C : Subgroup G, C ≤ B ∧ (∀ c ∈ C, CentralizesBar c K) ∧ Nat.card B ≤ p * Nat.card C := by
  let φ : ↥B →* MulAut (Bar2 K) := (UC6S846.rhoL K).comp (Subgroup.inclusion hBN)
  have hinj : Function.Injective (MulAut.conj : Bar2 K →* MulAut (Bar2 K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have hpow : ∀ b : ↥B, φ b ^ p = 1 := by
    intro b
    rw [← map_pow]
    have : b ^ p = 1 := Subtype.ext (by simpa using hB.2 _ b.2)
    rw [this, map_one]
  have hinn : φ.range ≤ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
    rintro _ ⟨b, rfl⟩
    exact uc22p2214_inner_of_prime_Sz hSz hp hpn (hpow b)
  set Q : Subgroup (Bar2 K) := φ.range.comap MulAut.conj with hQ
  have hQcard : Nat.card Q = Nat.card φ.range := by
    rw [← Subgroup.map_comap_eq_self hinn, Subgroup.card_map_of_injective hinj]
  have hQel : IsElemAbelian p Q := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · obtain ⟨a, ha⟩ : MulAut.conj (x : Bar2 K) ∈ φ.range := x.2
      obtain ⟨b, hb⟩ : MulAut.conj (y : Bar2 K) ∈ φ.range := y.2
      have hab : a * b = b * a := by
        haveI := hB.1
        exact mul_comm' a b
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← ha, ← hb, ← map_mul, hab,
        map_mul]
    · obtain ⟨a, ha⟩ : MulAut.conj x ∈ φ.range := hx
      rw [map_pow, ← ha, hpow, map_one]
  have hQle : Nat.card Q ≤ p := uc22s21r8100_card_le_of_isSz hSz hp hp2 hQel
  refine ⟨φ.ker.map B.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨hBN b.2, fun l hl => ?_⟩
    have h1 : UC6S846.rhoL K (Subgroup.inclusion hBN b) = 1 := hb
    have h2 : UC6S846.rhoL K (Subgroup.inclusion hBN b) (QuotientGroup.mk ⟨l, hl⟩) =
        QuotientGroup.mk ⟨l, hl⟩ := by
      rw [h1, MulAut.one_apply]
    exact (UC6S846.rhoL_fix_iff K _ ⟨l, hl⟩).1 h2
  · rw [Subgroup.card_map_of_injective B.subtype_injective, ← Subgroup.card_ker_mul_card_range φ,
      mul_comm p]
    exact Nat.mul_le_mul_left _ (hQcard ▸ hQle)

end CFSG.LocalAnalysis.UniquenessCase.UC22

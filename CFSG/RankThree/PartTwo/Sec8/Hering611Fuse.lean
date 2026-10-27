module

public import CFSG.RankThree.PartTwo.Sec8.Hering611Inv
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)


section Certs


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}

theorem exists_E37_containing (F : Frame611 G A c L E T d) {x : G}
    (hx : x = c ∨ (x ∈ L ∧ x ^ 3 = 1)) :
    ∃ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 3 ^ 7 ∧ x ∈ B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := F.mem_S.1.1
  have hc3 : c ^ 3 = 1 := hAe.2 c F.c_mem
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c F.mem_L
  obtain ⟨φ⟩ := F.iso_L
  have hLcC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have key : ∀ X : Subgroup G, X ≤ L → IsPGroup 3 X → ∃ B : Subgroup G,
      CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 3 ^ 7 ∧ X ≤ B ∧ c ∈ B := by
    intro X hXL hX3
    obtain ⟨S₀, hXS₀, hS₀L, hS₀e, hS₀card⟩ := exists_elemAbelian_sylow φ hXL hX3
    have hS₀c : ∀ a ∈ S₀, a * c = c * a := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLcC (hS₀L ha))
    obtain ⟨hBe, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hS₀e
      (fun h => F.c_not_mem_L (hS₀L h)) hc3 hS₀c
    refine ⟨S₀ ⊔ Subgroup.zpowers c, hBe, ?_, hXS₀.trans le_sup_left,
      Subgroup.mem_sup_right (Subgroup.mem_zpowers c)⟩
    rw [hBcard, hS₀card]
    norm_num
  rcases hx with rfl | ⟨hxL, hx3⟩
  · obtain ⟨B, hBe, hBcard, -, hxB⟩ := key ⊥ bot_le
      (IsPGroup.of_card (G := (⊥ : Subgroup G)) (n := 0) (by rw [Subgroup.card_bot, pow_zero]))
    exact ⟨B, hBe, hBcard, hxB⟩
  · have hX3 : IsPGroup 3 (Subgroup.zpowers x) := fun g => by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨1, Subtype.ext ?_⟩
      change (g : G) ^ 3 ^ 1 = 1
      rw [← hj, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3,
        one_zpow]
    obtain ⟨B, hBe, hBcard, hXB, -⟩ := key (Subgroup.zpowers x)
      (Subgroup.zpowers_le.mpr hxL) hX3
    exact ⟨B, hBe, hBcard, hXB (Subgroup.mem_zpowers x)⟩

theorem false_of_fusion (F : Frame611 G A c L E T d)
    (hrank : ∀ X : Subgroup G, CFSG.Assembly.IsElemAbelian 3 X →
      X ≤ Subgroup.centralizer ({d} : Set G) → Nat.card X ≤ 3 ^ 6)
    {x : G} (hx : x = c ∨ (x ∈ L ∧ x ^ 3 = 1)) (hconj : IsConj x d) : False := by
  obtain ⟨B, hBe, hBcard, hxB⟩ := exists_E37_containing F hx
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  set B' := B.map (MulAut.conj g).toMonoidHom with hB'
  have hB'e : CFSG.Assembly.IsElemAbelian 3 B' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ B hBe
  have hdB' : d ∈ B' := ⟨x, hxB, by simpa [MulAut.conj_apply] using hg⟩
  have hB'd : B' ≤ Subgroup.centralizer ({d} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hB'e.1.is_comm.comm ⟨y, hy⟩ ⟨d, hdB'⟩))
  have h := hrank B' hB'e hB'd
  rw [hB', Subgroup.card_map_of_injective (MulAut.conj g).injective, hBcard] at h
  norm_num at h

end Certs

end CFSG.RankThree.PartTwo.Sec8.Hering611

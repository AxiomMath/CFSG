module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneToral
import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRankOne_su6_case_one {G : Type} [Group G] [Finite G] {x : G} {L T : Subgroup G}
    {m : ℕ} (h3 : 3 ∣ 2 ^ m + 1) (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hx : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hL : commutator L = ⊤) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTx : T ≤ Subgroup.centralizer ({x} : Set G)) (hTL : L ≤ Subgroup.centralizer (T : Set G))
    (hlab : GGHasLabel (⟨.twA, 5, m⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L)) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨E, hEL, hE, hEcard, hEc⟩ := ggRankOne_toral_four h3 hL hlab
  have hxC : ∀ l ∈ L, l * x = x * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hXC : ∀ y ∈ Subgroup.zpowers x, ∀ l ∈ L, l * y = y * l := by
    intro y hy l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_right (hxC l hl) k
  have hX : IsElemAbelian 3 (Subgroup.zpowers x) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      show (a : G) * b = b * a
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hEX : ∀ a ∈ E, ∀ c ∈ Subgroup.zpowers x, a * c = c * a := fun a ha c hc =>
    hXC c hc a (hEL ha)
  have hA : IsElemAbelian 3 (E ⊔ Subgroup.zpowers x) :=
    TableB.isElemAbelian_sup hE hX hEX
  have hdisj : Disjoint E (Subgroup.zpowers x) := by
    rw [Subgroup.disjoint_def]
    intro e he hXe
    rw [hEc e he fun l hl => (hXC e hXe l hl).symm]
  have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => hXC y hy g (hEL hg))
  have hcard : Nat.card (E ⊔ Subgroup.zpowers x : Subgroup G) = 3 ^ 5 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E (Subgroup.zpowers x)
      hXN hdisj, hEcard, Nat.card_zpowers, orderOf_eq_prime hx hx1]
    norm_num
  have hET : E ≤ Subgroup.normalizer (T : Set G) :=
    (hEL.trans hTL).trans (Subgroup.centralizer_le_normalizer _)
  have hxT : x ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp (hTx ht)
  have hXT : Subgroup.zpowers x ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.zpowers_le.mpr hxT).trans (Subgroup.centralizer_le_normalizer _)
  have hTN : E ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (T : Set G) := sup_le hET hXT
  have hloc : IsTwoLocal (Subgroup.normalizer (T : Set G)) := ⟨T, hT, hT2, rfl⟩
  exact TableB.le_twoLocalRank (by norm_num : 1 < 3) hloc
    (TableB.le_pRank_of_le (by norm_num : 1 < 3) hTN hA hcard)

end CFSG.StandardType

end

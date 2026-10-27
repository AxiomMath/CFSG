module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowSpor
public import Certificates.Certificate148006

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Sporadic.Schreier

theorem good427_of_orderOf_ne_fifteen {S : Type} [Group S] [Finite S]
    (h15 : ∀ g : S, orderOf g ≠ 15) {y : S} (hy : orderOf y = 3) :
    Good427 (Subgroup.centralizer ({y} : Set S)) := by
  intro K hKC _ _ hT
  obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hT
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := K) 5
    (by rw [ha]; exact ⟨12 * 2 ^ a, by ring⟩)
  have hfC : (f : S) ∈ Subgroup.centralizer ({y} : Set S) := hKC f.2
  have hcomm : Commute y (f : S) := (Subgroup.mem_centralizer_singleton_iff.mp hfC).symm
  have hf' : orderOf (f : S) = 5 := by rw [Subgroup.orderOf_coe]; exact hf
  apply h15 (y * f)
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hy, hf']; norm_num), hy, hf']

theorem mathieu_noFifteen :
    (orderTables m11Certificate 15).length = 0 ∧ (orderTables m12Certificate 15).length = 0 := by
  have h := Certificates.certificate148006
  simp only [mathieuNoFifteenCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

section M11


theorem orderOf_ne_fifteen_m11 : ∀ g : Blueprint.NativeSporadic.M11, orderOf g ≠ 15 := by
  intro g hg
  have h := card_orderOf_eq (by norm_num) m11Certificate m11Certificate_check.1 (m := 15)
    (by norm_num)
  rw [mathieu_noFifteen.1, m11Certificate_originalSubgroup] at h
  haveI : Finite {x : Blueprint.NativeSporadic.M11 // orderOf x = 15} := Subtype.finite
  haveI : Nonempty {x : Blueprint.NativeSporadic.M11 // orderOf x = 15} := ⟨⟨g, hg⟩⟩
  exact (Nat.card_pos (α := {x : Blueprint.NativeSporadic.M11 // orderOf x = 15})).ne' h

theorem noCfgS427_m11 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Spor .M11) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M11 ≃* Spor .M11 := b
  have hcard : Nat.card S = 7920 :=
    (Nat.card_congr (e.trans b'.symm).toEquiv).trans CFSG.Sporadic.Mathieu.card_M11
  refine ⟨noCfgS427_of_model (G' := ↥Blueprint.NativeSporadic.M11) (e.trans b'.symm)
    (RonanK429H.center_eq_bot_of_simple_nonab hna) (not_three_dvd_outer_of_mulEquiv e spor_m11.1)
    fun y hy => good427_of_orderOf_ne_fifteen orderOf_ne_fifteen_m11 hy,
    noONS427_of_card (by rw [hcard]; norm_num)⟩

end M11

section M12


theorem orderOf_ne_fifteen_m12 : ∀ g : Blueprint.NativeSporadic.M12, orderOf g ≠ 15 := by
  intro g hg
  have h := card_orderOf_eq (by norm_num) m12Certificate m12Certificate_check (m := 15)
    (by norm_num)
  rw [mathieu_noFifteen.2, m12Certificate_originalSubgroup] at h
  haveI : Finite {x : Blueprint.NativeSporadic.M12 // orderOf x = 15} := Subtype.finite
  haveI : Nonempty {x : Blueprint.NativeSporadic.M12 // orderOf x = 15} := ⟨⟨g, hg⟩⟩
  exact (Nat.card_pos (α := {x : Blueprint.NativeSporadic.M12 // orderOf x = 15})).ne' h

theorem noCfgS427_m12 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Spor .M12) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M12 ≃* Spor .M12 := b
  have hcard : Nat.card S = 95040 :=
    (Nat.card_congr (e.trans b'.symm).toEquiv).trans CFSG.Sporadic.Mathieu.card_M12
  refine ⟨noCfgS427_of_model (G' := ↥Blueprint.NativeSporadic.M12) (e.trans b'.symm)
    (RonanK429H.center_eq_bot_of_simple_nonab hna) (not_three_dvd_outer_of_mulEquiv e spor_m12.1)
    fun y hy => good427_of_orderOf_ne_fifteen orderOf_ne_fifteen_m12 hy,
    noONS427_of_card (by rw [hcard]; norm_num)⟩

end M12

section Rows



section M11Row


theorem rowOf427_m11
    : RowOf427 (Spor .M11) := rowOf427_of_noCfgS noCfgS427_m11

end M11Row

section M12Row


theorem rowOf427_m12
    : RowOf427 (Spor .M12) := rowOf427_of_noCfgS noCfgS427_m12

end M12Row

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end

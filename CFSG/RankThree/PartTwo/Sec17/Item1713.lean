module

public import CFSG.RankThree.PartTwo.Sec17.Item17Statements
public import CFSG.RankThree.PartTwo.Sec16.Item16Statements
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

omit [Finite G] in
theorem coprime_three_card_of_mem_scriptQ {Q : Subgroup G} (hQ : Q ∈ scriptQ A LB) :
    Nat.Coprime 3 (Nat.card Q) := by
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
  exact hQ.1.2.1 ⟨3, Nat.prime_three⟩ h3 rfl

omit [Finite G] in
theorem inf_centralizer_mem_scriptQ (hAab : IsMulCommutative A) {s : Set G} (hsA : s ⊆ A)
    {Q : Subgroup G} (hQ : Q ∈ scriptQ A LB) : Q ⊓ Subgroup.centralizer s ∈ scriptQ A LB := by
  refine mem_scriptQ_of_le hQ inf_le_left (le_normalizer_inf hQ.1.2.2 ?_)
  have hAC : A ≤ Subgroup.centralizer s := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hAab.is_comm.comm ⟨b, hsA hb⟩ ⟨a, ha⟩)
  exact hAC.trans Subgroup.le_normalizer

theorem le_of_forall_inf_centralizer_le (hA : IsE27 A) {B Q X : Subgroup G}
    (hB : IsHyperplane A B) (hQ : Q ∈ scriptQ A LB)
    (h : ∀ b ∈ B, b ≠ 1 → Q ⊓ Subgroup.centralizer ({b} : Set G) ≤ X) : Q ≤ X := by
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [hA.2] at this
    omega
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg Subtype.val
        (hA.1.1.is_comm.comm ⟨x, hB.1 x.2⟩ ⟨y, hB.1 y.2⟩))⟩⟩,
      fun x hx => hA.1.2 x (hB.1 hx)⟩
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three B Q hBe (by rw [hB9]; norm_num)
    (hB.1.trans hQ.1.2.2) (coprime_three_card_of_mem_scriptQ hQ)
  rw [← hgen]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSB, hS3⟩ := hS
  have hS1 : S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hS3
    norm_num at hS3
  obtain ⟨b, hbS, hb1⟩ := (Subgroup.bot_or_exists_ne_one S).resolve_left hS1
  have hle : Subgroup.centralizer (S : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbS)
  exact (inf_le_inf_left Q hle).trans (h b (hSB hbS) hb1)

theorem rank3II_17_13_of (hA : IsE27 A) (h1712 : Item1712 A LB) (h172 : Item172 A LB) :
    Item1713 A LB := by
  intro Y₀ hY₀
  by_contra hall
  push Not at hall
  obtain ⟨B, hB, hBY, -⟩ := h1712
  obtain ⟨Q, hQ, hQM⟩ := h172 Y₀ hY₀
  refine hQM (le_of_forall_inf_centralizer_le hA hB hQ fun b hb hb1 => ?_)
  have hQb : Q ⊓ Subgroup.centralizer ({b} : Set G) ∈ scriptQ A LB :=
    inf_centralizer_mem_scriptQ hA.1.1 (Set.singleton_subset_iff.mpr (hB.1 hb)) hQ
  exact (le_delta hQb inf_le_right).trans (hall _ (hBY b hb hb1))

theorem rank3II_17_14_of {L : Subgroup G} (hY0 : (scriptY0 A LB).Nonempty)
    (h1713 : Item1713 A LB) (h165 : Item165 A LB L) : Item1714 L := by
  intro n hn hiso
  obtain ⟨Y, hY⟩ := hY0
  obtain ⟨Y₀, -, hY₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A LB)) hY
  obtain ⟨Z, hZ, hZM⟩ := h1713 Y₀ hY₀
  exact hZM (h165 ⟨n, hn, hiso⟩ Y₀ hY₀ Z hZ)

end CFSG.RankThree.PartTwo.Sec17

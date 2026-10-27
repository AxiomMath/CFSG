module

public import CFSG.RankThree.PartTwo.Notation
import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLie
import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PFour
import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Res2Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_fixed_eq_one_coprime {X S : Subgroup G}
    (habel : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hSX : S ≤ Subgroup.normalizer (X : Set G))
    (hcop : (Nat.card S).Coprime (Nat.card X)) {x : G} (hx : x ∈ ⁅S, X⁆)
    (hfix : ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ = 1) : x = 1 := by
  have h := CFSG.LocalAnalysis.EvenBN.Common.mem_of_mem_commutator_sup_of_fixed (A := S)
    (Y := X) (Z := ⊥) bot_le
    (fun y hy y' hy' => by rw [Subgroup.mem_bot]; simp [habel y hy y' hy'])
    hSX Subgroup.le_normalizer_of_normal hcop (Subgroup.mem_sup_left hx)
    (fun s hs => by rw [Subgroup.mem_bot]; exact hfix s hs)
  exact Subgroup.mem_bot.1 h

theorem exists_fourGroupsMinus_le_of_comm {E T : Subgroup G} (hE : IsElemAbelian 3 E)
    (hT : IsPGroup 2 T) (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) (hne : ⁅T, E⁆ ≠ ⊥) :
    ∃ V ∈ fourGroupsMinus E, V ≤ T := by
  have hST : ⁅T, E⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro t ht e he
    rw [commutatorElement_def]
    have e1 : t * e * t⁻¹ * e⁻¹ = t * (e * t⁻¹ * e⁻¹) := by group
    rw [e1]
    exact T.mul_mem ht ((Subgroup.mem_normalizer_iff.1 (hET he) t⁻¹).1 (T.inv_mem ht))
  have hS2 : IsPGroup 2 (⁅T, E⁆ : Subgroup G) :=
    hT.of_injective (Subgroup.inclusion hST) (Subgroup.inclusion_injective hST)
  have hnormS : E ≤ Subgroup.normalizer ((⁅T, E⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right T E
  have hEp : IsPGroup 3 E := by
    intro g
    exact ⟨1, Subtype.ext (by simpa using hE.2 g.1 g.2)⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3)).1 hEp
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hT
  have hcop : (Nat.card E).Coprime (Nat.card T) := by
    rw [hm, hn]
    exact Nat.Coprime.pow m n (by norm_num)
  have hfix : ∀ x ∈ ⁅T, E⁆, (∀ e ∈ E, e * x = x * e) → x = 1 := by
    intro x hx hcent
    refine commutator_fixed_eq_one_coprime hTc hET hcop ?_ ?_
    · rw [Subgroup.commutator_comm] at hx
      exact hx
    · intro s hs
      rw [hcent s hs]
      group
  obtain ⟨H, hHS, hH1, hHN, hHinv, ⟨b, hb, hbC⟩, -, hcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.D3P.exists_fourgroup E ⁅T, E⁆ hE hS2 hne hnormS hfix
  have hHT : H ≤ T := hHS.trans hST
  obtain ⟨x, hxH, hx1⟩ : ∃ x : G, x ∈ H ∧ x ≠ 1 := by
    obtain ⟨x0, hx0⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hH1
    exact ⟨x0, x0.2, fun h => hx0 (Subtype.ext h)⟩
  obtain ⟨-, h4, h5, -, -, h8⟩ := hcard b hb hbC x hxH hx1
  have hyH : b * x * b⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 (hHN hb) x).1 hxH
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hHinv x hxH).1
  have hd1 : (1 : G) ≠ x := hx1.symm
  have hd2 : (1 : G) ≠ b * x * b⁻¹ := h5.symm
  have hd3 : (1 : G) ≠ x * (b * x * b⁻¹) := by
    intro h
    apply h4
    rw [eq_inv_of_mul_eq_one_right h.symm, hxinv]
  have hd4 : x ≠ b * x * b⁻¹ := fun h => h4 h.symm
  have hd5 : x ≠ x * (b * x * b⁻¹) := by
    intro h
    exact h5 (mul_left_cancel ((mul_one x).trans h)).symm
  have hd6 : b * x * b⁻¹ ≠ x * (b * x * b⁻¹) := by
    intro h
    exact hx1 (mul_right_cancel (h.symm.trans (one_mul _).symm))
  have hset : (H : Set G) = {1, x, b * x * b⁻¹, x * (b * x * b⁻¹)} := by
    ext z
    constructor
    · intro hz
      rcases h8 z hz with h | h | h | h <;> simp [h]
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h | h | h <;> rw [h]
      · exact H.one_mem
      · exact hxH
      · exact hyH
      · exact H.mul_mem hxH hyH
  have hcardH : Nat.card H = 4 :=
    (Nat.card_coe_set_eq (H : Set G)).trans
      (Set.ncard_eq_four.2 ⟨1, x, b * x * b⁻¹, x * (b * x * b⁻¹), hd1, hd2, hd3, hd4, hd5,
        hd6, hset⟩)
  have hab : IsElemAbelian 2 H :=
    ⟨⟨⟨fun a b => Subtype.ext ((hHinv a a.2).2 b b.2)⟩⟩, fun a ha => by
      rw [pow_two]
      exact (hHinv a ha).1⟩
  have hH4 : H ∈ fourGroups E := mem_fourGroups_iff.2 ⟨hHN, hab, hcardH⟩
  rcases Item211Res2Proof.mem_fourGroupsPlus_or_mem_fourGroupsMinus (fun e he => hE.2 e he) hH4
    with hP | hM
  · exact absurd ((mem_fourGroupsPlus_iff.1 hP).2 hb) hbC
  · exact ⟨H, hM, hHT⟩

end CFSG.RankThree.PartTwo.Sec21.Hering214Even

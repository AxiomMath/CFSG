module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.RankThree.Asc83Table.E9
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434F42

open CFSG.Assembly (IsElemAbelian)

theorem isElemAbelian_of_le {G : Type*} [Group G] {p : ℕ} {E F : Subgroup G}
    (hF : IsElemAbelian p F) (h : E ≤ F) : IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hF h

theorem exists_e9_le_e81 {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : 3 * Nat.card Q = 3 ^ (Nat.card G).factorization 3)
    (hgood : ∀ x ∈ Q, ∀ y ∈ Q, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x → x ≠ 1 →
      y ∉ Subgroup.zpowers x →
      ∃ E : Subgroup G, IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ x ∈ E ∧ y ∈ E)
    {P : Subgroup G} (hP : IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    ∃ P₁ : Subgroup G, P₁ ≤ P ∧ Nat.card P₁ = 9 ∧
      ∃ E : Subgroup G, IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ P₁ ≤ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  have he1 : 1 ≤ (Nat.card G).factorization 3 := by
    by_contra h
    have h0 : (Nat.card G).factorization 3 = 0 := by omega
    rw [h0] at hQ
    have : 0 < Nat.card Q := Nat.card_pos
    omega
  obtain ⟨k, hk⟩ : ∃ k, (Nat.card G).factorization 3 = k + 1 :=
    ⟨(Nat.card G).factorization 3 - 1, by omega⟩
  have hQcard : Nat.card Q = 3 ^ k := by
    rw [hk, pow_succ] at hQ
    omega
  have hQp : IsPGroup 3 Q := IsPGroup.of_card hQcard
  obtain ⟨S₀, hQS⟩ := hQp.exists_le_sylow
  have hS₀ : Nat.card (S₀ : Subgroup G) = 3 ^ (Nat.card G).factorization 3 :=
    Sylow.card_eq_multiplicity S₀
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hS₀ hPp
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'S : P' ≤ S₀ := Item434AltPerm.map_conj_inv_le hg
  have hP'e : IsElemAbelian 3 P' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP
  have hP'27 : Nat.card P' = 27 := by
    rw [hP', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP27]
  have hrel1 : Q.relIndex (S₀ : Subgroup G) = 3 := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := (S₀ : Subgroup G))
    rw [inf_of_le_left hQS, hS₀, ← hQ] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hrel2 : Q.relIndex P' ≤ 3 := by
    have := Subgroup.relIndex_le_of_le_right hP'S (H := Q) (by rw [hrel1]; norm_num)
    omega
  have h27 := Subgroup.relIndex_mul_card (H := Q) (K := P')
  rw [hP'27] at h27
  have hB9 : 9 ≤ Nat.card (Q ⊓ P' : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul hrel2 (Nat.le_of_lt_succ hlt)
    omega
  have hBe : IsElemAbelian 3 (Q ⊓ P' : Subgroup G) := isElemAbelian_of_le hP'e inf_le_right
  have hab : ∀ a ∈ (Q ⊓ P' : Subgroup G), ∀ b ∈ (Q ⊓ P' : Subgroup G), a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hBe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ (Q ⊓ P' : Subgroup G), x ≠ 1 := by
    by_contra hall
    push Not at hall
    have : (Q ⊓ P' : Subgroup G) ≤ ⊥ := fun a ha => Subgroup.mem_bot.2 (hall a ha)
    have := Subgroup.card_le_of_le this
    rw [Subgroup.card_bot] at this
    omega
  have hx3 : x ^ 3 = 1 := hBe.2 x hxB
  have hx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨y, hyB, hyx⟩ : ∃ y ∈ (Q ⊓ P' : Subgroup G), y ∉ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show (Q ⊓ P' : Subgroup G) ≤ Subgroup.zpowers x from hall)
    rw [Nat.card_zpowers, hx] at this
    omega
  have hy3 : y ^ 3 = 1 := hBe.2 y hyB
  obtain ⟨E, hEe, hE81, hxE, hyE⟩ :=
    hgood x hxB.1 y hyB.1 hx3 hy3 (hab x hxB y hyB) hx1 hyx
  have hP₁9 : Nat.card (Subgroup.closure ({x, y} : Set G)) = 9 :=
    Asc83Table.card_closure_pair_eq_nine hx3 hy3 (hab x hxB y hyB) hx1 hyx
  have hP₁E : Subgroup.closure ({x, y} : Set G) ≤ E := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hxE
    · exact hyE
  have hP₁P' : Subgroup.closure ({x, y} : Set G) ≤ P' := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hxB.2
    · exact hyB.2
  refine ⟨(Subgroup.closure ({x, y} : Set G)).map (MulAut.conj g).toMonoidHom, ?_, ?_,
    E.map (MulAut.conj g).toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hEe, ?_,
    Subgroup.map_mono hP₁E⟩
  · calc (Subgroup.closure ({x, y} : Set G)).map (MulAut.conj g).toMonoidHom
        ≤ P'.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hP₁P'
      _ = P := Item434AltPerm.map_conj_map_conj_inv P g
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP₁9]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE81

end CFSG.RankThree.PartTwo.Sec4.Item434F42

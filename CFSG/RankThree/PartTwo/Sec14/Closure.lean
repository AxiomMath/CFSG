module

public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Late.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree.PartTwo CFSG.GH74.GLS

variable {G : Type*} [Group G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem rank3II_14_4_1 {a : G} {Q Y : Subgroup G}
    (hQ : Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a})) (hYQ : Y ≤ Q)
    (hY : Y ∈ scriptY A) : Y ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a}) :=
  ⟨mem_scriptQ_of_le hQ.1 hYQ hY.2, hYQ.trans hQ.2⟩

theorem rank3II_14_4_2 {a b : G} {Q : Subgroup G}
    (hQ : Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a}))
    (hQb : Q ≤ Subgroup.centralizer {b}) :
    Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {b}) :=
  ⟨hQ.1, hQb⟩

theorem map_conj_eq_of_mem_normalizer' {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    A.map (MulAut.conj w).toMonoidHom = A :=
  CFSG.RankThree.PartTwo.Late.map_conj_eq_of_mem_normalizer hw

theorem map_conj_qBound (hnat : IsNaturalFamily A LB) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) {B : Subgroup G} (hB : IsHyperplane A B) :
    (qBound A LB B).map (MulAut.conj w).toMonoidHom =
      qBound A LB (B.map (MulAut.conj w).toMonoidHom) := by
  unfold qBound
  rw [Subgroup.map_sup, Subgroup.map_sup, map_pPrimeCoreOf, map_pPrimeCoreOf,
    map_conj_centralizer, map_conj_centralizer, map_conj_eq_of_mem_normalizer' hw,
    hnat w hw B hB]

theorem rank3II_14_4_5 (hnat : IsNaturalFamily A LB) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) {Q : Subgroup G} (hQ : Q ∈ scriptQ A LB) :
    Q.map (MulAut.conj w).toMonoidHom ∈ scriptQ A LB := by
  rw [mem_scriptQ_iff] at hQ ⊢
  obtain ⟨hQπ, hAQ, hQB⟩ := hQ
  refine ⟨fun q hq => hQπ q ?_, ?_, fun B' hB' => ?_⟩
  · rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective] at hq
  · rw [← Subgroup.map_equiv_normalizer_eq]
    calc A = A.map (MulAut.conj w).toMonoidHom := (map_conj_eq_of_mem_normalizer' hw).symm
      _ ≤ _ := Subgroup.map_mono hAQ
  · set B := B'.map (MulAut.conj w⁻¹).toMonoidHom with hBdef
    have hB : IsHyperplane A B := hB'.map_conj (inv_mem hw)
    have hBB' : B.map (MulAut.conj w).toMonoidHom = B' := by
      rw [hBdef, CFSG.RankThree.PartTwo.Late.map_conj_map_conj, mul_inv_cancel,
        CFSG.RankThree.PartTwo.Late.map_conj_one]
    rw [← hBB', ← map_conj_centralizer,
      ← Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective, ← map_conj_qBound hnat hw hB]
    exact Subgroup.map_mono (hQB B hB)

theorem rank3II_14_4_5_zero (hnat : IsNaturalFamily A LB) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A LB) :
    Q.map (MulAut.conj w).toMonoidHom ∈ scriptQZero A LB := by
  refine ⟨rank3II_14_4_5 hnat hw hQ.1, ?_⟩
  conv_lhs => rw [hQ.2]
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer' hw]

theorem mem_normalizer_deltaZero (hnat : IsNaturalFamily A LB) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) {Y : Subgroup G}
    (hwY : w ∈ Subgroup.normalizer (Y : Set G)) :
    w ∈ Subgroup.normalizer (deltaZero A LB Y : Set G) := by
  have key : ∀ v : G, v ∈ Subgroup.normalizer (A : Set G) →
      v ∈ Subgroup.normalizer (Y : Set G) →
      (deltaZero A LB Y).map (MulAut.conj v).toMonoidHom ≤ deltaZero A LB Y := by
    intro v hvA hvY
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun Q hQ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_deltaZero (rank3II_14_4_5_zero hnat hvA hQ.1) ?_
    calc Q.map (MulAut.conj v).toMonoidHom ≤ Y.map (MulAut.conj v).toMonoidHom :=
          Subgroup.map_mono hQ.2
      _ = Y := CFSG.RankThree.PartTwo.Late.map_conj_eq_of_mem_normalizer hvY
  have h₁ := key w hw hwY
  have h₂ := key w⁻¹ (inv_mem hw) (inv_mem hwY)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h₁ ⟨x, hx, rfl⟩
  · intro hx
    have := h₂ ⟨w * x * w⁻¹, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

end CFSG.RankThree.PartTwo.Sec14

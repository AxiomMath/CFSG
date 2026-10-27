module

public import CFSG.RankThree.Co2.Syl
public import CFSG.RankThree.Co2.JFusion

public noncomputable section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2.JM

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem jWords_size : jWords.size = 10 := rfl

theorem jWords_letters : ∀ k < jWords.size, ∀ l ∈ jWords[k]!, l < 42 := by
  decide +kernel

theorem matGrp_jWords_eq : matGrp jWords = (subW jWords).toSubmonoid.map crMat :=
  matGrp_eq_map jWords_letters (by
    rw [← card_map_subW]
    exact Nat.card_mono (Set.toFinite _) (map_subW_le jWords_letters))

theorem mem_J_iff {x : Cr} : x ∈ subW jWords ↔ crMat x ∈ matGrp jWords := by
  refine ⟨fun hx => map_subW_le jWords_letters ⟨x, hx, rfl⟩, fun hx => ?_⟩
  rw [matGrp_jWords_eq] at hx
  obtain ⟨y, hy, e⟩ := hx
  rw [← crMat_injective e]
  exact hy

theorem mem_T_iff {x : Cr} :
    x ∈ subW sylWords ↔ crMat x ∈ matGrp sylWords := by
  refine ⟨fun hx => map_subW_le sylWords_letters ⟨x, hx, rfl⟩, fun hx => ?_⟩
  rw [matGrp_sylWords_eq] at hx
  obtain ⟨y, hy, e⟩ := hx
  rw [← crMat_injective e]
  exact hy

variable (h : JFacts)

include h in
theorem card_matGrp_J : Nat.card (matGrp jWords) = 1024 := by
  have e := h.bij.image_eq
  have hI : Set.Iio (1024 : ℕ) = ((Finset.range 1024 : Finset ℕ) : Set ℕ) := by
    ext
    simp
  change Nat.card (matGrp jWords : Set M22) = 1024
  rw [Nat.card_coe_set_eq, ← e, h.bij.2.1.ncard_image, hI, Set.ncard_coe_finset,
    Finset.card_range]

include h in
theorem card_J : Nat.card (subW jWords) = 1024 := by
  rw [← card_map_subW, ← matGrp_jWords_eq, card_matGrp_J h]

theorem crMat_gensW_J {i : ℕ} (hi : i < 10) : crMat (gensW jWords i) = wordMat jWords[i]! :=
  crMat_wordCr (jWords_letters i (by rw [jWords_size]; exact hi))

include h in
theorem elemTwo_J : ElemTwo (subW jWords) := by
  apply elemTwo_closure
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨k, hk, rfl⟩
    rw [Set.mem_setOf_eq, jWords_size] at hi hk
    apply crMat_injective
    rw [map_mul, map_mul, crMat_gensW_J hi, crMat_gensW_J hk]
    exact h.comm i hi k hk
  · rintro _ ⟨i, hi, rfl⟩
    rw [Set.mem_setOf_eq, jWords_size] at hi
    apply crMat_injective
    rw [map_mul, map_one, crMat_gensW_J hi]
    exact h.sq i hi

include h in
theorem eq_J_of_elemTwo {A : Subgroup Cr}
    (hAT : A ≤ subW sylWords) (hA : ElemTwo A) (hcard : Nat.card A = 1024) :
    A = subW jWords := by
  have hB : crMat '' (A : Set Cr) = matGrp jWords := by
    refine h.ea tFacts_cert.2.1.le _ ?_ ⟨1, A.one_mem, map_one _⟩ ?_ ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact mem_T_iff.1 (hAT ha)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact ⟨a * b, A.mul_mem ha hb, map_mul crMat a b⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hA.2 a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hA.1 a ha, map_one]
    · rw [Nat.card_image_of_injective crMat_injective]
      exact hcard
  ext x
  have e1 : x ∈ A ↔ crMat x ∈ crMat '' (A : Set Cr) := crMat_injective.mem_set_image.symm
  have e2 : crMat x ∈ crMat '' (A : Set Cr) ↔ crMat x ∈ matGrp jWords := by rw [hB]; rfl
  exact e1.trans (e2.trans mem_J_iff.symm)

include h in
theorem exists_conj_J_of_elemTwo {A : Subgroup Cr}
    (hA : ElemTwo A) (hcard : Nat.card A = 1024) :
    ∃ g : Cr, A = (subW jWords).map (MulAut.conj g).toMonoidHom := by
  have hp : IsPGroup 2 A := by
    intro a
    refine ⟨1, ?_⟩
    rw [pow_one, sq]
    exact Subtype.ext (hA.1 _ a.2)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Cr Q sylT
  set A' := A.map (MulAut.conj g).toMonoidHom
  have hA'T : A' ≤ subW sylWords := by
    rw [← coe_sylT, ← hg, Sylow.coe_subgroup_smul]
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (Q : Subgroup Cr) (hQ ha)
  have hA' : A' = subW jWords := eq_J_of_elemTwo h hA'T (hA.conj g)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard])
  refine ⟨g⁻¹, ?_⟩
  rw [← hA', map_conj_mul, inv_mul_cancel]
  ext x
  simp

end CFSG.RankThree.Co2.JM

end

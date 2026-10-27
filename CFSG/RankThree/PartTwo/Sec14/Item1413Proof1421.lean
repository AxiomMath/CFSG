module

public import CFSG.RankThree.PartTwo.Sec14.Item148Solvable

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413

variable {G : Type} [Group G] [Finite G]

theorem eq_or_eq_of_set_eq {A L D : Subgroup G} {c : G}
    (hset : {F | F ∈ gammaA A (lB A) ∧ F ≤ D} = {Subgroup.zpowers c, D ⊓ L})
    {F : Subgroup G} (hF : F ∈ gammaA A (lB A)) (hFD : F ≤ D) :
    F = Subgroup.zpowers c ∨ F = D ⊓ L := by
  have hmem : F ∈ ({Subgroup.zpowers c, D ⊓ L} : Set (Subgroup G)) := hset ▸ ⟨hF, hFD⟩
  simpa using hmem

theorem zpowers_eq_of_set_eq {A L D : Subgroup G} {c x : G}
    (hset : {F | F ∈ gammaA A (lB A) ∧ F ≤ D} = {Subgroup.zpowers c, D ⊓ L})
    (hxD : x ∈ D) (hxL : x ∈ L) (hx : orderOf x = 3) :
    Subgroup.zpowers x = D ⊓ L ∧ Subgroup.zpowers x ∈ gammaA A (lB A) := by
  have hmem : D ⊓ L ∈ ({Subgroup.zpowers c, D ⊓ L} : Set (Subgroup G)) :=
    Set.mem_insert_of_mem _ rfl
  rw [← hset] at hmem
  obtain ⟨hΓ, -⟩ := hmem
  have h3 : Nat.card (D ⊓ L : Subgroup G) = 3 := hΓ.1.2.1
  have heq : Subgroup.zpowers x = D ⊓ L :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hxD, hxL⟩)
      (by rw [h3, Nat.card_zpowers, hx])
  exact ⟨heq, heq ▸ hΓ⟩

omit [Finite G] in
theorem le_centralizer_of_mem {A U : Subgroup G} {x : G}
    (hx : x ∈ A ⊓ Subgroup.centralizer (U : Set G)) :
    U ≤ Subgroup.centralizer ({x} : Set G) := fun u hu =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.2 u hu)

omit [Finite G] in
theorem mem_closure_left (x y : G) : x ∈ Subgroup.closure ({x, y} : Set G) :=
  Subgroup.subset_closure (Set.mem_insert x _)

omit [Finite G] in
theorem mem_closure_right (x y : G) : y ∈ Subgroup.closure ({x, y} : Set G) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))

theorem exists_scriptQPiStar_top {A U Y : Subgroup G}
    (hU : U ∈ scriptQPi A (lB A) Y (piOf 2)) :
    ∃ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), U ≤ T := by
  obtain ⟨T, hUT, hT⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2)))
    (a := U) ⟨⟨hU.1.1, le_top⟩, hU.2⟩
  exact ⟨T, hT, hUT⟩

theorem exists_scriptQPiStar_of_le {A U Y Y' : Subgroup G}
    (hU : U ∈ scriptQPiStar A (lB A) Y (piOf 2)) (hUY' : U ≤ Y') :
    ∃ S ∈ scriptQPiStar A (lB A) Y' (piOf 2), U ≤ S := by
  obtain ⟨S, hUS, hS⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) Y' (piOf 2)))
    (a := U) ⟨⟨hU.prop.1.1, hUY'⟩, hU.prop.2⟩
  exact ⟨S, hS, hUS⟩

theorem false_of_three {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hfail : Fail1411 A (lB A)) {Y Y' U₁ U₂ U₃ : Subgroup G} {e f : G}
    (hU₁ : U₁ ∈ scriptQPiStar A (lB A) Y (piOf 2)) (hU₃ : U₃ ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hU₂ : U₂ ∈ scriptQPiStar A (lB A) Y' (piOf 2)) (hne : U₁ ≠ U₃) (hU₂0 : U₂ ≠ ⊥)
    (hXU₂ : xA A ≤ Subgroup.normalizer (U₂ : Set G))
    (hXU₃ : xA A ≤ Subgroup.normalizer (U₃ : Set G))
    (hU₁e : U₁ ≤ Subgroup.centralizer ({e} : Set G))
    (hU₂e : U₂ ≤ Subgroup.centralizer ({e} : Set G))
    (hU₂f : U₂ ≤ Subgroup.centralizer ({f} : Set G))
    (hU₃f : U₃ ≤ Subgroup.centralizer ({f} : Set G))
    (hTe : TransOn A (lB A) (xA A) (Subgroup.centralizer ({e} : Set G)))
    (hTf : TransOn A (lB A) (xA A) (Subgroup.centralizer ({f} : Set G))) : False := by
  obtain ⟨S₁, hS₁, hUS₁⟩ := exists_scriptQPiStar_of_le hU₁ hU₁e
  obtain ⟨S₂, hS₂, hUS₂⟩ := exists_scriptQPiStar_of_le hU₂ hU₂e
  obtain ⟨x, hx, hS₁eq⟩ := hTe S₂ hS₂ S₁ hS₁
  have hU₂S₁ : U₂ ≤ S₁ := by
    rw [hS₁eq, ← Late.map_conj_eq_of_mem_normalizer (hXU₂ (Subgroup.mem_inf.mp hx).1)]
    exact Subgroup.map_mono hUS₂
  obtain ⟨T₃, hT₃, hUT₃⟩ := exists_scriptQPiStar_of_le hU₃ hU₃f
  obtain ⟨T₂, hT₂, hUT₂⟩ := exists_scriptQPiStar_of_le hU₂ hU₂f
  obtain ⟨y, hy, hT₃eq⟩ := hTf T₂ hT₂ T₃ hT₃
  have hU₂T₃ : U₂ ≤ T₃ := by
    rw [hT₃eq, ← Late.map_conj_eq_of_mem_normalizer (hXU₂ (Subgroup.mem_inf.mp hy).1)]
    exact Subgroup.map_mono hUT₂
  obtain ⟨S', hS', hS₁S'⟩ := exists_scriptQPiStar_top hS₁.prop
  obtain ⟨T', hT', hT₃T'⟩ := exists_scriptQPiStar_top hT₃.prop
  have hconj : IsConjIn (xA A) S' T' := by
    by_contra hc
    have h0 := rank3II_14_15_std h h146 hbot hfail.2 hS' hT' hc
    exact hU₂0 (le_bot_iff.mp (h0 ▸ le_inf (hU₂S₁.trans hS₁S') (hU₂T₃.trans hT₃T')))
  exact rank3II_14_14_not_isConjIn hU₁ hU₃ hne hS' (hUS₁.trans hS₁S') (hUT₃.trans hT₃T') hXU₃
    hconj.symm

end Proof1413

end CFSG.RankThree.PartTwo.Sec14

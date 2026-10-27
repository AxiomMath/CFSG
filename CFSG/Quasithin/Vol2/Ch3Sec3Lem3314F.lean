module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem335
public import CFSG.Quasithin.Vol2.Ch3Sec3UniqueMax

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem map_conj_of_setup (s : Setup331 G T M L) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (hT : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {u : G} (hu : u ∈ L ⊔ T) :
    L.map (MulAut.conj u).toMonoidHom = L ∨
      L.map (MulAut.conj u).toMonoidHom = CFSG.conjugate L t := by
  rcases lemma_1_2_1_three s.qtke s.simple s.nonabelian
      (a37ForSQTK_of_cat h37)
      (a38ForSQTK_of_cat h38) s.pCoreOf_ne_bot s.mem_cComp with
    hL | ⟨h2, -⟩
  · exact absurd (le_sup_right.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hL)) hT
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp h2
  have hmem : ∀ v ∈ L ⊔ T, L.map (MulAut.conj v).toMonoidHom ∈ ({x, y} : Set (Subgroup G)) :=
    fun v hv => hset ▸ ⟨v, hv, rfl⟩
  have hL1 : L ∈ ({x, y} : Set (Subgroup G)) := by
    have := hmem 1 (Subgroup.one_mem _)
    have e1 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
      ext z
      simp
    rwa [e1] at this
  have hLt : CFSG.conjugate L t ∈ ({x, y} : Set (Subgroup G)) :=
    hmem t⁻¹ ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))
  have hne : L ≠ CFSG.conjugate L t := by
    intro heq
    apply htn
    have h1 : t⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Ch3Sec3.mem_normalizer_of_map_conj_eq heq.symm
    simpa using inv_mem h1
  have hu' := hmem u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL1 hLt hu'
  rcases hL1 with h1 | h1 <;> rcases hLt with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rcases hu' with h3 | h3
    · exact Or.inl (h3.trans h1.symm)
    · exact Or.inr (h3.trans h2.symm)
  · rcases hu' with h3 | h3
    · exact Or.inr (h3.trans h2.symm)
    · exact Or.inl (h3.trans h1.symm)
  · exact absurd (h1.trans h2.symm) hne

theorem a38Types_of_setup (s : Setup331 G T M L) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (hT : ¬ T ≤ Subgroup.normalizer (L : Set G)) : A38Types (↥L ⧸ CFSG.pCore 2 ↥L) := by
  rcases lemma_1_2_1_three s.qtke s.simple s.nonabelian
      (a37ForSQTK_of_cat h37)
      (a38ForSQTK_of_cat h38) s.pCoreOf_ne_bot s.mem_cComp with hL | ⟨-, h⟩
  · exact absurd (le_sup_right.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hL)) hT
  · exact h

end CFSG.Quasithin.H13.Ins314

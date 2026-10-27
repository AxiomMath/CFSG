module

public import CFSG.Sporadic.Fi22.Fischer
public import CFSG.Fischer.OpenTranslation

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fischerEULocalClass_eq {X : Type} [Group X] (E : Set X) (e : X) :
    fischerEULocalClass E e = LocalImages E e := by
  ext y
  constructor
  · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩

theorem localIso_open_image :
    (localIso.trans psuOpenEquiv) '' LocalImages D a = fischerEUTransvections := by
  rw [MulEquiv.coe_trans, Set.image_comp, localIso_image, psuOpenEquiv_image]

theorem typeF22_open :
    fischerEUTypeF22 D := by
  refine ⟨a, a_mem_D, localIso.trans psuOpenEquiv, ?_⟩
  rw [fischerEULocalClass_eq]
  exact localIso_open_image

theorem localStructure_open
    {d : J} (hd : d ∈ D) : fischerEULocalStructure 22 d := by
  obtain ⟨h0, -, -⟩ := localStructureAt_of_mem_D hd
  obtain ⟨hc, hz, -, H, hH, ⟨iso⟩⟩ := h0 rfl
  obtain ⟨iso1, -⟩ := exists_psu_equiv hH
  refine ⟨fun _ => ⟨⟨hc, hz⟩, ⟨(iso.trans iso1.symm).trans psuOpenEquiv⟩⟩,
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem centerlessPair_open : fischerEUIsCenterlessPair D :=
  ⟨((CFSG.Fischer.pair_iff D).1 pair_D).2, center_eq_bot, isSimpleGroup_commutator_J⟩

theorem open_existence_22 :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (D' : Set G),
      fischerEUIsCenterlessPair D' ∧ fischerEUType 22 D' ∧
        (∀ D'' : Set G, fischerEUIsPair D'' → D'' = D') ∧
        ∀ d ∈ D', fischerEULocalStructure 22 d :=
  ⟨J, inferInstance, inferInstance, D, centerlessPair_open, Or.inl ⟨rfl, typeF22_open⟩,
    fun D'' hD'' => pair_eq_D D'' ((CFSG.Fischer.pair_iff D'').2 ⟨inferInstance, hD''⟩),
    fun _ hd => localStructure_open hd⟩

end CFSG.Sporadic.Fi22

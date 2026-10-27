module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.RExists
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec21.FF79 (Opp OppE)

abbrev ktil {G : Type} [Group G] (R : Subgroup G) : Subgroup G :=
  OppE 3 (Subgroup.centralizer (R : Set G))

abbrev mcore {G : Type} [Group G] (R : Subgroup G) : Subgroup G :=
  Opp 3 (Subgroup.centralizer (R : Set G))

abbrev Xq {G : Type} [Group G] (R : Subgroup G) : Type :=
  ↥(Subgroup.centralizer (R : Set G)) ⧸ CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (R : Set G))

abbrev Ksec {G : Type} [Group G] (R : Subgroup G) : Type :=
  ↥(CFSG.layer (Xq R))

theorem ktil_le_centralizer {G : Type} [Group G] (R : Subgroup G) :
    ktil R ≤ Subgroup.centralizer (R : Set G) :=
  Subgroup.map_subtype_le _

theorem mk_mem_layer {G : Type} [Group G] (R : Subgroup G) (k : ↥(ktil R)) :
    (QuotientGroup.mk ⟨(k : G), ktil_le_centralizer R k.2⟩ : Xq R) ∈ CFSG.layer (Xq R) := by
  obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp k.2
  have hx' : (⟨(k : G), ktil_le_centralizer R k.2⟩ :
      ↥(Subgroup.centralizer (R : Set G))) = x := Subtype.ext hxk.symm
  rw [hx']
  exact hx

def ktilHom {G : Type} [Group G] (R : Subgroup G) : ↥(ktil R) →* Ksec R where
  toFun k := ⟨QuotientGroup.mk ⟨(k : G), ktil_le_centralizer R k.2⟩, mk_mem_layer R k⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ktilHom_surjective {G : Type} [Group G] (R : Subgroup G) :
    Function.Surjective (ktilHom R) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hxk : (x : G) ∈ ktil R := Subgroup.mem_map.mpr ⟨x, hy, rfl⟩
  exact ⟨⟨(x : G), hxk⟩, Subtype.ext rfl⟩

end CFSG.StandardType.FF81.PropOne

end

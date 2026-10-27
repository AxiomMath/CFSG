module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.B6Sections
import CFSG.Quasithin.Background.A3StructureBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {H R M : Subgroup G}

theorem HypC23.satisfiesCPU (h : HypC23 H R M) (hlt : M < H) : SatisfiesCPU H R M :=
  ⟨h.cgs, hlt, h.radical, h.sylow.2.2⟩

theorem HypC23.of_satisfiesCPU (h : SatisfiesCPU H R M) (hH : IsSQTKIn H) : HypC23 H R M :=
  ⟨hH, h.2.2.1, h.2.1.le, h.1, le_conjClosure R M, h.2.2.1.isPGroup, h.2.2.2⟩


omit [Finite G] in
theorem preimage_congr_of_eq {X : Type} [Group X] (N N' : Subgroup X) [N.Normal] [N'.Normal]
    (h : N = N') (F : ∀ (Y : Type) [Group Y], Subgroup Y) :
    (F (X ⧸ N)).comap (QuotientGroup.mk' N) = (F (X ⧸ N')).comap (QuotientGroup.mk' N') := by
  subst h
  rfl

omit [Finite G] in
theorem oTwoFIn_eq_map_O2F (H : Subgroup G) : oTwoFIn H = (O2F ↥H).map H.subtype := by
  unfold oTwoFIn preimageModTwoCore O2F
  rw [preimage_congr_of_eq (X := ↥H) (CFSG.pCore 2 ↥H) (CFSG.Open.pCore 2 ↥H)
    (A3.pCore_eq_openCore 2 ↥H) (fun Y _ => CFSG.fittingSubgroup Y)]

omit [Finite G] in
theorem oTwoFstarIn_eq_map_O2Fstar (H : Subgroup G) :
    oTwoFstarIn H = (O2Fstar ↥H).map H.subtype := by
  unfold oTwoFstarIn preimageModTwoCore O2Fstar
  rw [preimage_congr_of_eq (X := ↥H) (CFSG.pCore 2 ↥H) (CFSG.Open.pCore 2 ↥H)
    (A3.pCore_eq_openCore 2 ↥H) (fun Y _ => CFSG.generalizedFitting Y)]

omit [Finite G] in
theorem oTwoEIn_eq_map_O2E (H : Subgroup G) : oTwoEIn H = (O2E ↥H).map H.subtype := by
  unfold oTwoEIn preimageModTwoCore O2E
  rw [preimage_congr_of_eq (X := ↥H) (CFSG.pCore 2 ↥H) (CFSG.Open.pCore 2 ↥H)
    (A3.pCore_eq_openCore 2 ↥H) (fun Y _ => CFSG.layer Y)]

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.A3Structure312Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace L3312

theorem oddNorm_of_isHat {Q X : Type} [Group Q] [Group X] (hQ : IsHat Q X)
    (hX : ∀ (W : Type) [Group W] [Finite W], Nonempty (W ≃* X) → AutSylowSelfNorm W)
    [Finite Q] (B : Subgroup Q) : OddNorm Q B := by
  obtain ⟨hq, -, ⟨e⟩⟩ := hQ
  exact AutSylowSelfNorm.oddNorm (autSylowSelfNorm_of_quotCenter hq.1 (hX _ ⟨e⟩)) B

variable {X : Type} [Group X]

theorem isMaxParabolic2_subgroupOf {L P : Subgroup X} (h : IsMaxParabolic2 L P) :
    IsMaxParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
  obtain ⟨hP, hne, hmax⟩ := h
  have hmapP : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hP.1
  refine ⟨(A312.isParabolic2_top_iff L _).mpr (by rw [hmapP]; exact hP), fun htop => hne ?_,
    fun Q hQ hQne hPQ => ?_⟩
  · rw [← hmapP, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · have h1 := hmax (Q.map L.subtype) ((A312.isParabolic2_top_iff L Q).mp hQ)
      (fun hQL => hQne ?_) (by rw [← hmapP]; exact Subgroup.map_mono hPQ)
    · apply Subgroup.map_injective L.subtype_injective
      rw [h1, hmapP]
    · apply Subgroup.map_injective L.subtype_injective
      rw [hQL, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem perfectCore_subgroupOf [Finite X] {L P : Subgroup X} (hPL : P ≤ L) :
    perfectCore (P.subgroupOf L) = (perfectCore P).subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPL,
    Subgroup.map_subgroupOf_eq_of_le ((perfectCore_le P).trans hPL)]

theorem oddNorm_lie2 (hLie : FactLie2Norm3312) [Finite X] {B L : Subgroup X}
    (hc : A312C2 B L) : OddNorm ↥L (B.subgroupOf L) := by
  obtain ⟨-, hL, P, hP, rfl⟩ := hc
  rw [← perfectCore_subgroupOf hP.1.1]
  intro A S hA hS hSB d hd hodd
  exact hLie _ hL A S _ hA hS (isMaxParabolic2_subgroupOf hP) hSB d hd hodd

end L3312

end CFSG.Quasithin.H13

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.CharP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.Faithful
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.OddCentral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

private theorem inf_centralizer_eq_bot {W : Type} [CommGroup W] [Finite W]
    {Y L A : Subgroup (MulAut W)} (hLY : L ≤ Y) (hF : Fstar Y = L) (hO2 : O2Trivial L)
    (hA : A ∈ E3.aSet 2 Y) :
    A ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥ := by
  classical
  have hAY : A ≤ Y := hA.1
  have hAab : IsElemAbelian2 A := hA.2.2.1
  set P : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (L : Set (MulAut W))
  have hPL : P ≤ L := fun x hx =>
    W4Row.mem_of_mem_centralizer_of_fstar_eq hLY hF (hAY hx.1) hx.2
  have hP2 : IsPGroup 2 P := (E3.isPGroup_of_isElemAbelian2 hAab).to_inf_left
  have hPZ : P.subgroupOf L ≤ Subgroup.center ↥L := by
    rw [← Subgroup.comap_map_eq_self_of_injective L.subtype_injective (Subgroup.center ↥L)]
    intro x hx
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_subgroupOf.mp hx).2 (y : MulAut W) y.2)
  exact hO2 P hPL (Subgroup.normal_of_le_center hPZ) hP2


theorem false_of_mem_aSet_two_of_normalizes {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L A X : Subgroup (MulAut W)} {t : StatedLieTag} {n p f : ℕ}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hLq : IsQuasisimple ↥L)
    (hO2 : O2Trivial L) (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : LieModel (↥L ⧸ Subgroup.center ↥L) t n p f) (hA : A ∈ E3.aSet 2 Y)
    (hXL : X ≤ L) (hXp : IsPGroup p ↥X) (hXZ : ¬ X ≤ (Subgroup.center ↥L).map L.subtype)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W))) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hAY : A ≤ Y := hA.1
  have hAne : A ≠ ⊥ := hA.2.1
  have hAab : IsElemAbelian2 A := hA.2.2.1
  have hLYnorm : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn
  have hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)) := hAY.trans hLYnorm
  have hAC : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥ :=
    inf_centralizer_eq_bot hLY hF hO2 hA
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hAp : Nat.Coprime (Nat.card A) p := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥A)).mp
      (E3.isPGroup_of_isElemAbelian2 hAab)
    rw [hn]
    exact (Nat.coprime_two_left.mpr hpodd).pow_left n
  obtain ⟨hRR, hBT⟩ := radRigid_holdsTits_of_lieModel (S := ↥L ⧸ Subgroup.center ↥L)
    hLq.2.1 hLq.2.2 hp hp2 hm
  obtain ⟨R, hRL, hRp, hAR, hARC⟩ :=
    exists_faithful_pSubgroup (G := MulAut W) (L := L) (A := A) (X := X)
      hp hLq hBT hRR hAL hAp hAC hXL hXp hXZ hAX
  have hRodd : Odd (Nat.card R) := by
    obtain ⟨m, hmcard⟩ := (IsPGroup.iff_card (p := p) (G := ↥R)).mp hRp
    rw [hmcard]
    exact hpodd.pow
  have hAcR : A ≤ Subgroup.centralizer (R : Set (MulAut W)) :=
    le_centralizer_of_mem_aSet_two_of_odd hW hA hRodd hAR
  have hAle : A ≤ A ⊓ Subgroup.centralizer (R : Set (MulAut W)) := le_inf le_rfl hAcR
  rw [hARC] at hAle
  exact hAne (le_bot_iff.mp hAle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

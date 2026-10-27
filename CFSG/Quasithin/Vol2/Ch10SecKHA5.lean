module

public import CFSG.Quasithin.Vol2.Ch10SecQ4Obl
public import CFSG.Quasithin.Vol2.Ch10SecKHA5c
public import CFSG.Quasithin.Vol2.Ch10SecKHA5o
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverFinal
public import CFSG.Quasithin.Vol2.Ch10SecKHA5i

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem factA314NoSL25Block
    : FactA314NoSL25Block := by
  intro Y _ hY hq S B hS hSB hs hLa hZ hc hQ
  have := hY.finite
  have hD : C10KH.IsSL25Group ↥B := C10KH.isSL25Group_of_block hs hLa hZ hc hQ
  have hqL : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) :=
    hs.2.2.2.1.resolve_right (L238.card_ne_three_of_isAltType le_rfl hLa)
  have hNorm : (B.subgroupOf (B ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSB)
  have hB : B ∈ lFamily S :=
    C1GN.mem_cComp_of_short hs hqL (A3.subnormal_of_normal le_sup_left hNorm)
  have hne : B ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective B.subtype := fun y =>
      ⟨⟨y, htop ▸ Subgroup.mem_top y⟩, rfl⟩
    have hN : ((CFSG.pCore 2 ↥B).map B.subtype).Normal :=
      Subgroup.Normal.map inferInstance _ hsurj
    have hp : IsPGroup 2 ((CFSG.pCore 2 ↥B).map B.subtype) :=
      (CFSG.pCore_isPGroup (G := ↥B) (p := 2)).map _
    have hle : (CFSG.pCore 2 ↥B).map B.subtype ≤ CFSG.pCore 2 Y := le_sSup ⟨hN, hp⟩
    rw [hY.o2] at hle
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective B.subtype_injective, hD.card_pCore,
      Subgroup.card_bot] at h1
    omega
  exact C10KH.noSL25_quasisimple Vol2Native.threeCoverFactCat A5.G3.a314ModelFacts
    C10KH.rank2NoSL25 (fun X _ _ h => C10KH.noSL25Norm_j4 h) Y hq hY.isSQTKCat hY.o2 S hS B hB
    hne hSB hD

end CFSG.Quasithin.Vol2.Ch10.SecF

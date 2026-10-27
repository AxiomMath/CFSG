module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixEAxis
public import CFSG.LocalAnalysis.SteinbergSFSingleCommPrincipalLayers
public import CFSG.LocalAnalysis.SteinbergSFSingleCommNextTwoCoresComplement

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores RootStandard TorusLayer PrincipalLayers
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped Matrix Pointwise

namespace LocalSixE

@[expose] def NontrivialModel (F : Type) [Group F] (n : ℕ) (S Y V : Subgroup F) (t : F) :
    Prop :=
  let R := CFSG.Open.standardComponentOddCore F
  let θ : F →* F ⧸ R := QuotientGroup.mk' R
  let D := normalClosure ((S.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R))
  IsSimpleGroup D ∧ (∃ x y : D, x * y ≠ y * x) ∧
    (StatedClassicalModel D .PSL 3 2 n ∨ StatedClassicalModel D .PSU 3 2 n) ∧
    SylowConclusion Y V t

end LocalSixE

open LocalSixE

namespace PrincipalLayers.AxisData

variable {F : Type} [Group F] [Finite F] {K : Type} [Field K] {n : ℕ}
  {S J Y V U : Subgroup F} {t : F} {hk : SL₂ K → F}

set_option quotPrecheck false in
local notation "𝐑" => CFSG.Open.standardComponentOddCore F
set_option quotPrecheck false in
local notation "θ" => QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F)
set_option quotPrecheck false in
local notation "𝐒𝐛" => S.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F))
set_option quotPrecheck false in
local notation "𝐃" => normalClosure ((S.map (QuotientGroup.mk'
  (CFSG.Open.standardComponentOddCore F)) : Subgroup (F ⧸ CFSG.Open.standardComponentOddCore F)) :
    Set (F ⧸ CFSG.Open.standardComponentOddCore F))

theorem exists_mul_ne_D (h : AxisData F K n S J Y V U t hk) : ∃ x y : 𝐃, x * y ≠ y * x := by
  obtain ⟨e, -⟩ := h.facts.2.2.2.1
  obtain ⟨a, b, hab⟩ := LinearUnitaryThree.exists_mul_ne_SL_two (k := K)
  refine ⟨⟨e a, Sb_le_D (e a).2⟩, ⟨e b, Sb_le_D (e b).2⟩, fun h1 => hab (e.injective ?_)⟩
  apply Subtype.ext
  rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  exact congrArg Subtype.val h1

theorem nontrivialModel (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector
      fun D _ => CFSG.Blueprint.Catalog D)
    (h : AxisData F K n S J Y V U t hk) (hVC : V ⊓ centralizer ({t} : Set F) ≤ U)
    (hV3 : Nat.card V = (2 ^ n) ^ 3) (hc : NontrivialAxisConclusion F K n S Y V t) :
    NontrivialModel F n S Y V t := by
  obtain ⟨hDs, hm⟩ := (h.models hSel hVC).1 hV3.ge
  exact ⟨hDs, h.exists_mul_ne_D, hm, (hc.2.2.1 n hm).2⟩

end PrincipalLayers.AxisData

end CFSG.LocalAnalysis.SymplecticFourStandard

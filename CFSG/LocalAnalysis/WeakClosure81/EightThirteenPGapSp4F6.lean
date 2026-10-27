module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapPull
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapMap
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4Iso

import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4F6Aux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  (statedSp_ext leviSp coe_leviSp torusHom coe_torusHom torusHom_mem_torus)
open CFSG.Assembly.LowTwoRank (StatedSp)
open Matrix

variable {F : Type} [Field F]

theorem sp4F6Data_unipotent {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card ↥(unipotent 2 F) = 256 ∧
    Nat.card ↥(unipotent 2 F ⊓ centralizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) :
      Set (StatedSp 2 F))) = 16 ∧
    CenterIrred (unipotent 2 F : Subgroup (StatedSp 2 F)) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num)
  exact ⟨by rw [card_unipotent, hF]; norm_num, wcgaps6_card_center hF,
    wcgaps6_centerIrred hF⟩

theorem sp4F6Data_statedSp {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (S : Sylow 2 (StatedSp 2 F)) :
    Nat.card ↥(S : Subgroup (StatedSp 2 F)) = 256 ∧
    Nat.card ↥((S : Subgroup (StatedSp 2 F)) ⊓ centralizer
      ((S : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F))) = 16 ∧
    CenterIrred (S : Subgroup (StatedSp 2 F)) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num)
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) 2 2
  haveI : Finite (StatedSp 2 F) := Subtype.finite
  haveI : Finite (Sylow 2 (StatedSp 2 F)) := Sylow.finite_of_finiteIndex P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 F) P S
  have hS : (S : Subgroup (StatedSp 2 F)) =
      (unipotent 2 F).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, hP, Subgroup.pointwise_smul_def]
    rfl
  obtain ⟨h256, hZ, hirr⟩ := sp4F6Data_unipotent hF
  refine ⟨?_, ?_, ?_⟩
  · rw [hS, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h256
  · rw [hS, wcgaps6_card_inf_centralizer_map (MulAut.conj g) (unipotent 2 F)]
    exact hZ
  · rw [hS]
    exact centerIrred_map (MulAut.conj g) hirr

theorem sp4F6Data_isSp4 {G : Type} [Group G] [Finite G] (h : IsSp4 G 2) (S : Sylow 2 G) :
    Nat.card ↥(S : Subgroup G) = 256 ∧
    Nat.card ↥((S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G)) = 16 ∧
    CenterIrred (S : Subgroup G) := by
  obtain ⟨F, hFld, hFin, hF, ⟨e⟩⟩ := exists_mulEquiv_statedSp_of_isSp4 h
  letI : Field F := hFld
  letI : Finite F := hFin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite (StatedSp 2 F) := Subtype.finite
  let T : Sylow 2 (StatedSp 2 F) :=
    @Sylow.mapSurjective 2 G _ _ (StatedSp 2 F) _ e.toMonoidHom e.surjective _ S
  obtain ⟨h256, hZ, hirr⟩ := sp4F6Data_statedSp hF T
  have hT : (T : Subgroup (StatedSp 2 F)) = (S : Subgroup G).map e.toMonoidHom :=
    @Sylow.coe_mapSurjective 2 G _ _ (StatedSp 2 F) _ e.toMonoidHom e.surjective _ S
  have hTS : T.map e.symm.toMonoidHom = (S : Subgroup G) := by
    rw [hT, Subgroup.map_map,
      show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G from by ext x; simp,
      Subgroup.map_id]
  refine ⟨?_, ?_, ?_⟩
  · rw [(Subgroup.card_map_of_injective (f := e.toMonoidHom) (K := (S : Subgroup G))
        e.injective).symm, ← hT]
    exact h256
  · have hZ' : Nat.card ↥((S.map e.toMonoidHom) ⊓ centralizer
        (((S.map e.toMonoidHom : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)))) = 16 := by
      rwa [hT] at hZ
    exact (wcgaps6_card_inf_centralizer_map e (S : Subgroup G)).symm.trans hZ'
  · rw [← hTS]
    exact centerIrred_map e.symm hirr

theorem borelGL32CenterOn_shapeSp4 : BorelGL32CenterOn ShapeSp4 :=
  borelGL32CenterOn_of_kills ShapeSp4 fun Y _ _ L hL S hSy => by
    obtain ⟨h256, hZ, hirr⟩ := sp4F6Data_isSp4 hL.2 hSy.toSylow
    exact borelKills_center_of_irred (S := (hSy.toSylow : Subgroup ↥L)) hSy.toSylow.isPGroup'
      (by rw [hZ, h256]; norm_num) hirr

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4Central
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4Par
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4Iso
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapMap
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)

private theorem wcgapsy_map_comp_symm {M : Type} [Group M] (e : M ≃* M) (H : Subgroup M) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    rw [← hyx, ← hzy]
    simpa using hz
  · intro hx
    exact Subgroup.mem_map.mpr ⟨e x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, by simp⟩

private theorem wcgapsy_map_symm_comp {M : Type} [Group M] (e : M ≃* M) (H : Subgroup M) :
    (H.map e.symm.toMonoidHom).map e.toMonoidHom = H := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    rw [← hyx, ← hzy]
    simpa using hz
  · intro hx
    exact Subgroup.mem_map.mpr ⟨e.symm x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, by simp⟩

private theorem wcgapsy_map_centralizer_eq {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (S : Subgroup M) :
    (Subgroup.centralizer (S : Set M)).map e.toMonoidHom =
      Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup M') : Set M') := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image (S : Set M) e.toMonoidHom
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx (e.toMonoidHom s) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)

private theorem wcgapsy_exists_sylow_eq_of_isSylowIn_top {M : Type} [Group M] [Finite M]
    {S : Subgroup M} (hS : IsSylowIn 2 S (⊤ : Subgroup M)) :
    ∃ P : Sylow 2 M, (P : Subgroup M) = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hS.isPGroup.toSylow ?_, IsPGroup.toSylow_coe _ _⟩
  have := hS.not_dvd_relIndex
  rwa [Subgroup.relIndex_top_right] at this

private theorem wcgapsy_charP_two_of_card_eq_four {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine charP_of_card_eq_prime_pow (p := 2) (f := 2) ?_
  rw [← Nat.card_eq_fintype_card, hF]
  norm_num

theorem rankTwoParabData_statedSp {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (S : Sylow 2 (StatedSp 2 F)) :
    RankTwoParabData (S : Subgroup (StatedSp 2 F)) := by
  haveI : CharP F 2 := wcgapsy_charP_two_of_card_eq_four hF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_unipotent (K := F) 2 2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 F) U S
  let e : StatedSp 2 F ≃* StatedSp 2 F := MulAut.conj g
  have hSmap : (S : Subgroup (StatedSp 2 F)) =
      (U : Subgroup (StatedSp 2 F)).map e.toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] <;> rfl
  have hUdata : RankTwoParabData (U : Subgroup (StatedSp 2 F)) := by
    rw [hU]
    exact rankTwoParabData_unipotent_sp4 (F := F) hF
  rw [hSmap]
  exact rankTwoParabData_map e hUdata

theorem centralKData_statedSp {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (S : Sylow 2 (StatedSp 2 F)) {A : Subgroup (StatedSp 2 F)}
    (hAS : A ≤ (S : Subgroup (StatedSp 2 F)))
    (hAc : A ≤ centralizer ((S : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)))
    (hA4 : Nat.card ↥A = 4) (hT : TISIn (⊤ : Subgroup (StatedSp 2 F)) A) :
    CentralKData (S : Subgroup (StatedSp 2 F)) A := by
  haveI : CharP F 2 := wcgapsy_charP_two_of_card_eq_four hF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_unipotent (K := F) 2 2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 F) U S
  let e : StatedSp 2 F ≃* StatedSp 2 F := MulAut.conj g
  let f : StatedSp 2 F ≃* StatedSp 2 F := e.symm
  have hSmap : (S : Subgroup (StatedSp 2 F)) =
      (U : Subgroup (StatedSp 2 F)).map e.toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] <;> rfl
  have hSf : (S : Subgroup (StatedSp 2 F)).map f.toMonoidHom =
      (U : Subgroup (StatedSp 2 F)) := by
    rw [hSmap]
    exact wcgapsy_map_comp_symm e (U : Subgroup (StatedSp 2 F))
  have hAU : (A.map f.toMonoidHom) ≤ (unipotent 2 F : Subgroup (StatedSp 2 F)) := by
    rw [← hU, ← hSf]
    exact Subgroup.map_mono (f := f.toMonoidHom) hAS
  have hAcU : (A.map f.toMonoidHom) ≤
      centralizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)) := by
    have h := Subgroup.map_mono (f := f.toMonoidHom) hAc
    rw [wcgapsy_map_centralizer_eq f (S : Subgroup (StatedSp 2 F)), hSf, hU] at h
    exact h
  have hA4' : Nat.card ↥(A.map f.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective, hA4]
  have hT' : TISIn (⊤ : Subgroup (StatedSp 2 F)) (A.map f.toMonoidHom) :=
    tisIn_top_map f hT
  have hUdata : CentralKData (unipotent 2 F : Subgroup (StatedSp 2 F))
      (A.map f.toMonoidHom) :=
    centralKData_unipotent_sp4 (F := F) hF hAU hAcU hA4' hT'
  have hSe : (unipotent 2 F : Subgroup (StatedSp 2 F)).map e.toMonoidHom =
      (S : Subgroup (StatedSp 2 F)) := by
    rw [← hU, ← hSmap]
  have hAe : (A.map f.toMonoidHom).map e.toMonoidHom = A :=
    wcgapsy_map_symm_comp e A
  have hmap : CentralKData ((unipotent 2 F : Subgroup (StatedSp 2 F)).map e.toMonoidHom)
      ((A.map f.toMonoidHom).map e.toMonoidHom) := centralKData_map e hUdata
  rw [hSe, hAe] at hmap
  exact hmap

theorem choiceOfKTop_statedSp {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (rk : Prop) : ChoiceOfKTop (StatedSp 2 F) rk := by
  refine choiceOfKTop_of_central_data rk fun S hS => ?_
  obtain ⟨P, rfl⟩ := wcgapsy_exists_sylow_eq_of_isSylowIn_top hS
  refine ⟨?_, Or.inr (rankTwoParabData_statedSp (F := F) hF P)⟩
  intro A hAS hAc _hAe hA4 hT
  exact centralKData_statedSp (F := F) hF P hAS hAc hA4 hT

theorem choiceOfKOn_shapeSp4 : ChoiceOfKOn ShapeSp4 :=
  choiceOfKOn_of_top ShapeSp4 fun Y _ _ L hL => by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_statedSp_of_isSp4 hL.2
    exact ⟨StatedSp 2 F, inferInstance, e, choiceOfKTop_statedSp hF _⟩

end CFSG.LocalAnalysis.WeakClosure81

end

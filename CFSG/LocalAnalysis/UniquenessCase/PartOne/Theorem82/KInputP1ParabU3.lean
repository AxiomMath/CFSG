module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Blueprint CFSG.Open
open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups
open scoped commutatorElement

theorem isCoatom_of_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {N : Subgroup G} (hN : IsCoatom (N.map e.toMonoidHom)) : IsCoatom N := by
  refine ⟨fun htop => hN.1 ?_, fun J hJ => ?_⟩
  · rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  · have hlt : N.map e.toMonoidHom < J.map e.toMonoidHom :=
      lt_of_le_of_ne (Subgroup.map_mono hJ.le) fun h =>
        hJ.ne (Subgroup.map_injective e.injective h)
    have := hN.2 _ hlt
    rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at this
    exact Subgroup.map_injective e.injective this

theorem isCoatom_and_solvable_normalizer_psu {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : LieModel X .PSU 3 2 f) (T : Sylow 2 X) :
    IsCoatom (Subgroup.normalizer ((T : Subgroup X) : Set X)) ∧
      Group.IsSolvable ↥(Subgroup.normalizer ((T : Subgroup X) : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (hX.statedClassicalModel_of_ne_zero (by norm_num))
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e T S
  have hN : (Subgroup.normalizer ((T : Subgroup X) : Set X)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [Subgroup.map_equiv_normalizer_eq, he', hS]
  have hst := UnitaryModel.normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq
  refine ⟨isCoatom_of_map_mulEquiv e' (by
    rw [hN]; exact UnitaryModel.isCoatom_normalizer_rootGroup J hJ hK hfix hq), ?_⟩
  have hsolv : Group.IsSolvable ↥(Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
    rw [hst]
    exact UnitaryModel.isSolvable_stabilizer_pinf J hJ hK hfix
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective).trans
      (MulEquiv.subgroupCongr hN)).toMonoidHom)
    ((Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective).trans
      (MulEquiv.subgroupCongr hN)).injective

theorem l3EvenParabolic_psu {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : LieModel X .PSU 3 2 f) (J K : Subgroup X) (hJ : J ≠ ⊤)
    (hpar : IsParabolicTwo ⊤ J) (hKJ : K ≤ J) (hK : ⁅K, K⁆ = K) : K = ⊥ := by
  obtain ⟨-, T, hT, hNT⟩ := hpar
  obtain ⟨hco, hsolv⟩ := isCoatom_and_solvable_normalizer_psu hX (sylowOfTopTwo hT)
  rw [coe_sylowOfTopTwo hT] at hco hsolv
  have hle : Subgroup.normalizer (T : Set X) ≤ J := by
    rw [top_inf_eq] at hNT
    exact hNT
  have hJeq : J = Subgroup.normalizer (T : Set X) := (hco.le_iff.mp hle).resolve_left hJ
  rw [hJeq] at hKJ
  haveI := hsolv
  exact eq_bot_of_perfect_of_le_solvable hKJ hK

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

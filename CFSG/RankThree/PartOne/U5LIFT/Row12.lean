module

public import CFSG.RankThree.PartOne.U5LIFT.Ctx
public import CFSG.RankThree.PartOne.LSTD.Frame
public import CFSG.RankThree.PartOne.LSTD.TorusFacts
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore
public import CFSG.RankThree.PartOne.S12.Facts

public section

namespace CFSG.RankThree.PartOne.U5LIFT

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Sec12Three
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.LSTD

theorem card_E_of_ne' {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (hF : Sec12Facts G p A c L E) (hEA : E ≠ A) : Nat.card E = p ^ 4 := by
  obtain ⟨-, r, -, -, -, -, hr8, hr9⟩ := hF.three
  refine hr9 ?_
  by_contra hlt
  exact hEA (hr8 (by omega))

theorem projU_mem_torusBar_iff {f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData 2 f K)
    (g : unitarySU 2 f K 5) :
    projU K f g ∈ torusBar K f ↔ (g : GL (Fin 5) K) ∈ torusSU 5 5 K := by
  have hcomap : (torusBar K f).comap (projU K f) =
      (torusSU 5 5 K).subgroupOf (unitarySU 2 f K 5) := by
    unfold torusBar
    rw [Subgroup.comap_map_eq, ker_projU]
    exact sup_eq_left.mpr (scalarsU_le_torus hU)
  have := Subgroup.ext_iff.mp hcomap g
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at this
  exact this

theorem exists_ctx_row12 (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G 5 A c L E) (hF : Sec12Facts G 5 A c L E) (hEA : E ≠ A)
    (hrow : RowModel 5 L 12) :
    ∃ (f : ℕ) (K : Type) (_ : Field K), 1 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧ ¬ 25 ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f ∧ Nonempty (U5Ctx A c L E f K) := by
  obtain ⟨-, hZ, f, hf1, h5, h25, hmod⟩ := hrow
  have hG : Sec12TwoGeneric 5 c L E := by
    rcases hF.two with hG | hS
    · exact hG
    · exfalso
      exact hZ (by rw [hS.center_card])
  have hE4 : Nat.card E = 5 ^ 4 := card_E_of_ne' hF hEA
  have R : Restr c L E (E ⊓ L) := restr_of_generic h hG
  have hcore : Table123Core 5 L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, hU, -, ε, hε⟩ := exists_r12iso hcore hGA hf1 h5 h25 hmod
  refine ⟨f, K, hKf, hf1, h5, h25, hmod, ⟨?_⟩⟩
  refine ⟨h, hE4, R, hU, two_le_of_five_dvd h5, h5,
    L.subtype.comp (ε.symm.toMonoidHom.comp (projU K f)), fun g => (ε.symm (projU K f g)).2,
    fun l hl => ?_, fun g hg => ?_, fun g => ?_⟩
  · obtain ⟨g, hg⟩ := projU_surjective (K := K) (f := f) (ε ⟨l, hl⟩)
    refine ⟨g, ?_⟩
    show ((ε.symm (projU K f g) : ↥L) : G) = l
    rw [hg, MulEquiv.symm_apply_apply]
  · have h1 : ε.symm (projU K f g) = 1 := Subtype.ext hg
    have h2 : projU K f g = 1 := by
      have := congrArg ε h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    rw [← ker_projU]
    exact h2
  · have h1 := hε (ε.symm (projU K f g))
    rw [MulEquiv.apply_symm_apply, projU_mem_torusBar_iff hU] at h1
    rw [← h1]
    show ((ε.symm (projU K f g) : ↥L) : G) ∈ E ↔ _
    exact ⟨fun hE => Subgroup.mem_inf.mpr ⟨hE, (ε.symm (projU K f g)).2⟩,
      fun hE => (Subgroup.mem_inf.mp hE).1⟩

end CFSG.RankThree.PartOne.U5LIFT

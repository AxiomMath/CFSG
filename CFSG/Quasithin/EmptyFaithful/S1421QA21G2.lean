module

public import CFSG.Quasithin.EmptyFaithful.S1421QA21Abs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2

public section

namespace CFSG.Quasithin.QA21

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L

set_option linter.unusedSectionVars false

section Sl2

variable {K : Type} [Field K]

theorem not_isSolvable_sl2 [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro hs
  have hsimple := sl2_isSimple hK4
  obtain ⟨a, b, hab⟩ := sl2_nonabelian hK4
  exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hs a b)

end Sl2

section Ordinary

variable {τ : Tag} {K : Type} [Field K]

theorem solvable_le_borelGroup
    (hN : ∀ i : Fin τ.rank, ¬ Group.IsSolvable ↥(posWeylGroup τ K i))
    {A : Subgroup (ModGL τ K)} (hAC : A ≤ adjointGroup τ K) (hUA : posUnipotent τ K ≤ A)
    (hA : Group.IsSolvable ↥A) : A ≤ borelGroup τ K := by
  have hle := (chevalley_positive_root_overgroup_parabolic_containment hAC hUA).1
  have hJ : {k | weylElt τ K k 1 ∈ A} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hk
    apply hN k
    have hNA : posWeylGroup τ K k ≤ A :=
      sup_le hUA ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hk))
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNA)
      (Subgroup.inclusion_injective hNA)
  rw [hJ, parabolicSubgroup_empty] at hle
  exact hle

theorem not_isSolvable_posWeylGroup [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    (i : Fin τ.rank) : ¬ Group.IsSolvable ↥(posWeylGroup τ K i) := by
  intro hs
  obtain ⟨ρ, hρ, hrange⟩ := exists_rankOne_injective (K := K) (τ := τ) i
  have hle : ρ.range ≤ posWeylGroup τ K i := by
    rw [hrange]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact posUnipotent_le_posWeylGroup i (xUnit_mem_posUnipotent i c)
    · exact yUnit_mem_posWeylGroup i c
  have hr : Group.IsSolvable ↥ρ.range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact not_isSolvable_sl2 hK4
    (Group.isSolvable_of_isSolvable_injective (f := (MonoidHom.ofInjective hρ).toMonoidHom)
      (MulEquiv.injective _))

end Ordinary

section G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem borelAmbient_g2 {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    BorelAmbient (ModGL Tag.G2 K) (adjointGroup Tag.G2 K) (posUnipotent Tag.G2 K)
      (borelGroup Tag.G2 K) (fun j : Fin 2 => parabolicSubgroup Tag.G2 K {g2Index j}) := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hself := (borel_self_normalizers Tag.G2 K).1
  refine ⟨posUnipotent_le_adjointGroup, ?_, hself.le, fun j => borelGroup_le_parabolicSubgroup _,
    fun A hAC hUA hA => solvable_le_borelGroup (not_isSolvable_posWeylGroup hK4) hAC hUA hA⟩
  rw [← hself]
  exact inf_le_right

theorem borelPkg_g2 {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : ChevalleyExceptionalModel X .G2 2 f) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup X, BorelPkg X U P := by
  obtain ⟨K, hF, hFin, hcp, φ, hK, hφU, hres, -⟩ := even_rank_two_residual_G2 hX hU
  have hf : 2 ≤ f := (exists_mulEquiv_G2_model hX).1
  exact ⟨_, (borelAmbient_g2 hK hf).borelPkg φ hφU hres⟩

end G2

end CFSG.Quasithin.QA21

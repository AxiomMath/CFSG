module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.RankThree.PartTwo.Census.OddClassical.SymplecticWitness
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Matrix Subgroup CFSG CFSG.RankThree.PartTwo.Census
  CFSG.RankThree.Classical CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

section Emb

variable {K : Type} [Field K]

@[expose] def planes12 : Fin 2 → Fin 3 := fun i => ⟨i.val + 1, by omega⟩

theorem planes12_injective : Function.Injective planes12 := by
  intro a b h
  have := congrArg Fin.val h
  simp only [planes12] at this
  exact Fin.ext (by omega)

theorem planes12_ne_zero (a : Fin 2) : planes12 a ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  change a.val + 1 = 0 at h'
  omega

theorem map_planes12_ne_inl_zero (a : Fin 2 ⊕ Fin 2) :
    Sum.map planes12 planes12 a ∉ coords (0 : Fin 3) := by
  intro hmem
  rcases a with a | a
  · rcases mem_coords.mp hmem with h | h
    · exact planes12_ne_zero a (Sum.inl_injective h)
    · exact absurd h (by simp)
  · rcases mem_coords.mp hmem with h | h
    · exact absurd h (by simp)
    · exact planes12_ne_zero a (Sum.inr_injective h)

@[expose] noncomputable def sp4Emb6 : StatedSp 2 K →* StatedProj (StatedSp 3 K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K))).comp
    (spEmbed planes12 planes12_injective)

theorem sp4Emb6_injective : Function.Injective (sp4Emb6 (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [sp4Emb6, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hg
  obtain ⟨u, hu⟩ := hg
  have h := congrArg (fun x : GL (Fin 3 ⊕ Fin 3) K => (x : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))
    hu
  have e := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
  have hnot : (Sum.inl (0 : Fin 3) : Fin 3 ⊕ Fin 3) ∉ Set.range (Sum.map planes12 planes12) := by
    rintro ⟨a, ha⟩
    exact map_planes12_ne_inl_zero a (by rw [ha]; exact mem_coords.mpr (Or.inl rfl))
  have e1 : (((spEmbed planes12 planes12_injective g : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (Sum.inl 0) (Sum.inl 0) = 1 := by
    have := isSupp_spEmbed planes12_injective g (Sum.inl 0) (Sum.inl 0) (fun h' => hnot h'.1)
    rw [Matrix.one_apply_eq] at this
    exact this
  rw [e1] at e
  have hu0 : (u : K) = 1 := by simpa [Matrix.GeneralLinearGroup.coe_scalar] using e
  have hu1 : u = 1 := Units.ext hu0
  subst hu1
  have hg1 : spEmbed planes12 planes12_injective g = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [← hu]
    simp
  exact spEmbed_injective planes12_injective (hg1.trans (map_one _).symm)

theorem planeInvolution_mem_suppGroup_zero :
    planeInvolution 3 K ∈ suppGroup (coords (0 : Fin 3)) := by
  rw [mem_suppGroup]
  intro r t hrt
  change ((planeInvolution 3 K : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K).val r t = _
  rw [coe_planeInvolution]
  rcases r with r | r <;> rcases t with t | t <;> fin_cases r <;> fin_cases t <;>
    simp_all [mem_coords, planeSign]

@[expose] noncomputable def sp6Invol : StatedProj (StatedSp 3 K) :=
  QuotientGroup.mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K))
    (planeInvolution 3 K)

theorem sp4Emb6_comm (g : StatedSp 2 K) : sp4Emb6 g * sp6Invol = sp6Invol * sp4Emb6 g := by
  have h1 : spEmbed planes12 planes12_injective g ∈ suppGroup (coords (0 : Fin 3))ᶜ := by
    refine suppGroup_mono ?_ (isSupp_spEmbed planes12_injective g)
    rintro _ ⟨a, rfl⟩ hmem
    exact map_planes12_ne_inl_zero a hmem
  have hc := commute_suppGroup_compl planeInvolution_mem_suppGroup_zero h1
  rw [sp4Emb6, sp6Invol, MonoidHom.comp_apply, ← map_mul, ← map_mul, ← hc.eq]

theorem orderOf_sp6Invol (h2 : (2 : K) ≠ 0) : orderOf (sp6Invol : StatedProj (StatedSp 3 K)) = 2 := by
  have hsq : (sp6Invol : StatedProj (StatedSp 3 K)) ^ 2 = 1 := by
    rw [sp6Invol, ← map_pow, planeInvolution_sq, map_one]
  refine orderOf_eq_prime hsq fun h1 => ?_
  rw [sp6Invol, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact planeInvolution_not_mem h2 (by norm_num) h1

end Emb

end CFSG.RankThree.PartOne.SLB4B

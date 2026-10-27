module

public import CFSG.RankThree.PartOne.S11d.OrthFixedLayer
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDickson
public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.RankThree.OrthogonalInvolutions

section Basic

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

abbrev piOrth (Q : QuadraticForm K V) : orthDerived Q →* ProjOrthDerived Q :=
  QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))

theorem piOrth_injective (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V] :
    Function.Injective (piOrth Q) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgs := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff g).mp hg)
  exact Subtype.ext (eq_one_of_mem_scalars_of_mem_orthDerived hQ g.2 hgs)

omit [CharP K 2] [FiniteDimensional K V] in
theorem piOrth_surjective : Function.Surjective (piOrth Q) := QuotientGroup.mk'_surjective _

theorem commute_of_piOrth_commute (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    {a b : orthDerived Q} (h : Commute (piOrth Q a) (piOrth Q b)) : Commute a b :=
  piOrth_injective hQ (by rw [map_mul, map_mul]; exact h.eq)

theorem centralizerImage_eq (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    (x : orthDerived Q) :
    centralizerImage Q (x : V ≃ₗ[K] V) =
      Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q)) := by
  rw [← map_centralizer_eq_centralizerImage x]
  ext t
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]
  · intro ht
    obtain ⟨g, rfl⟩ := piOrth_surjective t
    refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr (piOrth_injective hQ ?_), rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp ht

end Basic

section Layer

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}

@[expose] def DicksonDerived {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate) : Prop :=
  ∀ g : ↥(TauCeti.QuadraticMap.orthogonalGroup R), dicksonHom R hR g = 1 →
    (g : W ≃ₗ[K] W) ∈ orthDerived R

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem nontrivial_of_four_le_finrank_fixed {x : V ≃ₗ[K] V} [FiniteDimensional K V]
    (h4 : 4 ≤ finrank K (fixedSpace x)) : Nontrivial V :=
  Module.nontrivial_of_finrank_pos (R := K)
    (lt_of_lt_of_le (by norm_num : 0 < 4) (h4.trans (Submodule.finrank_le _)))

theorem isSolvable_centralizer_fixedComponentImage (hQ : (polarBilin Q).Nondegenerate)
    (hK : 4 ≤ Nat.card K) {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1) (h4 : 4 ≤ finrank K (fixedSpace x)) :
    Group.IsSolvable ↥(centralizerImage Q x ⊓
      Subgroup.centralizer (fixedComponentImage Q x : Set (ProjOrthDerived Q))) := by
  have : Nontrivial V := nontrivial_of_four_le_finrank_fixed h4
  have key : ∀ t : ↥(centralizerImage Q x ⊓
      Subgroup.centralizer (fixedComponentImage Q x : Set (ProjOrthDerived Q))),
      ∃ g : orthDerived Q, (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q x ∧
        (∀ w ∈ fixedSpace x, (g : V ≃ₗ[K] V) w = w) ∧ piOrth Q g = t.1 := by
    intro t
    obtain ⟨ht1, ht2⟩ := Subgroup.mem_inf.mp t.2
    obtain ⟨g, hg, hgt⟩ := ht1
    have hgM : (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q x := Subgroup.mem_subgroupOf.mp hg
    refine ⟨g, hgM, ?_, hgt⟩
    refine hx.fixes_of_commute hQ hK h4 hgM fun f hf v => ?_
    have hfΩ : f ∈ orthDerived Q := hx.supportedFixedDerived_le_orthDerived hf
    have hL : piOrth Q ⟨f, hfΩ⟩ ∈ fixedComponentImage Q x :=
      ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp ht2 _ hL
    rw [← hgt, ← map_mul, ← map_mul] at h1
    have h2 := congrArg (fun a : orthDerived Q => (a : V ≃ₗ[K] V) v) (piOrth_injective hQ h1)
    exact h2.symm
  refine Group.isSolvable_of_comm fun a b => ?_
  obtain ⟨ga, hga, hfa, hta⟩ := key a
  obtain ⟨gb, hgb, hfb, htb⟩ := key b
  have hcomm : (ga : V ≃ₗ[K] V) * gb = gb * ga :=
    hx.commute_of_fixes_fixedSpace hmult (Subgroup.mem_inf.mp hga).2 (Subgroup.mem_inf.mp hgb).2
      hfa hfb
  apply Subtype.ext
  change a.1 * b.1 = b.1 * a.1
  rw [← hta, ← htb, ← map_mul, ← map_mul]
  exact congrArg (piOrth Q) (Subtype.ext hcomm)

theorem mem_fixedComponentImage_of_two_pow (hQ : (polarBilin Q).Nondegenerate)
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hodd : Odd p)
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1) (h4 : 4 ≤ finrank K (fixedSpace x))
    (hD : DicksonDerived (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate)
    {t : ProjOrthDerived Q} (ht : t ∈ centralizerImage Q x) (h2 : ∃ k : ℕ, orderOf t = 2 ^ k) :
    t ∈ fixedComponentImage Q x := by
  have : Nontrivial V := nontrivial_of_four_le_finrank_fixed h4
  obtain ⟨k, hk⟩ := h2
  obtain ⟨g, hg, rfl⟩ := ht
  have hgM : (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q x := Subgroup.mem_subgroupOf.mp hg
  have hgo : orderOf g = 2 ^ k := by
    rw [← hk]
    exact (orderOf_injective (piOrth Q) (piOrth_injective hQ) g).symm
  have hgk : (g : V ≃ₗ[K] V) ^ (2 ^ k) = 1 := by
    have := pow_orderOf_eq_one g
    rw [hgo] at this
    exact congrArg Subtype.val this
  have hgR : ∀ r ∈ othersSpace x.toLinearMap (X - 1), (g : V ≃ₗ[K] V) r = r :=
    hx.apply_eq_of_two_pow hmult (Subgroup.mem_inf.mp hgM).2 hgk
  have hblock : (g : V ≃ₗ[K] V) ∈ supportedBlock Q x (X - 1) := mem_supportedBlock.mpr ⟨hgM, hgR⟩
  have hr : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    by_contra hnot
    have hbot := fixedSpace_eq_bot_of_not_mem hnot
    rw [hbot, finrank_bot] at h4
    omega
  have hgO : (g : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (Subgroup.mem_inf.mp hgM).1
  have hdick : dicksonHom Q hQ ⟨g, hgO⟩ = 1 := dicksonHom_apply_orthDerived_eq_one hQ g.2
  rw [hx.dicksonHom_eq_restrict_of_mem_supportedBlock hodd hQ hr hblock] at hdick
  have hmem := hD _ hdick
  refine ⟨g, Subgroup.mem_subgroupOf.mpr (mem_supportedFixedDerived.mpr ⟨hblock, ?_⟩), rfl⟩
  exact hmem

end Layer

end CFSG.RankThree.PartOne

module

public import CFSG.Timmesfeld.ARS.DegenUniform
public import CFSG.Timmesfeld.Transvection.Defs
public import CFSG.Open.LocalVocabulary
import CFSG.ClassicalGroups.PCoreSection
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

@[expose] def closureStab (Δ : Set (Subgroup H)) : Subgroup H :=
  ⨅ D ∈ Δ, stabSet (Degen.cl Δ D)

theorem mem_closureStab {g : H} :
    g ∈ closureStab Δ ↔ ∀ D ∈ Δ, g ∈ stabSet (Degen.cl Δ D) := by
  simp only [closureStab, Subgroup.mem_iInf]

namespace IsTransvectionClass

theorem conjSub_mem_gen (hΔ : IsTransvectionClass Δ) :
    ∀ X ∈ Δ, ∀ g ∈ gen Δ, conjSub X g ∈ Δ :=
  fun X hX g _ => hΔ.root.conjSub_mem hX g

theorem stabSet_eq_top (hΔ : IsTransvectionClass Δ) : stabSet Δ = ⊤ :=
  eq_top_iff.2 fun g _ => Degen.mem_stabSet_of_mem_gen hΔ.conjSub_mem_gen
    (by rw [show gen Δ = ⊤ from hΔ.root.gen]; exact Subgroup.mem_top g)

theorem noIsolated_of_center_eq_bot (hΔ : IsTransvectionClass Δ)
    (hZ : Subgroup.center H = ⊥) : NoIsolated Δ := by
  by_contra hno
  simp only [NoIsolated, not_forall, not_exists, not_and] at hno
  obtain ⟨A₀, hA₀, hA₀opp⟩ := hno
  have hA₀c : ∀ B ∈ Δ, Commuting A₀ B := by
    intro B hB
    by_cases hBA : A₀ = B
    · subst hBA; exact hΔ.root.commuting_self hA₀
    · rcases hΔ.commuting_or_opposite hA₀ hB hBA with h | h
      · exact h
      · exact absurd h (hA₀opp B hB)
  have htop : (⊤ : Subgroup H) ≤ Subgroup.centralizer (A₀ : Set H) := by
    rw [← hΔ.root.gen]
    exact iSup₂_le fun B hB => commuting_iff_le_centralizer.1 (hA₀c B hB)
  have hle : A₀ ≤ Subgroup.center H := fun a ha => Subgroup.mem_center_iff.2 fun g =>
    ((Subgroup.mem_centralizer_iff.1 (htop (Subgroup.mem_top g))) a ha).symm
  rw [hZ, le_bot_iff] at hle
  exact hΔ.root.ne_bot A₀ hA₀ hle

theorem closureStab_normal (hΔ : IsTransvectionClass Δ) : (closureStab Δ).Normal := by
  have hst : ∀ h : H, h ∈ stabSet Δ := fun h => by
    rw [hΔ.stabSet_eq_top]; exact Subgroup.mem_top h
  refine ⟨fun g hg h => mem_closureStab.2 fun D hD => ?_⟩
  rw [mem_stabSet, conjSet_mul, conjSet_mul, Degen.conjSet_cl (hst h⁻¹),
    mem_stabSet.1 ((mem_closureStab.1 hg) _ (hΔ.root.conjSub_mem hD h⁻¹)),
    Degen.conjSet_cl (hst h), ← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem gen_cl_inf_closureStab_le (hΔ : IsTransvectionClass Δ) {E : Subgroup H}
    (hE : E ∈ Δ) :
    gen (Degen.cl Δ E) ⊓ closureStab Δ ≤ pCoreOf 2 (closureStab Δ) := by
  refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf inf_le_right ?_ ?_
  · intro x hx y hy
    obtain ⟨hyE, hyS⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨?_, (closureStab Δ).mul_mem ((closureStab Δ).mul_mem hx hyS)
      ((closureStab Δ).inv_mem hx)⟩
    have h1 : x * y * x⁻¹ ∈ conjSub (gen (Degen.cl Δ E)) x := conj_mem_conjSub x hyE
    rwa [conjSub_gen, mem_stabSet.1 ((mem_closureStab.1 hx) E hE)] at h1
  · intro y
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, pow_two]
    exact Degen.mul_self_of_mem_gen_cl hΔ.root subset_rfl (Subgroup.mem_inf.1 y.2).1

theorem pCoreOf_closureStab_normal (hΔ : IsTransvectionClass Δ) :
    (pCoreOf 2 (closureStab Δ)).Normal := by
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (closureStab Δ)
  rw [Subgroup.normalizer_eq_top_iff.2 hΔ.closureStab_normal, top_le_iff,
    Subgroup.normalizer_eq_top_iff] at h
  exact h

theorem normCl_le_closureStab [Finite H] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    {E F : Subgroup H} (hE : E ∈ Δ) (hF : F ∈ Δ) (hEF : ¬ Commuting E F) :
    Degen.normCl Δ E F ≤ closureStab Δ := by
  intro x hx
  refine mem_closureStab.2 fun D hD => ?_
  by_cases hED : Commuting E D
  · exact Degen.gen_cl_le_stabSet_of_commuting hE hED (Subgroup.mem_inf.1 hx).1
  · exact (Subgroup.mem_inf.1 (Degen.normCl_le_normCl hΔ.root hiso subset_rfl
      hΔ.conjSub_mem_gen hΔ.noSpecial hE hF hD hEF hED hx)).2

theorem gen_cl_eq [Finite H] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    (h2 : pCoreOf 2 (closureStab Δ) = ⊥) {E : Subgroup H} (hE : E ∈ Δ) :
    gen (Degen.cl Δ E) = E := by
  refine le_antisymm (fun y hy => ?_) (le_gen (Degen.mem_cl_self hE))
  obtain ⟨F, hF, hEF⟩ := hiso E hE
  have hEF' : ¬ Commuting E F := hEF.not_commuting (hΔ.root.ne_bot E hE)
  obtain ⟨a, ha, hya⟩ := Degen.exists_mul_mem_normCl_of_mem_gen hΔ.root subset_rfl
    hΔ.conjSub_mem_gen hΔ.noSpecial hE hF hEF' hy
  have h1 : y * a ∈ pCoreOf 2 (closureStab Δ) :=
    hΔ.gen_cl_inf_closureStab_le hE (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hya).1,
      hΔ.normCl_le_closureStab hiso hE hF hEF' hya⟩)
  rw [h2, Subgroup.mem_bot] at h1
  rw [eq_inv_of_mul_eq_one_left h1, hΔ.root.inv_eq hE ha]
  exact ha

theorem pointsDetermined_of_forall_nilpotent [Finite H]
    (hΔ : IsTransvectionClass Δ)
    (hN : ∀ N : Subgroup H, N.Normal → Group.IsNilpotent N → N = ⊥) :
    PointsDetermined Δ := by
  have hZ : Subgroup.center H = ⊥ := hN _ inferInstance inferInstance
  have hiso := hΔ.noIsolated_of_center_eq_bot hZ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : pCoreOf 2 (closureStab Δ) = ⊥ :=
    hN _ hΔ.pCoreOf_closureStab_normal
      (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 _).isNilpotent
  intro A hA B hB hAB
  have hBA : B ∈ Degen.cl Δ A := ⟨hB, hAB⟩
  have hAB' : A ∈ Degen.cl Δ B := ⟨hA, fun C hC => (hAB C hC).symm⟩
  exact le_antisymm ((le_gen hAB').trans (hΔ.gen_cl_eq hiso h2 hB).le)
    ((le_gen hBA).trans (hΔ.gen_cl_eq hiso h2 hA).le)

end IsTransvectionClass
end CFSG.Timmesfeld.Transvection

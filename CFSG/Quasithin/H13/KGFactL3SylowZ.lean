module

public import CFSG.Quasithin.H13.A5S136abQ
public import CFSG.GH74.KGroups.L3EpsSylow
public import CFSG.Quasithin.Vol2.KGFactL3EvenMat

public section

namespace CFSG.Quasithin.H13.KGL3Syl

open Matrix CFSG.Quasithin.H13.Ch4.KGSL3 CFSG.Quasithin.H13.KGL3Even
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank

theorem isCyclic_center_of {X : Type*} [Group X] {T : Subgroup X}
    (h : IsCyclic ↥(T ⊓ Subgroup.centralizer (T : Set X))) : IsCyclic (Subgroup.center ↥T) := by
  let f : ↥(T ⊓ Subgroup.centralizer (T : Set X)) →* Subgroup.center ↥T :=
    { toFun := fun z => ⟨⟨z, (Subgroup.mem_inf.mp z.2).1⟩, Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp z.2).2) g g.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine isCyclic_of_surjective f fun w => ⟨⟨w.1.1, Subgroup.mem_inf.mpr ⟨w.1.2,
    Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩⟩, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨g, hg⟩)

theorem isCyclic_of_card_le_two {A : Type*} [Group A] [Finite A] (h : Nat.card A ≤ 2) :
    IsCyclic A := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  rcases (show Nat.card A = 1 ∨ Nat.card A = 2 by omega) with h1 | h2
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h2

theorem isCyclic_center_sylow_odd {X : Type} [Group X] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2) (hX : StatedClassicalModel X t 3 p f)
    (T : Sylow 2 X) : IsCyclic (Subgroup.center ↥(T : Subgroup X)) :=
  isCyclic_center_of (CFSG.GH74.KGroups.L3Eps.l3eps_center_sylow ht hp2 hX T.isPGroup'
    fun _ h hle => (T.is_maximal' h hle).le).1

section Unitri

variable {F : Type} [Field F]

theorem uSL_mem_unitri (c₀ c₁ : F) : uSL c₀ c₁ ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change uMat c₀ c₁ i j = 0
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [uMat]
  · change uMat c₀ c₁ i i = 1
    fin_cases i <;> simp [uMat]

theorem vSL_mem_unitri (a c : F) : vSL a c ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change vMat a c i j = 0
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [vMat]
  · change vMat a c i i = 1
    fin_cases i <;> simp [vMat]

theorem center_unitri_entries {u : ↥(unitriangular 3 F)}
    (hu : u ∈ Subgroup.center ↥(unitriangular 3 F)) :
    ((u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧
      ((u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
  have hcross : ∀ s ∈ unitriangular 3 F,
      ((u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 *
        (s : Matrix (Fin 3) (Fin 3) F) 1 2 = (s : Matrix (Fin 3) (Fin 3) F) 0 1 *
          ((u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 := by
    intro s hs
    have hc : ((s : Matrix (Fin 3) (Fin 3) F) *
        ((u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 0 2 =
        (((u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (s : Matrix (Fin 3) (Fin 3) F)) 0 2 :=
      congrArg (fun g : ↥(unitriangular 3 F) =>
        ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2)
        (Subgroup.mem_center_iff.mp hu ⟨s, hs⟩)
    rw [unitri_entries hs, unitri_entries u.2] at hc
    simp [Matrix.mul_apply, Fin.sum_univ_three] at hc
    linear_combination -hc
  have h1 := hcross _ (uSL_mem_unitri 0 1)
  have h2 := hcross _ (vSL_mem_unitri 1 0)
  change _ * uMat 0 1 1 2 = uMat 0 1 0 1 * _ at h1
  change _ * vMat 1 0 1 2 = vMat 1 0 0 1 * _ at h2
  simp [uMat, vMat] at h1 h2
  exact ⟨h1, h2.symm⟩

theorem card_center_unitri_le [Finite F] :
    Nat.card (Subgroup.center ↥(unitriangular 3 F)) ≤ Nat.card F := by
  refine Nat.card_le_card_of_injective
    (fun u : Subgroup.center ↥(unitriangular 3 F) =>
      (((u : ↥(unitriangular 3 F)) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2)
    fun u v huv => ?_
  obtain ⟨hu1, hu2⟩ := center_unitri_entries u.2
  obtain ⟨hv1, hv2⟩ := center_unitri_entries v.2
  refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
  rw [unitri_entries (u : ↥(unitriangular 3 F)).2, unitri_entries (v : ↥(unitriangular 3 F)).2,
    hu1, hu2, hv1, hv2]
  simp only at huv
  rw [huv]

end Unitri

theorem isCyclic_center_sylow_psl3_two {X : Type} [Group X] [Finite X]
    (hX : StatedClassicalModel X .PSL 3 2 1) (T : Sylow 2 X) :
    IsCyclic (Subgroup.center ↥(T : Subgroup X)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.KGroups.L3Eps.exists_projectiveSL_equiv hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have : Finite (projectiveSL 3 F) := Finite.of_equiv X e.toEquiv
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  let T' : Sylow 2 (projectiveSL 3 F) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have e₁ : ↥(T : Subgroup X) ≃* ↥(T' : Subgroup (projectiveSL 3 F)) :=
    (T : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective
  have e₃ : ↥(Q : Subgroup (projectiveSL 3 F)) ≃* ↥(unitriangular 3 F) :=
    (MulEquiv.subgroupCongr hQ).trans (unitriangularEquivProj 3).symm
  have hZ := Subgroup.centerCongr ((e₁.trans (Sylow.equiv T' Q)).trans e₃)
  refine isCyclic_of_card_le_two ?_
  rw [Nat.card_congr hZ.toEquiv]
  calc _ ≤ Nat.card F := card_center_unitri_le
    _ = 2 := by rw [hF, pow_one]

theorem factL3SylowCenterCyclic_holds : CFSG.Quasithin.H13.A5.FactL3SylowCenterCyclic := by
  intro s p e _ _ hpe X _ _ hX T
  by_cases hp2 : p = 2
  · subst hp2
    have he1 : e = 1 := hpe.resolve_left fun h => h rfl
    subst he1
    cases s
    · exfalso
      have hm : StatedClassicalModel X .PSU 3 2 1 := hX
      obtain ⟨-, -, -, hne⟩ := hm.1
      exact hne rfl
    · exact isCyclic_center_sylow_psl3_two hX T
  · cases s
    · exact isCyclic_center_sylow_odd (t := .PSU) (Or.inr rfl) hp2 hX T
    · exact isCyclic_center_sylow_odd (t := .PSL) (Or.inl rfl) hp2 hX T

end CFSG.Quasithin.H13.KGL3Syl

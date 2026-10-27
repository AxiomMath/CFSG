module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Roots
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart7
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.RankThree.PartOne.K133H.F4Weyl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangInner

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem f4_root_eq_of_modp
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c c' : Fin Tag.F4.rank → ℤ}
    (hc : IsRoot .F4 c) (hc' : IsRoot .F4 c') (h : ∀ j, (c' j : ZMod p) = (c j : ZMod p)) :
    c' = c := by
  choose v hv using fun j =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub (c j) (c' j) p).1 (h j).symm
  have hd : c' - c = (p : ℤ) • v := funext fun j => by
    rw [Pi.sub_apply, hv j, Pi.smul_apply, smul_eq_mul]
  by_contra hne
  have hv0 : v ≠ 0 := by
    intro hv0
    apply hne
    rw [hv0, smul_zero] at hd
    exact sub_eq_zero.mp hd
  have hpos : 0 < iform v v := iform_self_pos hv0
  have hdd : iform (c' - c) (c' - c) = (p : ℤ) ^ 2 * iform v v := by
    rw [hd, iform_smul_left, iform_smul_right]
    ring
  have hexp : iform (c' - c) (c' - c) = iform c' c' - 2 * iform c' c + iform c c := by
    rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm c c']
    ring
  have hcc := CFSG.SeitzReduction.F4Pilot.iform_self_eq_two_or_four hc
  have hcc' := CFSG.SeitzReduction.F4Pilot.iform_self_eq_two_or_four hc'
  have hcross : -4 ≤ iform c' c := by
    have h1 := ggTBJ_f4_abs_corootPair_le hc' hc
    have h2 := corootPair_mul hc c'
    have h3 := abs_le.1 h1
    rw [iform_comm c c'] at h2
    rcases hcc with h4 | h4 <;> rw [h4] at h2 <;> nlinarith
  have hR : (2 : ℤ) ∣ (p : ℤ) ^ 2 * iform v v := by
    rw [← hdd, hexp]
    omega
  have hP : Odd ((p : ℤ) ^ 2) := ((Int.odd_coe_nat p).mpr (hp.odd_of_ne_two hp2)).pow
  have hQ : Even (iform v v) :=
    (Int.even_mul.mp (even_iff_two_dvd.mpr hR)).resolve_left (Int.not_even_iff_odd.mpr hP)
  have hvv : 2 ≤ iform v v := by
    obtain ⟨r, hr⟩ := hQ
    omega
  have hp3 : (3 : ℤ) ≤ p := by
    have h2 := hp.two_le
    have : p ≠ 2 := hp2
    omega
  have h9 : (9 : ℤ) ≤ (p : ℤ) ^ 2 := by nlinarith
  have hlow : (9 : ℤ) * 2 ≤ (p : ℤ) ^ 2 * iform v v :=
    mul_le_mul h9 hvv (by norm_num) (by positivity)
  rcases hcc with h4 | h4 <;> rcases hcc' with h5 | h5 <;> linarith

theorem mem_closure_rootReflection_of_fix_F4
    {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin Tag.F4.rank → Lˣ} (ha : ∀ i, a i ^ p = 1) (i : KernelComponent (rootCharHom a))
    {w : WeylGroup .F4} (hw : w ∈ rootCharStabilizerSubgroup a)
    (hfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      ∀ j, ((w • c) j : ZMod p) = (c j : ZMod p)) :
    w ∈ Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) := by
  replace hfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      w • c = c := fun c hc hcΨ =>
    f4_root_eq_of_modp hp hp2 hc.1 (IsRoot.smul hc.1 w) (hfix c hc hcΨ)
  have hwK : w ∈ kernelReflectionGroup a := by
    by_cases h3 : p = 3
    · subst p
      rw [CFSG.StandardType.F4ExplicitPos.ThreeExact.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three_without13604
        a ha] at hw
      exact hw
    · refine mem_kernelReflectionGroup_of_coprime hp ha hw ?_
      have hcard : orderOf w ∣ 1152 := by
        rw [← CFSG.RankThree.PartOne.K133H.card_weylGroup_F4]
        exact orderOf_dvd_natCard w
      refine Nat.Coprime.coprime_dvd_left hcard ?_
      have h1152 : (1152 : ℕ) = 2 ^ 7 * 3 ^ 2 := by norm_num
      rw [h1152]
      refine Nat.coprime_mul_iff_left.2 ⟨Nat.Coprime.pow_left _ ?_, Nat.Coprime.pow_left _ ?_⟩
      · exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
      · exact (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm h3)
  obtain ⟨u, huC, hu⟩ := f4Three_exists_restrict i hwK
  have hset : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) =
      Subgroup.closure {s : WeylGroup .F4 | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ} := by
    congr 1
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩
  have huC' : u ∈ Subgroup.closure {s : WeylGroup .F4 | ∃ γ ∈ componentRoots (rootCharHom a) i,
      s = rootReflection γ} := hset ▸ huC
  have huA : u ∈ Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) :=
    hset.symm ▸ huC
  have hA_le_K : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) ≤
      kernelReflectionGroup a := by
    have hEq : kernelReflectionGroup a = kernelWeylGroup (rootCharHom a) := rfl
    rw [hEq, kernelWeylGroup_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, rfl⟩
    exact Subgroup.subset_closure ⟨γ, hγ.1, rfl⟩
  have hA_fix : ∀ u ∈ Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i),
      ∀ d ∈ kernelRoots (rootCharHom a), d ∉ componentRoots (rootCharHom a) i → u • d = d := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem r hr =>
      obtain ⟨γ, hγ, rfl⟩ := hr
      intro d hd hdΨ
      have hdi : (⟦⟨d, hd⟩⟧ : KernelComponent (rootCharHom a)) ≠ i := by
        intro h
        exact hdΨ ⟨hd, h⟩
      exact rootReflection_smul_eq_of_ne hdi.symm hγ ⟨hd, rfl⟩
    | one =>
      intro d _ _
      rw [one_smul]
    | mul x y _ _ hx hy =>
      intro d hd hdΨ
      rw [mul_smul, hy d hd hdΨ]
      exact hx d hd hdΨ
    | inv x _ hx =>
      intro d hd hdΨ
      simpa [hx d hd hdΨ] using inv_smul_smul x d
  have hzu_in : ∀ γ ∈ componentRoots (rootCharHom a) i, (w * u⁻¹) • γ = γ := by
    intro γ hγ
    rw [mul_smul]
    have huγ : u⁻¹ • γ ∈ componentRoots (rootCharHom a) i :=
      (f4Three_smul_mem_component_iff i (inv_mem huC') γ).2 hγ
    rw [hu (u⁻¹ • γ) huγ, smul_inv_smul]
  have hzu_out : ∀ d ∈ kernelRoots (rootCharHom a), d ∉ componentRoots (rootCharHom a) i →
      (w * u⁻¹) • d = d := by
    intro d hd hdΨ
    rw [mul_smul]
    have hufix : u⁻¹ • d = d := by
      have h := hA_fix u huA d hd hdΨ
      calc u⁻¹ • d = u⁻¹ • (u • d) := by rw [h]
        _ = d := inv_smul_smul u d
    rw [hufix, hfix d hd hdΨ]
  have hK_le_U : kernelReflectionGroup a ≤ unionWeylGroup (rootCharHom a) Set.univ := by
    have hEq : kernelReflectionGroup a = kernelWeylGroup (rootCharHom a) := rfl
    rw [hEq, kernelWeylGroup_eq_closure, closure_rootReflection_kernelRoots]
    exact iSup_le fun j => componentWeylGroup_le_unionWeylGroup (Set.mem_univ j)
  have hunion : unionRoots (rootCharHom a) (Set.univ : Set (KernelComponent (rootCharHom a))) =
      kernelRoots (rootCharHom a) := by
    ext α
    exact ⟨fun h => h.1, fun h => ⟨h, Set.mem_univ _⟩⟩
  have hz1 : w * u⁻¹ = 1 := by
    refine CFSG.LieType.Chevalley.eq_one_of_forall_smul_eq (J := Set.univ)
      (hK_le_U (mul_mem hwK (inv_mem (hA_le_K huA)))) ?_
    intro α hα
    rw [hunion] at hα
    by_cases hαΨ : α ∈ componentRoots (rootCharHom a) i
    · exact hzu_in α hαΨ
    · exact hzu_out α hα hαΨ
  rw [mul_inv_eq_one.1 hz1]
  exact huA

end CFSG.StandardType

end

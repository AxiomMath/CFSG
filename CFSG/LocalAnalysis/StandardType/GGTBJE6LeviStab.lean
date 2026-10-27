module

public import Certificates.Certificate13724
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FiveAux.Steinberg
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangInner
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Roots
public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem e6_root_eq_of_modp
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c c' : Fin Tag.E6.rank → ℤ}
    (hc : IsRoot .E6 c) (hc' : IsRoot .E6 c') (h : ∀ j, (c' j : ZMod p) = (c j : ZMod p)) :
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
  have hcc : iform c c = 2 :=
    CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two (τ := Tag.E6) (by decide) hc
  have hcc' : iform c' c' = 2 :=
    CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two (τ := Tag.E6) (by decide) hc'
  have hcross : |iform c' c| ≤ 2 := by
    have h1 := ggTBJ_e6_abs_corootPair_le hc hc'
    have h2 := corootPair_mul hc' c
    rw [hcc'] at h2
    have h4 : corootPair c' c = iform c' c := by omega
    rwa [h4] at h1
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
    omega
  have h9 : (9 : ℤ) ≤ (p : ℤ) ^ 2 := by nlinarith
  have hlow : (9 : ℤ) * 2 ≤ (p : ℤ) ^ 2 * iform v v :=
    mul_le_mul h9 hvv (by norm_num) (by positivity)
  have hup : iform (c' - c) (c' - c) ≤ 8 := by
    rw [hexp, hcc, hcc']
    have h3 := abs_le.1 hcross
    linarith
  rw [← hdd] at hlow
  linarith

theorem mem_closure_rootReflection_of_fix_E6_of_stab
    {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin Tag.E6.rank → Lˣ} (hstab : rootCharStabilizerSubgroup a = kernelReflectionGroup a)
    (i : KernelComponent (rootCharHom a)) {w : WeylGroup .E6}
    (hw : w ∈ rootCharStabilizerSubgroup a)
    (hfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      ∀ j, ((w • c) j : ZMod p) = (c j : ZMod p)) :
    w ∈ Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) := by
  replace hfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      w • c = c := fun c hc hcΨ =>
    e6_root_eq_of_modp hp hp2 hc.1 (IsRoot.smul hc.1 w) (hfix c hc hcΨ)
  have hwK : w ∈ kernelReflectionGroup a := hstab ▸ hw
  obtain ⟨u, huC, hu⟩ := f4Three_exists_restrict i hwK
  have hset : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) =
      Subgroup.closure {s : WeylGroup .E6 | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ} := by
    congr 1
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩
  have huC' : u ∈ Subgroup.closure {s : WeylGroup .E6 | ∃ γ ∈ componentRoots (rootCharHom a) i,
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

theorem mem_closure_rootReflection_of_fix_E6
    {L : Type} [Field L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {a : Fin Tag.E6.rank → Lˣ}
    (ha : ∀ i, a i ^ p = 1) (i : KernelComponent (rootCharHom a)) {w : WeylGroup .E6}
    (hw : w ∈ rootCharStabilizerSubgroup a)
    (hfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      ∀ j, ((w • c) j : ZMod p) = (c j : ZMod p)) :
    w ∈ Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) := by
  have hstab : rootCharStabilizerSubgroup a = kernelReflectionGroup a := by
    by_cases h5 : p = 5
    · subst p
      exact CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E6_five
        a ha
    · refine le_antisymm (fun w hw => ?_) (kernelReflectionGroup_le a)
      refine mem_kernelReflectionGroup_of_coprime hp ha hw ?_
      have hcard : orderOf w ∣ 51840 := by
        rw [← CFSG.RankThree.E6.card_weylGroup_E6]
        exact orderOf_dvd_natCard w
      refine Nat.Coprime.coprime_dvd_left hcard ?_
      have h51840 : (51840 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 := by norm_num
      rw [h51840, Nat.coprime_mul_iff_left]
      refine ⟨?_, (Nat.coprime_primes Nat.prime_five hp).2 (Ne.symm h5)⟩
      rw [Nat.coprime_mul_iff_left]
      exact ⟨Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)),
        Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))⟩
  exact mem_closure_rootReflection_of_fix_E6_of_stab hp hp2 hstab i hw hfix

end CFSG.StandardType

end

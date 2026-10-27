module

public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13722
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignLevi
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviWeyl
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE8
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.FiveCharE8
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.SevenCharE8
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.RankThree.PartOne.KE.EDualStabilizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangInner
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSplit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem mem_closure_rootReflection_of_fix_E8
    {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin Tag.E8.rank → Lˣ} (ha : ∀ i, a i ^ p = 1) (i : KernelComponent (rootCharHom a))
    {w : WeylGroup .E8} (hw : w ∈ rootCharStabilizerSubgroup a)
    (hfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      ∀ j, ((w • c) j : ZMod p) = (c j : ZMod p)) :
    w ∈ Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) := by
  replace hfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      w • c = c := by
    intro c hc hcΨ
    choose v hv using fun j =>
      (ZMod.intCast_eq_intCast_iff_dvd_sub (c j) ((w • c) j) p).1 (hfix c hc hcΨ j).symm
    have hcv : w • c - c = (p : ℤ) • v := funext fun j => by
      rw [Pi.sub_apply, hv j, Pi.smul_apply, smul_eq_mul]
    refine CFSG.SeitzReduction.E8Pilot.eq_of_dvd_iform_sub (hp.two_le.lt_of_ne' hp2) hc.1
      (IsRoot.smul hc.1 w) fun k => ?_
    rw [← CFSG.LieType.Steinberg.Adjoint.iform_sub_left, hcv,
      CFSG.LieType.Steinberg.Adjoint.iform_smul_left]
    exact dvd_mul_right _ _
  have hwK : w ∈ kernelReflectionGroup a := by
    by_cases h3 : p = 3
    · subst p
      rw [rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three a ha] at hw
      exact hw
    by_cases h5 : p = 5
    · subst p
      rw [rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five a ha] at hw
      exact hw
    by_cases h7 : p = 7
    · subst p
      rw [rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_seven a ha] at hw
      exact hw
    · have hp7 : 7 < p := by
        have h2 : 2 ≤ p := hp.two_le
        by_contra hle
        have hle' : p ≤ 7 := by omega
        have hp4 : p ≠ 4 := fun e => by rw [e] at hp; exact absurd hp (by decide)
        have hp6 : p ≠ 6 := fun e => by rw [e] at hp; exact absurd hp (by decide)
        omega
      have hnd := CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp hp7
        (Or.inr (Or.inr rfl))
      refine mem_kernelReflectionGroup_of_coprime hp ha hw ?_
      refine Nat.coprime_comm.2 ((hp.coprime_iff_not_dvd).2 fun h => hnd ?_)
      exact h.trans (orderOf_dvd_natCard w)
  obtain ⟨u, huC, hu⟩ := f4Three_exists_restrict i hwK
  have hset : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) =
      Subgroup.closure {s : WeylGroup .E8 | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ} := by
    congr 1
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩
  have huC' : u ∈ Subgroup.closure {s : WeylGroup .E8 | ∃ γ ∈ componentRoots (rootCharHom a) i,
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

theorem ggTBJE8Levi_mem_closure_of_fix
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Fin 8 → MulAut ↥Bs} {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    {f : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i)
    {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) p)
    {a : Fin Tag.E8.rank → Lˣ} (g : ↥Bs)
    (hχ : ∀ v : Fin Tag.E8.rank → ℤ, rootCharHom a (Multiplicative.ofAdd v) =
      ζ ^ (∑ j, (v j : ZMod p) * α j (ι (Additive.ofMul g))).val)
    (i : KernelComponent (rootCharHom a)) {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer X Bs)
    (htg : t g = g)
    (htΨ : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      ggLin (p := p) ι t (∑ j, (c j : ZMod p) • h j) = ∑ j, (c j : ZMod p) • h j) :
    t ∈ Subgroup.closure {t' | t' ∈ ggAutomizer X Bs ∧
      ∃ c ∈ componentRoots (rootCharHom a) i, ∀ w,
        ggLin (p := p) ι t' w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j} := by
  obtain ⟨e, he, hlift⟩ := ggTBJE8Levi_weylLift ι hlin hpair hf
  let F : WeylGroup .E8 →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp e.toMonoidHom
  have hF : ∀ j, (F (simple .E8 j) : MulAut ↥Bs) = φ j := by
    intro j
    change (f (e (simple .E8 j)) : MulAut ↥Bs) = φ j
    rw [he j]
    exact hf j
  have hFh : ∀ (u : WeylGroup .E8) (c : Fin Tag.E8.rank → ℤ),
      ggLin (p := p) ι (F u : MulAut ↥Bs) (∑ j, (c j : ZMod p) • h j) =
        ∑ j, ((u • c) j : ZMod p) • h j := by
    intro u c
    simpa [F] using (hlift u c (0 : V)).1
  have hFα : ∀ (u : WeylGroup .E8) (c : Fin Tag.E8.rank → ℤ) (v : V),
      ∑ j, ((u • c) j : ZMod p) * α j (ggLin (p := p) ι (F u : MulAut ↥Bs) v) =
        ∑ j, (c j : ZMod p) * α j v := by
    intro u c v
    simpa [F] using (hlift u c v).2
  let w : WeylGroup .E8 := e.symm (f.symm ⟨t, ht⟩)
  have hFw : F w = ⟨t, ht⟩ := by
    change f (e (e.symm (f.symm ⟨t, ht⟩))) = ⟨t, ht⟩
    simp
  have hFwMul : (F w : MulAut ↥Bs) = t := by
    rw [hFw]
  have ha : ∀ j, a j ^ p = 1 := by
    intro j
    have hsingle : rootCharHom a (Multiplicative.ofAdd (Pi.single j 1)) = a j := by
      show CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a (Pi.single j 1) = a j
      rw [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar]
      exact (Finset.prod_eq_single j (s := Finset.univ)
        (f := fun k => a k ^ (Pi.single j 1) k)
        (fun k _ hkj => by rw [Pi.single_eq_of_ne hkj]; simp)
        (fun hj => absurd (Finset.mem_univ j) hj)).trans (by simp)
    have hζp : ζ ^ p = 1 := by
      apply Units.ext
      simpa using hζ.pow_eq_one
    rw [← hsingle, hχ (Pi.single j 1), ← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have hw : w ∈ rootCharStabilizerSubgroup a := by
    rw [mem_rootCharStabilizerSubgroup]
    intro v
    show rootCharHom a (Multiplicative.ofAdd (w • v)) =
      rootCharHom a (Multiplicative.ofAdd v)
    rw [hχ (w • v), hχ v]
    have hexp : (∑ j, (((w • v) j : ZMod p)) *
        α j (ι (Additive.ofMul g))) =
        ∑ j, ((v j : ZMod p)) * α j (ι (Additive.ofMul g)) := by
      have hfixg : ggLin (p := p) ι (F w : MulAut ↥Bs) (ι (Additive.ofMul g)) =
          ι (Additive.ofMul g) := by
        rw [ggLin_apply_ofMul, hFwMul, htg]
      simpa [hfixg] using hFα w v (ι (Additive.ofMul g))
    rw [hexp]
  have hfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      ∀ j, ((w • c) j : ZMod p) = (c j : ZMod p) := by
    intro c hc hcΨ
    have hli8 : LinearIndependent (ZMod p) h := by
      have hdet : (Matrix.of fun j k => α j (h k)).det ≠ 0 := by
        have hmat : (Matrix.of fun j k => α j (h k)) =
            (CartanMatrix.E₈).map (Int.cast : ℤ → ZMod p) := by
          ext j k
          simpa using hpair j k
        rw [hmat, ← Int.cast_det, CartanMatrix.E₈_det]
        simpa using (one_ne_zero : (1 : ZMod p) ≠ 0)
      exact linearIndependent_of_det_ne_zero h α hdet
    have hli : LinearIndependent (ZMod p) (fun j : Fin Tag.E8.rank => h j) := hli8
    have hH : (∑ j, (((w • c) j : ZMod p)) • h j) =
        ∑ j, ((c j : ZMod p)) • h j := by
      have hgrad := hFh w c
      rw [hFwMul] at hgrad
      rw [htΨ c hc hcΨ] at hgrad
      exact hgrad.symm
    have hcoef : ∀ j, (((w • c) j : ZMod p) - (c j : ZMod p)) = 0 := by
      intro j
      exact Fintype.linearIndependent_iff.mp hli
        (fun k => ((w • c) k : ZMod p) - (c k : ZMod p)) (by
          simp only [sub_smul, Finset.sum_sub_distrib, hH, sub_self]) j
    exact fun j => sub_eq_zero.mp (hcoef j)
  have hwClos : w ∈ Subgroup.closure
      (rootReflection '' componentRoots (rootCharHom a) i) :=
    mem_closure_rootReflection_of_fix_E8 (p := p) (Fact.out : p.Prime) hp2 ha i hw hfix
  have hΨ : ∀ c ∈ componentRoots (rootCharHom a) i, IsRoot .E8 c := by
    intro c hc
    obtain ⟨h, -⟩ := hc
    exact h.1
  let ψ : WeylGroup .E8 →* MulAut ↥Bs := (ggAutomizer X Bs).subtype.comp F
  have hψw : ψ w = t := by
    change ((F w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = t
    exact hFwMul
  have hmem : ψ w ∈ Subgroup.closure
      ((fun c => ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) ''
        componentRoots (rootCharHom a) i) := by
    have h1 : ψ w ∈ (Subgroup.closure
        (rootReflection '' componentRoots (rootCharHom a) i)).map ψ :=
      Subgroup.mem_map_of_mem ψ hwClos
    rw [MonoidHom.map_closure] at h1
    rw [Set.image_image] at h1
    simpa [ψ] using h1
  rw [hψw] at hmem
  have hEq := ggTBJE8Levi_reflSet_eq (p := p) ι hlin (F := F) hF hFh hFα
    (Ψ := componentRoots (rootCharHom a) i) hΨ
  rw [← hEq] at hmem
  exact hmem

end CFSG.StandardType

end

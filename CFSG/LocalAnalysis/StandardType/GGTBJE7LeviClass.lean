module

public import Certificates.Certificate13605
public import Certificates.Certificate13721
public import Certificates.Certificate13723
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviClass
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviStab
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignLevi
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE7
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.SevenCharE7
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FiveAux.Steinberg
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviCore
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e7Lift_det : (CartanMatrix.E₇).det = 2 := by
  rw [← CFSG.LieType.Chevalley.laplaceDet_eq_det]
  decide +kernel

private theorem e7Lift_two_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp2 h2

section

open CFSG.HardMathSupport.Timmesfeld.Steinberg
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

private theorem e7Lift_mem_closure_rootReflection_of_fix
    {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin Tag.E7.rank → Lˣ} (ha : ∀ i, a i ^ p = 1) (i : KernelComponent (rootCharHom a))
    {w : WeylGroup .E7} (hw : w ∈ rootCharStabilizerSubgroup a)
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
    refine CFSG.SeitzReduction.E7Pilot.eq_of_dvd_iform_sub (hp.two_le.lt_of_ne' hp2) hc.1
      (IsRoot.smul hc.1 w) fun k => ?_
    rw [← CFSG.LieType.Steinberg.Adjoint.iform_sub_left, hcv,
      CFSG.LieType.Steinberg.Adjoint.iform_smul_left]
    exact dvd_mul_right _ _
  have hwK : w ∈ kernelReflectionGroup a := by
    by_cases h3 : p = 3
    · subst p
      rw [rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three a ha] at hw
      exact hw
    by_cases h5 : p = 5
    · subst p
      rw [rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_five a ha] at hw
      exact hw
    by_cases h7 : p = 7
    · subst p
      rw [rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven a ha] at hw
      exact hw
    · have hp7 : 7 < p := by
        have h2 : 2 ≤ p := hp.two_le
        by_contra hle
        have hle' : p ≤ 7 := by omega
        have hp4 : p ≠ 4 := fun e => by rw [e] at hp; exact absurd hp (by decide)
        have hp6 : p ≠ 6 := fun e => by rw [e] at hp; exact absurd hp (by decide)
        omega
      have hnd := CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp hp7
        (Or.inr (Or.inl rfl))
      refine mem_kernelReflectionGroup_of_coprime hp ha hw ?_
      refine Nat.coprime_comm.2 ((hp.coprime_iff_not_dvd).2 fun h => hnd ?_)
      exact h.trans (orderOf_dvd_natCard w)
  obtain ⟨u, huC, hu⟩ := f4Three_exists_restrict i hwK
  have hset : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) =
      Subgroup.closure {s : WeylGroup .E7 | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ} := by
    congr 1
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩
  have huC' : u ∈ Subgroup.closure {s : WeylGroup .E7 | ∃ γ ∈ componentRoots (rootCharHom a) i,
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

end

theorem ggTBJE7Levi_mem_closure_of_fix
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Fin 7 → MulAut ↥Bs} {h : Fin 7 → V} {α : Fin 7 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    {f : CoxeterMatrix.E₇.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.E₇.simple i) : MulAut ↥Bs) = φ i)
    {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) p)
    {a : Fin Tag.E7.rank → Lˣ} (g : ↥Bs)
    (hχ : ∀ v : Fin Tag.E7.rank → ℤ, rootCharHom a (Multiplicative.ofAdd v) =
      ζ ^ (∑ j, (v j : ZMod p) * α j (ι (Additive.ofMul g))).val)
    (i : KernelComponent (rootCharHom a)) {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer X Bs)
    (htg : t g = g)
    (htΨ : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      ggLin (p := p) ι t (∑ j, (c j : ZMod p) • h j) = ∑ j, (c j : ZMod p) • h j) :
    t ∈ Subgroup.closure {t' | t' ∈ ggAutomizer X Bs ∧
      ∃ c ∈ componentRoots (rootCharHom a) i, ∀ w,
        ggLin (p := p) ι t' w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j} := by
  obtain ⟨e, he, hlift⟩ := ggTBJE7Levi_weylLift ι hlin hpair hf
  let F : WeylGroup .E7 →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp e.toMonoidHom
  have hF : ∀ j, (F (simple .E7 j) : MulAut ↥Bs) = φ j := by
    intro j
    change (f (e (simple .E7 j)) : MulAut ↥Bs) = φ j
    rw [he j]
    exact hf j
  have hFh : ∀ (u : WeylGroup .E7) (c : Fin Tag.E7.rank → ℤ),
      ggLin (p := p) ι (F u : MulAut ↥Bs) (∑ j, (c j : ZMod p) • h j) =
        ∑ j, ((u • c) j : ZMod p) • h j := by
    intro u c
    simpa [F] using (hlift u c (0 : V)).1
  have hFα : ∀ (u : WeylGroup .E7) (c : Fin Tag.E7.rank → ℤ) (v : V),
      ∑ j, ((u • c) j : ZMod p) * α j (ggLin (p := p) ι (F u : MulAut ↥Bs) v) =
        ∑ j, (c j : ZMod p) * α j v := by
    intro u c v
    simpa [F] using (hlift u c v).2
  let w : WeylGroup .E7 := e.symm (f.symm ⟨t, ht⟩)
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
            (CartanMatrix.E₇).map (Int.cast : ℤ → ZMod p) := by
          ext j k
          simpa using hpair j k
        rw [hmat, ← Int.cast_det, e7Lift_det]
        simpa using e7Lift_two_ne_zero p hp2
      exact linearIndependent_of_det_ne_zero h α hdet
    have hli : LinearIndependent (ZMod p) (fun j : Fin Tag.E7.rank => h j) := hli8
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
    e7Lift_mem_closure_rootReflection_of_fix (p := p) (Fact.out : p.Prime) hp2 ha i hw hfix
  have hΨ : ∀ c ∈ componentRoots (rootCharHom a) i, IsRoot .E7 c := by
    intro c hc
    obtain ⟨h, -⟩ := hc
    exact h.1
  let ψ : WeylGroup .E7 →* MulAut ↥Bs := (ggAutomizer X Bs).subtype.comp F
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
  have hEq := ggTBJE7Levi_reflSet_eq (p := p) ι hlin (F := F) hF hFh hFα
    (Ψ := componentRoots (rootCharHom a) i) hΨ
  rw [← hEq] at hmem
  exact hmem

private theorem e7Lift_exists_section {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (_ι : Additive ↥Bs ≃+ V) {h : Fin 7 → V} {α : Fin 7 → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p)) :
    ∃ σ : (Fin 7 → ZMod p) →ₗ[ZMod p] V,
      ∀ t, LinearMap.pi α (σ t) = t := by
  classical
  let M : Matrix (Fin 7) (Fin 7) (ZMod p) := Matrix.of fun i j => α i (h j)
  have hMdet : M.det = (2 : ZMod p) := by
    have hmat : M = (CartanMatrix.E₇).map (Int.cast : ℤ → ZMod p) := by
      ext i j
      exact hpair i j
    rw [hmat, ← Int.cast_det, e7Lift_det]
    norm_num
  have hMunit : IsUnit M.det := by
    rw [hMdet]
    exact isUnit_iff_ne_zero.mpr (e7Lift_two_ne_zero p hp2)
  let L : (Fin 7 → ZMod p) →ₗ[ZMod p] V :=
    { toFun := fun t => ∑ k, t k • h k
      map_add' := by
        intro x y
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, add_smul]
      map_smul' := by
        intro c t
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [Pi.smul_apply, smul_eq_mul, smul_smul, RingHom.id_apply] }
  have hTL : ∀ t : Fin 7 → ZMod p, LinearMap.pi α (L t) = M *ᵥ t := by
    intro t
    ext j
    change α j (∑ k, t k • h k) = (M *ᵥ t) j
    rw [Matrix.mulVec, dotProduct]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
    simp only [M, Matrix.of_apply]
    ring
  refine ⟨L.comp (Matrix.mulVecLin M⁻¹), fun t => ?_⟩
  calc
    LinearMap.pi α ((L.comp (Matrix.mulVecLin M⁻¹)) t) = LinearMap.pi α (L (M⁻¹ *ᵥ t)) := by
      rw [LinearMap.comp_apply, Matrix.mulVecLin_apply]
    _ = M *ᵥ (M⁻¹ *ᵥ t) := hTL _
    _ = (M * M⁻¹) *ᵥ t := by rw [Matrix.mulVec_mulVec]
    _ = (1 : Matrix (Fin 7) (Fin 7) (ZMod p)) *ᵥ t := by
      rw [Matrix.mul_nonsing_inv M hMunit]
    _ = t := by rw [Matrix.one_mulVec]

private theorem e7Lift_finrank_rootAnn {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) {h : Fin 7 → V}
    {α : Fin 7 → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    (hX : ∃ b : ↥Bs, b ≠ 1 ∧ ∀ j, α j (ι (Additive.ofMul b)) = 0)
    (Ψ : Set (Fin Tag.E7.rank → ℤ))
    (hcount : Nat.card {b : ↥Bs // ∀ c ∈ Ψ,
      ∑ j, (c j : ZMod p) * α j (ι (Additive.ofMul b)) = 0} ≤ p ^ 3) :
    Module.finrank (ZMod p) (ggRootAnn p Ψ) ≤ 2 := by
  classical
  obtain ⟨σ, hσ⟩ := e7Lift_exists_section (p := p) hp2 ι hpair
  let T : V →ₗ[ZMod p] (Fin 7 → ZMod p) := LinearMap.pi α
  obtain ⟨b0, hb0, hb0α⟩ := hX
  let w0 : V := ι (Additive.ofMul b0)
  have hw0T : T w0 = 0 := by
    ext j
    exact hb0α j
  have hw0 : w0 ≠ 0 := by
    intro hzero
    have h' : Additive.ofMul b0 = 0 := ι.injective (by simpa [w0] using hzero)
    exact hb0 (by simpa using h')
  let B := {b : ↥Bs // ∀ c ∈ Ψ,
    ∑ j, (c j : ZMod p) * α j (ι (Additive.ofMul b)) = 0}
  have hBcard : Nat.card B ≤ p ^ 3 := hcount
  let φ : (ZMod p) × (ggRootAnn p Ψ) → B := fun q =>
    let t : Fin 7 → ZMod p := q.2.1
    ⟨Additive.toMul (ι.symm (q.1 • w0 + σ t)), by
      intro c hc
      have hι : ι (Additive.ofMul (Additive.toMul (ι.symm (q.1 • w0 + σ t)))) =
          q.1 • w0 + σ t := by simp
      have hT : T (q.1 • w0 + σ t) = t := by
        rw [map_add, map_smul, hw0T, hσ]
        simp
      calc
        ∑ j, (c j : ZMod p) * α j (ι (Additive.ofMul
            (Additive.toMul (ι.symm (q.1 • w0 + σ t)))))
            = ∑ j, (c j : ZMod p) * t j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hι]
              change (c j : ZMod p) * T (q.1 • w0 + σ t) j = (c j : ZMod p) * t j
              rw [hT]
        _ = 0 := by simpa [t] using q.2.2 c hc⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨a, t⟩ ⟨b, s⟩ hφ
    have ht : t.1 = s.1 := by
      have hb : Additive.toMul (ι.symm (a • w0 + σ t.1)) =
          Additive.toMul (ι.symm (b • w0 + σ s.1)) := congrArg Subtype.val hφ
      have hv : a • w0 + σ t.1 = b • w0 + σ s.1 := by
        simpa using congrArg (fun x : ↥Bs => ι (Additive.ofMul x)) hb
      have hT := congrArg (LinearMap.pi α) hv
      have hw0' : LinearMap.pi α w0 = 0 := hw0T
      simp only [map_add, map_smul, hw0', smul_zero, zero_add] at hT
      change (LinearMap.pi α) (σ t.1) = (LinearMap.pi α) (σ s.1) at hT
      rw [hσ t.1, hσ s.1] at hT
      exact hT
    have hsm : a • w0 = b • w0 := by
      have hb : Additive.toMul (ι.symm (a • w0 + σ t.1)) =
          Additive.toMul (ι.symm (b • w0 + σ s.1)) := congrArg Subtype.val hφ
      have hv : a • w0 + σ t.1 = b • w0 + σ s.1 := by
        simpa using congrArg (fun x : ↥Bs => ι (Additive.ofMul x)) hb
      rw [ht] at hv
      exact add_right_cancel hv
    have hab : a = b := by
      have hzero : (a - b) • w0 = 0 := by
        rw [sub_smul, hsm, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero_iff_left hw0).mp hzero)
    exact Prod.ext hab (Subtype.ext ht)
  have hcard : p * Nat.card (ggRootAnn p Ψ) ≤ p ^ 3 := by
    calc
      p * Nat.card (ggRootAnn p Ψ)
          = Nat.card (ZMod p) * Nat.card (ggRootAnn p Ψ) := by rw [Nat.card_zmod]
      _ = Nat.card ((ZMod p) × ggRootAnn p Ψ) := (Nat.card_prod _ _).symm
      _ ≤ Nat.card B := Nat.card_le_card_of_injective φ hφinj
      _ ≤ p ^ 3 := hBcard
  have hpow : Nat.card (ggRootAnn p Ψ) =
      p ^ Module.finrank (ZMod p) (ggRootAnn p Ψ) := by
    simpa [Nat.card_zmod] using
      (@Module.natCard_eq_pow_finrank (ZMod p) (ggRootAnn p Ψ) _ _ _
        (Module.Finite.of_finite))
  have hle : Module.finrank (ZMod p) (ggRootAnn p Ψ) ≤ 2 := by
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have h1 : Module.finrank (ZMod p) (ggRootAnn p Ψ) + 1 ≤ 3 := by
      apply (Nat.pow_le_pow_iff_right hp1).1
      calc
        p ^ (Module.finrank (ZMod p) (ggRootAnn p Ψ) + 1) =
            p * p ^ Module.finrank (ZMod p) (ggRootAnn p Ψ) := by
          rw [pow_succ, Nat.mul_comm]
        _ = p * Nat.card (ggRootAnn p Ψ) := by rw [hpow]
        _ ≤ p ^ 3 := hcard
    omega
  exact hle

theorem ggTBJE7Levi_of_class
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs X J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Fin 7 → MulAut ↥Bs} {h : Fin 7 → V} {α : Fin 7 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    {f : CoxeterMatrix.E₇.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.E₇.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hX : ∃ b : ↥Bs, b ≠ 1 ∧ ∀ j, α j (ι (Additive.ofMul b)) = 0)
    {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) p)
    {a : Fin Tag.E7.rank → Lˣ} (ha : ∀ i, a i ^ p = 1) (ha1 : ∃ j, a j ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hJ : ggAutomizer J Bs = Subgroup.closure {t | t ∈ ggAutomizer X Bs ∧
      ∃ c ∈ componentRoots (rootCharHom a) i, ∀ w,
        ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j})
    (hcount : Nat.card {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
      ∑ j, (c j : ZMod p) * α j (ι (Additive.ofMul b)) = 0} ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hfinrank : Module.finrank (ZMod p)
      (ggRootAnn p (componentRoots (rootCharHom a) i)) ≤ 2 :=
    e7Lift_finrank_rootAnn (p := p) hp2 ι hpair hX (componentRoots (rootCharHom a) i) hcount
  have h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
    have h := le_compRank_of_finrank_ggRootAnn (τ := .E7) (p := p)
      (componentRoots (rootCharHom a) i) hfinrank
    have hrank : Tag.E7.rank = 7 := rfl
    omega
  obtain ⟨v, S, hS, hΨclass⟩ :=
    e7_class_levi (p := p) (Fact.out : p.Prime) hp2 hζ a ha ha1 i h5
  let Ψ : Set (Fin Tag.E7.rank → ℤ) := componentRoots (rootCharHom a) i
  have hΨeq : Ψ = (fun α => v • α) '' parabolicRoots .E7 {j : Fin 7 | j ∉ S} := hΨclass
  have hJΨ : ggAutomizer J Bs = Subgroup.closure {t | t ∈ ggAutomizer X Bs ∧
      ∃ c ∈ Ψ, ∀ w,
        ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) •
          ∑ j, (c j : ZMod p) • h j} := hJ
  obtain ⟨e, he, hlift⟩ := ggTBJE7Levi_weylLift (p := p) ι hlin hpair hf
  let F : WeylGroup .E7 →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp e.toMonoidHom
  have hF : ∀ j, (F (simple .E7 j) : MulAut ↥Bs) = φ j := by
    intro j
    change (f (e (simple .E7 j)) : MulAut ↥Bs) = φ j
    rw [he j]
    exact hf j
  have hFh : ∀ (u : WeylGroup .E7) (c : Fin Tag.E7.rank → ℤ),
      ggLin (p := p) ι (F u : MulAut ↥Bs) (∑ j, (c j : ZMod p) • h j) =
        ∑ j, ((u • c) j : ZMod p) • h j := by
    intro u c
    simpa [F] using (hlift u c (0 : V)).1
  have hFα : ∀ (u : WeylGroup .E7) (c : Fin Tag.E7.rank → ℤ) (w : V),
      ∑ j, ((u • c) j : ZMod p) * α j (ggLin (p := p) ι (F u : MulAut ↥Bs) w) =
        ∑ j, (c j : ZMod p) * α j w := by
    intro u c w
    simpa [F] using (hlift u c w).2
  have hΨroot : ∀ c ∈ Ψ, IsRoot .E7 c := by
    intro c hc
    obtain ⟨h, -⟩ := hc
    exact h.1
  have hset : Subgroup.closure (rootReflection '' Ψ) =
      Subgroup.closure {s : WeylGroup .E7 | ∃ γ ∈ Ψ, s = rootReflection γ} := by
    congr 1
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩
  have hJrefl : ggAutomizer J Bs = Subgroup.closure
      ((fun c => ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) '' Ψ) := by
    rw [hJΨ]
    rw [ggTBJE7Levi_reflSet_eq (p := p) (F := F) (Ψ := Ψ) ι hlin hF hFh hFα hΨroot]
  let ψ : WeylGroup .E7 →* MulAut ↥Bs := (ggAutomizer X Bs).subtype.comp F
  have hJmap : ggAutomizer J Bs = Subgroup.map ψ (Subgroup.closure (rootReflection '' Ψ)) := by
    rw [hJrefl, MonoidHom.map_closure, Set.image_image]
    rfl
  have hpar : Subgroup.closure (rootReflection '' Ψ) =
      Subgroup.closure ((fun j : Fin 7 => v * simple .E7 j * v⁻¹) ''
        {j : Fin 7 | j ∉ S}) := by
    rw [hset, hΨeq, closure_rootReflection_smul_parabolicRoots (τ := .E7) v
      {j : Fin 7 | j ∉ S}]
    rfl
  have hJmap2 : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 7 // j ∉ S} => ψ (v * simple .E7 j.1 * v⁻¹)) := by
    rw [hJmap, hpar, MonoidHom.map_closure, Set.image_image, Set.image_eq_range]
    rfl
  let u : CoxeterMatrix.E₇.Group := e v
  have hψsimple : ∀ j, ψ (simple .E7 j) = φ j := by
    intro j
    change ((F (simple .E7 j) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = φ j
    exact hF j
  have hψv : ψ v = (f u : MulAut ↥Bs) := rfl
  have hgen : ∀ j : {j : Fin 7 // j ∉ S}, ψ (v * simple .E7 j.1 * v⁻¹) =
      (f u : MulAut ↥Bs) * φ j.1 * (f u : MulAut ↥Bs)⁻¹ := by
    intro j
    rw [map_mul, map_mul, map_inv, hψv, hψsimple j.1]
  have hJ' : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 7 // j ∉ S} =>
        (f u : MulAut ↥Bs) * φ j.1 * (f u : MulAut ↥Bs)⁻¹) := by
    rw [hJmap2]
    have hfunext : (fun j : {j : Fin 7 // j ∉ S} => ψ (v * simple .E7 j.1 * v⁻¹)) =
        (fun j : {j : Fin 7 // j ∉ S} =>
          (f u : MulAut ↥Bs) * φ j.1 * (f u : MulAut ↥Bs)⁻¹) := funext hgen
    rw [hfunext]
  exact ggE7LeviDatum_of_conj (p := p) (M := CoxeterMatrix.E₇) (C := CartanMatrix.E₇)
    hp2 rfl ggIntCartan_E₇ hlin hrefl hpair hf hclos u hS hJ'

end CFSG.StandardType

end

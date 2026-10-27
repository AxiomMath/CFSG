module

public import CFSG.LocalAnalysis.StandardType.GGQ2EichlerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggTrE_range_reflection {U : Type} [AddCommGroup U] [Module (ZMod 3) U] {ι : Type}
    (h : ι → U) (α : ι → Module.Dual (ZMod 3) U) (s : ι → U ≃ₗ[ZMod 3] U)
    (hs : ∀ i v, s i v = v - α i v • h i) :
    Set.range s = {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j} := by
  ext t
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, hs i⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, LinearEquiv.ext fun v => by rw [hj v, hs j v]⟩

@[expose] def GGWeylNoEichlerRhoOn {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (C : Matrix Λ Λ ℤ) : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 3) U] (h : Λ → U)
    (α : Λ → Module.Dual (ZMod 3) U),
    LinearIndependent (ZMod 3) h → Submodule.span (ZMod 3) (Set.range h) = ⊤ →
    (∀ i j, α i (h j) = ((C i j : ℤ) : ZMod 3)) →
    ∀ g ∈ ggQ2WeylOf h α, g ≠ 1 → ∃ (v : U) (i : Λ), α i (g (g v) + g v + v) ≠ 0

theorem ggQ2_noEichler_of_rho {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hρ : GGWeylNoEichlerRhoOn M.cartan) (φ : MulAut ↥Bs)
    (hφ : φ ∈ ggAutomizer L Bs) : ¬ GGEichler (ggLin (p := 3) M.model φ) := by
  intro hE
  classical
  set g : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model φ with hg
  have hαc : ∀ i : M.Λ, M.root i (M.coroot i) = 2 := by
    intro i
    rw [M.pairing, M.isCartan.1]
    norm_num
  let s : M.Λ → M.V ≃ₗ[ZMod 3] M.V := fun i => ggLin (p := 3) M.model (M.simple i)
  have hs : ∀ i, s i = Module.reflection (hαc i) := by
    intro i
    refine LinearEquiv.ext fun v => ?_
    change ggLin (p := 3) M.model (M.simple i) v = Module.reflection (hαc i) v
    rw [M.simple_apply, Module.reflection_apply]
  let cs := M.coxeter.toCoxeterSystem
  have hliftV : M.coxeter.IsLiftable (fun i => Module.reflection (hαc i)) :=
    isLiftable_reflection_of_intCartan M.isCartan M.coroot M.root hαc M.pairing
  let ΦV : M.coxeter.Group →* (M.V ≃ₗ[ZMod 3] M.V) :=
    cs.lift ⟨fun i => Module.reflection (hαc i), hliftV⟩
  have hΦVsimple : ∀ i, ΦV (cs.simple i) = s i := by
    intro i
    dsimp only [ΦV]
    rw [CoxeterSystem.lift_apply_simple, hs i]
  have hΦVrange : ΦV.range = Subgroup.closure (Set.range s) := by
    have himageV : ΦV '' Set.range cs.simple = Set.range s := by
      ext t
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hΦVsimple i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨cs.simple i, ⟨i, rfl⟩, hΦVsimple i⟩
    rw [MonoidHom.range_eq_map, ← cs.subgroup_closure_range_simple, MonoidHom.map_closure,
      himageV]
  have hφ' : φ ∈ Subgroup.closure (Set.range M.simple) := by
    rwa [M.automizer_L] at hφ
  have hg_mem : g ∈ Subgroup.closure (Set.range s) := by
    have hmap : Subgroup.map (ggLin (p := 3) M.model)
        (Subgroup.closure (Set.range M.simple)) = Subgroup.closure (Set.range s) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨φ, hφ', rfl⟩
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (by rw [hΦVrange]; exact hg_mem)
  let Um : Type := M.Λ → ZMod 3
  let hm : M.Λ → Um := fun j => Pi.single j 1
  let αm : M.Λ → Module.Dual (ZMod 3) Um :=
    fun i => ∑ j, (M.cartan i j : ZMod 3) • LinearMap.proj j
  have hhm_eq : hm = fun j => Pi.basisFun (ZMod 3) M.Λ j := by
    funext j
    simp only [hm, Pi.basisFun_apply]
  have hhm_li : LinearIndependent (ZMod 3) hm := by
    rw [hhm_eq]
    exact (Pi.basisFun (ZMod 3) M.Λ).linearIndependent
  have hhm_span : Submodule.span (ZMod 3) (Set.range hm) = ⊤ := by
    rw [hhm_eq]
    exact (Pi.basisFun (ZMod 3) M.Λ).span_eq
  have hpairm : ∀ i j, αm i (hm j) = (M.cartan i j : ZMod 3) := by
    intro i j
    have hsplit : αm i (hm j) = ∑ k, (M.cartan i k : ZMod 3) * (hm j k) := by
      dsimp only [αm]
      rw [LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [hsplit, Finset.sum_eq_single j]
    · simp only [hm, Pi.single_eq_same, mul_one]
    · intro k _ hk
      simp only [hm, Pi.single_eq_of_ne hk, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hαm : ∀ i, αm i (hm i) = 2 := by
    intro i
    rw [hpairm i i, M.isCartan.1]
    norm_num
  have hliftm : M.coxeter.IsLiftable (fun i => Module.reflection (hαm i)) :=
    isLiftable_reflection_of_intCartan M.isCartan hm αm hαm hpairm
  let Φm : M.coxeter.Group →* (Um ≃ₗ[ZMod 3] Um) :=
    cs.lift ⟨fun i => Module.reflection (hαm i), hliftm⟩
  have hΦmsimple : ∀ i, Φm (cs.simple i) = Module.reflection (hαm i) := by
    intro i
    dsimp only [Φm]
    rw [CoxeterSystem.lift_apply_simple]
  have hinjm : Function.Injective Φm := by
    have hraw := ggCartanFaithfulInputFixed_holds 3 (by norm_num) (by norm_num) M.Λ M.coxeter
      M.cartan M.isWeyl M.isCartan Um hm αm hαm hpairm hhm_li
    simpa only [Φm] using hraw
  have hΦmrange : Φm.range = ggQ2WeylOf hm αm := by
    change Φm.range = Subgroup.closure
      {t : Um ≃ₗ[ZMod 3] Um | ∃ j, ∀ v, t v = v - αm j v • hm j}
    have himagem : Φm '' Set.range cs.simple
        = Set.range (fun i => Module.reflection (hαm i)) := by
      ext t
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hΦmsimple i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨cs.simple i, ⟨i, rfl⟩, hΦmsimple i⟩
    rw [MonoidHom.range_eq_map, ← cs.subgroup_closure_range_simple, MonoidHom.map_closure,
      himagem, ggTrE_range_reflection hm αm (fun i => Module.reflection (hαm i))
        (fun i v => Module.reflection_apply v (hαm i))]
  let π : Um →ₗ[ZMod 3] M.V := Fintype.linearCombination (ZMod 3) M.coroot
  have hπsingle : ∀ j, π (hm j) = M.coroot j := by
    intro j
    dsimp only [π]
    rw [Fintype.linearCombination_apply, Finset.sum_eq_single j]
    · simp only [hm, Pi.single_eq_same, one_smul]
    · intro k _ hk
      simp only [hm, Pi.single_eq_of_ne hk, zero_smul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hπroot : ∀ i, (M.root i).comp π = αm i := by
    intro i
    refine LinearMap.ext_on hhm_span ?_
    rintro x ⟨j, rfl⟩
    rw [LinearMap.comp_apply, hπsingle j, M.pairing, hpairm i j]
  have hπroot' : ∀ i u, M.root i (π u) = αm i u := by
    intro i u
    rw [← LinearMap.comp_apply, hπroot i]
  have hΦmsimpleV : ∀ i u, π (Φm (cs.simple i) u) = ΦV (cs.simple i) (π u) := by
    intro i u
    rw [hΦmsimple i, Module.reflection_apply, map_sub, map_smul, hπsingle i]
    rw [hΦVsimple i, hs i, Module.reflection_apply, hπroot' i]
  have hinter : ∀ (w : M.coxeter.Group) (u : Um), π (Φm w u) = ΦV w (π u) := by
    intro w
    induction w using CoxeterSystem.simple_induction_left cs with
    | one => intro u; simp
    | mul_simple_left w i ih =>
        intro u
        rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        rw [hΦmsimpleV i (Φm w u), ih u]
  have hπzero : ∀ u : Um, π (Φm w (Φm w u) + Φm w u + u) = 0 := by
    intro u
    rw [map_add, map_add, hinter w (Φm w u), hinter w u, hw]
    exact hE.2 (π u)
  have hzero : ∀ (u : Um) (i : M.Λ),
      αm i (Φm w (Φm w u) + Φm w u + u) = 0 := by
    intro u i
    rw [← hπroot' i, hπzero u, map_zero]
  have hgm_mem : Φm w ∈ ggQ2WeylOf hm αm := by
    rw [← hΦmrange]
    exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
  have hgm_one : Φm w = 1 := by
    by_contra hne
    obtain ⟨v, i, hvi⟩ :=
      hρ Um hm αm hhm_li hhm_span hpairm (Φm w) hgm_mem hne
    exact hvi (hzero v i)
  have hwone : w = 1 := hinjm (by rw [hgm_one, map_one])
  exact hE.1 (by rw [← hw, hwone, map_one])

theorem ggWeylNoEichlerRhoOn_of_fin {n : ℕ} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (h : GGWeylNoEichlerRho C₀) {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin n ≃ Λ)
    {C : Matrix Λ Λ ℤ} (hC : ∀ i j, C (e i) (e j) = C₀ i j) : GGWeylNoEichlerRhoOn C := by
  intro U _ _ z α hz hspan hpair g hg hne
  let z' : Fin n → U := fun i => z (e i)
  let α' : Fin n → Module.Dual (ZMod 3) U := fun i => α (e i)
  have hz' : LinearIndependent (ZMod 3) z' := by
    dsimp only [z']
    exact hz.comp e e.injective
  have hspan' : Submodule.span (ZMod 3) (Set.range z') = ⊤ := by
    have hrange : Set.range z' = Set.range z := by
      ext u
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨j, rfl⟩
        obtain ⟨k, rfl⟩ := e.surjective j
        exact ⟨k, rfl⟩
    rw [hrange]
    exact hspan
  have hpair' : ∀ i j, α' i (z' j) = ((C₀ i j : ℤ) : ZMod 3) := by
    intro i j
    change α (e i) (z (e j)) = ((C₀ i j : ℤ) : ZMod 3)
    rw [hpair (e i) (e j), hC i j]
  have hW : ggQ2WeylOf z' α' = ggQ2WeylOf z α := by
    simp only [ggQ2WeylOf]
    congr 1
    ext t
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨e j, hj⟩
    · rintro ⟨j, hj⟩
      obtain ⟨k, rfl⟩ := e.surjective j
      exact ⟨k, hj⟩
  have hg' : g ∈ ggQ2WeylOf z' α' := by
    rw [hW]
    exact hg
  obtain ⟨v, i, hvi⟩ := h U z' α' hz' hspan' hpair' g hg' hne
  exact ⟨v, e i, hvi⟩

end CFSG.StandardType

end

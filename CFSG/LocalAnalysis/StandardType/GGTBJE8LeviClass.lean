module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviCore
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped Matrix

private theorem ggTBJE8Levi_exists_section {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p)) :
    ∃ σ : (Fin 8 → ZMod p) →ₗ[ZMod p] V,
      ∀ t, LinearMap.pi α (σ t) = t := by
  classical
  let M : Matrix (Fin 8) (Fin 8) (ZMod p) := Matrix.of fun i j => α i (h j)
  have hMdet : M.det = 1 := by
    have hmat : M = (CartanMatrix.E₈).map (Int.cast : ℤ → ZMod p) := by
      ext i j
      exact hpair i j
    rw [hmat, ← Int.cast_det, CartanMatrix.E₈_det, Int.cast_one]
  have hMunit : IsUnit M.det := by rw [hMdet]; exact isUnit_one
  let L : (Fin 8 → ZMod p) →ₗ[ZMod p] V :=
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
  have hTL : ∀ t : Fin 8 → ZMod p, LinearMap.pi α (L t) = M *ᵥ t := by
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
    _ = (1 : Matrix (Fin 8) (Fin 8) (ZMod p)) *ᵥ t := by
      rw [Matrix.mul_nonsing_inv M hMunit]
    _ = t := by rw [Matrix.one_mulVec]

private theorem ggTBJE8Levi_finrank_rootAnn {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (hX : ∃ b : ↥Bs, b ≠ 1 ∧ ∀ j, α j (ι (Additive.ofMul b)) = 0)
    (Ψ : Set (Fin Tag.E8.rank → ℤ))
    (hcount : Nat.card {b : ↥Bs // ∀ c ∈ Ψ,
      ∑ j, (c j : ZMod p) * α j (ι (Additive.ofMul b)) = 0} ≤ p ^ 3) :
    Module.finrank (ZMod p) (ggRootAnn p Ψ) ≤ 2 := by
  classical
  obtain ⟨σ, hσ⟩ := ggTBJE8Levi_exists_section (p := p) ι hpair
  let T : V →ₗ[ZMod p] (Fin 8 → ZMod p) := LinearMap.pi α
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
    let t : Fin 8 → ZMod p := q.2.1
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
  haveI : Module.Finite (ZMod p) (ggRootAnn p Ψ) := Module.Finite.of_finite
  have hpow : Nat.card (ggRootAnn p Ψ) =
      p ^ Module.finrank (ZMod p) (ggRootAnn p Ψ) := by
    simpa [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod p) (V := ggRootAnn p Ψ))
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

theorem ggTBJE8Levi_of_class
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs X J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Fin 8 → MulAut ↥Bs} {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    {f : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hX : ∃ b : ↥Bs, b ≠ 1 ∧ ∀ j, α j (ι (Additive.ofMul b)) = 0)
    {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) p)
    {a : Fin Tag.E8.rank → Lˣ} (ha : ∀ i, a i ^ p = 1) (ha1 : ∃ j, a j ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hJ : ggAutomizer J Bs = Subgroup.closure {t | t ∈ ggAutomizer X Bs ∧
      ∃ c ∈ componentRoots (rootCharHom a) i, ∀ w,
        ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j})
    (hcount : Nat.card {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
      ∑ j, (c j : ZMod p) * α j (ι (Additive.ofMul b)) = 0} ≤ p ^ 3)
    (hA8 : p = 3 → ∀ v : WeylGroup .E8, componentRoots (rootCharHom a) i ≠
      (fun c => v • c) '' kacE8.rootsOf (e8A8Nodes : Set (Option (Fin Tag.E8.rank)))) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hfinrank : Module.finrank (ZMod p)
      (ggRootAnn p (componentRoots (rootCharHom a) i)) ≤ 2 :=
    ggTBJE8Levi_finrank_rootAnn (p := p) ι hpair hX (componentRoots (rootCharHom a) i) hcount
  have h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i) := by
    have h := le_compRank_of_finrank_ggRootAnn (τ := .E8) (p := p)
      (componentRoots (rootCharHom a) i) hfinrank
    have hrank : Tag.E8.rank = 8 := rfl
    omega
  rcases e8_class_levi_or_a8 (p := p) (Fact.out : p.Prime) hp2 hζ a ha ha1 i h6 with
    ⟨v, S, hS, hΨclass⟩ | ⟨hp3, v, hΨclass⟩
  · let Ψ : Set (Fin Tag.E8.rank → ℤ) := componentRoots (rootCharHom a) i
    have hΨeq : Ψ = (fun α => v • α) '' parabolicRoots .E8 {j : Fin 8 | j ∉ S} := hΨclass
    have hJΨ : ggAutomizer J Bs = Subgroup.closure {t | t ∈ ggAutomizer X Bs ∧
        ∃ c ∈ Ψ, ∀ w,
          ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) •
            ∑ j, (c j : ZMod p) • h j} := hJ
    obtain ⟨e, he, hlift⟩ := ggTBJE8Levi_weylLift (p := p) ι hlin hpair hf
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
    have hFα : ∀ (u : WeylGroup .E8) (c : Fin Tag.E8.rank → ℤ) (w : V),
        ∑ j, ((u • c) j : ZMod p) * α j (ggLin (p := p) ι (F u : MulAut ↥Bs) w) =
          ∑ j, (c j : ZMod p) * α j w := by
      intro u c w
      simpa [F] using (hlift u c w).2
    have hΨroot : ∀ c ∈ Ψ, IsRoot .E8 c := by
      intro c hc
      obtain ⟨h, -⟩ := hc
      exact h.1
    have hset : Subgroup.closure (rootReflection '' Ψ) =
        Subgroup.closure {s : WeylGroup .E8 | ∃ γ ∈ Ψ, s = rootReflection γ} := by
      congr 1
      ext s
      simp only [Set.mem_image, Set.mem_setOf_eq]
      exact ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩
    have hJrefl : ggAutomizer J Bs = Subgroup.closure
        ((fun c => ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) '' Ψ) := by
      rw [hJΨ]
      rw [ggTBJE8Levi_reflSet_eq (p := p) (F := F) (Ψ := Ψ) ι hlin hF hFh hFα hΨroot]
    let ψ : WeylGroup .E8 →* MulAut ↥Bs := (ggAutomizer X Bs).subtype.comp F
    have hJmap : ggAutomizer J Bs = Subgroup.map ψ (Subgroup.closure (rootReflection '' Ψ)) := by
      rw [hJrefl, MonoidHom.map_closure, Set.image_image]
      rfl
    have hpar : Subgroup.closure (rootReflection '' Ψ) =
        Subgroup.closure ((fun j : Fin 8 => v * simple .E8 j * v⁻¹) ''
          {j : Fin 8 | j ∉ S}) := by
      rw [hset, hΨeq, closure_rootReflection_smul_parabolicRoots (τ := .E8) v
        {j : Fin 8 | j ∉ S}]
      rfl
    have hJmap2 : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Fin 8 // j ∉ S} => ψ (v * simple .E8 j.1 * v⁻¹)) := by
      rw [hJmap, hpar, MonoidHom.map_closure, Set.image_image, Set.image_eq_range]
      rfl
    let u : CoxeterMatrix.E₈.Group := e v
    have hψsimple : ∀ j, ψ (simple .E8 j) = φ j := by
      intro j
      change ((F (simple .E8 j) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = φ j
      exact hF j
    have hψv : ψ v = (f u : MulAut ↥Bs) := rfl
    have hgen : ∀ j : {j : Fin 8 // j ∉ S}, ψ (v * simple .E8 j.1 * v⁻¹) =
        (f u : MulAut ↥Bs) * φ j.1 * (f u : MulAut ↥Bs)⁻¹ := by
      intro j
      rw [map_mul, map_mul, map_inv, hψv, hψsimple j.1]
    have hJ' : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Fin 8 // j ∉ S} =>
          (f u : MulAut ↥Bs) * φ j.1 * (f u : MulAut ↥Bs)⁻¹) := by
      rw [hJmap2]
      have hfunext : (fun j : {j : Fin 8 // j ∉ S} => ψ (v * simple .E8 j.1 * v⁻¹)) =
          (fun j : {j : Fin 8 // j ∉ S} =>
            (f u : MulAut ↥Bs) * φ j.1 * (f u : MulAut ↥Bs)⁻¹) := funext hgen
      rw [hfunext]
    exact ggE8LeviDatum_of_conj (p := p) (M := CoxeterMatrix.E₈) (C := CartanMatrix.E₈)
      hp2 rfl ggIntCartan_E₈ hlin hrefl hpair hf hclos u hS hJ'
  · exfalso
    exact hA8 hp3 v hΨclass

end CFSG.StandardType

end

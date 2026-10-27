module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import CFSG.LocalAnalysis.StandardType.GGMaxRankWeyl
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggTBJE8Levi_weylLift
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Fin 8 → MulAut ↥Bs} {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    {f : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i) :
    ∃ e : WeylGroup .E8 ≃* CoxeterMatrix.E₈.Group,
      (∀ i, e (simple .E8 i) = CoxeterMatrix.E₈.simple i) ∧
      ∀ (u : WeylGroup .E8) (c : Fin Tag.E8.rank → ℤ) (w : V),
        ggLin (p := p) ι (f (e u) : MulAut ↥Bs) (∑ j, (c j : ZMod p) • h j) =
            ∑ j, ((u • c) j : ZMod p) • h j ∧
          ∑ j, ((u • c) j : ZMod p) * α j (ggLin (p := p) ι (f (e u) : MulAut ↥Bs) w) =
            ∑ j, (c j : ZMod p) * α j w := by
  let e : WeylGroup .E8 ≃* CoxeterMatrix.E₈.Group := ggE8Equiv.symm
  have he : ∀ i, e (simple .E8 i) = CoxeterMatrix.E₈.simple i := by
    intro i
    apply ggE8Equiv.injective
    rw [MulEquiv.apply_symm_apply]
    exact (ggE8Equiv_simple i).symm
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer X Bs
  let Φ : WeylGroup .E8 →* ↥A := f.toMonoidHom.comp e.toMonoidHom
  let ρ : WeylGroup .E8 →* (V ≃ₗ[ZMod p] V) := (ggLin (p := p) ι).comp (A.subtype.comp Φ)
  have hρu : ∀ u, ρ u = ggLin (p := p) ι (f (e u) : MulAut ↥Bs) := fun u => rfl
  have hρ : ∀ (i : Fin Tag.E8.rank) (v : V), ρ (simple .E8 i) v = v - α i v • h i := by
    intro i v
    have hfun : ρ (simple .E8 i) = ggLin (p := p) ι (φ i) := by
      change ggLin (p := p) ι (((Φ (simple .E8 i)) : ↥A) : MulAut ↥Bs) =
        ggLin (p := p) ι (φ i)
      rw [show Φ (simple .E8 i) = f (CoxeterMatrix.E₈.simple i) by
        show f (e (simple .E8 i)) = f (CoxeterMatrix.E₈.simple i)
        rw [he i]]
      rw [show ((f (CoxeterMatrix.E₈.simple i) : ↥A) : MulAut ↥Bs) = φ i from hf i]
    rw [hfun]
    exact hlin i v
  refine ⟨e, he, ?_⟩
  intro u c w
  constructor
  · simpa only [hρu u] using ggMaxRank_weyl_coroot_smul (p := p) h α hpair ρ hρ u c
  · simpa only [hρu u] using ggMaxRank_weyl_dual_smul (p := p) h α hpair ρ hρ u c w

theorem ggTBJE8Levi_reflSet_eq
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Fin 8 → MulAut ↥Bs} {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {F : WeylGroup .E8 →* ↥(ggAutomizer X Bs)}
    (hF : ∀ i, (F (simple .E8 i) : MulAut ↥Bs) = φ i)
    (hFh : ∀ (u : WeylGroup .E8) (c : Fin Tag.E8.rank → ℤ),
      ggLin (p := p) ι (F u : MulAut ↥Bs) (∑ j, (c j : ZMod p) • h j) =
        ∑ j, ((u • c) j : ZMod p) • h j)
    (hFα : ∀ (u : WeylGroup .E8) (c : Fin Tag.E8.rank → ℤ) (w : V),
      ∑ j, ((u • c) j : ZMod p) * α j (ggLin (p := p) ι (F u : MulAut ↥Bs) w) =
        ∑ j, (c j : ZMod p) * α j w)
    {Ψ : Set (Fin Tag.E8.rank → ℤ)} (hΨ : ∀ c ∈ Ψ, IsRoot .E8 c) :
    {t | t ∈ ggAutomizer X Bs ∧ ∃ c ∈ Ψ, ∀ w,
        ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j} =
      (fun c => ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) '' Ψ := by
  have hR : ∀ c ∈ Ψ, ∀ w,
      ggLin (p := p) ι ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) w =
        w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j := by
    intro c hc w
    obtain ⟨u, j, huj⟩ := isRoot_iff_exists_smul_single.1 (hΨ c hc)
    have hroot : rootReflection c = u * simple .E8 j * u⁻¹ := rootReflection_eq_conj huj
    have huc : u⁻¹ • c = (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := by
      rw [← huj, ← mul_smul, inv_mul_cancel, one_smul]
    have hHj : (∑ k, ((Pi.single j 1 : Fin Tag.E8.rank → ℤ) k : ZMod p) • h k) = h j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have hFroot : ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        (F u : MulAut ↥Bs) * (F (simple .E8 j) : MulAut ↥Bs) *
          (F u⁻¹ : MulAut ↥Bs) := by
      rw [hroot]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have hcancel : ggLin (p := p) ι (F u : MulAut ↥Bs)
        (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) = w := by
      rw [← LinearEquiv.mul_apply, ← map_mul]
      simp
    have hFuh : ggLin (p := p) ι (F u : MulAut ↥Bs) (h j) =
        ∑ k, (c k : ZMod p) • h k := by
      have h1 := hFh u (Pi.single j 1)
      rw [hHj, huj] at h1
      exact h1
    have hAj : α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) =
        ∑ k, (c k : ZMod p) * α k w := by
      have h1 := hFα u⁻¹ c w
      rw [huc] at h1
      have hsingle : (∑ k, ((Pi.single j 1 : Fin Tag.E8.rank → ℤ) k : ZMod p) *
          α k (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w)) =
          α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      rwa [hsingle] at h1
    calc
      ggLin (p := p) ι ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) w
          = ggLin (p := p) ι (F u : MulAut ↥Bs)
              (ggLin (p := p) ι (F (simple .E8 j) : MulAut ↥Bs)
                (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w)) := by
            rw [hFroot, map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply]
      _ = ggLin (p := p) ι (F u : MulAut ↥Bs)
              (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w -
                α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) • h j) := by
            rw [hF j, hlin j]
      _ = ggLin (p := p) ι (F u : MulAut ↥Bs)
              (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) -
            α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) •
              ggLin (p := p) ι (F u : MulAut ↥Bs) (h j) := by
            rw [map_sub, map_smul]
      _ = w - (∑ k, (c k : ZMod p) * α k w) • ∑ k, (c k : ZMod p) • h k := by
            rw [hcancel, hAj, hFuh]
  ext t
  constructor
  · rintro ⟨-, c, hc, hform⟩
    refine ⟨c, hc, ?_⟩
    apply ggLin_injective (p := p) ι
    ext w
    rw [hform w, hR c hc w]
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(F (rootReflection c)).2, c, hc, hR c hc⟩

end CFSG.StandardType

end

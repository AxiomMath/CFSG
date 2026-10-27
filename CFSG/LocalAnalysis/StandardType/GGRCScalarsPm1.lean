module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGRCSimpleBond
public import CFSG.LocalAnalysis.StandardType.GGRCTriangleLattice
public import CFSG.LocalAnalysis.StandardType.GGRCLatticeTriple
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialFrame
public import CFSG.LocalAnalysis.StandardType.GGRCTwistedTriangle
public import CFSG.LocalAnalysis.StandardType.GGRCLinRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRC_scalars_pm1 (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hWL : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL) (h8 : 8 ≤ Fintype.card Λ)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hind : LinearIndependent (ZMod p) h)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b} => φ (some j)))
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (hirr : ZS.AbsIrred p (Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o))))
    (hmon : ∀ a ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)),
      ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) :
    ∃ b' : Module.Basis (Fin n) (ZMod p) V,
      ∀ a ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)),
        ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
          (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b' i) = c i • b' (σ i) := by
  classical
  have hp2 : p ≠ 2 := by omega
  let r : Option Λ → (V ≃ₗ[ZMod p] V) := fun o => ggLin (p := p) ι (φ o)
  let A : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r)
  have hreflLin : ∀ o, GGLinRefl (r o) :=
    fun o => (ggRC_isReflection_iff_linRefl ι (φ o)).mp (hrefl o)
  have hgen : A = Subgroup.closure {x | x ∈ A ∧ GGLinRefl x} := by
    apply le_antisymm
    · apply Subgroup.closure_mono
      intro x hx
      obtain ⟨o, rfl⟩ := hx
      exact ⟨Subgroup.subset_closure (Set.mem_range_self o), hreflLin o⟩
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
  have hA : A = (Subgroup.closure (Set.range φ)).map (ggLin (p := p) ι) := by
    have hr : Set.range r = (ggLin (p := p) ι) '' Set.range φ := by
      rw [show r = (ggLin (p := p) ι) ∘ φ from rfl, Set.range_comp]
    change Subgroup.closure (Set.range r) =
      (Subgroup.closure (Set.range φ)).map (ggLin (p := p) ι)
    rw [hr, ← MonoidHom.map_closure (ggLin (p := p) ι) (Set.range φ)]
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_basis f
  have hcard_le : Fintype.card (Option Λ) ≤ n := by
    have h1 := hind.fintype_card_le_finrank
    rwa [Module.finrank_eq_card_basis f, Fintype.card_fin] at h1
  have hn : 3 ≤ n := by
    have h9 : 9 ≤ Fintype.card (Option Λ) := by
      rw [Fintype.card_option]; omega
    omega
  by_contra hbad
  obtain ⟨bf, hbfmon, hbfperm, -⟩ := ggRC_monomial_frame hp2 f A hirr hgen hmon
  have hbadb : ¬ ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (bf i) = c i • bf (σ i) := by
    intro hgood
    exact hbad ⟨bf, hgood⟩
  obtain ⟨j, j', hjb, hj'b, hjne, hMjj'⟩ := ggRC_exists_simple_bond hWL h8 b
  have hCLjj' : CL j j' = -1 ∧ CL j' j = -1 := by
    rcases hCL.2 j j' hjne with ⟨hM, h1, h2⟩ | ⟨hM, h1, h2⟩ | ⟨hM, _, _, _⟩ | ⟨hM, _, _, _⟩
    · rw [hM] at hMjj'; omega
    · exact ⟨h1, h2⟩
    · rw [hM] at hMjj'; omega
    · rw [hM] at hMjj'; omega
  have hαjj' : α (some j) (h (some j')) = -1 := by
    rw [hL j j', hCLjj'.1]; norm_num
  have hαj'j : α (some j') (h (some j)) = -1 := by
    rw [hL j' j, hCLjj'.2]; norm_num
  have hpair : α (some j) (h (some j')) * α (some j') (h (some j)) = 1 := by
    rw [hαjj', hαj'j]; norm_num
  have hind2 : LinearIndependent (ZMod p) ![h (some j), h (some j')] := by
    have hinj : Function.Injective ![some j, some j'] := by
      intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq]
    have hfun : ![h (some j), h (some j')] = h ∘ ![some j, some j'] := by
      funext i
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hfun]
    exact hind.comp ![some j, some j'] hinj
  have hsl : ∀ w, r (some j) w = w - α (some j) w • h (some j) := fun w => hφ (some j) w
  have hsl' : ∀ w, r (some j') w = w - α (some j') w • h (some j') := fun w => hφ (some j') w
  have hsA : r (some j) ∈ A := Subgroup.subset_closure (Set.mem_range_self (some j))
  have hsA' : r (some j') ∈ A := Subgroup.subset_closure (Set.mem_range_self (some j'))
  have hsr : GGLinRefl (r (some j)) := hreflLin (some j)
  have hsr' : GGLinRefl (r (some j')) := hreflLin (some j')
  have h2 : α (some j) (h (some j)) = 2 := by
    rw [hL j j, hCL.1 j]; norm_num
  have h2' : α (some j') (h (some j')) = 2 := by
    rw [hL j' j', hCL.1 j']; norm_num
  obtain ⟨δ, hδA, ζ, hζ0, hζ1, hζ2, hrel1, hrel2, hrel3, hnc_lin⟩ :=
    ggRC_twisted_triangle hp5 hn bf A hbfperm hgen hbfmon hbadb hsA hsA' hsr hsr'
      hsl hsl' h2 h2' hpair hind2
  have hδ_map : δ ∈ (Subgroup.closure (Set.range φ)).map (ggLin (p := p) ι) := by
    rwa [← hA]
  obtain ⟨ψ, hψ, hδ_eq⟩ := Subgroup.mem_map.mp hδ_map
  let ht : V := δ (h (some j))
  let αt : Module.Dual (ZMod p) V := (α (some j)).comp (δ⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap
  have hαt : αt ht = 2 := by
    simp [αt, ht, h2]
  have htl : ∀ w, ggLin (p := p) ι (ψ * φ (some j) * ψ⁻¹) w = w - αt w • ht := by
    intro w
    have h1 : ggLin (p := p) ι (ψ * φ (some j) * ψ⁻¹) = δ * r (some j) * δ⁻¹ := by
      rw [map_mul, map_mul, map_inv, hδ_eq]
    rw [h1, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsl, map_sub, map_smul]
    simp [αt, ht]
  have hnc : ψ * φ (some j) * ψ⁻¹ * φ (some j') ≠
      φ (some j') * (ψ * φ (some j) * ψ⁻¹) := by
    intro hcon
    apply hnc_lin
    have hc := congrArg (ggLin (p := p) ι) hcon
    simpa only [map_mul, map_inv, hδ_eq] using hc
  obtain ⟨m, Q, v, μ, hQ, hv, hμ, hcongr⟩ :=
    ggRC_lattice_triple hJr hPump hLB hSP hp5 hH hφ h2 h2' hAL hAK hJ hjb hj'b hψ hαt htl hnc
  let a : Fin 3 → Fin 3 → ZMod p :=
    fun i k => (![α (some j), α (some j'), αt] i) (![h (some j), h (some j'), ht] k)
  have ha01 : a 0 1 = α (some j) (h (some j')) := by simp [a]
  have ha10 : a 1 0 = α (some j') (h (some j)) := by simp [a]
  have ha12 : a 1 2 = α (some j') (δ (h (some j))) := by simp [a, ht]
  have ha21 : a 2 1 = α (some j) (δ⁻¹ (h (some j'))) := by simp [a, αt]
  have ha02 : a 0 2 = α (some j) (δ (h (some j))) := by simp [a, ht]
  have ha20 : a 2 0 = α (some j) (δ⁻¹ (h (some j))) := by simp [a, αt]
  have h01 : a 0 1 * a 1 0 = 1 := by rw [ha01, ha10]; exact hpair
  have h12 : a 1 2 * a 2 1 = 1 := by rw [ha12, ha21]; exact hrel1
  have h02 : a 0 2 * a 2 0 = 2 + ζ + ζ⁻¹ := by rw [ha02, ha20]; exact hrel2
  have hcyc : a 1 0 * a 2 1 * a 0 2 = 1 + ζ⁻¹ := by rw [ha10, ha21, ha02]; exact hrel3
  exact ggRC_triangle_not_lattice (a := a) hp5 hζ0 hζ1 hζ2 hQ hv hμ hcongr h01 h12 h02 hcyc

end CFSG.StandardType

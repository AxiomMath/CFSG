module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGRCTriangleLattice
public import CFSG.LocalAnalysis.StandardType.GGRCLatticeTripleTwo
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialFrame
public import CFSG.LocalAnalysis.StandardType.GGRCTwistedTriangle
public import CFSG.LocalAnalysis.StandardType.GGRCLinRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRC_scalars_pm1_two (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    (hCL : GGIntCartan ML CL)
    (hbond : ∃ j j' : Λ, j ≠ b₁ ∧ j ≠ b₂ ∧ j' ≠ b₁ ∧ j' ≠ b₂ ∧ j ≠ j' ∧ ML.M j j' = 3)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p))
    (hφtop : ∀ o, φ o ∈ ggAutomizer ⊤ Bs)
    (hJL : ∀ j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, φ (Sum.inl j) ∈ ggAutomizer L Bs)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)))
    {n : ℕ} (hn : 3 ≤ n) (f : Module.Basis (Fin n) (ZMod p) V)
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
  let r : Λ ⊕ Λa → (V ≃ₗ[ZMod p] V) := fun o => ggLin (p := p) ι (φ o)
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
  by_contra hbad
  obtain ⟨bf, hbfmon, hbfperm, -⟩ := ggRC_monomial_frame hp2 f A hirr hgen hmon
  have hbadb : ¬ ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (bf i) = c i • bf (σ i) := by
    intro hgood
    exact hbad ⟨bf, hgood⟩
  obtain ⟨j, j', hj1, hj2, hj'1, hj'2, hjne, hMjj'⟩ := hbond
  have hCLjj' : CL j j' = -1 ∧ CL j' j = -1 := by
    rcases hCL.2 j j' hjne with ⟨hM, h1, h2⟩ | ⟨hM, h1, h2⟩ | ⟨hM, _, _, _⟩ | ⟨hM, _, _, _⟩
    · rw [hM] at hMjj'; omega
    · exact ⟨h1, h2⟩
    · rw [hM] at hMjj'; omega
    · rw [hM] at hMjj'; omega
  have hαjj' : α (Sum.inl j) (h (Sum.inl j')) = -1 := by
    rw [hL j j', hCLjj'.1]; norm_num
  have hαj'j : α (Sum.inl j') (h (Sum.inl j)) = -1 := by
    rw [hL j' j, hCLjj'.2]; norm_num
  have hpair : α (Sum.inl j) (h (Sum.inl j')) * α (Sum.inl j') (h (Sum.inl j)) = 1 := by
    rw [hαjj', hαj'j]; norm_num
  have h2 : α (Sum.inl j) (h (Sum.inl j)) = 2 := by
    rw [hL j j, hCL.1 j]; norm_num
  have h2' : α (Sum.inl j') (h (Sum.inl j')) = 2 := by
    rw [hL j' j', hCL.1 j']; norm_num
  have hind2 : LinearIndependent (ZMod p) ![h (Sum.inl j), h (Sum.inl j')] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 : 2 * s - t = 0 := by
      have haj := congrArg (α (Sum.inl j)) hst
      simp only [map_add, map_smul, smul_eq_mul, map_zero, h2, hαjj'] at haj
      ring_nf at haj ⊢
      exact haj
    have e2 : -s + 2 * t = 0 := by
      have haj := congrArg (α (Sum.inl j')) hst
      simp only [map_add, map_smul, smul_eq_mul, map_zero, h2', hαj'j] at haj
      ring_nf at haj ⊢
      exact haj
    have h3 : (3 : ZMod p) ≠ 0 := by
      intro h3z
      have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3z
      have := Nat.le_of_dvd (by norm_num : 0 < 3) hdvd
      omega
    have h3s : (3 : ZMod p) * s = 0 := by
      have hsum : (2 * s - t) * 2 + (-s + 2 * t) = 0 := by rw [e1, e2]; ring
      have hcanon : (2 * s - t) * 2 + (-s + 2 * t) = 3 * s := by ring
      rwa [hcanon] at hsum
    have hs : s = 0 := by
      rcases mul_eq_zero.mp h3s with h3z | hs
      · exact absurd h3z h3
      · exact hs
    have ht_eq : t = 2 * s := by
      have h := e1
      rw [sub_eq_zero] at h
      exact h.symm
    exact ⟨hs, by rw [hs] at ht_eq; simpa using ht_eq⟩
  have hsl : ∀ w, r (Sum.inl j) w = w - α (Sum.inl j) w • h (Sum.inl j) := fun w => hφ (Sum.inl j) w
  have hsl' : ∀ w, r (Sum.inl j') w = w - α (Sum.inl j') w • h (Sum.inl j') := fun w => hφ (Sum.inl j') w
  have hsA : r (Sum.inl j) ∈ A := Subgroup.subset_closure (Set.mem_range_self (Sum.inl j))
  have hsA' : r (Sum.inl j') ∈ A := Subgroup.subset_closure (Set.mem_range_self (Sum.inl j'))
  have hsr : GGLinRefl (r (Sum.inl j)) := hreflLin (Sum.inl j)
  have hsr' : GGLinRefl (r (Sum.inl j')) := hreflLin (Sum.inl j')
  obtain ⟨δ, hδA, ζ, hζ0, hζ1, hζ2, hrel1, hrel2, hrel3, hnc_lin⟩ :=
    ggRC_twisted_triangle hp5 hn bf A hbfperm hgen hbfmon hbadb hsA hsA' hsr hsr'
      hsl hsl' h2 h2' hpair hind2
  have hδ_map : δ ∈ (Subgroup.closure (Set.range φ)).map (ggLin (p := p) ι) := by
    rwa [← hA]
  obtain ⟨ψ, hψ, hδ_eq⟩ := Subgroup.mem_map.mp hδ_map
  let ht : V := δ (h (Sum.inl j))
  let αt : Module.Dual (ZMod p) V := (α (Sum.inl j)).comp (δ⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap
  have hαt : αt ht = 2 := by
    simp [αt, ht, h2]
  have htl : ∀ w, ggLin (p := p) ι (ψ * φ (Sum.inl j) * ψ⁻¹) w = w - αt w • ht := by
    intro w
    have h1 : ggLin (p := p) ι (ψ * φ (Sum.inl j) * ψ⁻¹) = δ * r (Sum.inl j) * δ⁻¹ := by
      rw [map_mul, map_mul, map_inv, hδ_eq]
    rw [h1, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsl, map_sub, map_smul]
    simp [αt, ht]
  have hnc : ψ * φ (Sum.inl j) * ψ⁻¹ * φ (Sum.inl j') ≠
      φ (Sum.inl j') * (ψ * φ (Sum.inl j) * ψ⁻¹) := by
    intro hcon
    apply hnc_lin
    have hc := congrArg (ggLin (p := p) ι) hcon
    simpa only [map_mul, map_inv, hδ_eq] using hc
  obtain ⟨m, Q, v, μ, hQ, hv, hμ, hcongr⟩ :=
    ggRC_lattice_triple_two hJr hPump hLB hSP hp5 hH hφ h2 h2' hφtop hJL hJ
      ⟨hj1, hj2⟩ ⟨hj'1, hj'2⟩ hψ hαt htl hnc
  let a : Fin 3 → Fin 3 → ZMod p :=
    fun i k => (![α (Sum.inl j), α (Sum.inl j'), αt] i) (![h (Sum.inl j), h (Sum.inl j'), ht] k)
  have ha01 : a 0 1 = α (Sum.inl j) (h (Sum.inl j')) := by simp [a]
  have ha10 : a 1 0 = α (Sum.inl j') (h (Sum.inl j)) := by simp [a]
  have ha12 : a 1 2 = α (Sum.inl j') (δ (h (Sum.inl j))) := by simp [a, ht]
  have ha21 : a 2 1 = α (Sum.inl j) (δ⁻¹ (h (Sum.inl j'))) := by simp [a, αt]
  have ha02 : a 0 2 = α (Sum.inl j) (δ (h (Sum.inl j))) := by simp [a, ht]
  have ha20 : a 2 0 = α (Sum.inl j) (δ⁻¹ (h (Sum.inl j))) := by simp [a, αt]
  have h01 : a 0 1 * a 1 0 = 1 := by rw [ha01, ha10]; exact hpair
  have h12 : a 1 2 * a 2 1 = 1 := by rw [ha12, ha21]; exact hrel1
  have h02 : a 0 2 * a 2 0 = 2 + ζ + ζ⁻¹ := by rw [ha02, ha20]; exact hrel2
  have hcyc : a 1 0 * a 2 1 * a 0 2 = 1 + ζ⁻¹ := by rw [ha10, ha21, ha02]; exact hrel3
  exact ggRC_triangle_not_lattice (a := a) hp5 hζ0 hζ1 hζ2 hQ hv hμ hcongr h01 h12 h02 hcyc

end CFSG.StandardType

end

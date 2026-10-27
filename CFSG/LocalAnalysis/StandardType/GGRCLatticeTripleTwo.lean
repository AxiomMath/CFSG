module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDichotomy
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpConj
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpCartan

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6e1_ggInduced_mono' {G : Type} [Group G] {H H' : Subgroup G} {Bs : Subgroup G}
    (h : H ≤ H') {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced H Bs) : φ ∈ ggInduced H' Bs := by
  obtain ⟨g, hg, hgN, hgφ⟩ := hφ
  exact ⟨g, h hg, hgN, hgφ⟩

theorem ggRC_lattice_triple_two (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ}
    {Λa : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    {j j' : Λ} (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hαj : α (Sum.inl j) (h (Sum.inl j)) = 2) (hαj' : α (Sum.inl j') (h (Sum.inl j')) = 2)
    (hφtop : ∀ o, φ o ∈ ggAutomizer ⊤ Bs)
    (hJL : ∀ j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, φ (Sum.inl j) ∈ ggAutomizer L Bs)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)))
    (hj : j ≠ b₁ ∧ j ≠ b₂) (hj' : j' ≠ b₁ ∧ j' ≠ b₂) {ψ : MulAut ↥Bs}
    (hψ : ψ ∈ Subgroup.closure (Set.range φ)) {ht : V} {αt : Module.Dual (ZMod p) V}
    (hαt : αt ht = 2)
    (htl : ∀ w, ggLin (p := p) ι (ψ * φ (Sum.inl j) * ψ⁻¹) w = w - αt w • ht)
    (hnc : ψ * φ (Sum.inl j) * ψ⁻¹ * φ (Sum.inl j') ≠
      φ (Sum.inl j') * (ψ * φ (Sum.inl j) * ψ⁻¹)) :
    ∃ (m : ℕ) (Q : Matrix (Fin m) (Fin m) ℤ) (v : Fin 3 → Fin m → ℤ) (μ : Fin 3 → ZMod p),
      GGLatForm Q ∧ (∀ k, GGLatRoot Q (v k)) ∧ (∀ k, μ k ≠ 0) ∧
      ∀ i k : Fin 3, (![α (Sum.inl j), α (Sum.inl j'), αt] i)
          (![h (Sum.inl j), h (Sum.inl j'), ht] k) * μ k = μ i * (ggLatCartan Q (v k) (v i) : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hcfg, hop, hInn, hNT, -, -, hsc⟩ := hH
  have hφL : ∀ i : Λ, (i ≠ b₁ ∧ i ≠ b₂) → φ (Sum.inl i) ∈ ggInduced L Bs := fun i hi =>
    mem_ggAutomizer_iff.mp (hJL ⟨i, hi⟩)
  have hφJ : ∀ i : Λ, (i ≠ b₁ ∧ i ≠ b₂) → φ (Sum.inl i) ∈ ggInduced J Bs := by
    intro i hi
    have h : φ (Sum.inl i) ∈ ggAutomizer J Bs := by
      rw [hJ]
      exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
    exact mem_ggAutomizer_iff.mp h
  have hφrange : Set.range φ ⊆ ggInduced ⊤ Bs := by
    rintro _ ⟨o, rfl⟩
    exact mem_ggAutomizer_iff.mp (hφtop o)
  have hψtop : ψ ∈ ggAutomizer ⊤ Bs := Subgroup.closure_mono hφrange hψ
  have hψind : ψ ∈ ggInduced ⊤ Bs := by
    rw [ggAutomizer_eq] at hψtop
    exact hψtop
  obtain ⟨g, -, hgN, hgψval⟩ := hψind
  have hgψ : ggConjAut Bs hgN = ψ := by
    ext b
    simp only [ggConjAut_apply, hgψval b]
  have hrefl_j : GGIsReflection p (φ (Sum.inl j)) :=
    ggIsReflection_of_eq_reflection hp2 ι hαj (ggLin_eq_reflection ι hαj (hφ (Sum.inl j)))
  obtain ⟨Jr, hind_j, hJC_j, hpc_j⟩ :=
    (hJr G p B Bs x L D J hcfg hInn hNT hp5 (φ (Sum.inl j)) (hφL j hj) hrefl_j).1
  obtain ⟨hrt, hindt, hJCt, hpct⟩ :=
    ggRealization_conj hp hgN hrefl_j hind_j hJC_j hpc_j
  rw [hgψ] at hrt hindt hJCt hpct
  have hPumpAll := hPump G p B Bs x L D J hcfg hop hInn hNT hsc hp5
  have hmain : ∃ X : Subgroup G, GGAutLattice p Bs X ∧
      ψ * φ (Sum.inl j) * ψ⁻¹ ∈ ggInduced X Bs ∧
      φ (Sum.inl j) ∈ ggInduced X Bs ∧ φ (Sum.inl j') ∈ ggInduced X Bs := by
    rcases ggDichotomy_refined hLB hSP hcfg hInn hrt hindt hJCt hpct with
      hLt | ⟨d, K', hnb', hJK', hJtK'⟩ | hcomm
    · exact ⟨L, hPumpAll.1, l6e1_ggInduced_mono' hLt hindt, hφL j hj, hφL j' hj'⟩
    · rcases hPumpAll.2 d K' hnb' with hlat | hnoref
      · exact ⟨K', hlat, l6e1_ggInduced_mono' hJtK' hindt,
          l6e1_ggInduced_mono' hJK' (hφJ j hj),
          l6e1_ggInduced_mono' hJK' (hφJ j' hj')⟩
      · exact absurd hrt (hnoref _ (l6e1_ggInduced_mono' hJtK' hindt))
    · exfalso
      exact hnc (hcomm (φ (Sum.inl j')) (hφJ j' hj'))
  obtain ⟨X, hXlat, htX, hsX, hs'X⟩ := hmain
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have htvec : ∀ k : Fin 3,
      ![φ (Sum.inl j), φ (Sum.inl j'), ψ * φ (Sum.inl j) * ψ⁻¹] k ∈ ggInduced X Bs := by
    intro k
    fin_cases k
    · simpa using hsX
    · simpa using hs'X
    · simpa using htX
  have hαvec : ∀ k : Fin 3,
      (![α (Sum.inl j), α (Sum.inl j'), αt] k) (![h (Sum.inl j), h (Sum.inl j'), ht] k) = 2 := by
    intro k
    fin_cases k
    · simpa using hαj
    · simpa using hαj'
    · simpa using hαt
  have hlinvec : ∀ k w,
      ggLin (p := p) ι (![φ (Sum.inl j), φ (Sum.inl j'), ψ * φ (Sum.inl j) * ψ⁻¹] k) w =
        w - ![α (Sum.inl j), α (Sum.inl j'), αt] k w •
          ![h (Sum.inl j), h (Sum.inl j'), ht] k := by
    intro k w
    fin_cases k
    · simpa using hφ (Sum.inl j) w
    · simpa using hφ (Sum.inl j') w
    · simpa using htl w
  obtain ⟨m, Q, v, μ, hQ, hroot, hμ, hcart, -, -⟩ :=
    ggAutLattice_cartan (p := p) hp2 hBs ι hXlat (κ := Fin 3)
      (t := ![φ (Sum.inl j), φ (Sum.inl j'), ψ * φ (Sum.inl j) * ψ⁻¹])
      (h := ![h (Sum.inl j), h (Sum.inl j'), ht])
      (α := ![α (Sum.inl j), α (Sum.inl j'), αt]) htvec hαvec hlinvec
  exact ⟨m, Q, v, μ, hQ, hroot, hμ, hcart⟩

end CFSG.StandardType

end

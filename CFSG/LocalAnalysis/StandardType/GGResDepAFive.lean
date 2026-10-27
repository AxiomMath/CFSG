module

public import CFSG.LocalAnalysis.StandardType.GGDepAConfig
public import CFSG.LocalAnalysis.StandardType.GGDepAYFixed
public import CFSG.LocalAnalysis.StandardType.GGDepAKSide
public import CFSG.LocalAnalysis.StandardType.GGDepAPattern
public import CFSG.LocalAnalysis.StandardType.GGDepACaseI
public import CFSG.LocalAnalysis.StandardType.GGDepACaseII
public import CFSG.LocalAnalysis.StandardType.GGDepASmall
public import CFSG.LocalAnalysis.StandardType.GGResLeaves

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nDD5_five_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    5 ≤ p := by
  have hp : p.Prime := Fact.out
  have h2 : 2 ≤ p := hp.two_le
  by_contra h
  have hlt : p < 5 := by omega
  interval_cases p <;>
    first
      | exact absurd rfl hp2
      | exact absurd rfl hp3
      | exact absurd hp (by norm_num)

private theorem l05nDD5_cases_small {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hp : 5 ≤ p)
    (hN5 : 5 ≤ N) (hN10 : N ≤ 10) :
    (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10) := by
  have hprime : p.Prime := Fact.out
  have hpN_le : p ≤ N := Nat.le_of_dvd (by omega) hpN
  have hp10 : p ≤ 10 := le_trans hpN_le hN10
  have hp57 : p = 5 ∨ p = 7 := by
    interval_cases p <;>
      first
        | exact Or.inl rfl
        | exact Or.inr rfl
        | exact absurd hprime (by norm_num)
  rcases hp57 with rfl | rfl
  · have hN : N = 5 ∨ N = 10 := by
      interval_cases N <;>
        first
          | exact Or.inl rfl
          | exact Or.inr rfl
          | exact absurd hpN (by norm_num)
    rcases hN with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · have hN : N = 7 := by
      interval_cases N <;>
        first
          | rfl
          | exact absurd hpN (by norm_num)
    subst hN
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)

private theorem l05nDD5_large (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hN : 11 ≤ N) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {x : V} (F : GGDepAFrame p N h α x) (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (ra : V ≃ₗ[ZMod p] V) (ha : V)
    (αa : Module.Dual (ZMod p) V) (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2)
    (hjoin : ∃ c, αa (h c) ≠ 0) (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N)) : False := by
  by_cases hnH : ha ∈ Submodule.span (ZMod p) (Set.range h)
  · exact ggDepA_caseII_false hKG hp hN F r hr ra ha αa hra hαa hw hnt hcard hnH
  · exact ggDepA_caseI_false hKG hp hN F r hr ra ha αa hra hαa hjoin hw hnt hcard hnH

private theorem l05nDD5_small (hS5 : GGDepASmallCells 5 5) (hS7 : GGDepASmallCells 7 7)
    (hS10 : GGDepASmallCells 5 10) {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hpN : p ∣ N)
    (hN5 : 5 ≤ N) (hN10 : N ≤ 10) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {x : V} (F : GGDepAFrame p N h α x) (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (ra : V ≃ₗ[ZMod p] V) (ha : V)
    (αa : Module.Dual (ZMod p) V) (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2)
    (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK) (e : Fin (N - 1) ≃ Λ)
    (hend : (e.symm b).val = 0 ∨ (e.symm b).val + 2 = N)
    (hKss : ∀ i j : {i : Λ // i ≠ b},
      α (e.symm i.1) (h (e.symm j.1)) = (CK (some i) (some j) : ZMod p))
    (hKn : ∀ i : {i : Λ // i ≠ b}, αa (h (e.symm i.1)) = (CK none (some i) : ZMod p))
    (hKs : ∀ i : {i : Λ // i ≠ b}, α (e.symm i.1) ha = (CK (some i) none : ZMod p))
    (hy : ∃ y : V, y ∉ Submodule.span (ZMod p) {x} ∧
      ∀ c : Fin (N - 1), c ≠ e.symm b → α c y = 0) : False := by
  have hJ' : ∀ i j : {i : Λ // i ≠ b}, (CK (some i) (some j) : ZMod p) =
      (CartanMatrix.A (N - 1) (e.symm i.1) (e.symm j.1) : ZMod p) := by
    intro i j
    rw [← hKss i j, F.pair]
  have hNcases : N = 5 ∨ N = 7 ∨ N = 10 := by
    rcases l05nDD5_cases_small hpN hp hN5 hN10 with ⟨-, hN⟩ | ⟨-, hN⟩ | ⟨-, hN⟩
    · exact Or.inl hN
    · exact Or.inr (Or.inl hN)
    · exact Or.inr (Or.inr hN)
  obtain ⟨c0, m, n, hpat, hclause⟩ := ggDepA_pattern hp hNcases e hend hWK hCK hJ'
  have hpair : ∀ c : Fin (N - 1), c ≠ e.symm b →
      αa (h c) = (if c = c0 then (m : ZMod p) else 0) ∧
      α c ha = (if c = c0 then (n : ZMod p) else 0) := by
    intro c hc
    have hcb : e c ≠ b := by
      intro h
      exact hc ((Equiv.symm_apply_apply e c).symm.trans (congrArg e.symm h))
    let i : {i : Λ // i ≠ b} := ⟨e c, hcb⟩
    have hii : e.symm i.1 = c := by simp [i]
    obtain ⟨h1, h2⟩ := hclause i
    rw [hii] at h1 h2
    constructor
    · calc αa (h c) = αa (h (e.symm i.1)) := by rw [hii]
        _ = (CK none (some i) : ZMod p) := hKn i
        _ = ((if c = c0 then m else 0 : ℤ) : ZMod p) := by rw [h1]
        _ = (if c = c0 then (m : ZMod p) else 0) := by by_cases h : c = c0 <;> simp [h]
    · calc α c ha = α (e.symm i.1) ha := by rw [hii]
        _ = (CK (some i) none : ZMod p) := hKs i
        _ = ((if c = c0 then n else 0 : ℤ) : ZMod p) := by rw [h2]
        _ = (if c = c0 then (n : ZMod p) else 0) := by by_cases h : c = c0 <;> simp [h]
  rcases l05nDD5_cases_small hpN hp hN5 hN10 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ggDepA_small_false hS5 F r hr ra ha αa hra hαa hw (e.symm b) c0 m n hpat hpair hy hnt
  · exact ggDepA_small_false hS7 F r hr ra ha αa hra hαa hw (e.symm b) c0 m n hpat hpair hy hnt
  · exact ggDepA_small_false hS10 F r hr ra ha αa hra hαa hw (e.symm b) c0 m n hpat hpair hy hnt

theorem ggResDepAFiveInput_of_inputs (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hS5 : GGDepASmallCells 5 5)
    (hS7 : GGDepASmallCells 7 7) (hS10 : GGDepASmallCells 5 10) : GGResDepAFiveInput := by
  intro G _ _ p B Bs x L D J y K hH _ hFork hStd hE6 hP
  exfalso
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hAL, hAK, hdel, hJ⟩ := hP.2
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp3 : p ≠ 3 := hP.1
  have hp : 5 ≤ p := l05nDD5_five_le hp2 hp3
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hdep : ¬ LinearIndependent (ZMod p) fun i : Λ => h (some i) := hsel
  have htypA : GGIsTypeA ML := htyp
  have hαL : ∀ c : Λ, α (some c) (h (some c)) = 2 := by
    intro c
    have h1 := hL c c
    rw [hCL.1 c] at h1
    simpa using h1
  obtain ⟨N, e, hN3, hpN, hend, hCartan, F⟩ :=
    ggDepA_frame_of_config hFix hp2 hH hxBs hCL htypA hdel hφ hL hdep hAL
  have hN5 : 5 ≤ N := by
    have hpos : 0 < N := by omega
    have := Nat.le_of_dvd hpos hpN
    omega
  obtain ⟨hαa, hw, hjoin, hnt, hcard⟩ :=
    ggDepA_kside hFix hFixK hOrb hp2 hH hxBs hWL hCL hWK hCK hφ hL hK hAL hAK e hN5 F
  obtain ⟨y', hy'x, hy'α⟩ := ggDepA_y_fixed hp2 hH hxBs hφ hαL hJ
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (some (e i)))
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (φ none)
  let ha : V := h none
  let αa : Module.Dual (ZMod p) V := α none
  have hr : ∀ i v, r i v = v - α (some (e i)) v • h (some (e i)) := fun i v => hφ (some (e i)) v
  have hra : ∀ v, ra v = v - αa v • ha := fun v => hφ none v
  have hKss : ∀ i j : {i : Λ // i ≠ b},
      (fun i : Fin (N - 1) => α (some (e i))) (e.symm i.1)
        ((fun i : Fin (N - 1) => h (some (e i))) (e.symm j.1)) =
        (CK (some i) (some j) : ZMod p) := by
    intro i j
    simpa using hK (some i) (some j)
  have hKn : ∀ i : {i : Λ // i ≠ b},
      αa ((fun i : Fin (N - 1) => h (some (e i))) (e.symm i.1)) = (CK none (some i) : ZMod p) := by
    intro i
    simpa [αa] using hK none (some i)
  have hKs : ∀ i : {i : Λ // i ≠ b},
      (fun i : Fin (N - 1) => α (some (e i))) (e.symm i.1) ha = (CK (some i) none : ZMod p) := by
    intro i
    simpa [ha] using hK (some i) none
  have hy : ∃ y : V, y ∉ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hxBs⟩)} ∧
      ∀ c : Fin (N - 1), c ≠ e.symm b → α (some (e c)) y = 0 := by
    refine ⟨y', hy'x, ?_⟩
    intro c hc
    exact hy'α (e c) (fun h => hc ((Equiv.symm_apply_apply e c).symm.trans (congrArg e.symm h)))
  by_cases hN11 : 11 ≤ N
  · exact l05nDD5_large hKG hp hN11 F r hr ra ha αa hra hαa hjoin hw hnt hcard
  · have hN10 : N ≤ 10 := by omega
    exact l05nDD5_small hS5 hS7 hS10 hp hpN hN5 hN10 F r hr ra ha αa hra hαa hw hnt
      hWK hCK e hend hKss hKn hKs hy

end CFSG.StandardType

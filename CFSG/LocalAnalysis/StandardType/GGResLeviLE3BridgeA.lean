module

public import CFSG.LocalAnalysis.StandardType.GGForkF1

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGWeylSimpleSystemsConj
public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.StandardType.GGResILineExit
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS4aAuxA
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
public import CFSG.LocalAnalysis.StandardType.GGResXDatumA
public import CFSG.LocalAnalysis.StandardType.GGRCTypeADet
public import CFSG.RankThree.PartOne.S12.Sec1511EILin
public import TauCeti.Combinatorics.SimpleGraph.BranchComponents

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l05nBL_refl_conj {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {φ : MulAut ↥Bs} (h : GGIsReflection p φ) (ψ : MulAut ↥Bs) :
    GGIsReflection p (ψ * φ * ψ⁻¹) := by
  refine ⟨by rw [conj_pow, h.1, mul_one, mul_inv_cancel], ?_⟩
  rw [← h.2]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv (ψ⁻¹ : MulAut ↥Bs).toEquiv fun b => ?_)
  show ψ (φ (ψ⁻¹ b)) = b ↔ φ (ψ⁻¹ b) = ψ⁻¹ b
  constructor
  · intro hb
    have h1 := congrArg (ψ⁻¹ : MulAut ↥Bs) hb
    rwa [MulAut.inv_apply_self] at h1
  · intro hb
    rw [hb, MulAut.apply_inv_self]

theorem l05nBL_lin_conj {p : ℕ} [Fact p.Prime] {E : Type} [Group E] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) (u φ : MulAut E)
    {g : Module.Dual (ZMod p) V} {z : V}
    (hφ : ∀ v, ggLin (p := p) ι φ v = v - g v • z) (v : V) :
    ggLin (p := p) ι (u * φ * u⁻¹) v =
      v - g ((ggLin (p := p) ι u).symm v) • ggLin (p := p) ι u z := by
  rw [map_mul, map_mul, map_inv]
  show ggLin (p := p) ι u (ggLin (p := p) ι φ ((ggLin (p := p) ι u).symm v)) = _
  rw [hφ, map_sub, map_smul, LinearEquiv.apply_symm_apply]

theorem l05nBL_closure_conj {E : Type} [Group E] (S : Subgroup E) (u : E) (hu : u ∈ S) :
    Subgroup.map (MulAut.conj u).toMonoidHom S = S := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hy) (Subgroup.inv_mem _ hu)
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨u⁻¹ * x * u, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hx) hu
    · show u * (u⁻¹ * x * u) * u⁻¹ = x
      group

theorem l05nBL_rankOne {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {f f' : Module.Dual (ZMod p) V} {x x' : V}
    (hf : f x = 2) (hf' : f' x' = 2) (h : ∀ v, f v • x = f' v • x') :
    ∃ c : (ZMod p)ˣ, x' = (c : ZMod p) • x ∧ f' = (↑(c⁻¹) : ZMod p) • f := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, map_zero] at hf
    exact h2 hf.symm
  have hfx : f' x ≠ 0 := by
    intro h0
    have h1 := h x
    rw [hf, h0, zero_smul] at h1
    exact hx0 ((smul_eq_zero.mp h1).resolve_left h2)
  have hc0 : 2 * (f' x)⁻¹ ≠ 0 := mul_ne_zero h2 (inv_ne_zero hfx)
  have hxc : x' = (2 * (f' x)⁻¹) • x := by
    have h1 := h x
    rw [hf] at h1
    have h2' : (f' x)⁻¹ • ((2 : ZMod p) • x) = x' := by
      calc (f' x)⁻¹ • ((2 : ZMod p) • x) = (f' x)⁻¹ • (f' x • x') :=
            congrArg ((f' x)⁻¹ • ·) h1
        _ = ((f' x)⁻¹ * f' x) • x' := smul_smul (f' x)⁻¹ (f' x) x'
        _ = (1 : ZMod p) • x' := by rw [inv_mul_cancel₀ hfx]
        _ = x' := one_smul _ _
    calc x' = (f' x)⁻¹ • ((2 : ZMod p) • x) := h2'.symm
      _ = ((f' x)⁻¹ * 2) • x := smul_smul (f' x)⁻¹ (2 : ZMod p) x
      _ = (2 * (f' x)⁻¹) • x := by rw [mul_comm]
  refine ⟨Units.mk0 (2 * (f' x)⁻¹) hc0, hxc, ?_⟩
  apply LinearMap.ext
  intro v
  have h1' : f v • x = (f' v * (2 * (f' x)⁻¹)) • x := by
    rw [h v, hxc]
    exact smul_smul (f' v) (2 * (f' x)⁻¹) x
  have hzero : (f v - f' v * (2 * (f' x)⁻¹)) • x = 0 := by
    rw [sub_smul, h1', sub_self]
  have hcoe : f v - f' v * (2 * (f' x)⁻¹) = 0 :=
    (smul_eq_zero.mp hzero).resolve_right hx0
  have hfv : f' v * (2 * (f' x)⁻¹) = f v := (sub_eq_zero.mp hcoe).symm
  change f' v = (2 * (f' x)⁻¹)⁻¹ * f v
  calc f' v = (f' v * (2 * (f' x)⁻¹)) * (2 * (f' x)⁻¹)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hc0, mul_one]
    _ = f v * (2 * (f' x)⁻¹)⁻¹ := by rw [hfv]
    _ = (2 * (f' x)⁻¹)⁻¹ * f v := by rw [mul_comm]

theorem l05nBL_cartan_eq_zero_iff {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {i j : Λ} (hij : i ≠ j) : C i j = 0 ↔ M.M i j = 2 := by
  constructor
  · intro h
    rcases hC.2 i j hij with ⟨hm, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩
    · exact hm
    · rw [h] at h1; exact absurd h1 (by norm_num)
    · rw [h, zero_mul] at h1; exact absurd h1 (by norm_num)
    · rw [h, zero_mul] at h1; exact absurd h1 (by norm_num)
  · intro h
    rcases hC.2 i j hij with ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩
    · exact h1
    · exact absurd (hm.symm.trans h) (by norm_num)
    · exact absurd (hm.symm.trans h) (by norm_num)
    · exact absurd (hm.symm.trans h) (by norm_num)

theorem l05nBL_weylFixed {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M) :
    GGIsWeylMatrixFixed M := h

theorem l05nBL_nonempty {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M) :
    Nonempty ι := by
  rcases h with ⟨n, e, hn, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact ⟨e ⟨0, by omega⟩⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩

theorem l05nBL_graph_adj {Λ : Type} [Fintype Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hWM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (i j : Λ) :
    (TauCeti.diagramGraph C).Adj i j ↔ i ≠ j ∧ M.M i j ≠ 2 := by
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (l05nBL_weylFixed hWM) hC
  rw [TauCeti.IsFiniteType.diagramGraph_adj_iff hFT]
  constructor
  · rintro ⟨hij, hCij⟩
    exact ⟨hij, fun hM => hCij ((l05nBL_cartan_eq_zero_iff hC hij).2 hM)⟩
  · rintro ⟨hij, hMij⟩
    exact ⟨hij, fun h0 => hMij ((l05nBL_cartan_eq_zero_iff hC hij).1 h0)⟩

theorem l05nBL_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b)
    {a b : α} (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

theorem l05nBL_reindex_trans {ι κ ν : Type} (M : CoxeterMatrix ι) (e : ι ≃ κ)
    (f : κ ≃ ν) : (M.reindex e).reindex f = M.reindex (e.trans f) := by
  apply CoxeterMatrix.ext
  funext x y
  simp only [CoxeterMatrix.reindex_apply, Equiv.trans_apply, Equiv.symm_trans_apply]

theorem l05nBL_weyl_reindex {ι κ : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M)
    (f : ι ≃ κ) : GGIsWeylMatrix (M.reindex f) := by
  rcases h with ⟨n, e, hn, h | ⟨hn, h⟩ | ⟨hn, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩
  · exact Or.inl ⟨n, e.trans f, hn, Or.inl (by rw [h, l05nBL_reindex_trans])⟩
  · exact Or.inl ⟨n, e.trans f, by omega, Or.inr (Or.inl ⟨hn, by rw [h, l05nBL_reindex_trans]⟩)⟩
  · exact Or.inl ⟨n, e.trans f, by omega,
      Or.inr (Or.inr ⟨hn, by rw [h, l05nBL_reindex_trans]⟩)⟩
  · exact Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nBL_reindex_trans]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nBL_reindex_trans]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nBL_reindex_trans]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f,
      by rw [h, l05nBL_reindex_trans]⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans f,
      by rw [h, l05nBL_reindex_trans]⟩))))

theorem l05nBL_intCartan_reindex {Γ Δ : Type} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (h : GGIntCartan M C) (e : Δ ≃ Γ) :
    GGIntCartan (M.reindex e.symm) (fun o o' => C (e o) (e o')) := by
  constructor
  · intro o
    simpa using h.1 (e o)
  · intro o o' hne
    have hene : e o ≠ e o' := fun hh => hne (e.injective hh)
    have hh := h.2 (e o) (e o') hene
    simpa only [CoxeterMatrix.reindex_apply, Equiv.symm_symm] using hh

@[expose] def l05nBL_sideSum {G : Type} [Group G] [Finite G] (k : ℕ) (p : ℕ) [Fact p.Prime]
    (Bs X J : Subgroup G) : Prop :=
  ∃ (Λj : Type) (_ : Fintype Λj) (_ : DecidableEq Λj) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (M : CoxeterMatrix (Λj ⊕ Λa)) (C : Matrix (Λj ⊕ Λa) (Λj ⊕ Λa) ℤ)
    (MJ : CoxeterMatrix Λj) (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
    (ι : Additive ↥Bs ≃+ V) (φ : Λj ⊕ Λa → MulAut ↥Bs) (h : Λj ⊕ Λa → V)
    (α : Λj ⊕ Λa → Module.Dual (ZMod p) V),
    1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 3 ∧ Nat.card Λa = k ∧ GGIsWeylMatrix M ∧
      GGIntCartan M C ∧ GGIsWeylMatrix MJ ∧
      (∀ j j' : Λj, MJ.M j j' = M.M (Sum.inl j) (Sum.inl j')) ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧ (∀ o o', α o (h o') = (C o o' : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ o, (f (M.simple o) : MulAut ↥Bs) = φ o) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∃ fJ : MJ.Group ≃* ↥(ggAutomizer J Bs),
        ∀ j, (fJ (MJ.simple j) : MulAut ↥Bs) = φ (Sum.inl j)) ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Λj => φ (Sum.inl j)) ∧
      GGReflConjSimple p (ggAutomizer J Bs) (fun j : Λj => φ (Sum.inl j))

theorem l05nBL_reindex {G : Type} [Group G] [Finite G] (k : ℕ) {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {Λj : Type} [Fintype Λj] [DecidableEq Λj] {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (e : Λj ⊕ Λa ≃ Λ) {MJ : CoxeterMatrix Λj} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hcard1 : 1 ≤ Nat.card Λa) (hcard2 : Nat.card Λa ≤ 3)
    (hk : Nat.card Λa = k)
    (hWM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hWMJ : GGIsWeylMatrix MJ)
    (hMJ : ∀ j j' : Λj, MJ.M j j' = M.M (e (Sum.inl j)) (e (Sum.inl j')))
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (f : M.Group ≃* ↥(ggAutomizer X Bs)) (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (fJ : MJ.Group ≃* ↥(ggAutomizer J Bs))
    (hfJ : ∀ j, (fJ (MJ.simple j) : MulAut ↥Bs) = φ (e (Sum.inl j)))
    (hclosJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Λj => φ (e (Sum.inl j))))
    (hconj : GGReflConjSimple p (ggAutomizer J Bs) (fun j : Λj => φ (e (Sum.inl j)))) :
    l05nBL_sideSum k p Bs X J := by
  refine ⟨Λj, inferInstance, inferInstance, Λa, inferInstance, inferInstance,
    M.reindex e.symm, (fun o o' => C (e o) (e o')), MJ, V, inferInstance, inferInstance,
    ι, φ ∘ e, h ∘ e, α ∘ e, hcard1, hcard2, hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact l05nBL_weyl_reindex hWM e.symm
  · exact l05nBL_intCartan_reindex hC e
  · exact hWMJ
  · intro j j'
    rw [CoxeterMatrix.reindex_apply, Equiv.symm_symm]
    exact hMJ j j'
  · intro o w
    exact hlin (e o) w
  · intro o
    exact hrefl (e o)
  · intro o o'
    exact hpair (e o) (e o')
  · refine ⟨(M.reindexGroupEquiv e.symm).trans f, ?_⟩
    intro o
    show f ((M.reindexGroupEquiv e.symm) ((M.reindex e.symm).simple o)) = φ (e o)
    rw [CoxeterMatrix.reindexGroupEquiv_apply_simple, Equiv.symm_symm]
    exact hf (e o)
  · rw [Function.Surjective.range_comp e.surjective φ]
    exact hclos
  · exact ⟨fJ, hfJ⟩
  · exact hclosJ
  · exact hconj

theorem l05nBL_sum_of_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (h : GGResSideDatum p Bs X J) : l05nBL_sideSum 1 p Bs X J := by
  obtain ⟨Λ, i1, i2, b, M, C, MJ, V, i3, i4, ι, φ, hc, α, hWM, hC, hWMJ, hMJ, hlin, hrefl,
    hpair, hf, hclos, hfJ, hclosJ, hconj⟩ := h
  letI := i1; letI := i2; letI := i3; letI := i4
  obtain ⟨f, hf⟩ := hf
  obtain ⟨fJ, hfJ⟩ := hfJ
  let e : {j : Λ // j ≠ b} ⊕ Unit ≃ Λ :=
    { toFun := fun o => match o with
        | Sum.inl j => (j : Λ)
        | Sum.inr _ => b
      invFun := fun i => if hi : i = b then Sum.inr () else Sum.inl ⟨i, hi⟩
      left_inv := by
        intro o
        cases o with
        | inl j => simp [dif_neg j.2]
        | inr u => simp
      right_inv := by
        intro i
        by_cases hi : i = b
        · simp [dif_pos hi, hi]
        · simp [dif_neg hi] }
  exact l05nBL_reindex 1 (p := p) (X := X) (J := J) e ι φ hc α (by simp) (by simp) (by simp)
    hWM hC hWMJ (fun j j' => hMJ j j') hlin hrefl hpair f hf hclos fJ hfJ hclosJ hconj

theorem l05nBL_sum_of_levi {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (h : GGResLeviSideDatumLE3 p Bs X J) :
    ∃ k, 2 ≤ k ∧ k ≤ 3 ∧ l05nBL_sideSum k p Bs X J := by
  obtain ⟨Λ, i1, i2, S, M, C, MJ, V, i3, i4, ι, φ, h, α, hS1, hS2, hWM, hC, hWMJ, hMJ,
    hlin, hrefl, hpair, hfx, hclos, hfJx, hclosJ, hconj⟩ := h
  letI := i1; letI := i2; letI := i3; letI := i4
  obtain ⟨f, hf⟩ := hfx
  obtain ⟨fJ, hfJ⟩ := hfJx
  let e : {i : Λ // i ∉ S} ⊕ {i : Λ // i ∈ S} ≃ Λ :=
    (Equiv.sumComm _ _).trans (Equiv.sumCompl (fun i : Λ => i ∈ S))
  have he : ∀ j : {i : Λ // i ∉ S}, e (Sum.inl j) = j.1 := by
    intro j
    simp only [e, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl,
      Equiv.sumCompl_apply_inr]
  have hcard : Nat.card {i : Λ // i ∈ S} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp
  refine ⟨S.card, hS1, hS2, ?_⟩
  refine l05nBL_reindex S.card (p := p) (X := X) (J := J) e ι φ h α ?_ ?_ hcard
    hWM hC hWMJ ?_ hlin hrefl hpair f hf hclos fJ hfJ hclosJ hconj
  · omega
  · omega
  · intro j j'
    rw [he j, he j']
    exact hMJ j j'

theorem ggResL_rank_core_add_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] {C : Matrix Λ Λ ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hdiag : ∀ i, C i i = 2)
    (hgen : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 ≤ Module.finrank (ZMod p) V := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.2.1.1 hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  let v : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  have hv : v ≠ 0 := by
    intro h0
    have h1 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      exact ι.injective (by simpa [v] using h0)
    exact hx1 (by simpa using congrArg Subtype.val h1)
  have hαv : ∀ i, α i v = 0 := by
    intro i
    have hmem : φ i ∈ ggAutomizer L Bs := by
      rw [hgen]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hfix : φ i ⟨x, hxBs⟩ = ⟨x, hxBs⟩ :=
      ggResI_automizer_fix hxBs hxL (φ i) hmem
    have hfixlin : ggLin (p := p) ι (φ i) v = v := by
      dsimp only [v]
      exact (ggLin_fix_iff (p := p) ι (φ i) ⟨x, hxBs⟩).mp hfix
    refine ggResI_alpha_eq_zero hp2 (hlin i) ?_ hfixlin
    rw [hpair i i, hdiag i]
    norm_num
  exact CFSG.StandardType.LevTwo.levTwoS4a_rank_core_add_one hpair hv hαv

theorem ggResK_rank_core_add_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] {C : Matrix Λ Λ ℤ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hdiag : ∀ i, C i i = 2)
    (hgen : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 ≤ Module.finrank (ZMod p) V := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hSHat : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hSHat.2.1
  have hy1 : y ≠ 1 := hSHat.2.2.1
  have hyK : K ≤ Subgroup.centralizer ({y} : Set G) := hSHat.2.2.2.1
  let v : V := ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))
  have hv : v ≠ 0 := by
    intro h0
    have h1 : (⟨y, hyBs⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      exact ι.injective (by simpa [v] using h0)
    exact hy1 (by simpa using congrArg Subtype.val h1)
  have hαv : ∀ i, α i v = 0 := by
    intro i
    have hmem : φ i ∈ ggAutomizer K Bs := by
      rw [hgen]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hfix : φ i ⟨y, hyBs⟩ = ⟨y, hyBs⟩ :=
      ggResI_automizer_fix hyBs hyK (φ i) hmem
    have hfixlin : ggLin (p := p) ι (φ i) v = v := by
      dsimp only [v]
      exact (ggLin_fix_iff (p := p) ι (φ i) ⟨y, hyBs⟩).mp hfix
    refine ggResI_alpha_eq_zero hp2 (hlin i) ?_ hfixlin
    rw [hpair i i, hdiag i]
    norm_num
  exact CFSG.StandardType.LevTwo.levTwoS4a_rank_core_add_one hpair hv hαv

theorem ggResJ_rootKernel_card {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G} {I : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : I → MulAut ↥Bs) (h : I → V)
    (α : I → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range φ))
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      ((b : G) ∈ Subgroup.centralizer (J : Set G))) :
    Nat.card (LinearMap.ker (LinearMap.pi α)) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
  classical
  let F : Submodule (ZMod p) V := LinearMap.ker (LinearMap.pi α)
  let K : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  let f : ↥K → ↥F := fun b =>
    ⟨ι (Additive.ofMul (⟨b.1, b.2.1⟩ : ↥Bs)), by
      rw [LinearMap.mem_ker]
      funext i
      have hJb : J ≤ Subgroup.centralizer ({b.1} : Set G) := by
        intro j hj
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ((Subgroup.mem_centralizer_iff.mp b.2.2) j hj).symm
      have hmem : φ i ∈ ggAutomizer J Bs := by
        rw [hgen]
        exact Subgroup.subset_closure ⟨i, rfl⟩
      have hfix := ggResI_automizer_fix b.2.1 hJb (φ i) hmem
      exact ggResI_alpha_eq_zero_of_refl ι (hlin i) (hrefl i)
        ((ggLin_fix_iff (p := p) ι (φ i) ⟨b.1, b.2.1⟩).mp hfix)⟩
  let g : ↥F → ↥K := fun v =>
    let b : ↥Bs := Additive.toMul (ι.symm (v : V))
    have hb : ι (Additive.ofMul b) = (v : V) := by simp [b]
    have hα : ∀ i, α i (ι (Additive.ofMul b)) = 0 := by
      intro i
      have hv0 : LinearMap.pi α (v : V) = 0 := LinearMap.mem_ker.mp v.2
      have hi := congrArg (fun f : I → ZMod p => f i) hv0
      simpa [hb] using hi
    have hfixgen : ∀ i, φ i b = b := by
      intro i
      exact (ggLin_fix_iff (p := p) ι (φ i) b).mpr (by
        rw [hlin i, hα i, zero_smul, sub_zero])
    have hfixall : ∀ a ∈ ggAutomizer J Bs, a b = b := by
      rw [hgen]
      exact ggFixed_of_mem_closure φ b hfixgen
    ⟨b, b.2, hfwd b hfixall⟩
  have hgf : ∀ v : ↥F, f (g v) = v := by
    intro v
    apply Subtype.ext
    show ι (Additive.ofMul (Additive.toMul (ι.symm (v : V)))) = (v : V)
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hfinj : Function.Injective f := by
    intro b₁ b₂ hb
    apply Subtype.ext
    have hv : (f b₁ : V) = (f b₂ : V) := congrArg Subtype.val hb
    have hb' : (⟨b₁.1, b₁.2.1⟩ : ↥Bs) = ⟨b₂.1, b₂.2.1⟩ :=
      Additive.ofMul.injective (ι.injective hv)
    exact congrArg (fun x : ↥Bs => (x : G)) hb'
  have hfg : ∀ b : ↥K, g (f b) = b := fun b => hfinj (hgf (f b))
  let e : ↥K ≃ ↥F :=
    { toFun := f
      invFun := g
      left_inv := hfg
      right_inv := hgf }
  simpa [F, K] using (Nat.card_congr e).symm

theorem ggResJ_rootKernel_finrank_le_three {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G} {I : Type} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (φ : I → MulAut ↥Bs) (h : I → V)
    (α : I → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range φ))
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      ((b : G) ∈ Subgroup.centralizer (J : Set G)))
    (hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    Module.finrank (ZMod p) (LinearMap.ker (LinearMap.pi α)) ≤ 3 := by
  let F : Submodule (ZMod p) V := LinearMap.ker (LinearMap.pi α)
  have hcardF : Nat.card ↥F ≤ p ^ 3 := by
    simpa [F] using
      (ggResJ_rootKernel_card ι φ h α hlin hrefl hgen hfwd).le.trans hcard
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hpow := FiniteField.pow_finrank_eq_natCard p ↥F
  have hle : p ^ Module.finrank (ZMod p) ↥F ≤ p ^ 3 := by
    rw [hpow]
    exact hcardF
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle

theorem ggGamma_card_ge_cartan_rank {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive Bs ≃+ V) (φ : Λ → MulAut Bs)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hPair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hmem : ∀ i, φ i ∈ ggAutomizer X Bs) :
    p ^ Matrix.rank (C.map (Int.castRingHom (ZMod p))) ≤ Nat.card (ggGamma X hN).range := by
  classical
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  haveI : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hA : IsElemAbelian p (ggGamma X hN).range :=
    isElemAbelian_range (fun a b => hBs.1.is_comm.comm a b)
      (fun b => Subtype.ext (hBs.2 b b.2)) (ggGamma X hN)
  obtain ⟨W, iW, iWmod, ⟨ξ⟩⟩ := exists_ggLinData hA
  haveI : Finite W := Finite.of_equiv (Additive (ggGamma X hN).range) ξ.toEquiv
  haveI : Module.Finite (ZMod p) W := Module.Finite.of_finite
  let q : V →ₗ[ZMod p] W :=
    (ξ.toAddMonoidHom.comp ((ggGamma X hN).rangeRestrict.toAdditive.comp
      ι.symm.toAddMonoidHom)).toZModLinearMap p
  have hq (b : Bs) : q (ι (Additive.ofMul b)) =
      ξ (Additive.ofMul ((ggGamma X hN).rangeRestrict b)) := by
    simp [q]
  have hqs : Function.Surjective q := by
    intro w
    obtain ⟨a, rfl⟩ := ξ.surjective w
    obtain ⟨b, hb⟩ := (ggGamma X hN).rangeRestrict_surjective a.toMul
    refine ⟨ι (Additive.ofMul b), ?_⟩
    rw [hq, hb]
    rfl
  have hker : ∀ i, ∀ v ∈ q.ker, α i v = 0 := by
    intro i v hv
    obtain ⟨b, rfl⟩ := ι.surjective v
    have hz : ξ (Additive.ofMul ((ggGamma X hN).rangeRestrict b.toMul)) = 0 := by
      rw [← hq]
      exact LinearMap.mem_ker.mp hv
    have hz' : Additive.ofMul ((ggGamma X hN).rangeRestrict b.toMul) = 0 :=
      ξ.injective (by simpa using hz)
    have hgam : ggGamma X hN b.toMul = 1 :=
      congrArg (fun a : Additive (ggGamma X hN).range => (a.toMul : MulAut X)) hz'
    have hbC : (b.toMul : G) ∈ Subgroup.centralizer (X : Set G) :=
      (ggGamma_eq_one_iff X hN b.toMul).mp hgam
    obtain ⟨g, hgX, hgN, hφg⟩ := mem_ggAutomizer_iff.mp (hmem i)
    have hfix : φ i b.toMul = b.toMul := by
      apply Subtype.ext
      rw [hφg b.toMul, Subgroup.mem_centralizer_iff.mp hbC g hgX]
      group
    have hfixV : ggLin (p := p) ι (φ i) (ι b) = ι b := by
      rw [ggLin_apply, ι.symm_apply_apply, hfix]
      rfl
    rw [hlin] at hfixV
    have hh : h i ≠ 0 := by
      intro hh
      have hdiag : α i (h i) = 2 := by rw [hPair, hC.1 i]; norm_num
      rw [hh, map_zero] at hdiag
      exact h2 hdiag.symm
    exact (smul_eq_zero.mp (sub_eq_self.mp hfixV)).resolve_right hh
  have hbound := LevTwo.levTwoS4a_rank_core_add hPair hker
  have hdim := LinearMap.finrank_range_add_finrank_ker q
  rw [LinearMap.range_eq_top.mpr hqs, finrank_top] at hdim
  have hrank : Matrix.rank (C.map (Int.castRingHom (ZMod p))) ≤
      Module.finrank (ZMod p) W := by omega
  have hcard : p ^ Module.finrank (ZMod p) W = Nat.card (ggGamma X hN).range := by
    rw [FiniteField.pow_finrank_eq_natCard]
    exact (card_eq_of_ggLin ξ).symm
  rw [← hcard]
  exact Nat.pow_le_pow_right hp.pos hrank

private theorem card_ge_pow_three_of_perm_four {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {H : Type} [Group H] {A : Subgroup H} [Finite A] (hA : IsElemAbelian p A)
    (ρ : Equiv.Perm (Fin 4) →* MulAut A) (hρ : Function.Injective ρ) :
    p ^ 3 ≤ Nat.card A := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨V, iV, iM, ⟨ι⟩⟩ := exists_ggLinData hA
  haveI : Finite V := Finite.of_equiv (Additive A) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let τ := (ggLin (p := p) ι).comp ρ
  have hτ : Function.Injective τ := (ggLin_injective ι).comp hρ
  have hV : Nontrivial V := by
    by_contra hn
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    have heq : τ (Equiv.swap (0 : Fin 4) 1) = τ 1 :=
      LinearEquiv.ext fun _ => Subsingleton.elim _ _
    have h01 := congrArg (fun σ : Equiv.Perm (Fin 4) => σ 0) (hτ heq)
    norm_num at h01
  have hpos : 0 < Module.finrank (ZMod p) V := Module.finrank_pos_iff.mpr hV
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  have hdim : 3 ≤ Module.finrank (ZMod p) V := by
    by_contra hbad
    exact CFSG.RankThree.PartOne.Sec1511.false_of_injective_perm_four h2
      (by omega) τ hτ
  have hcard : p ^ Module.finrank (ZMod p) V = Nat.card A := by
    rw [FiniteField.pow_finrank_eq_natCard]
    exact (card_eq_of_ggLin ι).symm
  rw [← hcard]
  exact Nat.pow_le_pow_right hp.pos hdim

theorem GGResXDatumA.card_gamma_ge_rank_sub_one {G : Type} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hD : GGResXDatumA p Bs X n) :
    p ^ (n - 1) ≤ Nat.card (ggGamma X hN).range := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM,
    hW, hC, hlin, hRef, hPair, ⟨f, hf⟩, hgen⟩ := hD
  have hmem : ∀ i, φ i ∈ ggAutomizer X Bs := fun i => hf i ▸ (f (M.simple i)).2
  have hcard := ggGamma_card_ge_cartan_rank hp2 hBs hN hC ι φ h α hlin hPair hmem
  have hrank := ggIntCartan_card_le_rank_add_one hW hC p hp2
  have hnodes : Fintype.card Λ = n := by simpa using (Fintype.card_congr e).symm
  rw [hnodes] at hrank
  exact (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega : n - 1 ≤
    Matrix.rank (C.map (Int.castRingHom (ZMod p))))).trans hcard

theorem GGResXDatumA.card_gamma_ge_pow_three {G : Type} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hD : GGResXDatumA p Bs X n)
    (hn : 3 ≤ n) : p ^ 3 ≤ Nat.card (ggGamma X hN).range := by
  by_cases h3 : n = 3
  · subst n
    obtain ⟨e⟩ := hD.mulEquiv_perm
    let ρ : Equiv.Perm (Fin 4) →* MulAut (ggGamma X hN).range :=
      ((ggAutomizer (MulAut.conj : X →* MulAut X).range
        (ggGamma X hN).range).subtype.comp (ggAutomizerGammaHom hN)).comp e.symm.toMonoidHom
    have hρ : Function.Injective ρ := by
      intro a b hab
      apply e.symm.injective
      apply hD.gamma_injective hp2 hBs hN (by omega)
      exact Subtype.ext hab
    have hA : IsElemAbelian p (ggGamma X hN).range :=
      isElemAbelian_range (fun a b => hBs.1.is_comm.comm a b)
        (fun b => Subtype.ext (hBs.2 b b.2)) (ggGamma X hN)
    exact card_ge_pow_three_of_perm_four hp2 hA ρ hρ
  · exact (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega : 3 ≤ n - 1)).trans
      (GGResXDatumA.card_gamma_ge_rank_sub_one hp2 hBs hN hD)

theorem ggRes_exactThree_singular_chart_of_axis_bound {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (haxis : Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 ≤
      Module.finrank (ZMod p) V)
    (S : Finset Λ) (hS : S.card = 3)
    (hgen : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun i : {i : Λ // i ∉ S} => φ i.1))
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G)) :
    Module.finrank (ZMod p) V = Fintype.card Λ ∧
      Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 = Fintype.card Λ ∧
      Module.finrank (ZMod p)
        (LinearMap.ker (LinearMap.pi fun i : {i : Λ // i ∉ S} => α i.1)) = 3 ∧
      ((GGIsTypeA M ∧ p ∣ Fintype.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 M)) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧ B < Bs := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hker := ggResJ_rootKernel_finrank_le_three ι
    (fun i : {i : Λ // i ∉ S} => φ i.1) (fun i => h i.1) (fun i => α i.1)
    (fun i => hlin i.1) (fun i => hrefl i.1) hgen hfwd
    hcfg.card_bstar_inf_centralizer_J_le
  obtain ⟨hdim, hrank, hker3⟩ := LevTwo.levTwoS4a_exactThree_rank_squeeze_of_axis_bound
    haxis S hS (ggIntCartan_card_le_rank_add_one hM hC p hp2) hker
  have htype := ggRC_singular_typeA_or_E6_of_rank (Fact.out : p.Prime) hp2 hM hC hrank
  have hcard := ggResJ_rootKernel_card ι
    (fun i : {i : Λ // i ∉ S} => φ i.1) (fun i => h i.1) (fun i => α i.1)
    (fun i => hlin i.1) (fun i => hrefl i.1) hgen hfwd
  have hpow := FiniteField.pow_finrank_eq_natCard p
    (LinearMap.ker (LinearMap.pi fun i : {i : Λ // i ∉ S} => α i.1))
  rw [hker3, hcard] at hpow
  have hlt : B < Bs := hcfg.B_lt_Bs_of_centralizer_J_card (by
    rw [← hpow]
    exact (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mpr (by omega))
  exact ⟨hdim, hrank, hker3, htype, hpow.symm, hlt⟩

theorem ggRes_exactThree_singular_chart {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {v : V} (hv : v ≠ 0) (hvα : ∀ i, α i v = 0)
    (S : Finset Λ) (hS : S.card = 3)
    (hgen : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun i : {i : Λ // i ∉ S} => φ i.1))
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G)) :
    Module.finrank (ZMod p) V = Fintype.card Λ ∧
      Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 = Fintype.card Λ ∧
      Module.finrank (ZMod p)
        (LinearMap.ker (LinearMap.pi fun i : {i : Λ // i ∉ S} => α i.1)) = 3 ∧
      ((GGIsTypeA M ∧ p ∣ Fintype.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 M)) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧ B < Bs := by
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  exact ggRes_exactThree_singular_chart_of_axis_bound hcfg ι φ h α hM hC hlin hrefl hpair
    (LevTwo.levTwoS4a_rank_core_add_one hpair hv hvα) S hS hgen hfwd

theorem ggResLeviExact3_automizerJ_eq_bot_of_card_le_four
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X Y : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hp5 : p ≠ 5) (hcard : Nat.card Bs ≤ p ^ 4)
    (hD : GGResLeviDatumExact3 p Bs X J Y ggSelAny ggTypAny) :
    ggAutomizer J Bs = ⊥ := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    hfL, hfK, hgenL, hgenK, hconn, hgenJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  haveI : Finite V := Finite.of_equiv _ ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hpow : p ^ Module.finrank (ZMod p) V ≤ p ^ 4 := by
    rw [FiniteField.pow_finrank_eq_natCard p V, ← card_eq_of_ggLin ι]
    exact hcard
  have hdim : Module.finrank (ZMod p) V ≤ 4 := by
    by_contra hn
    have hlt : p ^ 4 < p ^ Module.finrank (ZMod p) V :=
      Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  have haxis : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) + 1 ≤
      Module.finrank (ZMod p) V := by
    rcases hX with rfl | rfl
    · exact ggResL_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w)
        hpair hCL.1 hgenL
    · exact ggResK_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w)
        hpair hCL.1 hgenL
  have hn : Fintype.card Λ ≤ 3 := by
    by_contra hnot
    have hlow := ggIntCartan_four_le_rank hML hCL hp2 hp5 (by omega)
    omega
  have hfull : ∀ i : Λ, i ∈ S := by
    have hle : S.card ≤ Fintype.card Λ := Finset.card_le_univ S
    have heq : S = Finset.univ := Finset.eq_univ_of_card S (by omega)
    simp [heq]
  haveI : IsEmpty {i : Λ // i ∉ S} := ⟨fun i => i.2 (hfull i.1)⟩
  simpa only [Set.range_eq_empty, Subgroup.closure_empty] using hgenJ

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}

theorem ggResK_exactThree_added_three_or_two_singular_of_tbFix (hTBF : GGTBFixInput)
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (hS : S.card = 3) (ha3 : Nat.card Λa ≤ 3)
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hpair : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (C i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hgenL : ggAutomizer L Bs = Subgroup.closure
      (Set.range fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id))) :
    Nat.card Λa = 3 ∨
      (Nat.card Λa = 2 ∧
        Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 = Fintype.card Λ ∧
        Module.finrank (ZMod p) V = Fintype.card Λ ∧
        ((GGIsTypeA M ∧ p ∣ Fintype.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 M))) := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hlower := ggResK_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w)
    hpair hC.1 hgenK
  have hupper : Module.finrank (ZMod p) V ≤
      Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) + 1 := by
    obtain ⟨_, hBs, hxB, _, _⟩ := hH.1.tableB_facts
    apply ggFinrank_le_of_fix_le (hBs.2 x hxB) ι
      (fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id))
      (fun o => h (o.map Subtype.val id)) (fun o => α (o.map Subtype.val id))
      (fun o w => hlin (o.map Subtype.val id) w)
    intro b hb
    exact hTBF G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1
      y K hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 b (by
        rw [hgenL]
        exact ggFixed_of_mem_closure _ b hb)
  have hsub : Fintype.card {i : Λ // i ∈ S} = 3 := by
    rw [Fintype.card_subtype]
    simpa using hS
  rw [Fintype.card_sum, Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub] at hupper
  have hadded : Fintype.card Λa = Nat.card Λa := Nat.card_eq_fintype_card.symm
  rw [hadded] at hupper
  have hnodes := ggIntCartan_card_le_rank_add_one hM hC p hp2
  have hthree : 3 ≤ Fintype.card Λ := by
    simpa [hS] using S.card_le_univ
  by_cases ha : Nat.card Λa = 3
  · exact Or.inl ha
  · have ha2 : Nat.card Λa = 2 := by omega
    have hrank : Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 =
        Fintype.card Λ := by omega
    have hdim : Module.finrank (ZMod p) V = Fintype.card Λ := by omega
    exact Or.inr ⟨ha2, hrank, hdim,
      ggRC_singular_typeA_or_E6_of_rank (Fact.out : p.Prime) hp2 hM hC hrank⟩

end CFSG.StandardType

end

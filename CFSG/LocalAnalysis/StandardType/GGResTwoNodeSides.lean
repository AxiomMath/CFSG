module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import TauCeti.Combinatorics.SimpleGraph.BranchComponents

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nTn_refl_conj {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
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

private theorem l05nTn_lin_conj {p : ℕ} [Fact p.Prime] {E : Type} [Group E] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) (u φ : MulAut E)
    {g : Module.Dual (ZMod p) V} {z : V}
    (hφ : ∀ v, ggLin (p := p) ι φ v = v - g v • z) (v : V) :
    ggLin (p := p) ι (u * φ * u⁻¹) v =
      v - g ((ggLin (p := p) ι u).symm v) • ggLin (p := p) ι u z := by
  rw [map_mul, map_mul, map_inv]
  show ggLin (p := p) ι u (ggLin (p := p) ι φ ((ggLin (p := p) ι u).symm v)) = _
  rw [hφ, map_sub, map_smul, LinearEquiv.apply_symm_apply]

private theorem l05nTn_closure_conj {E : Type} [Group E] (S : Subgroup E) (u : E) (hu : u ∈ S) :
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

private theorem l05nTn_rankOne {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
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

private theorem l05nTn_cartan_eq_zero_iff {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
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

private theorem l05nTn_weylFixed {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M) :
    GGIsWeylMatrixFixed M := h

private theorem l05nTn_nonempty {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M) :
    Nonempty ι := by
  rcases h with ⟨n, e, hn, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact ⟨e ⟨0, by omega⟩⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩

private theorem l05nTn_graph_adj {Λ : Type} [Fintype Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hWM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (i j : Λ) :
    (TauCeti.diagramGraph C).Adj i j ↔ i ≠ j ∧ M.M i j ≠ 2 := by
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (l05nTn_weylFixed hWM) hC
  rw [TauCeti.IsFiniteType.diagramGraph_adj_iff hFT]
  constructor
  · rintro ⟨hij, hCij⟩
    exact ⟨hij, fun hM => hCij ((l05nTn_cartan_eq_zero_iff hC hij).2 hM)⟩
  · rintro ⟨hij, hMij⟩
    exact ⟨hij, fun h0 => hMij ((l05nTn_cartan_eq_zero_iff hC hij).1 h0)⟩

private theorem l05nTn_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b)
    {a b : α} (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

private theorem l05nTn_reindex_trans {ι κ ν : Type} (M : CoxeterMatrix ι) (e : ι ≃ κ)
    (f : κ ≃ ν) : (M.reindex e).reindex f = M.reindex (e.trans f) := by
  apply CoxeterMatrix.ext
  funext x y
  simp only [CoxeterMatrix.reindex_apply, Equiv.trans_apply, Equiv.symm_trans_apply]

private theorem l05nTn_weyl_reindex {ι κ : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M)
    (f : ι ≃ κ) : GGIsWeylMatrix (M.reindex f) := by
  rcases h with ⟨n, e, hn, h | ⟨hn, h⟩ | ⟨hn, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩
  · exact Or.inl ⟨n, e.trans f, hn, Or.inl (by rw [h, l05nTn_reindex_trans])⟩
  · exact Or.inl ⟨n, e.trans f, by omega, Or.inr (Or.inl ⟨hn, by rw [h, l05nTn_reindex_trans]⟩)⟩
  · exact Or.inl ⟨n, e.trans f, by omega,
      Or.inr (Or.inr ⟨hn, by rw [h, l05nTn_reindex_trans]⟩)⟩
  · exact Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nTn_reindex_trans]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nTn_reindex_trans]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nTn_reindex_trans]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f,
      by rw [h, l05nTn_reindex_trans]⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans f,
      by rw [h, l05nTn_reindex_trans]⟩))))

private def l05nTn_SideSum {G : Type} [Group G] [Finite G] (k : ℕ) (p : ℕ) [Fact p.Prime]
    (Bs X J : Subgroup G) : Prop :=
  ∃ (Λj : Type) (_ : Fintype Λj) (_ : DecidableEq Λj) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (M : CoxeterMatrix (Λj ⊕ Λa)) (C : Matrix (Λj ⊕ Λa) (Λj ⊕ Λa) ℤ)
    (MJ : CoxeterMatrix Λj) (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
    (ι : Additive ↥Bs ≃+ V) (φ : Λj ⊕ Λa → MulAut ↥Bs) (h : Λj ⊕ Λa → V)
    (α : Λj ⊕ Λa → Module.Dual (ZMod p) V),
    1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 2 ∧ Nat.card Λa = k ∧ GGIsWeylMatrix M ∧
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

private theorem l05nTA_intCartan_reindex {Γ Δ : Type} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (h : GGIntCartan M C) (e : Δ ≃ Γ) :
    GGIntCartan (M.reindex e.symm) (fun o o' => C (e o) (e o')) := by
  constructor
  · intro o
    simpa using h.1 (e o)
  · intro o o' hne
    have hene : e o ≠ e o' := fun hh => hne (e.injective hh)
    have hh := h.2 (e o) (e o') hene
    simpa only [CoxeterMatrix.reindex_apply, Equiv.symm_symm] using hh

private theorem l05nTA_reindex {G : Type} [Group G] [Finite G] (k : ℕ) {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {Λj : Type} [Fintype Λj] [DecidableEq Λj] {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (e : Λj ⊕ Λa ≃ Λ) {MJ : CoxeterMatrix Λj} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hcard1 : 1 ≤ Nat.card Λa) (hcard2 : Nat.card Λa ≤ 2)
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
    l05nTn_SideSum k p Bs X J := by
  refine ⟨Λj, inferInstance, inferInstance, Λa, inferInstance, inferInstance,
    M.reindex e.symm, (fun o o' => C (e o) (e o')), MJ, V, inferInstance, inferInstance,
    ι, φ ∘ e, h ∘ e, α ∘ e, hcard1, hcard2, hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact l05nTn_weyl_reindex hWM e.symm
  · exact l05nTA_intCartan_reindex hC e
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

private theorem l05nTn_sum_of_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (h : GGResSideDatum p Bs X J) : l05nTn_SideSum 1 p Bs X J := by
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
  exact l05nTA_reindex 1 (p := p) (X := X) (J := J) e ι φ hc α (by simp) (by simp) (by simp)
    hWM hC hWMJ (fun j j' => hMJ j j') hlin hrefl hpair f hf hclos fJ hfJ hclosJ hconj

private theorem l05nTn_sum_of_two {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (h : GGResTwoNodeSideDatum p Bs X J) : l05nTn_SideSum 2 p Bs X J := by
  obtain ⟨Λ, i1, i2, b₁, b₂, M, C, MJ, V, i3, i4, ι, φ, hc, α, hb, hWM, hC, hWMJ, hMJ, hlin,
    hrefl, hpair, hf, hclos, hfJ, hclosJ, hconj⟩ := h
  letI := i1; letI := i2; letI := i3; letI := i4
  obtain ⟨f, hf⟩ := hf
  obtain ⟨fJ, hfJ⟩ := hfJ
  let e : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Bool ≃ Λ :=
    { toFun := fun o => match o with
        | Sum.inl j => (j : Λ)
        | Sum.inr false => b₁
        | Sum.inr true => b₂
      invFun := fun i => if h₁ : i = b₁ then Sum.inr false
        else if h₂ : i = b₂ then Sum.inr true
        else Sum.inl ⟨i, h₁, h₂⟩
      left_inv := by
        intro o
        cases o with
        | inl j => simp [dif_neg j.2.1, dif_neg j.2.2]
        | inr b =>
          cases b with
          | false => simp
          | true => simp [dif_neg hb.symm]
      right_inv := by
        intro i
        by_cases h₁ : i = b₁
        · simp only [dif_pos h₁]
          exact h₁.symm
        · by_cases h₂ : i = b₂
          · simp only [dif_neg h₁, dif_pos h₂]
            exact h₂.symm
          · simp only [dif_neg h₁, dif_neg h₂] }
  exact l05nTA_reindex 2 (p := p) (X := X) (J := J) e ι φ hc α (by simp) (by simp) (by simp)
    hWM hC hWMJ (fun j j' => hMJ j j') hlin hrefl hpair f hf hclos fJ hfJ hclosJ hconj

private theorem l05nTB_isTree {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C) :
    (TauCeti.diagramGraph C).IsTree := by
  classical
  have hadj := l05nTn_graph_adj (M := M) (C := C) hW hC
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (l05nTn_weylFixed hW) hC
  have hpre : (TauCeti.diagramGraph C).Preconnected := by
    intro i j
    rw [SimpleGraph.reachable_iff_reflTransGen]
    exact l05nTn_rtg_mono (fun u v huv => (hadj u v).2 huv) (ggRC_weyl_connected hW i j)
  have hconn : (TauCeti.diagramGraph C).Connected :=
    (SimpleGraph.connected_iff _).2 ⟨hpre, l05nTn_nonempty hW⟩
  exact TauCeti.IsFiniteType.isTree_diagramGraph hFT hconn

private theorem l05nTB_rtg_map {α β : Type} {r : α → α → Prop} {p : β → β → Prop}
    (f : α → β) (h : ∀ a b, r a b → p (f a) (f b)) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p (f a) (f b) := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

private theorem l05nTB_reach_J {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C) (a : Λa) {i j : Jn}
    (h : Relation.ReflTransGen (fun u v : Jn => u ≠ v ∧ M.M (Sum.inl u) (Sum.inl v) ≠ 2) i j) :
    ((TauCeti.diagramGraph C).induce ({Sum.inr a}ᶜ : Set (Jn ⊕ Λa))).Reachable
      ⟨Sum.inl i, by simp⟩ ⟨Sum.inl j, by simp⟩ := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  refine l05nTB_rtg_map
    (fun u : Jn => (⟨Sum.inl u, by simp⟩ :
      {x : Jn ⊕ Λa // x ∈ ({Sum.inr a}ᶜ : Set (Jn ⊕ Λa))})) ?_ h
  intro u v huv
  rw [SimpleGraph.induce_adj]
  exact (l05nTn_graph_adj (M := M) (C := C) hW hC (Sum.inl u) (Sum.inl v)).2
    ⟨fun h => huv.1 (Sum.inl.inj h), huv.2⟩

private theorem l05nTB_J_unique {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hJ : ∀ i j : Jn, Relation.ReflTransGen
      (fun u v : Jn => u ≠ v ∧ M.M (Sum.inl u) (Sum.inl v) ≠ 2) i j)
    (a : Λa) (j j' : Jn) (hj : M.M (Sum.inr a) (Sum.inl j) ≠ 2)
    (hj' : M.M (Sum.inr a) (Sum.inl j') ≠ 2) : j = j' := by
  classical
  have htree := l05nTB_isTree (M := M) (C := C) hW hC
  have hadj := l05nTn_graph_adj (M := M) (C := C) hW hC
  have hnb1 : (TauCeti.diagramGraph C).Adj (Sum.inr a) (Sum.inl j) :=
    (hadj _ _).2 ⟨Sum.inr_ne_inl, hj⟩
  have hnb2 : (TauCeti.diagramGraph C).Adj (Sum.inr a) (Sum.inl j') :=
    (hadj _ _).2 ⟨Sum.inr_ne_inl, hj'⟩
  let x : ↥((TauCeti.diagramGraph C).neighborSet (Sum.inr a)) :=
    ⟨Sum.inl j, (SimpleGraph.mem_neighborSet _ _ _).2 hnb1⟩
  let y : ↥((TauCeti.diagramGraph C).neighborSet (Sum.inr a)) :=
    ⟨Sum.inl j', (SimpleGraph.mem_neighborSet _ _ _).2 hnb2⟩
  have heq : (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree (Sum.inr a)) x =
      (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree (Sum.inr a)) y := by
    rw [TauCeti.IsTree.neighborSetEquivConnectedComponentCompl_apply,
      TauCeti.IsTree.neighborSetEquivConnectedComponentCompl_apply]
    exact SimpleGraph.ConnectedComponent.sound
      (l05nTB_reach_J (M := M) (C := C) hW hC a (hJ j j'))
  have hval : (x : Jn ⊕ Λa) = (y : Jn ⊕ Λa) :=
    congrArg Subtype.val ((TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree
      (Sum.inr a)).injective heq)
  exact Sum.inl.inj hval

private theorem l05nTB_not_both {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn] [Fintype Λa]
    [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)} {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hJ : ∀ i j : Jn, Relation.ReflTransGen
      (fun u v : Jn => u ≠ v ∧ M.M (Sum.inl u) (Sum.inl v) ≠ 2) i j)
    (a a' : Λa) (j j' : Jn) (haa' : a ≠ a')
    (hadd : M.M (Sum.inr a) (Sum.inr a') ≠ 2)
    (hj : M.M (Sum.inr a) (Sum.inl j) ≠ 2)
    (hj' : M.M (Sum.inr a') (Sum.inl j') ≠ 2) : False := by
  classical
  have htree := l05nTB_isTree (M := M) (C := C) hW hC
  have hadj := l05nTn_graph_adj (M := M) (C := C) hW hC
  have hnb1 : (TauCeti.diagramGraph C).Adj (Sum.inr a) (Sum.inr a') :=
    (hadj _ _).2 ⟨fun h => haa' (Sum.inr.inj h), hadd⟩
  have hnb2 : (TauCeti.diagramGraph C).Adj (Sum.inr a) (Sum.inl j) :=
    (hadj _ _).2 ⟨Sum.inr_ne_inl, hj⟩
  have hedge : ((TauCeti.diagramGraph C).induce ({Sum.inr a}ᶜ : Set (Jn ⊕ Λa))).Adj
      ⟨Sum.inr a', by simpa using haa'.symm⟩ ⟨Sum.inl j', by simp⟩ := by
    rw [SimpleGraph.induce_adj]
    exact (hadj _ _).2 ⟨Sum.inr_ne_inl, hj'⟩
  have hreach : ((TauCeti.diagramGraph C).induce ({Sum.inr a}ᶜ : Set (Jn ⊕ Λa))).Reachable
      ⟨Sum.inr a', by simpa using haa'.symm⟩ ⟨Sum.inl j, by simp⟩ := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    refine Relation.ReflTransGen.head hedge ?_
    rw [← SimpleGraph.reachable_iff_reflTransGen]
    exact l05nTB_reach_J (M := M) (C := C) hW hC a (hJ j' j)
  let x : ↥((TauCeti.diagramGraph C).neighborSet (Sum.inr a)) :=
    ⟨Sum.inr a', (SimpleGraph.mem_neighborSet _ _ _).2 hnb1⟩
  let y : ↥((TauCeti.diagramGraph C).neighborSet (Sum.inr a)) :=
    ⟨Sum.inl j, (SimpleGraph.mem_neighborSet _ _ _).2 hnb2⟩
  have heq : (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree (Sum.inr a)) x =
      (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree (Sum.inr a)) y := by
    rw [TauCeti.IsTree.neighborSetEquivConnectedComponentCompl_apply,
      TauCeti.IsTree.neighborSetEquivConnectedComponentCompl_apply]
    exact SimpleGraph.ConnectedComponent.sound hreach
  have hval : (x : Jn ⊕ Λa) = (y : Jn ⊕ Λa) :=
    congrArg Subtype.val ((TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree
      (Sum.inr a)).injective heq)
  exact Sum.inr_ne_inl hval

private theorem l05nTB_three {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (hcard : Nat.card Λa ≤ 2) (a b c : Λa) : a = b ∨ a = c ∨ b = c := by
  by_contra h
  have hab : a ≠ b := fun h' => h (Or.inl h')
  have hac : a ≠ c := fun h' => h (Or.inr (Or.inl h'))
  have hbc : b ≠ c := fun h' => h (Or.inr (Or.inr h'))
  have hc3 : ({a, b, c} : Finset Λa).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have hle := Finset.card_le_univ ({a, b, c} : Finset Λa)
  rw [hc3] at hle
  have hcard' : Nat.card Λa = Fintype.card Λa := Nat.card_eq_fintype_card
  omega

private theorem l05nTn_mu {U : Type} [Group U] {Jn Λa : Type} [Fintype Jn] [DecidableEq Jn]
    [Fintype Λa] [DecidableEq Λa] {M : CoxeterMatrix (Jn ⊕ Λa)}
    {C : Matrix (Jn ⊕ Λa) (Jn ⊕ Λa) ℤ} (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hJ : ∀ i j : Jn,
      Relation.ReflTransGen (fun u v : Jn => u ≠ v ∧ M.M (Sum.inl u) (Sum.inl v) ≠ 2) i j)
    (hcard : Nat.card Λa ≤ 2) (c : Jn → U) :
    ∃ μ : Λa → U, (∀ a j, M.M (Sum.inr a) (Sum.inl j) ≠ 2 → μ a = (c j)⁻¹) ∧
      ∀ a a', a ≠ a' → M.M (Sum.inr a) (Sum.inr a') ≠ 2 → μ a = μ a' := by
  classical
  have huniq := l05nTB_J_unique (M := M) (C := C) hW hC hJ
  have hboth := l05nTB_not_both (M := M) (C := C) hW hC hJ
  have hthree := l05nTB_three (Λa := Λa) hcard
  let P : Λa → Prop := fun a => ∃ j : Jn, M.M (Sum.inr a) (Sum.inl j) ≠ 2
  let mu : Λa → U := fun a =>
    if h : P a then (c (Classical.choose h))⁻¹
    else if h' : ∃ p : Λa × Jn, p.1 ≠ a ∧ M.M (Sum.inr a) (Sum.inr p.1) ≠ 2 ∧
        M.M (Sum.inr p.1) (Sum.inl p.2) ≠ 2 then
      (c (Classical.choose h').2)⁻¹
    else 1
  refine ⟨mu, ?_, ?_⟩
  · intro a j hj
    have hP : P a := ⟨j, hj⟩
    have hmu : mu a = (c (Classical.choose hP))⁻¹ := by
      dsimp only [mu]
      exact dif_pos hP
    rw [hmu, huniq a (Classical.choose hP) j (Classical.choose_spec hP) hj]
  · intro a a' haa' hadd
    by_cases hpa : P a
    · by_cases hpa' : P a'
      · exact absurd (hboth a a' (Classical.choose hpa) (Classical.choose hpa') haa' hadd
          (Classical.choose_spec hpa) (Classical.choose_spec hpa')) (by simp)
      · have hval_a : mu a = (c (Classical.choose hpa))⁻¹ := by
          dsimp only [mu]
          exact dif_pos hpa
        have hex : ∃ p : Λa × Jn, p.1 ≠ a' ∧ M.M (Sum.inr a') (Sum.inr p.1) ≠ 2 ∧
            M.M (Sum.inr p.1) (Sum.inl p.2) ≠ 2 :=
          ⟨(a, Classical.choose hpa), haa', by rwa [M.symmetric], Classical.choose_spec hpa⟩
        have hval_a' : mu a' = (c (Classical.choose hex).2)⁻¹ := by
          dsimp only [mu]
          rw [dif_neg hpa', dif_pos hex]
        have hbne : (Classical.choose hex).1 ≠ a' := (Classical.choose_spec hex).1
        have hb_eq : (Classical.choose hex).1 = a := by
          rcases hthree (Classical.choose hex).1 a a' with h | h | h
          · exact h
          · exact absurd h hbne
          · exact absurd h haa'
        have hbsj : M.M (Sum.inr (Classical.choose hex).1)
            (Sum.inl (Classical.choose hex).2) ≠ 2 := (Classical.choose_spec hex).2.2
        rw [hb_eq] at hbsj
        have hch : (Classical.choose hex).2 = Classical.choose hpa :=
          huniq a _ _ hbsj (Classical.choose_spec hpa)
        rw [hval_a, hval_a', hch]
    · by_cases hpa' : P a'
      · have hval_a' : mu a' = (c (Classical.choose hpa'))⁻¹ := by
          dsimp only [mu]
          exact dif_pos hpa'
        have hex : ∃ p : Λa × Jn, p.1 ≠ a ∧ M.M (Sum.inr a) (Sum.inr p.1) ≠ 2 ∧
            M.M (Sum.inr p.1) (Sum.inl p.2) ≠ 2 :=
          ⟨(a', Classical.choose hpa'), haa'.symm, hadd, Classical.choose_spec hpa'⟩
        have hval_a : mu a = (c (Classical.choose hex).2)⁻¹ := by
          dsimp only [mu]
          rw [dif_neg hpa, dif_pos hex]
        have hbne : (Classical.choose hex).1 ≠ a := (Classical.choose_spec hex).1
        have hb_eq : (Classical.choose hex).1 = a' := by
          rcases hthree (Classical.choose hex).1 a' a with h | h | h
          · exact h
          · exact absurd h hbne
          · exact absurd h (Ne.symm haa')
        have hbsj : M.M (Sum.inr (Classical.choose hex).1)
            (Sum.inl (Classical.choose hex).2) ≠ 2 := (Classical.choose_spec hex).2.2
        rw [hb_eq] at hbsj
        have hch : (Classical.choose hex).2 = Classical.choose hpa' :=
          huniq a' _ _ hbsj (Classical.choose_spec hpa')
        rw [hval_a, hval_a', hch]
      · have hno : ¬(∃ p : Λa × Jn, p.1 ≠ a ∧ M.M (Sum.inr a) (Sum.inr p.1) ≠ 2 ∧
            M.M (Sum.inr p.1) (Sum.inl p.2) ≠ 2) := by
          rintro ⟨⟨b, jj⟩, hbne, -, hj⟩
          rcases hthree b a a' with h | h | h
          · exact hbne h
          · exact hpa' (h ▸ ⟨jj, hj⟩)
          · exact haa' h
        have hno' : ¬(∃ p : Λa × Jn, p.1 ≠ a' ∧ M.M (Sum.inr a') (Sum.inr p.1) ≠ 2 ∧
            M.M (Sum.inr p.1) (Sum.inl p.2) ≠ 2) := by
          rintro ⟨⟨b, jj⟩, hbne, -, hj⟩
          rcases hthree b a' a with h | h | h
          · exact hbne h
          · exact hpa (h ▸ ⟨jj, hj⟩)
          · exact absurd h (Ne.symm haa')
        have hval_a : mu a = 1 := by
          dsimp only [mu]
          rw [dif_neg hpa, dif_neg hno]
        have hval_a' : mu a' = 1 := by
          dsimp only [mu]
          rw [dif_neg hpa', dif_neg hno']
        rw [hval_a, hval_a']

private structure l05nTn_Al {G : Type} [Group G] [Finite G] (k : ℕ) (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) where
  Λ : Type
  fin : Fintype Λ
  dec : DecidableEq Λ
  b₁ : Λ
  b₂ : Λ
  hb : b₁ ≠ b₂
  ML : CoxeterMatrix Λ
  CL : Matrix Λ Λ ℤ
  MJL : CoxeterMatrix {i : Λ // i ≠ b₁ ∧ i ≠ b₂}
  V : Type
  [acg : AddCommGroup V]
  [mod : Module (ZMod p) V]
  ι : Additive ↥Bs ≃+ V
  φL : Λ → MulAut ↥Bs
  hL : Λ → V
  αL : Λ → Module.Dual (ZMod p) V
  Λa : Type
  fina : Fintype Λa
  deca : DecidableEq Λa
  hΛa : 1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 2
  hk : Nat.card Λa = k
  MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)
  CK0 : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ
  φK : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa → MulAut ↥Bs
  hK : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa → V
  αK : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa → Module.Dual (ZMod p) V
  cc : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} → (ZMod p)ˣ
  fL : ML.Group ≃* ↥(ggAutomizer L Bs)
  fK : MK.Group ≃* ↥(ggAutomizer K Bs)
  hWML : GGIsWeylMatrix ML
  hCLL : GGIntCartan ML CL
  hWMJL : GGIsWeylMatrix MJL
  hMJL : ∀ j j' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, MJL.M j j' = ML.M j.1 j'.1
  hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i
  hreflL : ∀ i, GGIsReflection p (φL i)
  hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p)
  hfL : ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φL i
  hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL)
  hclosJL : ggAutomizer J Bs =
    Subgroup.closure (Set.range fun j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} => φL j.1)
  hWMK : GGIsWeylMatrix MK
  hCKK : GGIntCartan MK CK0
  hlinK : ∀ o w, ggLin (p := p) ι (φK o) w = w - αK o w • hK o
  hreflK : ∀ o, GGIsReflection p (φK o)
  hpairK : ∀ o o', αK o (hK o') = (CK0 o o' : ZMod p)
  hfK : ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φK o
  hclosK : ggAutomizer K Bs = Subgroup.closure (Set.range φK)
  hφK : ∀ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, φK (Sum.inl j) = φL j.1
  hhK : ∀ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, hK (Sum.inl j) = (cc j : ZMod p) • hL j.1
  hαK : ∀ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, αK (Sum.inl j) = (↑((cc j)⁻¹) : ZMod p) • αL j.1
  hord : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1

private theorem l05nTC_align_order {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G} {ΛL : Type} [Fintype ΛL] [DecidableEq ΛL]
    {ΛK : Type} [Fintype ΛK] [DecidableEq ΛK]
    {MJL : CoxeterMatrix ΛL} {MJK : CoxeterMatrix ΛK}
    {fJL : MJL.Group ≃* ↥(ggAutomizer J Bs)} {fJK : MJK.Group ≃* ↥(ggAutomizer J Bs)}
    (σ : ΛL ≃ ΛK) (w : ↥(ggAutomizer J Bs))
    (hσ : ∀ i, fJK (MJK.simple (σ i)) = w * fJL (MJL.simple i) * w⁻¹) :
    ∀ i j, MJK.M (σ i) (σ j) = MJL.M i j := by
  intro i j
  have h1 : orderOf (fJK (MJK.simple (σ i)) * fJK (MJK.simple (σ j))) = MJK.M (σ i) (σ j) := by
    rw [← map_mul]
    exact (orderOf_injective (fJK : MJK.Group →* ↥(ggAutomizer J Bs)) fJK.injective
      (MJK.simple (σ i) * MJK.simple (σ j))).trans (by
        simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
          CoxeterSystem.orderOf_simple_mul_simple MJK.toCoxeterSystem (σ i) (σ j))
  have h3 : orderOf (fJL (MJL.simple i) * fJL (MJL.simple j)) = MJL.M i j := by
    rw [← map_mul]
    exact (orderOf_injective (fJL : MJL.Group →* ↥(ggAutomizer J Bs)) fJL.injective
      (MJL.simple i * MJL.simple j)).trans (by
        simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
          CoxeterSystem.orderOf_simple_mul_simple MJL.toCoxeterSystem i j)
  have h2 : fJK (MJK.simple (σ i)) * fJK (MJK.simple (σ j)) =
      w * (fJL (MJL.simple i) * fJL (MJL.simple j)) * w⁻¹ := by
    rw [hσ i, hσ j]; group
  have hconj : ∀ x : ↥(ggAutomizer J Bs), orderOf (w * x * w⁻¹) = orderOf x := by
    intro x
    rw [← MulAut.conj_apply]
    exact orderOf_injective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective x
  rw [← h1, h2, hconj, h3]

private theorem l05nTC_intCartan_reindex {ι κ : Type} {M : CoxeterMatrix κ}
    {C : Matrix κ κ ℤ} (h : GGIntCartan M C) (e : ι ≃ κ) :
    GGIntCartan (M.reindex e.symm) (fun i j => C (e i) (e j)) := by
  constructor
  · intro i
    exact h.1 (e i)
  · intro i j hij
    have hij' : e i ≠ e j := fun hh => hij (e.injective hh)
    have h2 := h.2 (e i) (e j) hij'
    rw [CoxeterMatrix.reindex_apply, Equiv.symm_symm]
    exact h2

private theorem l05nTn_align (hConj : GGWeylSimpleSystemsConjInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ} {Bs L J K : Subgroup G}
    (hL : GGResTwoNodeSideDatum p Bs L J) (hK : l05nTn_SideSum k p Bs K J) :
    Nonempty (l05nTn_Al k p Bs L J K) := by
  obtain ⟨ΛL, i1L, i2L, b1L, b2L, ML, CL, MJL, VL, i3L, i4L, ιL, φL, hL1, αL,
    hbL, hWML, hCLL, hWMJL, hMJL, hlinL, hreflL, hpairL, hfLex, hclosL, hfJLex, hclosJL,
    hconjL⟩ := hL
  letI := i1L; letI := i2L; letI := i3L; letI := i4L
  obtain ⟨fL, hfL⟩ := hfLex
  obtain ⟨fJL, hfJL⟩ := hfJLex
  obtain ⟨Λj, i1K, i2K, Λa, i3K, i4K, MK0, CKraw, MJK, VK, i5K, i6K, ιK, φK0, hK0, αK0,
    hcard1, hcard2, hkK, hWMK0, hCKK0, hWMJK, hMJKK, hlinK0, hreflK0, hpairK0, hfK0ex, hclosK0,
    hfJKex, hclosJK, hconjK⟩ := hK
  letI := i1K; letI := i2K; letI := i5K; letI := i6K
  obtain ⟨fK0, hfK0⟩ := hfK0ex
  obtain ⟨fJK, hfJK⟩ := hfJKex
  have hT : ∀ k : Λj, ∃ (u : ↥(ggAutomizer J Bs)) (i : {i : ΛL // i ≠ b1L ∧ i ≠ b2L}),
      fJK (MJK.simple k) = u * fJL (MJL.simple i) * u⁻¹ := by
    intro k
    have hkA : φK0 (Sum.inl k) ∈ ggAutomizer J Bs := by
      rw [hclosJK]
      exact Subgroup.subset_closure ⟨k, rfl⟩
    obtain ⟨u, hu, i, hui⟩ := hconjL (φK0 (Sum.inl k)) hkA (hreflK0 (Sum.inl k))
    refine ⟨⟨u, hu⟩, i, ?_⟩
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk, hfJK k, hfJL i] using hui
  obtain ⟨σ, w, hσ⟩ := hConj (Λ := {i : ΛL // i ≠ b1L ∧ i ≠ b2L}) (Λ' := Λj) MJL MJK
    hWMJL hWMJK (↥(ggAutomizer J Bs)) fJL fJK hT
  have horder : ∀ i j : {i : ΛL // i ≠ b1L ∧ i ≠ b2L}, MJK.M (σ i) (σ j) = MJL.M i j :=
    l05nTC_align_order σ w hσ
  have hbij : Function.Bijective ((ιK.symm.trans ιL).toAddMonoidHom.toZModLinearMap p) :=
    (ιK.symm.trans ιL).bijective
  let e : VK ≃ₗ[ZMod p] VL := LinearEquiv.ofBijective _ hbij
  have he : ∀ x : VK, e x = ιL (ιK.symm x) := by
    intro x
    rw [LinearEquiv.ofBijective_apply]
    rfl
  let u : MulAut ↥Bs := (w : MulAut ↥Bs)⁻¹
  let W : VL ≃ₗ[ZMod p] VL := ggLin (p := p) ιL u
  let φK2 : Λj ⊕ Λa → MulAut ↥Bs := fun k => u * φK0 k * u⁻¹
  let hKt : Λj ⊕ Λa → VL := fun k => e (hK0 k)
  let αKt : Λj ⊕ Λa → Module.Dual (ZMod p) VL := fun k => (αK0 k).comp e.symm.toLinearMap
  let hK2 : Λj ⊕ Λa → VL := fun k => W (hKt k)
  let αK2 : Λj ⊕ Λa → Module.Dual (ZMod p) VL := fun k => (αKt k).comp W.symm.toLinearMap
  have hφKσ : ∀ i : {i : ΛL // i ≠ b1L ∧ i ≠ b2L},
      φK0 (Sum.inl (σ i)) = (w : MulAut ↥Bs) * φL i * (w : MulAut ↥Bs)⁻¹ := by
    intro i
    have h2 := congrArg (fun x : ↥(ggAutomizer J Bs) => (x : MulAut ↥Bs)) (hσ i)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hfJK, hfJL] using h2
  have hφ2 : ∀ i : {i : ΛL // i ≠ b1L ∧ i ≠ b2L}, φK2 (Sum.inl (σ i)) = φL i := by
    intro i
    show u * φK0 (Sum.inl (σ i)) * u⁻¹ = φL i
    rw [hφKσ i]
    show (w : MulAut ↥Bs)⁻¹ * ((w : MulAut ↥Bs) * φL i * (w : MulAut ↥Bs)⁻¹) *
      ((w : MulAut ↥Bs)⁻¹)⁻¹ = φL i
    group
  have hlin_t : ∀ k v, ggLin (p := p) ιL (φK0 k) v = v - αKt k v • hKt k := by
    intro k v
    have hes : ∀ x : VL, e.symm x = ιK (ιL.symm x) := by
      intro x
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, he]
      simp
    have htrans : ggLin (p := p) ιL (φK0 k) v =
        e (ggLin (p := p) ιK (φK0 k) (e.symm v)) := by
      rw [he, hes, ggLin_apply, ggLin_apply]
      congr 1
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    rw [htrans, hlinK0 k (e.symm v)]
    simp only [map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rfl
  have hlin2 : ∀ k v, ggLin (p := p) ιL (φK2 k) v = v - αK2 k v • hK2 k := by
    intro k v
    have h := l05nTn_lin_conj (p := p) ιL u (φK0 k) (hlin_t k) v
    simpa only [φK2, αK2, hK2, hKt, αKt, W, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply] using h
  have hpair2 : ∀ k k', αK2 k (hK2 k') = (CKraw k k' : ZMod p) := by
    intro k k'
    simpa only [αK2, hK2, hKt, αKt, W, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply] using hpairK0 k k'
  have hrefl2 : ∀ k, GGIsReflection p (φK2 k) := fun k => l05nTn_refl_conj (hreflK0 k) u
  have huJ : u ∈ ggAutomizer J Bs := by
    show (w : MulAut ↥Bs)⁻¹ ∈ ggAutomizer J Bs
    exact Subgroup.inv_mem _ w.2
  have huK : u ∈ ggAutomizer K Bs := by
    have h2 : Subgroup.closure (Set.range fun j : Λj => φK0 (Sum.inl j)) ≤
        Subgroup.closure (Set.range φK0) := by
      rw [Subgroup.closure_le]
      rintro γ ⟨j, rfl⟩
      exact Subgroup.subset_closure ⟨Sum.inl j, rfl⟩
    have h3 : (w : MulAut ↥Bs) ∈ Subgroup.closure (Set.range φK0) := h2 (hclosJK ▸ w.2)
    rw [← hclosK0] at h3
    simpa [u] using Subgroup.inv_mem _ h3
  have hlam : ∀ i : {i : ΛL // i ≠ b1L ∧ i ≠ b2L}, ∃ c : (ZMod p)ˣ,
      hK2 (Sum.inl (σ i)) = (c : ZMod p) • hL1 i.1 ∧
      αK2 (Sum.inl (σ i)) = (↑(c⁻¹) : ZMod p) • αL i.1 := by
    intro i
    have hf : αL i.1 (hL1 i.1) = 2 := by
      rw [hpairL i.1 i.1, hCLL.1 i.1]
      norm_num
    have hf' : αK2 (Sum.inl (σ i)) (hK2 (Sum.inl (σ i))) = 2 := by
      rw [hpair2 (Sum.inl (σ i)) (Sum.inl (σ i)), hCKK0.1 (Sum.inl (σ i))]
      norm_num
    have hcomm : ∀ v, αL i.1 v • hL1 i.1 = αK2 (Sum.inl (σ i)) v • hK2 (Sum.inl (σ i)) := by
      intro v
      have h1 := hlinL i.1 v
      have h2 := hlin2 (Sum.inl (σ i)) v
      rw [hφ2 i] at h2
      have hh : v - αL i.1 v • hL1 i.1 = v - αK2 (Sum.inl (σ i)) v • hK2 (Sum.inl (σ i)) :=
        h1.symm.trans h2
      have hh1 : αL i.1 v • hL1 i.1 - v =
          αK2 (Sum.inl (σ i)) v • hK2 (Sum.inl (σ i)) - v := by
        simpa [neg_sub] using congrArg Neg.neg hh
      simpa [sub_add_cancel] using congrArg (fun t => t + v) hh1
    exact l05nTn_rankOne hp2 hf hf' hcomm
  let cc : (i : {i : ΛL // i ≠ b1L ∧ i ≠ b2L}) → (ZMod p)ˣ := fun i => (hlam i).choose
  have hcc : ∀ i, hK2 (Sum.inl (σ i)) = (cc i : ZMod p) • hL1 i.1 ∧
      αK2 (Sum.inl (σ i)) = (↑((cc i)⁻¹) : ZMod p) • αL i.1 := fun i => (hlam i).choose_spec
  let τ : ({i : ΛL // i ≠ b1L ∧ i ≠ b2L} ⊕ Λa) ≃ (Λj ⊕ Λa) :=
    Equiv.sumCongr σ (Equiv.refl Λa)
  let MK : CoxeterMatrix ({i : ΛL // i ≠ b1L ∧ i ≠ b2L} ⊕ Λa) := MK0.reindex τ.symm
  let CK0 : Matrix ({i : ΛL // i ≠ b1L ∧ i ≠ b2L} ⊕ Λa)
      ({i : ΛL // i ≠ b1L ∧ i ≠ b2L} ⊕ Λa) ℤ := fun o o' => CKraw (τ o) (τ o')
  let φK : ({i : ΛL // i ≠ b1L ∧ i ≠ b2L} ⊕ Λa) → MulAut ↥Bs := fun o => φK2 (τ o)
  let hK : ({i : ΛL // i ≠ b1L ∧ i ≠ b2L} ⊕ Λa) → VL := fun o => hK2 (τ o)
  let αK : ({i : ΛL // i ≠ b1L ∧ i ≠ b2L} ⊕ Λa) → Module.Dual (ZMod p) VL :=
    fun o => αK2 (τ o)
  have hWMK : GGIsWeylMatrix MK := l05nTn_weyl_reindex hWMK0 τ.symm
  have hCKK : GGIntCartan MK CK0 := l05nTC_intCartan_reindex hCKK0 τ
  have hlinK : ∀ o w, ggLin (p := p) ιL (φK o) w = w - αK o w • hK o :=
    fun o w => hlin2 (τ o) w
  have hreflK : ∀ o, GGIsReflection p (φK o) := fun o => hrefl2 (τ o)
  have hpairK : ∀ o o', αK o (hK o') = (CK0 o o' : ZMod p) :=
    fun o o' => hpair2 (τ o) (τ o')
  have hφK : ∀ j : {i : ΛL // i ≠ b1L ∧ i ≠ b2L}, φK (Sum.inl j) = φL j.1 := fun j => hφ2 j
  have hhK : ∀ j : {i : ΛL // i ≠ b1L ∧ i ≠ b2L},
      hK (Sum.inl j) = (cc j : ZMod p) • hL1 j.1 := fun j => (hcc j).1
  have hαK : ∀ j : {i : ΛL // i ≠ b1L ∧ i ≠ b2L},
      αK (Sum.inl j) = (↑((cc j)⁻¹) : ZMod p) • αL j.1 := fun j => (hcc j).2
  have hord : ∀ i j : {i : ΛL // i ≠ b1L ∧ i ≠ b2L},
      MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1 := by
    intro i j
    rw [show MK.M (Sum.inl i) (Sum.inl j) = MK0.M (Sum.inl (σ i)) (Sum.inl (σ j)) from by
          rw [CoxeterMatrix.reindex_apply, Equiv.symm_symm]; rfl,
      ← hMJKK, horder, hMJL]
  let fK : MK.Group ≃* ↥(ggAutomizer K Bs) :=
    (MK0.reindexGroupEquiv τ.symm).trans (fK0.trans (MulAut.conj ⟨u, huK⟩))
  have hfK : ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φK o := by
    intro o
    show ((fK0.trans (MulAut.conj ⟨u, huK⟩))
      ((MK0.reindexGroupEquiv τ.symm) (MK.simple o)) : MulAut ↥Bs) = φK2 (τ o)
    rw [show (MK0.reindexGroupEquiv τ.symm) (MK.simple o) = MK0.simple (τ o) from rfl,
      MulEquiv.trans_apply, MulAut.conj_apply]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hfK0]
  have hclosK : ggAutomizer K Bs = Subgroup.closure (Set.range φK) := by
    have hclosK2 : ggAutomizer K Bs = Subgroup.closure (Set.range φK2) := by
      have hrange : Set.range φK2 = (MulAut.conj u).toMonoidHom '' Set.range φK0 := by
        ext γ; constructor
        · rintro ⟨k, rfl⟩
          exact ⟨φK0 k, ⟨k, rfl⟩, (MulAut.conj_apply u (φK0 k)).symm⟩
        · rintro ⟨γ, ⟨k, rfl⟩, rfl⟩
          exact ⟨k, MulAut.conj_apply u (φK0 k)⟩
      rw [hrange, ← MonoidHom.map_closure (MulAut.conj u).toMonoidHom (Set.range φK0),
        ← hclosK0]
      exact (l05nTn_closure_conj (ggAutomizer K Bs) u huK).symm
    have hrange : Set.range φK = Set.range φK2 := by
      ext γ; constructor
      · rintro ⟨o, rfl⟩
        exact ⟨τ o, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨τ.symm k, by simp [φK]⟩
    rw [hclosK2, hrange]
  exact ⟨ΛL, i1L, i2L, b1L, b2L, hbL, ML, CL, MJL, VL, ιL, φL, hL1, αL,
    Λa, i3K, i4K, ⟨hcard1, hcard2⟩, hkK, MK, CK0, φK, hK, αK, cc, fL, fK,
    hWML, hCLL, hWMJL, hMJL, hlinL, hreflL, hpairL, hfL, hclosL, hclosJL,
    hWMK, hCKK, hlinK, hreflK, hpairK, hfK, hclosK, hφK, hhK, hαK, hord⟩

private theorem l05nTD_scale_lin {p : ℕ} [Fact p.Prime] {E V : Type} [Group E] [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive E ≃+ V) (φ : MulAut E) (α : Module.Dual (ZMod p) V)
    (h : V) (μ : (ZMod p)ˣ)
    (hlin : ∀ v, ggLin (p := p) ι φ v = v - α v • h) (v : V) :
    ggLin (p := p) ι φ v = v - ((↑(μ⁻¹) : ZMod p) • α) v • ((μ : ZMod p) • h) := by
  rw [hlin v]
  congr 1
  rw [LinearMap.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  calc α v = α v * 1 := (mul_one _).symm
    _ = α v * ((↑(μ⁻¹) : ZMod p) * (μ : ZMod p)) := by rw [Units.inv_mul, mul_one]
    _ = ((↑(μ⁻¹) : ZMod p) * α v) * (μ : ZMod p) := by ring

private theorem l05nTD_pair_inl_inr {p : ℕ} [Fact p.Prime] {Jn La : Type} [Fintype Jn]
    [DecidableEq Jn] [Fintype La] [DecidableEq La] {MK : CoxeterMatrix (Jn ⊕ La)}
    {CK0 : Matrix (Jn ⊕ La) (Jn ⊕ La) ℤ} (hCKK : GGIntCartan MK CK0)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {αL : Jn → Module.Dual (ZMod p) V}
    {αK : Jn ⊕ La → Module.Dual (ZMod p) V} {hK : Jn ⊕ La → V} {cc : Jn → (ZMod p)ˣ}
    (hαK : ∀ j, αK (Sum.inl j) = (↑((cc j)⁻¹) : ZMod p) • αL j)
    (hpairK : ∀ o o', αK o (hK o') = (CK0 o o' : ZMod p))
    {μ : La → (ZMod p)ˣ}
    (hμ : ∀ a j, MK.M (Sum.inr a) (Sum.inl j) ≠ 2 → μ a = (cc j)⁻¹)
    (i : Jn) (a : La) :
    αL i ((μ a : ZMod p) • hK (Sum.inr a)) =
      (CK0 (Sum.inl i) (Sum.inr a) : ZMod p) := by
  have h1 : αK (Sum.inl i) (hK (Sum.inr a)) = (CK0 (Sum.inl i) (Sum.inr a) : ZMod p) :=
    hpairK _ _
  rw [hαK i, LinearMap.smul_apply, smul_eq_mul] at h1
  rw [map_smul, smul_eq_mul]
  by_cases hm : MK.M (Sum.inl i) (Sum.inr a) = 2
  · have h0 : CK0 (Sum.inl i) (Sum.inr a) = 0 :=
      (l05nTn_cartan_eq_zero_iff hCKK (by simp)).2 hm
    have hx : αL i (hK (Sum.inr a)) = 0 := by
      rw [h0, Int.cast_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (Units.ne_zero ((cc i)⁻¹))
    rw [hx, mul_zero, h0, Int.cast_zero]
  · have hm' : MK.M (Sum.inr a) (Sum.inl i) ≠ 2 := by
      rwa [MK.symmetric (Sum.inr a) (Sum.inl i)]
    rw [hμ a i hm']
    exact h1

private theorem l05nTD_pair_inr_inl {p : ℕ} [Fact p.Prime] {Jn La : Type} [Fintype Jn]
    [DecidableEq Jn] [Fintype La] [DecidableEq La] {MK : CoxeterMatrix (Jn ⊕ La)}
    {CK0 : Matrix (Jn ⊕ La) (Jn ⊕ La) ℤ} (hCKK : GGIntCartan MK CK0)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {hL : Jn → V}
    {αK : Jn ⊕ La → Module.Dual (ZMod p) V} {hK : Jn ⊕ La → V} {cc : Jn → (ZMod p)ˣ}
    (hhK : ∀ j, hK (Sum.inl j) = (cc j : ZMod p) • hL j)
    (hpairK : ∀ o o', αK o (hK o') = (CK0 o o' : ZMod p))
    {μ : La → (ZMod p)ˣ}
    (hμ : ∀ a j, MK.M (Sum.inr a) (Sum.inl j) ≠ 2 → μ a = (cc j)⁻¹)
    (a : La) (j : Jn) :
    ((↑((μ a)⁻¹) : ZMod p) • αK (Sum.inr a)) (hL j) =
      (CK0 (Sum.inr a) (Sum.inl j) : ZMod p) := by
  have h1 : αK (Sum.inr a) (hK (Sum.inl j)) =
      (CK0 (Sum.inr a) (Sum.inl j) : ZMod p) := hpairK _ _
  rw [hhK j, map_smul, smul_eq_mul] at h1
  rw [LinearMap.smul_apply, smul_eq_mul]
  by_cases hm : MK.M (Sum.inr a) (Sum.inl j) = 2
  · have h0 : CK0 (Sum.inr a) (Sum.inl j) = 0 :=
      (l05nTn_cartan_eq_zero_iff hCKK (by simp)).2 hm
    have hx : αK (Sum.inr a) (hL j) = 0 := by
      rw [h0, Int.cast_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (Units.ne_zero (cc j))
    rw [hx, mul_zero, h0, Int.cast_zero]
  · rw [hμ a j hm]
    simpa using h1

private theorem l05nTD_pair_inr_inr {p : ℕ} [Fact p.Prime] {Jn La : Type} [Fintype Jn]
    [DecidableEq Jn] [Fintype La] [DecidableEq La] {MK : CoxeterMatrix (Jn ⊕ La)}
    {CK0 : Matrix (Jn ⊕ La) (Jn ⊕ La) ℤ} (hCKK : GGIntCartan MK CK0)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {αK : Jn ⊕ La → Module.Dual (ZMod p) V} {hK : Jn ⊕ La → V}
    (hpairK : ∀ o o', αK o (hK o') = (CK0 o o' : ZMod p))
    {μ : La → (ZMod p)ˣ}
    (hμa : ∀ a a', a ≠ a' → MK.M (Sum.inr a) (Sum.inr a') ≠ 2 → μ a = μ a')
    (a a' : La) :
    ((↑((μ a)⁻¹) : ZMod p) • αK (Sum.inr a)) ((μ a' : ZMod p) • hK (Sum.inr a')) =
      (CK0 (Sum.inr a) (Sum.inr a') : ZMod p) := by
  rw [LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul]
  have h1 := hpairK (Sum.inr a) (Sum.inr a')
  by_cases haa : a = a'
  · subst haa
    rw [← mul_assoc, Units.inv_mul, one_mul]
    exact h1
  · by_cases hm : MK.M (Sum.inr a) (Sum.inr a') = 2
    · have h0 : CK0 (Sum.inr a) (Sum.inr a') = 0 :=
        (l05nTn_cartan_eq_zero_iff hCKK (by simpa using haa)).2 hm
      rw [h0, Int.cast_zero] at h1 ⊢
      rw [h1, mul_zero, mul_zero]
    · rw [hμa a a' haa hm]
      rw [← mul_assoc, Units.inv_mul, one_mul]
      exact h1

private def l05nTn_DatumK {G : Type} [Group G] (k : ℕ) (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
    b₁ ≠ b₂ ∧ Nat.card Λa = k ∧
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) ∧
      GGDeletedConnected2 ML b₁ b₂ ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j))

private theorem l05nTn_DatumK.toDatum {G : Type} [Group G] {k : ℕ} {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (hD : l05nTn_DatumK k p Bs L J K) (hk : k = 1 ∨ k = 2) :
    GGResTwoNodeDatum p Bs L J K ggSelAny ggTypAny := by
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hb, hcard, hWML, hCLL, hWMK, hCKK, hlin, hrefl, hpairLL, hpairCK, hfL, hfK,
    hclosL, hclosK, hdel, hclosJL⟩ := hD
  refine ⟨Λ, i1, i2, b₁, b₂, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hb, ?_, ?_, hWML, hCLL, hWMK, hCKK, trivial, hlin, hrefl, hpairLL, hpairCK, trivial,
    hfL, hfK, hclosL, hclosK, hdel, hclosJL⟩
  · rcases hk with rfl | rfl <;> omega
  · rcases hk with rfl | rfl <;> omega

private theorem l05nTn_datum {G : Type} [Group G] [Finite G] {k : ℕ} {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (D : l05nTn_Al k p Bs L J K) :
    l05nTn_DatumK k p Bs L J K := by
  letI := D.fin
  letI := D.dec
  letI := D.fina
  letI := D.deca
  letI := D.acg
  letI := D.mod
  obtain ⟨μ, hμJ, hμa⟩ :=
    l05nTn_mu (U := (ZMod p)ˣ) (M := D.MK) (C := D.CK0)
      D.hWMK D.hCKK (by
        intro i j
        simpa only [D.hMJL, D.hord] using ggRC_weyl_connected D.hWMJL i j)
      D.hΛa.2 D.cc
  let CK : Matrix ({i : D.Λ // i ≠ D.b₁ ∧ i ≠ D.b₂} ⊕ D.Λa)
      ({i : D.Λ // i ≠ D.b₁ ∧ i ≠ D.b₂} ⊕ D.Λa) ℤ :=
    fun o o' => match o, o' with
      | Sum.inl i, Sum.inl j => D.CL i.1 j.1
      | _, _ => D.CK0 o o'
  let φ : D.Λ ⊕ D.Λa → MulAut ↥Bs := fun o =>
    match o with
    | Sum.inl i => D.φL i
    | Sum.inr a => D.φK (Sum.inr a)
  let h : D.Λ ⊕ D.Λa → D.V := fun o =>
    match o with
    | Sum.inl i => D.hL i
    | Sum.inr a => (μ a : ZMod p) • D.hK (Sum.inr a)
  let α : D.Λ ⊕ D.Λa → Module.Dual (ZMod p) D.V := fun o =>
    match o with
    | Sum.inl i => D.αL i
    | Sum.inr a => (↑((μ a)⁻¹) : ZMod p) • D.αK (Sum.inr a)
  have hCK : GGIntCartan D.MK CK := by
    constructor
    · intro o
      cases o with
      | inl i => exact D.hCLL.1 i.1
      | inr a => exact D.hCKK.1 (Sum.inr a)
    · intro o o' hne
      cases o with
      | inl i =>
        cases o' with
        | inl j =>
          have hij : i ≠ j := fun h => hne (by rw [h])
          have h := D.hCLL.2 i.1 j.1 (fun hh => hij (Subtype.ext hh))
          rw [show D.MK.M (Sum.inl i) (Sum.inl j) = D.ML.M i.1 j.1 from D.hord i j]
          exact h
        | inr a => exact D.hCKK.2 (Sum.inl i) (Sum.inr a) (by simp)
      | inr a =>
        cases o' with
        | inl j => exact D.hCKK.2 (Sum.inr a) (Sum.inl j) (by simp)
        | inr a' => exact D.hCKK.2 (Sum.inr a) (Sum.inr a') (by simpa using hne)
  have hlin : ∀ o w, ggLin (p := p) D.ι (φ o) w = w - α o w • h o := by
    intro o w
    cases o with
    | inl i => exact D.hlinL i w
    | inr a =>
      exact l05nTD_scale_lin (p := p) D.ι (D.φK (Sum.inr a)) (D.αK (Sum.inr a))
        (D.hK (Sum.inr a)) (μ a) (D.hlinK (Sum.inr a)) w
  have hrefl : ∀ o, GGIsReflection p (φ o) := by
    intro o
    cases o with
    | inl i => exact D.hreflL i
    | inr a => exact D.hreflK (Sum.inr a)
  have hpairLL : ∀ i j : D.Λ, α (Sum.inl i) (h (Sum.inl j)) = (D.CL i j : ZMod p) :=
    fun i j => D.hpairL i j
  have hpairCK : ∀ o o' : {i : D.Λ // i ≠ D.b₁ ∧ i ≠ D.b₂} ⊕ D.Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p) := by
    intro o o'
    cases o with
    | inl i =>
      cases o' with
      | inl j => exact D.hpairL i.1 j.1
      | inr a => exact l05nTD_pair_inl_inr D.hCKK D.hαK D.hpairK hμJ i a
    | inr a =>
      cases o' with
      | inl j => exact l05nTD_pair_inr_inl D.hCKK D.hhK D.hpairK hμJ a j
      | inr a' => exact l05nTD_pair_inr_inr D.hCKK D.hpairK hμa a a'
  have hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : D.Λ // j ≠ D.b₁ ∧ j ≠ D.b₂} => φ (Sum.inl j)) ∪
        Set.range fun a : D.Λa => φ (Sum.inr a)) := by
    rw [D.hclosK]
    congr 1
    ext γ
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, (D.hφK j).symm⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, D.hφK j⟩
      · exact ⟨Sum.inr a, rfl⟩
  have hdel : GGDeletedConnected2 D.ML D.b₁ D.b₂ := by
    intro i j
    simpa only [D.hMJL] using ggRC_weyl_connected D.hWMJL i j
  have hfK' : ∀ o : {i : D.Λ // i ≠ D.b₁ ∧ i ≠ D.b₂} ⊕ D.Λa,
      (D.fK (D.MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id) := by
    intro o
    rw [D.hfK o]
    cases o with
    | inl j => rw [D.hφK j]; rfl
    | inr a => rfl
  refine ⟨D.Λ, D.fin, D.dec, D.b₁, D.b₂, D.Λa, D.fina, D.deca, D.ML, D.CL, D.MK, CK,
    D.V, D.acg, D.mod, D.ι, φ, h, α, D.hb, D.hk, D.hWML, D.hCLL, D.hWMK, hCK,
    hlin, hrefl, hpairLL, hpairCK, ⟨D.fL, fun i => D.hfL i⟩,
    ⟨D.fK, hfK'⟩, D.hclosL, hclosK, hdel, D.hclosJL⟩

theorem ggResTwoNodeDatum_of_sides (hConj : GGWeylSimpleSystemsConjInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs L J K : Subgroup G}
    (hL : GGResTwoNodeSideDatum p Bs L J)
    (hK : GGResSideDatum p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J) :
    GGResTwoNodeDatum p Bs L J K ggSelAny ggTypAny := by
  rcases hK with hK | hK
  · obtain ⟨D⟩ := l05nTn_align hConj hp2 hL (l05nTn_sum_of_one hK)
    exact l05nTn_DatumK.toDatum (l05nTn_datum D) (Or.inl rfl)
  · obtain ⟨D⟩ := l05nTn_align hConj hp2 hL (l05nTn_sum_of_two hK)
    exact l05nTn_DatumK.toDatum (l05nTn_datum D) (Or.inr rfl)

theorem ggResTwoNodeDatum_of_sides_card_one (hConj : GGWeylSimpleSystemsConjInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs L J K : Subgroup G}
    (hL : GGResTwoNodeSideDatum p Bs L J) (hK : GGResSideDatum p Bs K J) :
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
    b₁ ≠ b₂ ∧ Nat.card Λa = 1 ∧
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) ∧
      GGDeletedConnected2 ML b₁ b₂ ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) := by
  obtain ⟨D⟩ := l05nTn_align hConj hp2 hL (l05nTn_sum_of_one hK)
  exact l05nTn_datum D

theorem ggResTwoNodeDatum_of_sides_card_two (hConj : GGWeylSimpleSystemsConjInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs L J K : Subgroup G}
    (hL : GGResTwoNodeSideDatum p Bs L J) (hK : GGResTwoNodeSideDatum p Bs K J) :
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
    b₁ ≠ b₂ ∧ Nat.card Λa = 2 ∧
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) ∧
      GGDeletedConnected2 ML b₁ b₂ ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) := by
  obtain ⟨D⟩ := l05nTn_align hConj hp2 hL (l05nTn_sum_of_two hK)
  exact l05nTn_datum D

end CFSG.StandardType

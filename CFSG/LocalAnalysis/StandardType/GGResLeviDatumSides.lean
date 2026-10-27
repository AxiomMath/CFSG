module

public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import TauCeti.Combinatorics.SimpleGraph.BranchComponents
public import CFSG.YGroups.Y443.Native.Hom

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private structure l05nSd_Core {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X J : Subgroup G) where
  Λ : Type
  instFintype : Fintype Λ
  instDecEq : DecidableEq Λ
  b : Λ
  M : CoxeterMatrix Λ
  C : Matrix Λ Λ ℤ
  MJ : CoxeterMatrix {j : Λ // j ≠ b}
  V : Type
  instAddCommGroup : AddCommGroup V
  instModule : Module (ZMod p) V
  ι : Additive ↥Bs ≃+ V
  φ : Λ → MulAut ↥Bs
  h : Λ → V
  α : Λ → Module.Dual (ZMod p) V

private def l05nSd_Prop {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (D : l05nSd_Core p Bs X J) : Prop :=
  letI := D.instFintype
  letI := D.instDecEq
  letI := D.instAddCommGroup
  letI := D.instModule
  GGIsWeylMatrix D.M ∧ GGIntCartan D.M D.C ∧ GGIsWeylMatrix D.MJ ∧
    (∀ j j' : {j : D.Λ // j ≠ D.b}, D.MJ.M j j' = D.M.M j j') ∧
    (∀ i w, ggLin (p := p) D.ι (D.φ i) w = w - D.α i w • D.h i) ∧
    (∀ i, GGIsReflection p (D.φ i)) ∧
    (∀ i j, D.α i (D.h j) = (D.C i j : ZMod p)) ∧
    (∃ f : D.M.Group ≃* ↥(ggAutomizer X Bs),
      ∀ i, (f (D.M.simple i) : MulAut ↥Bs) = D.φ i) ∧
    ggAutomizer X Bs = Subgroup.closure (Set.range D.φ) ∧
    (∃ fJ : D.MJ.Group ≃* ↥(ggAutomizer J Bs),
      ∀ j, (fJ (D.MJ.simple j) : MulAut ↥Bs) = D.φ j) ∧
    ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : D.Λ // j ≠ D.b} => D.φ j) ∧
    GGReflConjSimple p (ggAutomizer J Bs) (fun j : {j : D.Λ // j ≠ D.b} => D.φ j)

private def l05nSd_Dat {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X J : Subgroup G) : Prop :=
  ∃ D : l05nSd_Core p Bs X J, l05nSd_Prop D

private theorem l05nSd_dat_iff {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} :
    GGResSideDatum p Bs X J ↔ l05nSd_Dat p Bs X J := by
  constructor
  · rintro ⟨Λ, i1, i2, b, M, C, MJ, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12⟩
    refine ⟨⟨Λ, i1, i2, b, M, C, MJ, V, i3, i4, ι, φ, h, α⟩, ?_⟩
    unfold l05nSd_Prop
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · rintro ⟨D, hD⟩
    unfold l05nSd_Prop at hD
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hD
    exact ⟨D.Λ, D.instFintype, D.instDecEq, D.b, D.M, D.C, D.MJ, D.V, D.instAddCommGroup,
      D.instModule, D.ι, D.φ, D.h, D.α, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

private theorem l05nSd_transport {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (hD : GGResSideDatum p Bs X J)
    {V' : Type} [AddCommGroup V'] [Module (ZMod p) V']
    (ι' : Additive ↥Bs ≃+ V') : GGResSideDatum p Bs X J := by
  obtain ⟨Λ, i1, i2, b, M, C, MJ, V, i3, i4, ι, φ, h, α,
    hWM, hC, hWMJ, hMJ, hlin, hrefl, hpair, hf, hclos, hfJ, hclosJ, hconj⟩ := hD
  letI := i3
  letI := i4
  have hbij : Function.Bijective ((ι.symm.trans ι').toAddMonoidHom.toZModLinearMap p) :=
    (ι.symm.trans ι').bijective
  let e : V ≃ₗ[ZMod p] V' := LinearEquiv.ofBijective _ hbij
  have he : ∀ x : V, e x = ι' (ι.symm x) := by
    intro x
    rw [LinearEquiv.ofBijective_apply]
    rfl
  have hes : ∀ x : V', e.symm x = ι (ι'.symm x) := by
    intro x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he]
    simp
  refine ⟨Λ, i1, i2, b, M, C, MJ, V', ‹AddCommGroup V'›, ‹Module (ZMod p) V'›, ι',
    φ, fun i => e (h i),
    fun i => (α i).comp (e.symm : V' ≃ₗ[ZMod p] V).toLinearMap, hWM, hC, hWMJ, hMJ, ?_, hrefl,
    ?_, hf, hclos, hfJ, hclosJ, hconj⟩
  · intro i w
    have h1 : ggLin (p := p) ι' (φ i) w = e (ggLin (p := p) ι (φ i) (e.symm w)) := by
      rw [he, hes, ggLin_apply, ggLin_apply]
      congr 1
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    rw [h1, hlin i (e.symm w), map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rfl
  · intro i j
    show ((α i).comp (e.symm : V' ≃ₗ[ZMod p] V).toLinearMap) (e (h j)) = _
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
    exact hpair i j

private theorem l05nSd_refl_conj {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
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

private theorem l05nSd_lin_conj {p : ℕ} [Fact p.Prime] {E : Type} [Group E] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) (u φ : MulAut E)
    {g : Module.Dual (ZMod p) V} {z : V}
    (hφ : ∀ v, ggLin (p := p) ι φ v = v - g v • z) (v : V) :
    ggLin (p := p) ι (u * φ * u⁻¹) v =
      v - g ((ggLin (p := p) ι u).symm v) • ggLin (p := p) ι u z := by
  rw [map_mul, map_mul, map_inv]
  show ggLin (p := p) ι u (ggLin (p := p) ι φ ((ggLin (p := p) ι u).symm v)) = _
  rw [hφ, map_sub, map_smul, LinearEquiv.apply_symm_apply]

private theorem l05nSd_closure_conj {E : Type} [Group E] (S : Subgroup E) (u : E) (hu : u ∈ S) :
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

private theorem l05nSd_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (hD : GGResSideDatum p Bs X J) (u : MulAut ↥Bs)
    (huX : u ∈ ggAutomizer X Bs) (huJ : u ∈ ggAutomizer J Bs) :
    GGResSideDatum p Bs X J := by
  obtain ⟨Λ, i1, i2, b, M, C, MJ, V, i3, i4, ι, φ, h, α,
    hWM, hC, hWMJ, hMJ, hlin, hrefl, hpair, hf, hclos, hfJ, hclosJ, hconj⟩ := hD
  letI := i3
  letI := i4
  have hrange : Set.range (fun i => u * φ i * u⁻¹) =
      (MulAut.conj u).toMonoidHom '' Set.range φ := by
    ext γ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨φ i, ⟨i, rfl⟩, (MulAut.conj_apply u (φ i)).symm⟩
    · rintro ⟨γ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, MulAut.conj_apply u (φ i)⟩
  have hrangeJ : Set.range (fun j : {j : Λ // j ≠ b} => u * φ j * u⁻¹) =
      (MulAut.conj u).toMonoidHom '' Set.range (fun j : {j : Λ // j ≠ b} => φ j) := by
    ext γ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨φ i, ⟨i, rfl⟩, (MulAut.conj_apply u (φ i)).symm⟩
    · rintro ⟨γ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, MulAut.conj_apply u (φ i)⟩
  refine ⟨Λ, i1, i2, b, M, C, MJ, V, ‹AddCommGroup V›, ‹Module (ZMod p) V›, ι,
    fun i => u * φ i * u⁻¹, fun i => ggLin (p := p) ι u (h i),
    fun i => (α i).comp ((ggLin (p := p) ι u).symm : V ≃ₗ[ZMod p] V).toLinearMap,
    hWM, hC, hWMJ, hMJ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v
    simpa [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using
      l05nSd_lin_conj (p := p) ι u (φ i) (hlin i) v
  · intro i
    exact l05nSd_refl_conj (hrefl i) u
  · intro i j
    show (α i) ((ggLin (p := p) ι u).symm (ggLin (p := p) ι u (h j))) = _
    rw [LinearEquiv.symm_apply_apply]
    exact hpair i j
  · refine ⟨hf.choose.trans (MulAut.conj ⟨u, huX⟩), fun i => ?_⟩
    rw [MulEquiv.trans_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hf.choose_spec i]
  · rw [hclos, hrange, ← MonoidHom.map_closure (MulAut.conj u).toMonoidHom (Set.range φ)]
    rw [show (Subgroup.closure (Set.range φ)).map (MulAut.conj u).toMonoidHom
        = Subgroup.closure (Set.range φ) from l05nSd_closure_conj _ u (hclos ▸ huX)]
  · refine ⟨hfJ.choose.trans (MulAut.conj ⟨u, huJ⟩), fun j => ?_⟩
    rw [MulEquiv.trans_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hfJ.choose_spec j]
  · rw [hclosJ, hrangeJ, ← MonoidHom.map_closure (MulAut.conj u).toMonoidHom
      (Set.range fun j : {j : Λ // j ≠ b} => φ j)]
    rw [show (Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ j)).map
        (MulAut.conj u).toMonoidHom
        = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ j)
      from l05nSd_closure_conj _ u (hclosJ ▸ huJ)]
  · intro t ht hrefl
    obtain ⟨v, hv, i, hti⟩ := hconj t ht hrefl
    exact ⟨v * u⁻¹, Subgroup.mul_mem _ hv (Subgroup.inv_mem _ huJ), i, by
      rw [hti]; group⟩

private theorem l05nSd_rankOne {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
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

private theorem l05nSd_cartan_eq_zero_iff {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
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

private theorem l05nSd_weylFixed {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M) :
    GGIsWeylMatrixFixed M := h

private theorem l05nSd_nonempty {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M) :
    Nonempty ι := by
  rcases h with ⟨n, e, hn, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact ⟨e ⟨0, by omega⟩⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩
  · exact ⟨e 0⟩

private theorem l05nSd_graph_adj {Λ : Type} [Fintype Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hWM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (i j : Λ) :
    (TauCeti.diagramGraph C).Adj i j ↔ i ≠ j ∧ M.M i j ≠ 2 := by
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (l05nSd_weylFixed hWM) hC
  rw [TauCeti.IsFiniteType.diagramGraph_adj_iff hFT]
  constructor
  · rintro ⟨hij, hCij⟩
    exact ⟨hij, fun hM => hCij ((l05nSd_cartan_eq_zero_iff hC hij).2 hM)⟩
  · rintro ⟨hij, hMij⟩
    exact ⟨hij, fun h0 => hMij ((l05nSd_cartan_eq_zero_iff hC hij).1 h0)⟩

private theorem l05nSd_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b)
    {a b : α} (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

private theorem l05nSd_exists_nbr_of_reach {Λ : Type} (G : SimpleGraph Λ) {x a : Λ}
    (hx : x ≠ a) (h : G.Reachable x a) : ∃ u, G.Adj u a := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  cases h with
  | refl => exact absurd rfl hx
  | tail _ hbc => exact ⟨_, hbc⟩

private theorem l05nSd_leaf {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hWM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (a : Λ)
    (hdel : ∀ i j : {j : Λ // j ≠ a},
      Relation.ReflTransGen (fun u v : {j : Λ // j ≠ a} => u ≠ v ∧ M.M u v ≠ 2) i j)
    (hne : Nonempty {j : Λ // j ≠ a}) :
    ∃! j : Λ, j ≠ a ∧ M.M a j ≠ 2 := by
  classical
  have hadj := l05nSd_graph_adj (M := M) (C := C) hWM hC
  have hadj' : ∀ i j : Λ, (TauCeti.diagramGraph C).Adj i j ↔ i ≠ j ∧ M.M j i ≠ 2 := by
    intro i j
    rw [hadj i j]
    constructor
    · rintro ⟨hij, hM⟩
      exact ⟨hij, fun h => hM (M.symmetric i j ▸ h)⟩
    · rintro ⟨hij, hM⟩
      exact ⟨hij, fun h => hM (M.symmetric j i ▸ h)⟩
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (l05nSd_weylFixed hWM) hC
  have hpre : (TauCeti.diagramGraph C).Preconnected := by
    intro i j
    rw [SimpleGraph.reachable_iff_reflTransGen]
    exact l05nSd_rtg_mono (fun u v huv => (hadj u v).2 huv) (ggRC_weyl_connected hWM i j)
  have hconn : (TauCeti.diagramGraph C).Connected :=
    (SimpleGraph.connected_iff _).2 ⟨hpre, l05nSd_nonempty hWM⟩
  have hGtree : (TauCeti.diagramGraph C).IsTree :=
    TauCeti.IsFiniteType.isTree_diagramGraph hFT hconn
  have hpreC : ((TauCeti.diagramGraph C).induce ({a}ᶜ : Set Λ)).Preconnected := by
    rw [Set.compl_singleton_eq]
    intro u v
    rw [SimpleGraph.reachable_iff_reflTransGen]
    refine l05nSd_rtg_mono (α := {j : Λ // j ≠ a})
      (r := fun u v : {j : Λ // j ≠ a} => u ≠ v ∧ M.M u v ≠ 2)
      (p := fun u v => ((TauCeti.diagramGraph C).induce ({a}ᶜ : Set Λ)).Adj u v)
      (fun x y hxy => SimpleGraph.induce_adj.mpr ((hadj x.1 y.1).2
        ⟨fun h => hxy.1 (Subtype.ext h), hxy.2⟩)) (hdel u v)
  haveI : Subsingleton ((TauCeti.diagramGraph C).induce ({a}ᶜ : Set Λ)).ConnectedComponent :=
    SimpleGraph.Preconnected.subsingleton_connectedComponent hpreC
  have hsub : Subsingleton ((TauCeti.diagramGraph C).neighborSet a) :=
    ⟨fun x y => (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl hGtree a).injective
      (Subsingleton.elim _ _)⟩
  have hEx : ∃ j, j ≠ a ∧ M.M a j ≠ 2 := by
    obtain ⟨j₀, hj₀⟩ := hne
    obtain ⟨u, hu⟩ := l05nSd_exists_nbr_of_reach (TauCeti.diagramGraph C) hj₀ (hpre j₀ a)
    exact ⟨u, (hadj' u a).1 hu⟩
  refine ⟨hEx.choose, hEx.choose_spec, ?_⟩
  intro j hj
  have hm1 : j ∈ (TauCeti.diagramGraph C).neighborSet a :=
    (SimpleGraph.mem_neighborSet (G := TauCeti.diagramGraph C) a j).2
      ((hadj a j).2 ⟨hj.1.symm, hj.2⟩)
  have hm2 : hEx.choose ∈ (TauCeti.diagramGraph C).neighborSet a :=
    (SimpleGraph.mem_neighborSet (G := TauCeti.diagramGraph C) a hEx.choose).2
      ((hadj a hEx.choose).2 ⟨hEx.choose_spec.1.symm, hEx.choose_spec.2⟩)
  exact Subtype.ext_iff.mp (Subsingleton.elim
    (⟨j, hm1⟩ : (TauCeti.diagramGraph C).neighborSet a)
    (⟨hEx.choose, hm2⟩ : (TauCeti.diagramGraph C).neighborSet a))

private theorem l05nSd_align_order {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G}
    {ΛL : Type} [Fintype ΛL] [DecidableEq ΛL] {bL : ΛL}
    {MJL : CoxeterMatrix {i : ΛL // i ≠ bL}}
    {ΛK : Type} [Fintype ΛK] [DecidableEq ΛK] {aK : ΛK}
    {MJK : CoxeterMatrix {k : ΛK // k ≠ aK}}
    {fJL : MJL.Group ≃* ↥(ggAutomizer J Bs)} {fJK : MJK.Group ≃* ↥(ggAutomizer J Bs)}
    (σ : {i : ΛL // i ≠ bL} ≃ {k : ΛK // k ≠ aK}) (w : ↥(ggAutomizer J Bs))
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

private theorem l05nSd_reindex_trans {ι κ ν : Type} (M : CoxeterMatrix ι) (e : ι ≃ κ)
    (f : κ ≃ ν) : (M.reindex e).reindex f = M.reindex (e.trans f) := by
  apply CoxeterMatrix.ext
  funext x y
  simp only [CoxeterMatrix.reindex_apply, Equiv.trans_apply, Equiv.symm_trans_apply]

private theorem l05nSd_weyl_reindex {ι κ : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M)
    (f : ι ≃ κ) : GGIsWeylMatrix (M.reindex f) := by
  rcases h with ⟨n, e, hn, h | ⟨hn, h⟩ | ⟨hn, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩
  · exact Or.inl ⟨n, e.trans f, hn, Or.inl (by rw [h, l05nSd_reindex_trans])⟩
  · exact Or.inl ⟨n, e.trans f, by omega, Or.inr (Or.inl ⟨hn, by rw [h, l05nSd_reindex_trans]⟩)⟩
  · exact Or.inl ⟨n, e.trans f, by omega,
      Or.inr (Or.inr ⟨hn, by rw [h, l05nSd_reindex_trans]⟩)⟩
  · exact Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nSd_reindex_trans]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nSd_reindex_trans]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nSd_reindex_trans]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f,
      by rw [h, l05nSd_reindex_trans]⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans f,
      by rw [h, l05nSd_reindex_trans]⟩))))

theorem ggResLeviDatum_of_sides (hConj : GGWeylSimpleSystemsConjInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs L J K : Subgroup G}
    (hL : GGResSideDatum p Bs L J)
    (hK : GGResSideDatum p Bs K J) : GGResLeviDatum p Bs L J K ggSelAny ggTypAny := by
  obtain ⟨ΛL, i1L, i2L, bL, ML, CL, MJL, VL, i3L, i4L, ιL, φL, hL1, αL,
    hWML, hCLL, hWMJL, hMJL, hlinL, hreflL, hpairL, hfL, hclosL, hfJL, hclosJL, hconjL⟩ := hL
  letI := i1L; letI := i2L; letI := i3L; letI := i4L
  obtain ⟨fL, hfL⟩ := hfL
  obtain ⟨fJL, hfJL⟩ := hfJL
  obtain ⟨ΛK, i1K, i2K, aK, MK0, CK0, MJK, VK, i3K, i4K, ιK, φK, hK1, αK,
    hWMK, hCKK, hWMJK, hMJK, hlinK, hreflK, hpairK, hfK, hclosK, hfJK, hclosJK, hconjK⟩ := hK
  letI := i1K; letI := i2K; letI := i3K; letI := i4K
  obtain ⟨fK, hfK⟩ := hfK
  obtain ⟨fJK, hfJK⟩ := hfJK
  have hT : ∀ k : {k : ΛK // k ≠ aK}, ∃ (u : ↥(ggAutomizer J Bs)) (i : {i : ΛL // i ≠ bL}),
      fJK (MJK.simple k) = u * fJL (MJL.simple i) * u⁻¹ := by
    intro k
    have hkA : φK k ∈ ggAutomizer J Bs := by
      rw [hclosJK]
      exact Subgroup.subset_closure ⟨k, rfl⟩
    obtain ⟨u, hu, i, hui⟩ := hconjL (φK k) hkA (hreflK k)
    refine ⟨⟨u, hu⟩, i, ?_⟩
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk, hfJK k, hfJL i] using hui
  obtain ⟨σ, w, hσ⟩ := hConj (Λ := {i : ΛL // i ≠ bL}) (Λ' := {k : ΛK // k ≠ aK}) MJL MJK
    hWMJL hWMJK (↥(ggAutomizer J Bs)) fJL fJK hT
  have horder : ∀ i j, MJK.M (σ i) (σ j) = MJL.M i j := l05nSd_align_order (p := p) σ w hσ
  have hbij : Function.Bijective ((ιK.symm.trans ιL).toAddMonoidHom.toZModLinearMap p) :=
    (ιK.symm.trans ιL).bijective
  let e : VK ≃ₗ[ZMod p] VL := LinearEquiv.ofBijective _ hbij
  have he : ∀ x : VK, e x = ιL (ιK.symm x) := by
    intro x
    rw [LinearEquiv.ofBijective_apply]
    rfl
  let u : MulAut ↥Bs := (w : MulAut ↥Bs)⁻¹
  let W : VL ≃ₗ[ZMod p] VL := ggLin (p := p) ιL u
  let φK2 : ΛK → MulAut ↥Bs := fun k => u * φK k * u⁻¹
  let hKt : ΛK → VL := fun k => e (hK1 k)
  let αKt : ΛK → Module.Dual (ZMod p) VL := fun k => (αK k).comp e.symm.toLinearMap
  let hK2 : ΛK → VL := fun k => W (hKt k)
  let αK2 : ΛK → Module.Dual (ZMod p) VL := fun k => (αKt k).comp W.symm.toLinearMap
  have hφKσ : ∀ i, φK (σ i) = (w : MulAut ↥Bs) * φL i * (w : MulAut ↥Bs)⁻¹ := by
    intro i
    have h2 := congrArg (fun x : ↥(ggAutomizer J Bs) => (x : MulAut ↥Bs)) (hσ i)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hfJK, hfJL] using h2
  have hφ2 : ∀ i, φK2 (σ i) = φL i := by
    intro i
    show u * φK (σ i) * u⁻¹ = φL i
    rw [hφKσ i]
    show (w : MulAut ↥Bs)⁻¹ * ((w : MulAut ↥Bs) * φL i * (w : MulAut ↥Bs)⁻¹) *
      ((w : MulAut ↥Bs)⁻¹)⁻¹ = φL i
    group
  have hlin_t : ∀ k v, ggLin (p := p) ιL (φK k) v = v - αKt k v • hKt k := by
    intro k v
    have hes : ∀ x : VL, e.symm x = ιK (ιL.symm x) := by
      intro x
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, he]
      simp
    have htrans : ggLin (p := p) ιL (φK k) v =
        e (ggLin (p := p) ιK (φK k) (e.symm v)) := by
      rw [he, hes, ggLin_apply, ggLin_apply]
      congr 1
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    rw [htrans, hlinK k (e.symm v)]
    simp only [map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rfl
  have hlin2 : ∀ k v, ggLin (p := p) ιL (φK2 k) v = v - αK2 k v • hK2 k := by
    intro k v
    have h := l05nSd_lin_conj (p := p) ιL u (φK k) (hlin_t k) v
    simpa only [φK2, αK2, hK2, hKt, αKt, W, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply] using h
  have hpair2 : ∀ k k', αK2 k (hK2 k') = (CK0 k k' : ZMod p) := by
    intro k k'
    simpa only [αK2, hK2, hKt, αKt, W, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply] using hpairK k k'
  have hrefl2 : ∀ k, GGIsReflection p (φK2 k) := fun k => l05nSd_refl_conj (hreflK k) u
  have huJ : u ∈ ggAutomizer J Bs := by
    show (w : MulAut ↥Bs)⁻¹ ∈ ggAutomizer J Bs
    exact Subgroup.inv_mem _ w.2
  have huK : u ∈ ggAutomizer K Bs := by
    have h2 : Subgroup.closure (Set.range fun j : {j : ΛK // j ≠ aK} => φK j) ≤
        Subgroup.closure (Set.range φK) := by
      rw [Subgroup.closure_le]
      rintro γ ⟨j, rfl⟩
      exact Subgroup.subset_closure ⟨(j : ΛK), rfl⟩
    have h3 : (w : MulAut ↥Bs) ∈ Subgroup.closure (Set.range φK) := h2 (hclosJK ▸ w.2)
    rw [← hclosK] at h3
    simpa [u] using Subgroup.inv_mem _ h3
  have hlam : ∀ i : {i : ΛL // i ≠ bL}, ∃ c : (ZMod p)ˣ,
      hK2 (σ i) = (c : ZMod p) • hL1 i.1 ∧ αK2 (σ i) = (↑(c⁻¹) : ZMod p) • αL i.1 := by
    intro i
    have hf : αL i.1 (hL1 i.1) = 2 := by
      rw [hpairL i.1 i.1, hCLL.1 i.1]
      norm_num
    have hf' : αK2 (σ i) (hK2 (σ i)) = 2 := by
      rw [hpair2 (σ i) (σ i), hCKK.1 (σ i)]
      norm_num
    have hcomm : ∀ v, αL i.1 v • hL1 i.1 = αK2 (σ i) v • hK2 (σ i) := by
      intro v
      have h1 := hlinL i.1 v
      have h2 := hlin2 (σ i) v
      rw [hφ2 i] at h2
      have hh : v - αL i.1 v • hL1 i.1 = v - αK2 (σ i) v • hK2 (σ i) := h1.symm.trans h2
      have hh1 : αL i.1 v • hL1 i.1 - v = αK2 (σ i) v • hK2 (σ i) - v := by
        simpa [neg_sub] using congrArg Neg.neg hh
      simpa [sub_add_cancel] using congrArg (fun t => t + v) hh1
    exact l05nSd_rankOne hp2 hf hf' hcomm
  have hneK : Nonempty {j : ΛK // j ≠ aK} := l05nSd_nonempty hWMJK
  have hdelK : ∀ i j : {j : ΛK // j ≠ aK},
      Relation.ReflTransGen (fun u v : {j : ΛK // j ≠ aK} => u ≠ v ∧ MK0.M u v ≠ 2) i j :=
    fun i j => by simpa [hMJK] using ggRC_weyl_connected hWMJK i j
  obtain ⟨j0, hj0, hj0uniq⟩ := l05nSd_leaf hWMK hCKK aK hdelK hneK
  let j0' : {i : ΛL // i ≠ bL} := σ.symm ⟨j0, hj0.1⟩
  have hσj0' : σ j0' = ⟨j0, hj0.1⟩ := Equiv.apply_symm_apply σ ⟨j0, hj0.1⟩
  let cc : (i : {i : ΛL // i ≠ bL}) → (ZMod p)ˣ := fun i => (hlam i).choose
  have hcc : ∀ i, hK2 (σ i) = (cc i : ZMod p) • hL1 i.1 ∧
      αK2 (σ i) = (↑((cc i)⁻¹) : ZMod p) • αL i.1 := fun i => (hlam i).choose_spec
  have hneigh : ∀ j : {i : ΛL // i ≠ bL}, CK0 aK (σ j) ≠ 0 ↔ j = j0' := by
    intro j
    constructor
    · intro hne0
      have hM : MK0.M aK (σ j).1 ≠ 2 := fun h2 =>
        hne0 ((l05nSd_cartan_eq_zero_iff hCKK (σ j).2.symm).2 h2)
      have h1 : σ j = ⟨j0, hj0.1⟩ := Subtype.ext (hj0uniq (σ j).1 ⟨(σ j).2, hM⟩)
      show j = σ.symm ⟨j0, hj0.1⟩
      rw [← h1, Equiv.symm_apply_apply]
    · intro hj
      have h1 : σ j = ⟨j0, hj0.1⟩ := by rw [hj]; exact Equiv.apply_symm_apply σ _
      rw [h1]
      exact fun h0 => hj0.2 ((l05nSd_cartan_eq_zero_iff hCKK hj0.1.symm).1 h0)
  have hcross1 : ∀ j : {i : ΛL // i ≠ bL},
      (cc j : ZMod p) * αK2 aK (hL1 j.1) = (CK0 aK (σ j) : ZMod p) := by
    intro j
    have h := hpair2 aK (σ j)
    rw [(hcc j).1, map_smul, smul_eq_mul] at h
    exact h
  have hcross2 : ∀ j : {i : ΛL // i ≠ bL},
      (↑((cc j)⁻¹) : ZMod p) * αL j.1 (hK2 aK) = (CK0 (σ j) aK : ZMod p) := by
    intro j
    have h := hpair2 (σ j) aK
    rw [(hcc j).2, LinearMap.smul_apply, smul_eq_mul] at h
    exact h
  let mu : (ZMod p)ˣ := (cc j0')⁻¹
  have hmu : (↑(mu⁻¹) : ZMod p) * (↑((cc j0')⁻¹) : ZMod p) = 1 := by
    have h : mu⁻¹ = cc j0' := by simp [mu]
    rw [h]
    exact Units.mul_inv (cc j0')
  let τ : Option {i : ΛL // i ≠ bL} ≃ ΛK :=
    { toFun := fun o => o.elim aK (fun i => (σ i : ΛK))
      invFun := fun k => if h : k = aK then none else some (σ.symm ⟨k, h⟩)
      left_inv := by
        intro o
        cases o with
        | none => simp
        | some i =>
          have h : ¬ ((σ i : ΛK) = aK) := fun hh => (σ i).2 hh
          show (if h' : (σ i : ΛK) = aK then none
              else some (σ.symm ⟨(σ i : ΛK), h'⟩)) = some i
          rw [dif_neg h]
          have heta : (⟨(σ i : ΛK), h⟩ : {k // k ≠ aK}) = σ i := Subtype.ext rfl
          rw [heta, Equiv.symm_apply_apply]
      right_inv := by
        intro k
        by_cases h : k = aK
        · simp [h]
        · simp only [h, dif_neg, not_false_eq_true, Option.elim_some]
          exact congrArg Subtype.val (Equiv.apply_symm_apply σ ⟨k, h⟩) }
  let MK : CoxeterMatrix (Option {i : ΛL // i ≠ bL}) := MK0.reindex τ.symm
  let CK : Matrix (Option {i : ΛL // i ≠ bL}) (Option {i : ΛL // i ≠ bL}) ℤ :=
    fun o o' => match o, o' with
      | some i, some j => CL i.1 j.1
      | none, some j => CK0 aK (σ j)
      | some i, none => CK0 (σ i) aK
      | none, none => 2
  have hMreindex : GGIsWeylMatrix MK := l05nSd_weyl_reindex hWMK τ.symm
  have hMnone : ∀ j : {i : ΛL // i ≠ bL}, MK none (some j) = MK0 aK (σ j) := by
    intro j
    rw [show MK = MK0.reindex τ.symm from rfl, CoxeterMatrix.reindex_apply, Equiv.symm_symm]
    change MK0.M aK (σ j) = MK0.M aK (σ j)
    rfl
  have hMsome : ∀ i : {i : ΛL // i ≠ bL}, MK (some i) none = MK0 (σ i) aK := by
    intro i
    rw [show MK = MK0.reindex τ.symm from rfl, CoxeterMatrix.reindex_apply, Equiv.symm_symm]
    change MK0.M (σ i) aK = MK0.M (σ i) aK
    rfl
  have hMss : ∀ i j : {i : ΛL // i ≠ bL}, MK (some i) (some j) = ML i.1 j.1 := by
    intro i j
    rw [show MK = MK0.reindex τ.symm from rfl, CoxeterMatrix.reindex_apply, Equiv.symm_symm]
    change MK0.M (σ i) (σ j) = ML i.1 j.1
    rw [← hMJK, horder, hMJL]
  have hCK : GGIntCartan MK CK := by
    constructor
    · intro o
      cases o with
      | none => rfl
      | some i => exact hCLL.1 i.1
    · intro o o' hne
      cases o with
      | none =>
        cases o' with
        | none => exact absurd rfl hne
        | some j =>
          have h := hCKK.2 aK (σ j) (fun hh => (σ j).2 hh.symm)
          rw [hMnone j]
          exact h
      | some i =>
        cases o' with
        | none =>
          have h := hCKK.2 (σ i) aK (fun hh => (σ i).2 hh)
          rw [hMsome i]
          exact h
        | some j =>
          have hij : i ≠ j := fun h => hne (by rw [h])
          have h := hCLL.2 i.1 j.1 (fun hh => hij (Subtype.ext hh))
          rw [hMss i j]
          exact h
  let φfin : Option ΛL → MulAut ↥Bs := fun o => o.elim (φK2 aK) φL
  let hfin : Option ΛL → VL := fun o => o.elim ((mu : ZMod p) • hK2 aK) hL1
  let αfin : Option ΛL → Module.Dual (ZMod p) VL :=
    fun o => o.elim ((↑(mu⁻¹) : ZMod p) • αK2 aK) αL
  have hlin_fin : ∀ o w, ggLin (p := p) ιL (φfin o) w = w - αfin o w • hfin o := by
    intro o w
    cases o with
    | none =>
      show ggLin (p := p) ιL (φK2 aK) w =
        w - ((↑(mu⁻¹) : ZMod p) • αK2 aK) w • ((mu : ZMod p) • hK2 aK)
      have hscal : (↑(mu⁻¹) : ZMod p) * (↑mu : ZMod p) = 1 := Units.inv_mul mu
      have hR : ((↑(mu⁻¹) : ZMod p) • αK2 aK) w • ((mu : ZMod p) • hK2 aK) =
          αK2 aK w • hK2 aK := by
        rw [LinearMap.smul_apply, smul_eq_mul, smul_smul]
        congr 1
        calc (↑(mu⁻¹) : ZMod p) * αK2 aK w * ↑mu
            = αK2 aK w * ((↑(mu⁻¹) : ZMod p) * ↑mu) := by ring
          _ = αK2 aK w * 1 := by rw [hscal]
          _ = αK2 aK w := by rw [mul_one]
      rw [hlin2 aK w, hR]
    | some i =>
      show ggLin (p := p) ιL (φL i) w = w - αL i w • hL1 i
      exact hlinL i w
  have hrefl_fin : ∀ o, GGIsReflection p (φfin o) := by
    intro o
    cases o with
    | none => exact hrefl2 aK
    | some i => exact hreflL i
  have hpairLL_fin : ∀ i j : ΛL, αfin (some i) (hfin (some j)) = (CL i j : ZMod p) :=
    fun i j => hpairL i j
  have hpairCK_fin : ∀ o o' : Option {i : ΛL // i ≠ bL},
      αfin (o.map Subtype.val) (hfin (o'.map Subtype.val)) = (CK o o' : ZMod p) := by
    intro o o'
    simp only [αfin, hfin, CK, Option.map_none, Option.map_some]
    cases o with
    | none =>
      cases o' with
      | none =>
        show ((↑(mu⁻¹) : ZMod p) • αK2 aK) ((mu : ZMod p) • hK2 aK) = ((2 : ℤ) : ZMod p)
        rw [LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, hpair2 aK aK, hCKK.1 aK,
          ← mul_assoc, Units.inv_mul, one_mul]
      | some j =>
        show ((↑(mu⁻¹) : ZMod p) • αK2 aK) (hL1 j.1) = ((CK0 aK (σ j) : ℤ) : ZMod p)
        rw [LinearMap.smul_apply, smul_eq_mul]
        by_cases hj : j = j0'
        · subst hj
          have h1 : (mu⁻¹ : (ZMod p)ˣ) = cc j0' := by simp [mu]
          rw [show (↑(mu⁻¹) : ZMod p) = (cc j0' : ZMod p) from by rw [h1]]
          exact hcross1 j0'
        · have h0 : CK0 aK (σ j) = 0 := by
            by_contra hc
            exact hj ((hneigh j).1 hc)
          have hz : αK2 aK (hL1 j.1) = 0 := by
            have h := hcross1 j
            rw [h0] at h
            exact (mul_eq_zero.mp (by simpa using h)).resolve_left (Units.ne_zero (cc j))
          rw [hz, mul_zero, h0]
          norm_num
    | some i =>
      cases o' with
      | none =>
        show αL i.1 ((mu : ZMod p) • hK2 aK) = ((CK0 (σ i) aK : ℤ) : ZMod p)
        rw [map_smul, smul_eq_mul]
        by_cases hi : i = j0'
        · subst hi
          exact hcross2 j0'
        · have h0' : CK0 aK (σ i) = 0 := by
            by_contra hc
            exact hi ((hneigh i).1 hc)
          have hM : MK0.M aK (σ i).1 = 2 :=
            (l05nSd_cartan_eq_zero_iff hCKK (σ i).2.symm).1 h0'
          have h0 : CK0 (σ i) aK = 0 :=
            (l05nSd_cartan_eq_zero_iff hCKK (σ i).2).2 (by
              rw [MK0.symmetric (σ i).1 aK]; exact hM)
          have hz : αL i.1 (hK2 aK) = 0 := by
            have h := hcross2 i
            rw [h0, Int.cast_zero] at h
            exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero ((cc i)⁻¹))
          rw [hz, mul_zero, h0]
          norm_num
      | some j =>
        exact hpairL i.1 j.1
  have hclosL_fin :
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : ΛL => φfin (some i)) := by
    have h1 : (Set.range fun i : ΛL => φfin (some i)) = Set.range φL := by
      ext γ; constructor <;> rintro ⟨i, rfl⟩ <;> exact ⟨i, rfl⟩
    rw [hclosL, h1]
  have hclosK2 : ggAutomizer K Bs = Subgroup.closure (Set.range φK2) := by
    have hrange : Set.range φK2 = (MulAut.conj u).toMonoidHom '' Set.range φK := by
      ext γ; constructor
      · rintro ⟨k, rfl⟩
        exact ⟨φK k, ⟨k, rfl⟩, (MulAut.conj_apply u (φK k)).symm⟩
      · rintro ⟨γ, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, MulAut.conj_apply u (φK k)⟩
    rw [hrange, ← MonoidHom.map_closure (MulAut.conj u).toMonoidHom (Set.range φK), ← hclosK]
    exact (l05nSd_closure_conj (ggAutomizer K Bs) u huK).symm
  have hrange2 : Set.range φK2 =
      Set.range (fun j : {j : ΛL // j ≠ bL} => φfin (some j.1)) ∪ {φfin none} := by
    have h1 : (fun j : {j : ΛL // j ≠ bL} => φfin (some j.1)) =
        (fun j => φK2 (σ j)) := funext fun j => (hφ2 j).symm
    have h2 : φfin none = φK2 aK := rfl
    rw [h1, h2]
    ext γ; constructor
    · rintro ⟨k, rfl⟩
      by_cases hk : k = aK
      · subst hk; exact Or.inr rfl
      · refine Or.inl ⟨σ.symm ⟨k, hk⟩, ?_⟩
        change φK2 (σ (σ.symm ⟨k, hk⟩)) = φK2 k
        rw [Equiv.apply_symm_apply]
    · rintro (⟨j, rfl⟩ | rfl)
      · exact ⟨σ j, rfl⟩
      · exact ⟨aK, rfl⟩
  have hclosK_fin : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : ΛL // j ≠ bL} => φfin (some j.1)) ∪ {φfin none}) := by
    rw [hclosK2, hrange2]
  have hdelL : GGDeletedConnected ML bL := by
    intro i j
    simpa [hMJL] using ggRC_weyl_connected hWMJL i j
  have hclosJ_fin : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : ΛL // j ≠ bL} => φfin (some j.1)) := by
    have h1 : (Set.range fun j : {j : ΛL // j ≠ bL} => φfin (some j.1)) =
        Set.range (fun j : {j : ΛL // j ≠ bL} => φL j.1) := by
      ext γ; constructor <;> rintro ⟨j, rfl⟩ <;> exact ⟨j, rfl⟩
    rw [hclosJL, h1]
  refine ⟨ΛL, i1L, i2L, bL, ML, CL, MK, CK, VL, i3L, i4L, ιL, φfin, hfin, αfin,
    hWML, hCLL, hMreindex, hCK, trivial, hlin_fin, hrefl_fin, hpairLL_fin, hpairCK_fin,
    trivial, ⟨fL, fun i => hfL i⟩,
    ⟨(MK0.reindexGroupEquiv τ.symm).trans (fK.trans (MulAut.conj ⟨u, huK⟩)), ?_⟩,
    hclosL_fin, hclosK_fin, hdelL, hclosJ_fin⟩
  ·
    intro o
    show ((fK.trans (MulAut.conj ⟨u, huK⟩)) ((MK0.reindexGroupEquiv τ.symm) (MK.simple o)) :
      MulAut ↥Bs) = φfin (o.map Subtype.val)
    rw [show (MK0.reindexGroupEquiv τ.symm) (MK.simple o) = MK0.simple (τ o) from rfl,
      MulEquiv.trans_apply, MulAut.conj_apply]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hfK]
    show u * φK (τ o) * u⁻¹ = φfin (o.map Subtype.val)
    cases o with
    | none => rfl
    | some i =>
      exact hφ2 i

private theorem l05nSd_rowSeven_le_nonLevi {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    (h : GGResRowAt ggRowSeven p J X) : GGResRowAt ggRowNonLevi p J X := by
  obtain ⟨a, c, ha, hc, hJ, hX, hr⟩ := h
  exact ⟨a, c, ha, hc, hJ, hX, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))⟩

theorem ggResModelInput_of_sides (hConj : GGWeylSimpleSystemsConjInput)
    (h : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResSideDatum p Bs L J ∧ GGResSideDatum p Bs K J) ∨
        GGResRowAt ggRowNonLevi p J L ∨ GGResRowAt ggRowNonLevi p J K) :
    GGResModelInput := by
  intro G _ _ p B Bs x L D J y K hH hp
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  rcases h G p B Bs x L D J y K hH with ⟨hL, hK⟩ | hNL | hNK
  · exact Or.inl (ggResLeviDatum_of_sides hConj hp2 hL hK)
  · exact Or.inr (Or.inl hNL)
  · exact Or.inr (Or.inr hNK)

theorem ggResModelInput_of_tbj (hConj : GGWeylSimpleSystemsConjInput) (hJ : GGTBJInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K)) :
    GGResModelInput := by
  apply ggResModelInput_of_sides hConj
  intro G _ _ p B Bs x L D J y K hH hp
  have hJL := (hJ G p B Bs x L D J y K hH).1
  have hJK := (hJ G p B Bs x L D J y K hH).2
  rcases (hX G p B Bs x L D J y K hH).1 with hXL | hSL
  · rcases (hX G p B Bs x L D J y K hH).2 with hXK | hSK
    · rcases hJL hXL with hL | hNL
      · rcases hJK hXK with hK | hNK
        · exact Or.inl ⟨hL, hK⟩
        · exact Or.inr (Or.inr hNK)
      · exact Or.inr (Or.inl hNL)
    · exact Or.inr (Or.inr (l05nSd_rowSeven_le_nonLevi hSK))
  · exact Or.inr (Or.inl (l05nSd_rowSeven_le_nonLevi hSL))

end CFSG.StandardType

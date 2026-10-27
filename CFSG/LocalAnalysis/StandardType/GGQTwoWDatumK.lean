module

public import CFSG.LocalAnalysis.StandardType.GGQTwoWDatum
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112ClassA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GGQ2WDatum

theorem root_eq_zero_of_fix {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2WDatum p) (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod p) {u}) :
    ∀ j : D.Λ, D.root j u = 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : CharP (ZMod p) 3 := by
      rw [← hp]
      infer_instance
    exact two_ne_zero_of_charP_three
  intro j
  have hfixj : D.simpleRefl j u = u :=
    (hfix u).mpr (Submodule.mem_span_singleton_self u) _ (D.simpleRefl_mem_weyl j)
  have hsmul : D.root j u • D.coroot j = 0 := by
    rw [D.simpleRefl_apply] at hfixj
    exact sub_eq_self.mp hfixj
  rcases smul_eq_zero.mp hsmul with h | h
  · exact h
  · exfalso
    exact h2ne (by
      calc (2 : ZMod p) = D.root j (D.coroot j) := (D.root_coroot_self j).symm
        _ = D.root j 0 := by rw [h]
        _ = 0 := map_zero (D.root j))

theorem coroot_not_mem_span_of_fix {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2WDatum p)
    (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod p) {u})
    (j : D.Λ) : D.coroot j ∉ Submodule.span (ZMod p) {u} := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : CharP (ZMod p) 3 := by
      rw [← hp]
      infer_instance
    exact two_ne_zero_of_charP_three
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hKA := D.root_eq_zero_of_fix hp u hfix j
  have h2 : (2 : ZMod p) = 0 := by
    calc (2 : ZMod p) = D.root j (D.coroot j) := (D.root_coroot_self j).symm
      _ = D.root j (c • u) := by rw [← hc]
      _ = c * D.root j u := by rw [map_smul, smul_eq_mul]
      _ = 0 := by rw [hKA, mul_zero]
  exact h2ne h2

theorem eq_zero_of_smul_coroot_mem_span {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2WDatum p)
    (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod p) {u})
    (j : D.Λ) (a : ZMod p) (h : a • D.coroot j ∈ Submodule.span (ZMod p) {u}) : a = 0 := by
  by_contra hne
  apply D.coroot_not_mem_span_of_fix hp u hfix j
  have h1 : D.coroot j = a⁻¹ • (a • D.coroot j) := by
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [h1]
  exact Submodule.smul_mem _ _ h

theorem mem_span_of_root_smul_coroot_mem {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2WDatum p)
    (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod p) {u}) (v : D.V)
    (hv : ∀ j : D.Λ, D.root j v • D.coroot j ∈ Submodule.span (ZMod p) {u}) :
    v ∈ Submodule.span (ZMod p) {u} := by
  have hv0 : ∀ j : D.Λ, D.root j v = 0 := fun j =>
    D.eq_zero_of_smul_coroot_mem_span hp u hfix j _ (hv j)
  have hfixW : ∀ g ∈ D.weyl, g v = v := by
    intro g hg
    refine Subgroup.closure_induction (p := fun x _ => x v = v) ?_ ?_ ?_ ?_ hg
    · rintro x ⟨k, rfl⟩
      rw [D.simpleRefl_apply, hv0 k, zero_smul, sub_zero]
    · rfl
    · intro x y _ _ hx' hy'
      rw [LinearEquiv.mul_apply, hy', hx']
    · intro x _ hx'
      apply x.injective
      rw [hx']
      exact x.apply_symm_apply v
  exact (hfix v).mp hfixW

private lemma ggQ2wd_cast_ne_zero (D : GGQ2WDatum 3) (hcard : 3 ≤ Fintype.card D.Λ)
    {i j : D.Λ} (hij : i ≠ j) (h : D.cartan i j ≠ 0) :
    (D.cartan i j : ZMod 3) ≠ 0 := by
  have hFT : TauCeti.IsFiniteType D.cartan :=
    isFiniteType_of_ggIsWeylMatrixFixed (D.isWeyl : GGIsWeylMatrixFixed D.coxeter) D.isCartan
  have hpre : (TauCeti.diagramGraph D.cartan).Preconnected :=
    (connected_diagramGraph_of_ggIsWeylMatrix (D.isWeyl : GGIsWeylMatrixFixed D.coxeter)
      D.isCartan).preconnected
  have hent : D.cartan i j = -1 ∨ D.cartan i j = -2 := by
    rcases D.isCartan.entries hij with ⟨-, h0, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact absurd h0 h
    · exact Or.inl h1
    · rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h1
      · exfalso
        have hprod : D.cartan i j * D.cartan j i = 3 := by rw [h1, h2]; norm_num
        have hcard2 := hFT.card_eq_two_of_apply_mul_apply_eq_three hpre hprod
        omega
  rcases hent with h1 | h1
  · rw [h1]
    decide
  · rw [h1]
    decide

theorem reflTransGen (D : GGQ2WDatum 3) (hcard : 3 ≤ Fintype.card D.Λ) :
    ∀ i j : D.Λ, Relation.ReflTransGen
      (fun i j : D.Λ => i ≠ j ∧ (D.cartan i j : ZMod 3) ≠ 0) i j := by
  intro i j
  have hGconn : (TauCeti.diagramGraph D.cartan).Connected :=
    connected_diagramGraph_of_ggIsWeylMatrix (D.isWeyl : GGIsWeylMatrixFixed D.coxeter) D.isCartan
  have hrt : Relation.ReflTransGen (TauCeti.diagramGraph D.cartan).Adj i j :=
    (SimpleGraph.reachable_iff_reflTransGen i j).mp (hGconn.preconnected i j)
  refine Relation.ReflTransGen.mono ?_ i j hrt
  intro u v huv
  rw [TauCeti.diagramGraph_adj] at huv
  obtain ⟨huvne, hc, -⟩ := huv
  exact ⟨huvne, ggQ2wd_cast_ne_zero D hcard huvne hc⟩

private lemma ggQ2wd_reflTransGen_eq {α R : Type*} (r : α → α → Prop) (g : α → R)
    (hstep : ∀ a b, r a b → g a = g b) {a b : α} (h : Relation.ReflTransGen r a b) :
    g a = g b := by
  induction h with
  | refl => rfl
  | tail hab hbc ih => exact ih.trans (hstep _ _ hbc)

theorem exists_scalar_of_commute {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2WDatum p)
    (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod p) {u})
    (hconn : ∀ i j : D.Λ, Relation.ReflTransGen
      (fun i j : D.Λ => i ≠ j ∧ (D.cartan i j : ZMod p) ≠ 0) i j)
    (f : D.V →ₗ[ZMod p] D.V)
    (hcomm : ∀ g ∈ D.weyl, ∀ v : D.V, f (g v) - g (f v) ∈ Submodule.span (ZMod p) {u}) :
    ∃ c : ZMod p, ∀ v : D.V, f v - c • v ∈ Submodule.span (ZMod p) {u} := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : CharP (ZMod p) 3 := by
      rw [← hp]
      infer_instance
    exact two_ne_zero_of_charP_three
  obtain ⟨j0⟩ := D.nonempty
  let Cj : D.Λ → ZMod p := fun j => D.root j (f (D.coroot j))
  have hu : ∀ j : D.Λ,
      (2 : ZMod p) • f (D.coroot j) - Cj j • D.coroot j ∈ Submodule.span (ZMod p) {u} := by
    intro j
    have hraw := hcomm (D.simpleRefl j) (D.simpleRefl_mem_weyl j) (D.coroot j)
    have hr : D.simpleRefl j (D.coroot j) = -D.coroot j := by
      rw [D.simpleRefl_apply, D.root_coroot_self j, two_smul]
      abel
    have hrf : D.simpleRefl j (f (D.coroot j)) =
        f (D.coroot j) - D.root j (f (D.coroot j)) • D.coroot j :=
      D.simpleRefl_apply j _
    have hvec : (2 : ZMod p) • f (D.coroot j) - Cj j • D.coroot j =
        -(f (D.simpleRefl j (D.coroot j)) - D.simpleRefl j (f (D.coroot j))) := by
      rw [hr, hrf, map_neg]
      dsimp only [Cj]
      module
    rw [hvec]
    exact Submodule.neg_mem _ hraw
  have hscalar : ∀ (j : D.Λ) (v : D.V), (2 : ZMod p) * D.root j (f v) = Cj j * D.root j v := by
    intro j v
    have hraw := hcomm (D.simpleRefl j) (D.simpleRefl_mem_weyl j) v
    have hr : D.simpleRefl j v = v - D.root j v • D.coroot j := D.simpleRefl_apply j v
    have hrf : D.simpleRefl j (f v) = f v - D.root j (f v) • D.coroot j :=
      D.simpleRefl_apply j (f v)
    have hsum := Submodule.add_mem _
      (Submodule.smul_mem _ (2 : ZMod p) hraw)
      (Submodule.smul_mem _ (D.root j v) (hu j))
    have hw : (2 * D.root j (f v) - D.root j v * Cj j) • D.coroot j ∈
        Submodule.span (ZMod p) {u} := by
      have hvec : (2 * D.root j (f v) - D.root j v * Cj j) • D.coroot j =
          (2 : ZMod p) • (f (D.simpleRefl j v) - D.simpleRefl j (f v)) +
            D.root j v • ((2 : ZMod p) • f (D.coroot j) - Cj j • D.coroot j) := by
        rw [hr, hrf, map_sub, map_smul]
        dsimp only [Cj]
        module
      rw [hvec]
      exact hsum
    have hz := D.eq_zero_of_smul_coroot_mem_span hp u hfix j _ hw
    exact (sub_eq_zero.mp hz).trans (mul_comm (D.root j v) (Cj j))
  have hadj : ∀ i j : D.Λ, (D.cartan i j : ZMod p) ≠ 0 → Cj i = Cj j := by
    intro i j hC
    have h1 : (2 : ZMod p) * D.root i (f (D.coroot j)) = Cj i * (D.cartan i j : ZMod p) := by
      rw [hscalar i (D.coroot j), D.pairing]
    have h2 : (2 : ZMod p) * D.root i (f (D.coroot j)) = Cj j * (D.cartan i j : ZMod p) := by
      have hzero : D.root i ((2 : ZMod p) • f (D.coroot j) - Cj j • D.coroot j) = 0 := by
        obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hu j)
        rw [← hd, map_smul, smul_eq_mul, D.root_eq_zero_of_fix hp u hfix i, mul_zero]
      have hexp : (2 : ZMod p) * D.root i (f (D.coroot j)) -
          Cj j * (D.cartan i j : ZMod p) = 0 := by
        have h := hzero
        rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, D.pairing] at h
        exact h
      exact sub_eq_zero.mp hexp
    exact mul_right_cancel₀ hC (h1.symm.trans h2)
  have hcommon : ∀ j : D.Λ, Cj j = Cj j0 := by
    intro j
    refine ggQ2wd_reflTransGen_eq
      (fun i l : D.Λ => i ≠ l ∧ (D.cartan i l : ZMod p) ≠ 0) Cj ?_ (hconn j j0)
    intro i l hil
    exact hadj i l hil.2
  refine ⟨(2 : ZMod p)⁻¹ * Cj j0, fun v => ?_⟩
  have hw : (2 : ZMod p) • f v - Cj j0 • v ∈ Submodule.span (ZMod p) {u} := by
    refine D.mem_span_of_root_smul_coroot_mem hp u hfix _ (fun j => ?_)
    have hzero : D.root j ((2 : ZMod p) • f v - Cj j0 • v) = 0 := by
      rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hscalar j v, hcommon j]
      exact sub_self _
    rw [hzero, zero_smul]
    exact Submodule.zero_mem _
  have hconv : (2 : ZMod p)⁻¹ • ((2 : ZMod p) • f v - Cj j0 • v) =
      f v - ((2 : ZMod p)⁻¹ * Cj j0) • v := by
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ h2ne, one_smul]
  rw [← hconv]
  exact Submodule.smul_mem _ _ hw

theorem A_or_E6_of_ker (D : GGQ2WDatum 3)
    (hker : ∃ κ : D.Λ → ZMod 3, κ ≠ 0 ∧
      ∀ i : D.Λ, ∑ j : D.Λ, (D.cartan i j : ZMod 3) * κ j = 0)
    (hcard : 3 ≤ Fintype.card D.Λ) :
    (∃ k : ℕ, 2 ≤ k ∧ ∃ e : Fin (3 * k - 1) ≃ D.Λ,
        ∀ i j, D.cartan (e i) (e j) = CartanMatrix.A (3 * k - 1) i j) ∨
      (∃ e : Fin 6 ≃ D.Λ, ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) := by
  obtain ⟨κ, hκ0, hκ⟩ := hker
  have hdet : ∀ {n : ℕ} {T : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ D.Λ),
      (∀ i j, D.cartan (e i) (e j) = T i j) → (T.det : ZMod 3) ≠ 0 → False := by
    intro n T e he hT
    apply hκ0
    have hv : ∀ i, ∑ j, (T i j : ZMod 3) * κ (e j) = 0 := fun i => by
      rw [← hκ (e i)]
      exact Fintype.sum_equiv e _ _ fun j => by rw [he]
    have hmap : ((Int.castRingHom (ZMod 3)).mapMatrix T).det ≠ 0 := by
      rw [← RingHom.map_det]
      exact hT
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero hmap
      (funext fun i => by simpa [Matrix.mulVec, dotProduct] using hv i)
    funext k
    simpa using congrFun h0 (e.symm k)
  have h1 : ((1 : ℤ) : ZMod 3) ≠ 0 := by decide
  have h2 : ((2 : ℤ) : ZMod 3) ≠ 0 := by decide
  rcases ggIntCartan_models D.isWeyl D.isCartan with ⟨n, e, hn, hA | ⟨hn2, hB | hCC⟩ | ⟨hn4, hD⟩⟩ |
    ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF | hF⟩ | ⟨e, hG | hG⟩
  ·
    left
    have hcn : Fintype.card D.Λ = n := by rw [← Fintype.card_congr e, Fintype.card_fin]
    have h3 : ((n + 1 : ℕ) : ZMod 3) = 0 := by
      by_contra h
      refine hdet e hA ?_
      rw [CartanMatrix.A_det]
      push_cast at h ⊢
      exact h
    obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff (n + 1) 3).mp h3
    have hn' : n = 3 * k - 1 := by omega
    subst hn'
    exact ⟨k, by omega, e, hA⟩
  · exact (hdet e hB (by rw [CartanMatrix.B_det (by omega)]; exact h2)).elim
  · exact (hdet e hCC (by rw [CartanMatrix.C_det (by omega)]; exact h2)).elim
  · exact (hdet e hD (by rw [CartanMatrix.D_det (by omega)]; decide)).elim
  · exact Or.inr ⟨e, hE6⟩
  · exact (hdet e hE7 (by rw [CartanMatrix.E₇_det]; exact h2)).elim
  · refine (hdet e hE8 ?_).elim
    have h8 : (CartanMatrix.E 8).det = 1 := by
      rw [CartanMatrix.E_det (by norm_num)]
      norm_num
    rw [h8]
    exact h1
  · exact (hdet e hF (by rw [CartanMatrix.F₄_det]; exact h1)).elim
  · exact (hdet (T := CartanMatrix.F₄.transpose) e hF
      (by rw [Matrix.det_transpose, CartanMatrix.F₄_det]; exact h1)).elim
  · exact (hdet e hG (by rw [CartanMatrix.G₂_det]; exact h1)).elim
  · exact (hdet (T := CartanMatrix.G₂.transpose) e hG
      (by rw [Matrix.det_transpose, CartanMatrix.G₂_det]; exact h1)).elim

end GGQ2WDatum

end CFSG.StandardType

end

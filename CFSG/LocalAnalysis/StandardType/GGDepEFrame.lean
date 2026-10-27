module

public import CFSG.LocalAnalysis.StandardType.GGDepEDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAConfig
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCartan

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem lr7ef_reflTransGen_of_closed {α : Type*} {r : α → α → Prop} {P : α → Prop}
    {a : α} (hcl : ∀ x y, P x → r x y → P y) (ha : P a) :
    ∀ b, Relation.ReflTransGen r a b → P b := by
  intro b hb
  induction hb with
  | refl => exact ha
  | tail hprev hr ih => exact hcl _ _ ih hr

private theorem lr7ef_connected_leaf {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} (hconn : GGDeletedConnected ML b) (e : Fin 6 ≃ Λ)
    (hML : ML = CoxeterMatrix.E₆.reindex e) :
    e.symm b = 0 ∨ e.symm b = 1 ∨ e.symm b = 5 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1, h5⟩ := hcon
  have key : ∀ (S : Finset (Fin 6)) (a v : Fin 6),
      a ≠ e.symm b → v ≠ e.symm b → a ∈ S → v ∉ S →
      (∀ p : Fin 6 × Fin 6, p.1 ∈ S → p.1 ≠ p.2 → CoxeterMatrix.E₆ p.1 p.2 ≠ 2 →
        p.2 ≠ e.symm b → p.2 ∈ S) → False := by
    intro S a v hac hvc haS hvS hcl
    let u : {i : Λ // i ≠ b} := ⟨e a, fun hb => hac (by rw [← hb, Equiv.symm_apply_apply])⟩
    let w : {i : Λ // i ≠ b} := ⟨e v, fun hb => hvc (by rw [← hb, Equiv.symm_apply_apply])⟩
    have hmain : e.symm w.1 ∈ S :=
      lr7ef_reflTransGen_of_closed
        (r := fun x y : {i : Λ // i ≠ b} => x ≠ y ∧ ML.M x.1 y.1 ≠ 2)
        (P := fun z => e.symm z.1 ∈ S)
        (fun x y hx hr => by
          obtain ⟨hne, hM2⟩ := hr
          refine hcl (e.symm x.1, e.symm y.1) hx ?_ ?_ ?_
          · intro hxy
            exact hne (Subtype.ext (e.symm.injective hxy))
          · intro h2
            exact hM2 (by rw [hML, CoxeterMatrix.reindex_apply]; exact h2)
          · intro hyb
            exact y.2 (by
              have := congrArg e hyb
              simpa using this))
        (by simpa [u] using haS) w (hconn u w)
    exact hvS (by simpa [w] using hmain)
  have hv0 : (e.symm b).val ≠ 0 := fun h => h0 (Fin.ext (by simpa using h))
  have hv1 : (e.symm b).val ≠ 1 := fun h => h1 (Fin.ext (by simpa using h))
  have hv5 : (e.symm b).val ≠ 5 := fun h => h5 (Fin.ext (by simpa using h))
  have hlt := (e.symm b).isLt
  have hcases : (e.symm b).val = 2 ∨ (e.symm b).val = 3 ∨ (e.symm b).val = 4 := by omega
  rcases hcases with h2 | h3 | h4
  · have hc : e.symm b = 2 := Fin.ext (by simpa using h2)
    exact key {0} 0 1 (by rw [hc]; decide) (by rw [hc]; decide) (by decide) (by decide)
      (by
        intro p hp hxy hM hy
        rw [hc] at hy
        revert p hp hxy hM hy
        decide +kernel)
  · have hc : e.symm b = 3 := Fin.ext (by simpa using h3)
    exact key {0, 2} 0 1 (by rw [hc]; decide) (by rw [hc]; decide) (by decide) (by decide)
      (by
        intro p hp hxy hM hy
        rw [hc] at hy
        revert p hp hxy hM hy
        decide +kernel)
  · have hc : e.symm b = 4 := Fin.ext (by simpa using h4)
    exact key {0, 1, 2, 3} 0 5 (by rw [hc]; decide) (by rw [hc]; decide) (by decide) (by decide)
      (by
        intro p hp hxy hM hy
        rw [hc] at hy
        revert p hp hxy hM hy
        decide +kernel)

private theorem lr7ef_cartan_of_reindex {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = CoxeterMatrix.E₆.reindex e) :
    ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCL.1]
    fin_cases i <;> decide
  · have heij : e i ≠ e j := fun h => hij (e.injective h)
    have h₂ : GGIntCartan ML (Matrix.reindex e e (CartanMatrix.E 6)) := by
      rw [hML]
      exact GGIntCartan.reindex e ggIntCartan_E₆
    have hMle : ML.M (e i) (e j) ≤ 3 := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      fin_cases i <;> fin_cases j <;> decide
    have h1 := (hCL.pair h₂ heij).2 hMle
    rw [h1.1]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem eq_span_singleton_of_cartan_E6 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    {x : V} (hdim : Module.finrank (ZMod 3) V = 6)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hx : x ≠ 0) (hxker : ∀ i, α i x = 0) :
    (LinearMap.pi α).ker = Submodule.span (ZMod 3) {x} := by
  let F : V →ₗ[ZMod 3] (Fin 6 → ZMod 3) := LinearMap.pi α
  let h' : Fin 6 → F.range := fun i => ⟨F (h i), ⟨h i, rfl⟩⟩
  let α' : Fin 6 → Module.Dual (ZMod 3) F.range :=
    fun i => (LinearMap.proj i).comp F.range.subtype
  have hpair' : ∀ i j, α' i (h' j) = (CartanMatrix.E 6 i j : ZMod 3) := hpair
  have h5 : 5 ≤ Module.finrank (ZMod 3) F.range :=
    (E6QTwo.five_le_finrank_span hpair').trans (Submodule.finrank_le _)
  have hle : Submodule.span (ZMod 3) {x} ≤ F.ker := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    change F x = 0
    funext i
    exact hxker i
  have hx1 : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {x}) = 1 :=
    finrank_span_singleton hx
  have hker1 : Module.finrank (ZMod 3) F.ker = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker F
    have hxle := Submodule.finrank_mono hle
    rw [hdim] at h
    rw [hx1] at hxle
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (hx1.trans hker1.symm)).symm

theorem ggDepE_frame_of_config_of_dim_six {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (hdim : Module.finrank (ZMod p) V = 6)
    {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hCL : GGIntCartan ML CL) (hE : GGIsTypeE6 ML) (hconn : GGDeletedConnected ML b)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hdep : ¬ LinearIndependent (ZMod p) fun i : Λ => h (some i))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i))) :
    ∃ e : Fin 6 ≃ Λ, (e.symm b = 0 ∨ e.symm b = 1 ∨ e.symm b = 5) ∧
      ML = CoxeterMatrix.E₆.reindex e ∧
      (∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j) ∧
      GGDepEFrame p (fun i => h (some (e i))) (fun i => α (some (e i)))
        (ι (Additive.ofMul ⟨x, hx⟩)) := by
  subst hp3
  obtain ⟨e, hML⟩ := hE
  have hcart := lr7ef_cartan_of_reindex e hCL hML
  have hpair : ∀ i j, α (some (e i)) (h (some (e j))) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hL, hcart]
  have hxne : ι (Additive.ofMul ⟨x, hx⟩) ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨x, hx⟩ : Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨x, hx⟩ : Bs) = 1 := congrArg Additive.toMul h1
    exact l05nDD1_x_ne_one hH (congrArg (fun z : Bs => (z : G)) h2)
  have hxker := l05nDD1_alpha_x (by norm_num : (3 : ℕ) ≠ 2) hH hx hφ hL hCL hAL
  refine ⟨e, lr7ef_connected_leaf hconn e hML, hML, hcart, rfl, hpair, hxne,
    (fun i => hxker (e i)), ?_, ?_⟩
  · intro v hv
    have hker := eq_span_singleton_of_cartan_E6 hdim hpair hxne (fun i => hxker (e i))
    rw [← hker, LinearMap.mem_ker]
    funext i
    exact hv i
  · intro hli
    exact hdep ((linearIndependent_equiv (R := ZMod 3) e).mp hli)

theorem ggDepE_frame_of_config (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} (hCL : GGIntCartan ML CL)
    (hE : GGIsTypeE6 ML) (hconn : GGDeletedConnected ML b)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hdep : ¬ LinearIndependent (ZMod p) fun i : Λ => h (some i))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i))) :
    ∃ e : Fin 6 ≃ Λ, (e.symm b = 0 ∨ e.symm b = 1 ∨ e.symm b = 5) ∧
      (∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j) ∧
      GGDepEFrame p (fun i => h (some (e i))) (fun i => α (some (e i)))
        (ι (Additive.ofMul ⟨x, hx⟩)) := by
  classical
  obtain ⟨e, hML⟩ := hE
  have hcart := lr7ef_cartan_of_reindex e hCL hML
  refine ⟨e, lr7ef_connected_leaf hconn e hML, hcart, ?_⟩
  have hx1 : (⟨x, hx⟩ : Bs) ≠ 1 := by
    intro h1
    exact l05nDD1_x_ne_one hH (by simpa using congrArg Subtype.val h1)
  have hx'ne : ι (Additive.ofMul ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hx1
    have h1 : Additive.ofMul (⟨x, hx⟩ : Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨x, hx⟩ : Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  have halpha := l05nDD1_alpha_x (p := p) hp2 hH hx hφ hL hCL hAL
  refine ⟨hp3, ?_, hx'ne, ?_, ?_, ?_⟩
  · intro i j
    rw [hL (e i) (e j), hcart i j]
  · intro i
    exact halpha (e i)
  · intro v hv
    exact l05nDD1_fix hFix hH hx hφ hAL v (fun j => by
      have hj := hv (e.symm j)
      simpa using hj)
  · intro hli
    exact hdep ((linearIndependent_equiv (R := ZMod p) e).mp hli)

end CFSG.StandardType

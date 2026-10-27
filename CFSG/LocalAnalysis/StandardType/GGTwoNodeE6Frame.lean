module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6DepAllDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6AllDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e6F_x_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : x ≠ 1 := by
  intro hx1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by rw [hDgen]; exact Subgroup.subset_closure (by simp)
  have hyp : y ^ p = 1 := hDea.2 y hyD
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hDgen, hx1, Subgroup.closure_le]
    intro a ha
    have ha' : a = 1 ∨ a = y := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers y
  have hyle : Nat.card (Subgroup.zpowers y) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hyp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
      _ ≤ p := hyle
  nlinarith [hcon, hp.two_le]

private theorem e6F_automizer_fixes_x {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hxBs : x ∈ Bs) :
    ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  have hcent : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hle : ggAutomizer L Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs) := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro ψ hψ
    obtain ⟨g, hgL, -, hg⟩ := hψ
    have hmem : g ∈ Subgroup.centralizer ({x} : Set G) := hcent hgL
    have hcomm : g * x = x * g :=
      ((Subgroup.mem_centralizer_iff.mp hmem) x (by simp)).symm
    change ψ • (⟨x, hxBs⟩ : ↥Bs) = (⟨x, hxBs⟩ : ↥Bs)
    rw [MulAut.smul_def]
    apply Subtype.ext
    have h : ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = g * x * g⁻¹ := by
      have h1 := hg (⟨x, hxBs⟩ : ↥Bs)
      simpa using h1
    rw [h, hcomm]
    group
  intro ψ hψ
  simpa only [MulAction.mem_stabilizer_iff, MulAut.smul_def] using hle hψ

private theorem e6F_alpha_x {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {Λ : Type} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α i (h j) = (CL i j : ZMod p))
    (hCL : GGIntCartan ML CL)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    ∀ j : Λ, α j (ι (Additive.ofMul ⟨x, hx⟩)) = 0 := by
  intro j
  have hfix := e6F_automizer_fixes_x hH.1 hx
  have hmem : φ j ∈ ggAutomizer L Bs := by
    rw [hAL]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hfixj : φ j ⟨x, hx⟩ = ⟨x, hx⟩ := hfix (φ j) hmem
  have hlin : ggLin (p := p) ι (φ j) (ι (Additive.ofMul ⟨x, hx⟩)) =
      ι (Additive.ofMul ⟨x, hx⟩) :=
    (ggLin_fix_iff (p := p) ι (φ j) ⟨x, hx⟩).mp hfixj
  have h1 := hφ j (ι (Additive.ofMul ⟨x, hx⟩))
  rw [hlin] at h1
  have h2 : α j (ι (Additive.ofMul ⟨x, hx⟩)) • h j = 0 :=
    sub_eq_self.mp h1.symm
  have h3 : α j (α j (ι (Additive.ofMul ⟨x, hx⟩)) • h j) = 0 := by
    rw [h2, map_zero]
  have hpair : α j (h j) = (2 : ZMod p) := by
    rw [hL j j, hCL.1 j]
    norm_num
  rw [map_smul, smul_eq_mul, hpair] at h3
  exact (mul_eq_zero.mp h3).resolve_right (zmod_two_ne_zero hp2)


theorem ggIndep_cartan_of_reindexE6 {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = CoxeterMatrix.E₆.reindex e) :
    ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j := by
  intro i j
  have hlab : ∀ a b : Fin 6, a ≠ b → CoxeterMatrix.E₆ a b = 2 ∨ CoxeterMatrix.E₆ a b = 3 := by
    intro a
    fin_cases a <;> decide
  by_cases hij : i = j
  · subst hij
    rw [hCL.1, ggIntCartan_E₆.1]
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hentry : ML (e i) (e j) = CoxeterMatrix.E₆ i j := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have h1 := hCL.2 (e i) (e j) hne
    have h2 := ggIntCartan_E₆.2 i j hij
    have hl := hlab i j hij
    rw [hentry] at h1
    rcases h1 with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, -, -, -⟩ | ⟨ha, -, -, -⟩ <;>
      rcases h2 with ⟨ha', hb', hc'⟩ | ⟨ha', hb', hc'⟩ | ⟨ha', -, -, -⟩ | ⟨ha', -, -, -⟩ <;>
      first | (exfalso; omega) | (rw [hb, hb'])

theorem e6F_cartan_kernel (j : Fin 6) :
    (CartanMatrix.E 6 j 0 : ZMod 3) - (CartanMatrix.E 6 j 2 : ZMod 3) + (CartanMatrix.E 6 j 4 : ZMod 3) -
      (CartanMatrix.E 6 j 5 : ZMod 3) = 0 := by
  have hint : ((3 : ℕ) : ℤ) ∣ CartanMatrix.E 6 j 0 - CartanMatrix.E 6 j 2 + CartanMatrix.E 6 j 4 -
      CartanMatrix.E 6 j 5 := by
    fin_cases j <;> decide
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (CartanMatrix.E 6 j 0 - CartanMatrix.E 6 j 2 + CartanMatrix.E 6 j 4 - CartanMatrix.E 6 j 5) 3).mpr
    hint
  push_cast at h
  exact h

theorem ggIndepE6_x_mem_span {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {h : Fin 6 → V}
    {α : Fin 6 → Module.Dual (ZMod 3) V} {x : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hfix : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod 3) {x}) :
    x ∈ Submodule.span (ZMod 3) (Set.range h) := by
  classical
  let v : V := h 0 - h 2 + h 4 - h 5
  have hv_mem : v ∈ Submodule.span (ZMod 3) (Set.range h) :=
    Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _
      (Submodule.subset_span ⟨0, rfl⟩) (Submodule.subset_span ⟨2, rfl⟩))
      (Submodule.subset_span ⟨4, rfl⟩)) (Submodule.subset_span ⟨5, rfl⟩)
  have hv_ker : ∀ j, α j v = 0 := by
    intro j
    simp only [v, map_sub, map_add, hpair]
    exact e6F_cartan_kernel j
  have hv_ne : v ≠ 0 := by
    intro h0
    have hsum : ∑ i : Fin 6, (fun i : Fin 6 => if i = 0 then (1 : ZMod 3) else if i = 2 then -1
        else if i = 4 then 1 else if i = 5 then -1 else 0) i • h i = 0 := by
      rw [Fin.sum_univ_six]
      simp only [v] at h0
      simp
      first
        | (rw [sub_eq_add_neg, sub_eq_add_neg] at h0; exact h0)
        | (rw [← h0]; abel)
        | (rw [← sub_eq_zero] at h0; rw [← h0]; abel)
        | (simpa [sub_eq_add_neg] using h0)
    have h2 := (Fintype.linearIndependent_iff.mp hind)
      (fun i : Fin 6 => if i = 0 then (1 : ZMod 3) else if i = 2 then -1
        else if i = 4 then 1 else if i = 5 then -1 else 0) hsum 0
    simp at h2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hfix v hv_ker)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv_ne
    rw [← hc, zero_smul]
  have hx : x = c⁻¹ • v := by
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hx]
  exact Submodule.smul_mem _ _ hv_mem

private theorem ggXDatumE6_common (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hML : ML = CoxeterMatrix.E₆.reindex e) (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    (∀ i j, α (e i) (h (e j)) = (CartanMatrix.E 6 i j : ZMod p)) ∧
      (ι (Additive.ofMul ⟨x, hx⟩) ≠ 0) ∧
      (∀ i : Fin 6, α (e i) (ι (Additive.ofMul ⟨x, hx⟩)) = 0) ∧
      (∀ v : V, (∀ i : Fin 6, α (e i) v = 0) →
        v ∈ Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hpair (e i) (e j), ggIndep_cartan_of_reindexE6 e hCL hML i j]
  · intro h0
    have hx1 : (⟨x, hx⟩ : Bs) ≠ 1 := by
      intro h1
      exact e6F_x_ne_one hH (by simpa using congrArg Subtype.val h1)
    apply hx1
    have h1 : Additive.ofMul (⟨x, hx⟩ : Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨x, hx⟩ : Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  · intro i
    exact e6F_alpha_x hp2 hH hx hφ hpair hCL hAL (e i)
  · intro v hv
    exact ggIndep_fixL hFix hH hx hφ hAL v (fun j => by
      have hj := hv (e.symm j)
      simpa using hj)

theorem ggXDatumE6_indep_frame (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hML : ML = CoxeterMatrix.E₆.reindex e) (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGIndepE6Frame (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)) := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hpair', hx_ne, hx_ker, hfix'⟩ :=
    ggXDatumE6_common hFix hp2 hH hx e hML hCL hφ hpair hAL
  have hind' : LinearIndependent (ZMod p) (fun i => h (e i)) :=
    (linearIndependent_equiv (R := ZMod p) e).mpr hind
  refine ⟨hpair', hind', hx_ne, hx_ker, ?_⟩
  subst hp3
  exact ggIndepE6_x_mem_span hpair' hind' hfix'

theorem ggXDatumE6_dep_frame (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hML : ML = CoxeterMatrix.E₆.reindex e) (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hdep : ¬ LinearIndependent (ZMod p) h) :
    GGDepE6Frame (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)) := by
  classical
  obtain ⟨hpair', hx_ne, hx_ker, hfix'⟩ :=
    ggXDatumE6_common hFix hp2 hH hx e hML hCL hφ hpair hAL
  refine ⟨hpair', hx_ne, hx_ker, hfix', ?_⟩
  intro hli
  exact hdep ((linearIndependent_equiv (R := ZMod p) e).mp hli)

end CFSG.StandardType

end

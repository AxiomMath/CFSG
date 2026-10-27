module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDepBasic
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepKer
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepLeaf
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIITypes
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def lr7ds_rho : Fin 6 → ZMod 3 := ![1, 0, 2, 0, 1, 2]

private theorem lr7ds_rho_eq_zero {q : Fin 6} (h : lr7ds_rho q = 0) : q = 1 ∨ q = 3 := by
  revert h
  revert q
  decide +kernel

private theorem lr7ds_kernel_rho (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (d : D.ι → ZMod 3)
    (hd : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * d j = 0) :
    ∀ q : Fin 6, d (e q) = d (e 0) * lr7ds_rho q := by
  obtain ⟨h1, h3, h2, h4, h5⟩ := ggQ2_caseII_kernel_E6 D e hE d hd
  intro q
  fin_cases q <;> simp [lr7ds_rho, h1, h2, h3, h4, h5, mul_comm]

private theorem lr7ds_ker_of_relation (D : GGQ2Lin 3)
    (e : Fin 6 ≃ D.ι) (hE : D.coxeter = CoxeterMatrix.E₆.reindex e)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i)
    (he0 : e 0 ≠ D.a) (d : {k // k ≠ D.a} → ZMod 3)
    (hrel : (∑ k, d k • D.root k) = 0) (h0 : d ⟨e 0, he0⟩ = 0) :
    d = 0 := by
  classical
  let d' : D.ι → ZMod 3 := fun i => if h : i ≠ D.a then d ⟨i, h⟩ else 0
  have hd'e0 : d' (e 0) = 0 := by
    simp only [d']; rw [dif_pos he0]; exact h0
  have hleft : ∀ j, ∑ i, d' i * (D.cartan i j : ZMod 3) = 0 := by
    intro j
    have hpairs : (∑ k : {k // k ≠ D.a}, d k * (D.cartan k.val j : ZMod 3)) = 0 := by
      have h := congrArg (fun φ : Dual (ZMod 3) D.V => φ (D.coroot j)) hrel
      simpa [Finset.sum_apply, LinearMap.smul_apply, D.pairing, smul_eq_mul] using h
    have hsub : (∑ k : {k // k ≠ D.a}, d k * (D.cartan k.val j : ZMod 3))
        = ∑ i ∈ Finset.univ.filter (fun i => i ≠ D.a), d' i * (D.cartan i j : ZMod 3) := by
      rw [← Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset D.ι))
        (f := fun i => d' i * (D.cartan i j : ZMod 3)) (p := fun i => i ≠ D.a)]
      simp [d']
      apply Finset.sum_congr rfl
      intro x _
      rw [if_neg x.2]
    have hfull : (∑ i ∈ Finset.univ.filter (fun i => i ≠ D.a), d' i * (D.cartan i j : ZMod 3))
        = ∑ i, d' i * (D.cartan i j : ZMod 3) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ≠ D.a
      · rw [if_pos hi]
      · rw [if_neg hi]
        have hdi : d' i = 0 := by simp only [d']; exact dif_neg hi
        rw [hdi, zero_mul]
    rw [← hfull, ← hsub]
    exact hpairs
  have hright : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * d' j = 0 := by
    intro i
    have h := hleft i
    calc ∑ j, (D.cartan i j : ZMod 3) * d' j
        = ∑ j, d' j * (D.cartan j i : ZMod 3) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_comm, hsym i j]
      _ = 0 := h
  have hcoord := lr7ds_kernel_rho D e hE d' hright
  have hd'zero : ∀ q : Fin 6, d' (e q) = 0 := by
    intro q
    rw [hcoord q, hd'e0, zero_mul]
  funext k
  simp only [Pi.zero_apply]
  have hdk : d' k.val = d k := by
    simp only [d']; rw [dif_pos k.2]
  rw [← hdk, ← e.apply_symm_apply k.val]
  exact hd'zero (e.symm k.val)

private theorem lr7ds_card_iota (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) :
    Fintype.card D.ι = 6 := by
  rw [← Fintype.card_congr e, Fintype.card_fin]

private theorem lr7ds_card_lambda (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) :
    Fintype.card {k // k ≠ D.a} = 5 := by
  have hι : Fintype.card D.ι = 6 := lr7ds_card_iota D e
  rw [Fintype.card_subtype_compl (fun k => k = D.a), Fintype.card_subtype_eq]
  omega

private theorem lr7ds_six_roots_aux (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (e : Fin 6 ≃ D.ι) (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (ha : D.a = e 1)
    (hdim : Module.finrank (ZMod 3) D.V = 6) (x : D.V) (hx0 : x ≠ 0)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {x}) :
    LinearIndependent (ZMod 3) D.root := by
  have hcard_Λ : Fintype.card {k // k ≠ D.a} = 5 := lr7ds_card_lambda D e
  have hspan_Λ : Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range (fun k : {k // k ≠ D.a} => D.root k))) = 5 := by
    have h := ggQ2_dep_finrank_eq D x hx0 hx
    rw [hdim] at h
    omega
  have hLI_Λ : LinearIndependent (ZMod 3) (fun k : {k // k ≠ D.a} => D.root k) := by
    rw [linearIndependent_iff_card_le_finrank_span, hcard_Λ]
    change 5 ≤ Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range (fun k : {k // k ≠ D.a} => D.root k)))
    rw [hspan_Λ]
  by_contra hnotLI
  rcases Fintype.not_linearIndependent_iff.mp hnotLI with ⟨d, hdsum, hdnz⟩
  have hcart := ggQ2xQ_cartan_E6 D e hE
  have hsym : ∀ i j, D.cartan i j = D.cartan j i := by
    intro i j
    obtain ⟨p, rfl⟩ := e.surjective i
    obtain ⟨q, rfl⟩ := e.surjective j
    rw [hcart p q, hcart q p]
    exact congrFun (congrFun (CartanMatrix.E_transpose 6) q) p
  have hdright : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * d j = 0 := by
    intro i
    have h := congrArg (fun φ : Dual (ZMod 3) D.V => φ (D.coroot i)) hdsum
    have hleft_i : ∑ j, d j * (D.cartan j i : ZMod 3) = 0 := by
      simpa [Finset.sum_apply, LinearMap.smul_apply, D.pairing, smul_eq_mul] using h
    calc ∑ j, (D.cartan i j : ZMod 3) * d j
        = ∑ j, d j * (D.cartan j i : ZMod 3) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_comm, hsym i j]
      _ = 0 := hleft_i
  have hcoord := lr7ds_kernel_rho D e hE d hdright
  have hda : d D.a = 0 := by
    rw [ha]
    have h := hcoord 1
    simpa [lr7ds_rho] using h
  have hd'ne : (fun k : {k // k ≠ D.a} => d k.val) ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := hdnz
    apply hi
    by_cases hia : i = D.a
    · rw [hia]; exact hda
    · exact congrFun h ⟨i, hia⟩
  have hd'sum : (∑ k : {k // k ≠ D.a}, d k.val • D.root k.val) = 0 := by
    have hfull : (∑ k ∈ Finset.univ.filter (fun k => k ≠ D.a), d k • D.root k)
        = ∑ k, d k • D.root k := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = D.a
      · subst hk; rw [if_neg (by simp), hda, zero_smul]
      · rw [if_pos hk]
    have hsub : (∑ k : {k // k ≠ D.a}, d k.val • D.root k.val)
        = ∑ k ∈ Finset.univ.filter (fun k => k ≠ D.a), d k • D.root k := by
      rw [← Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset D.ι))
        (f := fun k => d k • D.root k) (p := fun k => k ≠ D.a)]
      simp
    rw [hsub, hfull, hdsum]
  have hli := Fintype.linearIndependent_iff.mp hLI_Λ (fun k : {k // k ≠ D.a} => d k.val) hd'sum
  exact hd'ne (funext hli)

private theorem lr7ds_dual_apply_eq_zero (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (v : D.V) (hφ : ∀ φ : Dual (ZMod 3) D.V, φ v = 0) : v = 0 := by
  have hann : (Submodule.span (ZMod 3) {v}).dualAnnihilator = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro φ
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hφ φ, smul_zero]
  have hbot : Submodule.span (ZMod 3) {v} = ⊥ := (Submodule.dualAnnihilator_eq_top_iff).mp hann
  have : v ∈ (⊥ : Submodule (ZMod 3) D.V) := by
    rw [← hbot]
    exact Submodule.subset_span (Set.mem_singleton v)
  simpa using this

theorem ggQ2_dep_types (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (hB : ¬ D.Basis) (hII : ¬ D.CaseII) (_h4 : 4 ≤ Module.finrank (ZMod 3) D.V) (x y : D.V)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hy : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.b}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {y}) :
    ∃ e : Fin 6 ≃ D.ι, D.coxeter = CoxeterMatrix.E₆.reindex e ∧
      (∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) ∧ D.a = e 1 ∧
      ¬ LinearIndependent (ZMod 3) (fun k : {k // k ≠ D.a} => D.coroot k) ∧
      (Module.finrank (ZMod 3) D.V = 6 ∨ (Module.finrank (ZMod 3) D.V = 5 ∧ D.b = e 3)) := by
  have hsurv : ∃ e : Fin 6 ≃ D.ι, D.coxeter = CoxeterMatrix.E₆.reindex e ∧
      (∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) ∧ D.a = e 1 := by
    by_contra h
    have hR : ∀ d : D.ι → ZMod 3,
        (∀ i, ∑ j, (D.cartan i j : ZMod 3) * d j = 0) → d D.a = 0 → d = 0 := by
      intro d hd hda
      by_contra hd0
      obtain ⟨e', hE', hcart', ha'⟩ := ggQ2_dep_ker_right D d hd hda hd0
      exact h ⟨e', hE', hcart', ha'.symm⟩
    have hL : ∀ d : D.ι → ZMod 3,
        (∀ j, ∑ i, d i * (D.cartan i j : ZMod 3) = 0) → d D.a = 0 → d = 0 := by
      intro d hd hda
      by_contra hd0
      obtain ⟨e', hE', hcart', ha'⟩ := ggQ2_dep_ker_left D d hd hda hd0
      exact h ⟨e', hE', hcart', ha'.symm⟩
    rcases ggQ2_dep_basis_or_caseII D x hx0 hx hR hL with hb | hii
    · exact hB hb
    · exact hII hii
  obtain ⟨e, hE, hcart, ha⟩ := hsurv
  have hsym : ∀ i j, D.cartan i j = D.cartan j i := by
    intro i j
    obtain ⟨p, rfl⟩ := e.surjective i
    obtain ⟨q, rfl⟩ := e.surjective j
    rw [hcart p q, hcart q p]
    exact congrFun (congrFun (CartanMatrix.E_transpose 6) q) p
  obtain ⟨c, hc0, hcsum, hcrow⟩ := ggQ2_dep_relation D x hx hB
  have hca : c D.a = 0 := by
    rw [ha]
    exact (ggQ2_caseII_kernel_E6 D e hE c hcrow).1
  have hnotLI : ¬ LinearIndependent (ZMod 3) (fun k : {k // k ≠ D.a} => D.coroot k) := by
    refine Fintype.not_linearIndependent_iff.mpr ⟨fun k : {k // k ≠ D.a} => c k.val, ?_, ?_⟩
    · have hfull : (∑ k ∈ Finset.univ.filter (fun k => k ≠ D.a), c k • D.coroot k)
          = ∑ k, c k • D.coroot k := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = D.a
        · subst hk; rw [if_neg (by simp), hca, zero_smul]
        · rw [if_pos hk]
      have hsub : (∑ k : {k // k ≠ D.a}, c k.val • D.coroot k.val)
          = ∑ k ∈ Finset.univ.filter (fun k => k ≠ D.a), c k • D.coroot k := by
        rw [← Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset D.ι))
          (f := fun k => c k • D.coroot k) (p := fun k => k ≠ D.a)]
        simp
      rw [hsub, hfull, hcsum]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hc0
      by_cases hia : i = D.a
      · exact absurd (by rw [hia]; exact hca) hi
      · exact ⟨⟨i, hia⟩, hi⟩
  have he0 : e 0 ≠ D.a := by
    intro h
    have h01 : (0 : Fin 6) = 1 := e.injective (h.trans ha)
    exact (by decide : (0 : Fin 6) ≠ 1) h01
  let F : ({k // k ≠ D.a} → ZMod 3) →ₗ[ZMod 3] Dual (ZMod 3) D.V :=
    Fintype.linearCombination (ZMod 3) (fun k : {k // k ≠ D.a} => D.root k)
  have hker_le : Module.finrank (ZMod 3) F.ker ≤ 1 := by
    let ev : F.ker →ₗ[ZMod 3] ZMod 3 :=
      { toFun := fun d => d.1 ⟨e 0, he0⟩
        map_add' := by intro a b; rfl
        map_smul' := by intro a b; rfl }
    have h_inj : Function.Injective ev := by
      intro u w huw
      apply Subtype.ext
      have hu0 : (u.1 - w.1) ⟨e 0, he0⟩ = 0 := by
        have h : u.1 ⟨e 0, he0⟩ = w.1 ⟨e 0, he0⟩ := huw
        simp [h]
      have hrel : (∑ k, (u.1 - w.1) k • D.root k) = 0 := by
        have hz : F (u.1 - w.1) = 0 := by rw [map_sub, u.2, w.2, sub_zero]
        rwa [Fintype.linearCombination_apply] at hz
      exact sub_eq_zero.mp (lr7ds_ker_of_relation D e hE hsym he0 (u.1 - w.1) hrel hu0)
    have := LinearMap.finrank_le_finrank_of_injective (f := ev) h_inj
    simpa using this
  have hrange : F.range = Submodule.span (ZMod 3)
      (Set.range (fun k : {k // k ≠ D.a} => D.root k)) := by
    simp [F]
  have hdom : Module.finrank (ZMod 3) ({k // k ≠ D.a} → ZMod 3) = 5 := by
    rw [finrank_fintype_fun_eq_card, lr7ds_card_lambda D e]
  have hrank_ge : 4 ≤ Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range (fun k : {k // k ≠ D.a} => D.root k))) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker F
    rw [hdom, hrange] at hrn
    omega
  have hfin_ge : 5 ≤ Module.finrank (ZMod 3) D.V := by
    have heq := ggQ2_dep_finrank_eq D x hx0 hx
    omega
  have hfin_le : Module.finrank (ZMod 3) D.V ≤ 6 := by
    have h := ggQ2_dep_finrank_le D x hx
    rwa [lr7ds_card_iota D e] at h
  have hcard_ι : Fintype.card D.ι = 6 := lr7ds_card_iota D e
  have hb_eq : Module.finrank (ZMod 3) D.V ≠ 6 → D.b = e 3 := by
    intro h6
    have h5 : Module.finrank (ZMod 3) D.V = 5 := by omega
    have hcard_Λb : Fintype.card {k // k ≠ D.b} = 5 := by
      rw [Fintype.card_subtype_compl (fun k => k = D.b), Fintype.card_subtype_eq, hcard_ι]
    have hyi : ∀ k : {k // k ≠ D.b}, D.root k y = 0 := by
      have hyfix : ∀ g ∈ D.parab {k | k ≠ D.b}, g y = y :=
        (hy y).mpr (Submodule.subset_span (Set.mem_singleton y))
      intro k
      exact (ggQ2_dep_fixed_iff D {k | k ≠ D.b} y).mp hyfix k k.2
    have hnotLI_Λb : ¬ LinearIndependent (ZMod 3) (fun k : {k // k ≠ D.b} => D.root k) := by
      intro hLI
      have : Nonempty {k // k ≠ D.b} := ⟨⟨D.a, D.a_ne_b⟩⟩
      have hspan_top : Submodule.span (ZMod 3)
          (Set.range (fun k : {k // k ≠ D.b} => D.root k)) = ⊤ := by
        refine LinearIndependent.span_eq_top_of_card_eq_finrank hLI ?_
        rw [hcard_Λb, Subspace.dual_finrank_eq (K := ZMod 3) (V := D.V), h5]
      have hykill : ∀ φ : Dual (ZMod 3) D.V, φ y = 0 := by
        intro φ
        have hmem : φ ∈ Submodule.span (ZMod 3)
            (Set.range (fun k : {k // k ≠ D.b} => D.root k)) := by rw [hspan_top]; trivial
        rw [Submodule.mem_span_range_iff_exists_fun] at hmem
        obtain ⟨cc, hcc⟩ := hmem
        have hz : (∑ i, cc i • D.root i) y = 0 := by
          simp [Finset.sum_apply, hyi]
        rwa [hcc] at hz
      exact hy0 (lr7ds_dual_apply_eq_zero D y hykill)
    rcases Fintype.not_linearIndependent_iff.mp hnotLI_Λb with ⟨g, hgsum, g0, hg0⟩
    let g' : D.ι → ZMod 3 := fun i => if h : i ≠ D.b then g ⟨i, h⟩ else 0
    have hg'left : ∀ j, ∑ i, g' i * (D.cartan i j : ZMod 3) = 0 := by
      intro j
      have hpairs : (∑ k : {k // k ≠ D.b}, g k * (D.cartan k.val j : ZMod 3)) = 0 := by
        have h := congrArg (fun φ : Dual (ZMod 3) D.V => φ (D.coroot j)) hgsum
        simpa [Finset.sum_apply, LinearMap.smul_apply, D.pairing, smul_eq_mul] using h
      have hsub : (∑ k : {k // k ≠ D.b}, g k * (D.cartan k.val j : ZMod 3))
          = ∑ i ∈ Finset.univ.filter (fun i => i ≠ D.b), g' i * (D.cartan i j : ZMod 3) := by
        rw [← Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset D.ι))
          (f := fun i => g' i * (D.cartan i j : ZMod 3)) (p := fun i => i ≠ D.b)]
        simp [g']
        apply Finset.sum_congr rfl
        intro x _
        rw [if_neg x.2]
      have hfull : (∑ i ∈ Finset.univ.filter (fun i => i ≠ D.b), g' i * (D.cartan i j : ZMod 3))
          = ∑ i, g' i * (D.cartan i j : ZMod 3) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ≠ D.b
        · rw [if_pos hi]
        · rw [if_neg hi]
          have hgi : g' i = 0 := by simp only [g']; exact dif_neg hi
          rw [hgi, zero_mul]
      rw [← hfull, ← hsub]
      exact hpairs
    have hg'right : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * g' j = 0 := by
      intro i
      have h := hg'left i
      calc ∑ j, (D.cartan i j : ZMod 3) * g' j
          = ∑ j, g' j * (D.cartan j i : ZMod 3) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [mul_comm, hsym i j]
        _ = 0 := h
    have hg'coord := lr7ds_kernel_rho D e hE g' hg'right
    have hg'ne : g' ≠ 0 := by
      intro h
      apply hg0
      have hk0 : g' g0.val = 0 := by rw [h]; rfl
      simp only [g'] at hk0
      rw [dif_pos g0.2] at hk0
      simpa using hk0
    have hg'b : g' D.b = 0 := by
      simp only [g']; exact dif_neg (fun h : D.b ≠ D.b => h rfl)
    have hq0 : g' (e (e.symm D.b)) = 0 := by
      rw [e.apply_symm_apply]; exact hg'b
    have hg'0 : g' (e 0) ≠ 0 := by
      intro h0
      apply hg'ne
      funext i
      obtain ⟨p, rfl⟩ := e.surjective i
      simp [hg'coord p, h0]
    have hq : e.symm D.b = 1 ∨ e.symm D.b = 3 := by
      have h := hg'coord (e.symm D.b)
      rw [hq0] at h
      have hrho : lr7ds_rho (e.symm D.b) = 0 :=
        (mul_eq_zero.mp h.symm).resolve_left hg'0
      exact lr7ds_rho_eq_zero hrho
    rcases hq with hq1 | hq3
    · exfalso
      have : D.b = D.a := by rw [← e.apply_symm_apply D.b, hq1, ha]
      exact D.a_ne_b this.symm
    · rw [← e.apply_symm_apply D.b, hq3]
  refine ⟨e, hE, hcart, ha, hnotLI, ?_⟩
  by_cases h6 : Module.finrank (ZMod 3) D.V = 6
  · exact Or.inl h6
  · exact Or.inr ⟨by omega, hb_eq h6⟩

theorem ggQ2_dep_six_roots (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (e : Fin 6 ≃ D.ι) (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (ha : D.a = e 1)
    (hdim : Module.finrank (ZMod 3) D.V = 6) (x : D.V) (hx0 : x ≠ 0)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x}) :
    ∀ v : D.V, (∀ k, D.root k v = 0) → v = 0 := by
  have hLI := lr7ds_six_roots_aux D e hE ha hdim x hx0 hx
  have : Nonempty D.ι := ⟨D.a⟩
  have hspan_top : Submodule.span (ZMod 3) (Set.range D.root) = ⊤ := by
    refine LinearIndependent.span_eq_top_of_card_eq_finrank hLI ?_
    rw [lr7ds_card_iota D e, Subspace.dual_finrank_eq (K := ZMod 3) (V := D.V), hdim]
  intro v hv
  apply lr7ds_dual_apply_eq_zero D v
  intro φ
  have hmem : φ ∈ Submodule.span (ZMod 3) (Set.range D.root) := by rw [hspan_top]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hz : (∑ i, c i • D.root i) v = 0 := by
    simp [Finset.sum_apply, hv]
  rwa [hc] at hz

theorem ggQ2_e6_finrank (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V] (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (ha : D.a = e 1) (x : D.V) (hx0 : x ≠ 0)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x}) :
    Module.finrank (ZMod 3) D.V = 6 ∨ Module.finrank (ZMod 3) D.V = 5 := by
  have hcart := ggQ2xQ_cartan_E6 D e hE
  have hsym : ∀ i j, D.cartan i j = D.cartan j i := by
    intro i j
    obtain ⟨p, rfl⟩ := e.surjective i
    obtain ⟨q, rfl⟩ := e.surjective j
    rw [hcart p q, hcart q p]
    exact congrFun (congrFun (CartanMatrix.E_transpose 6) q) p
  have he0 : e 0 ≠ D.a := by
    intro h
    exact (by decide : (0 : Fin 6) ≠ 1) (e.injective (h.trans ha))
  let F : ({k // k ≠ D.a} → ZMod 3) →ₗ[ZMod 3] Dual (ZMod 3) D.V :=
    Fintype.linearCombination (ZMod 3) (fun k : {k // k ≠ D.a} => D.root k)
  have hker_le : Module.finrank (ZMod 3) F.ker ≤ 1 := by
    let ev : F.ker →ₗ[ZMod 3] ZMod 3 :=
      { toFun := fun d => d.1 ⟨e 0, he0⟩
        map_add' := by intro a b; rfl
        map_smul' := by intro a b; rfl }
    have h_inj : Function.Injective ev := by
      intro u w huw
      apply Subtype.ext
      have hu0 : (u.1 - w.1) ⟨e 0, he0⟩ = 0 := by
        have h : u.1 ⟨e 0, he0⟩ = w.1 ⟨e 0, he0⟩ := huw
        simp [h]
      have hrel : (∑ k, (u.1 - w.1) k • D.root k) = 0 := by
        have hz : F (u.1 - w.1) = 0 := by rw [map_sub, u.2, w.2, sub_zero]
        rwa [Fintype.linearCombination_apply] at hz
      exact sub_eq_zero.mp (lr7ds_ker_of_relation D e hE hsym he0 (u.1 - w.1) hrel hu0)
    have := LinearMap.finrank_le_finrank_of_injective (f := ev) h_inj
    simpa using this
  have hrange : F.range = Submodule.span (ZMod 3)
      (Set.range (fun k : {k // k ≠ D.a} => D.root k)) := by simp [F]
  have hrank_ge : 4 ≤ Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range (fun k : {k // k ≠ D.a} => D.root k))) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker F
    rw [finrank_fintype_fun_eq_card, lr7ds_card_lambda D e, hrange] at hrn
    omega
  have hfin_le : Module.finrank (ZMod 3) D.V ≤ 6 := by
    have h := ggQ2_dep_finrank_le D x hx
    rwa [lr7ds_card_iota D e] at h
  have := ggQ2_dep_finrank_eq D x hx0 hx
  omega

end CFSG.StandardType

end

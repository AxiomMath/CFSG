module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTBTorCartan

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6aF_ggIntCartan_three {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b) (hm : M a b = 3) :
    C a b = -1 ∧ C b a = -1 := by
  rcases hC.2 a b hab with ⟨h2, -⟩ | ⟨-, h1, h2⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exfalso; omega
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega

private theorem l6aF_ggIntCartan_two {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b) (hm : M a b = 2) :
    C a b = 0 ∧ C b a = 0 := by
  rcases hC.2 a b hab with ⟨-, h1, h2⟩ | ⟨h3, -, -⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

private theorem l6aF_coxeterA_entry (m : ℕ) (i j : Fin m) :
    (CoxeterMatrix.A m) i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

private theorem l6aF_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 :=
  rfl

theorem ggIndep_cartan_of_reindex {m : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (eA : Fin m ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = (CoxeterMatrix.A m).reindex eA) :
    ∀ i j : Fin m, CL (eA i) (eA j) = CartanMatrix.A m i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCL.1, l6aF_cartanA_entry]
    simp
  · have hentryM : ML (eA i) (eA j) = (CoxeterMatrix.A m) i j := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hne : eA i ≠ eA j := fun h => hij (eA.injective h)
    by_cases h3 : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
    · have hM3 : ML (eA i) (eA j) = 3 := by
        rw [hentryM, l6aF_coxeterA_entry, if_neg hij]
        rw [if_pos (h3.elim (fun h => Or.inr h) (fun h => Or.inl h))]
      have hthree := l6aF_ggIntCartan_three hCL hne hM3
      rw [hthree.1, l6aF_cartanA_entry, if_neg hij, if_pos h3]
    · have hM2 : ML (eA i) (eA j) = 2 := by
        rw [hentryM, l6aF_coxeterA_entry, if_neg hij]
        rw [if_neg (fun h => h3 (h.elim (fun h => Or.inr h) (fun h => Or.inl h)))]
      have htwo := l6aF_ggIntCartan_two hCL hne hM2
      rw [htwo.1, l6aF_cartanA_entry, if_neg hij, if_neg h3]

private theorem l6aF_x_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
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

private theorem l6aF_automizer_fixes_x {G : Type} [Group G] [Finite G] {p : ℕ}
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

private theorem l6aF_alpha_x {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
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
  have hfix := l6aF_automizer_fixes_x hH.1 hx
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

theorem ggIndep_fixL (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {Λ : Type} [Fintype Λ] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    ∀ v : V, (∀ j : Λ, α j v = 0) →
      v ∈ Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V) := by
  intro v hα
  let bb : Bs := Additive.toMul (ι.symm v)
  have hbbw : ι (Additive.ofMul bb) = v := by
    dsimp only [bb]
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hbb : ∀ j : Λ, φ j bb = bb := by
    intro j
    refine (ggLin_fix_iff (p := p) ι (φ j) bb).mpr ?_
    rw [hbbw]
    have h1 := hφ j v
    rw [hα j, zero_smul, sub_zero] at h1
    exact h1
  have hfixL : ∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb := by
    rw [hAL]
    exact ggFixed_of_mem_closure φ bb hbb
  have hxmem : (bb : G) ∈ Subgroup.zpowers x :=
    hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hfixL
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hbk : bb = (⟨x, hx⟩ : Bs) ^ k := Subtype.ext (by simpa using hk.symm)
  have hof : Additive.ofMul bb = k • Additive.ofMul (⟨x, hx⟩ : Bs) := by
    rw [hbk, ofMul_zpow]
  have hv : v = k • ι (Additive.ofMul ⟨x, hx⟩) := by
    have h := congrArg ι hof
    simpa [hbbw, map_zsmul] using h
  rw [hv]
  have hmem : ι (Additive.ofMul ⟨x, hx⟩) ∈
      Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V) :=
    Submodule.subset_span rfl
  have hsm := Submodule.smul_mem (Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V))
    (k : ZMod p) hmem
  rwa [Int.cast_smul_eq_zsmul] at hsm

private theorem l6aF_two_mul_pred_sub {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 2 ≤ N) :
    (2 : ZMod p) * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) = 0 := by
  have hNcast : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p N).2 hpN
  have hcast : ((N : ℕ) : ZMod p) = 2 * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) := by
    have h1 : ((N - 1 : ℕ) : ZMod p) = (N : ZMod p) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ N by omega)]; norm_num
    have h2 : ((N - 2 : ℕ) : ZMod p) = (N : ZMod p) - 2 := by
      rw [Nat.cast_sub (show 2 ≤ N by omega)]; norm_num
    rw [h1, h2]; ring
  rw [← hcast, hNcast]

theorem l6aF_A_mul_d {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N)
    (j : Fin (N - 1)) :
    ∑ k : Fin (N - 1), (CartanMatrix.A (N - 1) j k : ZMod p) *
      (((k : ℕ) + 1 : ℕ) : ZMod p) = 0 := by
  let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
  change ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * d k = 0
  rw [cartanA_row d j]
  have hc' : ∀ m : ℕ, (fun m => if hm : m < N - 1 then d ⟨m, hm⟩ else 0) m =
      (if m < N - 1 then (((m : ℕ) + 1 : ℕ) : ZMod p) else 0) := by
    intro m
    by_cases hm : m < N - 1
    · simp [d, hm]
    · simp [hm]
  have hprev : (j : ℕ) - 1 < N - 1 := by omega
  simp only [hc']
  by_cases hlast : (j : ℕ) + 1 < N - 1
  · rw [if_pos j.isLt, if_pos hlast]
    by_cases hj0 : (j : ℕ) = 0
    · rw [if_pos hj0, hj0]; norm_num
    · rw [if_neg hj0, if_pos hprev]
      have hsub : ((↑j - 1 : ℕ) : ZMod p) = (↑j : ZMod p) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ (j : ℕ))]
        norm_num
      simp only [Nat.cast_add, Nat.cast_one]
      rw [hsub]; ring
  · rw [if_pos j.isLt, if_neg hlast]
    have hlast' : (j : ℕ) + 1 = N - 1 := by omega
    by_cases hj0 : (j : ℕ) = 0
    · rw [if_pos hj0, hj0]
      have hN : N = 2 := by omega
      have h2 : (2 : ZMod p) = 0 := by
        have hNcast : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p N).2 hpN
        simpa [hN] using hNcast
      norm_num
      exact h2
    · rw [if_neg hj0, if_pos hprev]
      have hjval : (j : ℕ) = N - 2 := by omega
      have e1 : (N - 2 : ℕ) + 1 = N - 1 := by omega
      have e2 : (N - 2 : ℕ) - 1 + 1 = N - 2 := by omega
      rw [hjval, e1, e2]
      convert l6aF_two_mul_pred_sub (p := p) (N := N) hpN (by omega) using 1
      ring

theorem ggIndep_x_mem_span {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 2 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p))
    (hind : LinearIndependent (ZMod p) h)
    (hfix : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod p) {x}) :
    x ∈ Submodule.span (ZMod p) (Set.range h) := by
  classical
  let v : V := ∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k
  have hv_mem : v ∈ Submodule.span (ZMod p) (Set.range h) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hv_ker : ∀ j, α j v = 0 := by
    intro j
    have h1 := l6aF_A_mul_d hpN j
    simp only [v, map_sum, map_smul, smul_eq_mul, hpair]
    rw [← h1]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hv_ne : v ≠ 0 := by
    intro h0
    have h2 := (Fintype.linearIndependent_iff.mp hind)
      (fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)) h0 ⟨0, by omega⟩
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

theorem ggIndep_x_eq_smul_center {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 2 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p))
    (hind : LinearIndependent (ZMod p) h)
    (hfix : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod p) {x}) :
    ∃ c : ZMod p, c ≠ 0 ∧
      x = c • ∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k := by
  classical
  let v : V := ∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k
  have hv_ker : ∀ j, α j v = 0 := by
    intro j
    have h1 := l6aF_A_mul_d hpN j
    simp only [v, map_sum, map_smul, smul_eq_mul, hpair]
    rw [← h1]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hv_ne : v ≠ 0 := by
    intro h0
    have h2 := (Fintype.linearIndependent_iff.mp hind)
      (fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)) h0 ⟨0, by omega⟩
    simp at h2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hfix v hv_ker)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv_ne
    rw [← hc, zero_smul]
  exact ⟨c⁻¹, inv_ne_zero hc0, by
    show x = c⁻¹ • v
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

theorem ggIndep_center_functional_vanish {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)) {w : V}
    (hw : w ∈ Submodule.span (ZMod p) (Set.range h)) :
    (∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • α i) w = 0 := by
  classical
  refine Submodule.span_induction (p := fun w _ => (∑ i : Fin (N - 1),
    (((i : ℕ) + 1 : ℕ) : ZMod p) • α i) w = 0) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨j, rfl⟩
    have h1 := l6aF_A_mul_d hpN j
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hpair]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsymm : (CartanMatrix.A (N - 1) i j : ZMod p) = (CartanMatrix.A (N - 1) j i : ZMod p) := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      split_ifs <;> first | rfl | omega | simp_all
    rw [hsymm, mul_comm]
  · simp
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  · intro c a _ ha
    rw [map_smul, ha, smul_zero]

theorem ggXDatumA_indep_frame (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 5 ≤ N)
    (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGIndepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)) := by
  classical
  have hpair' : ∀ i j, α (e i) (h (e j)) = (CartanMatrix.A (N - 1) i j : ZMod p) := by
    intro i j
    rw [hpair (e i) (e j), ggIndep_cartan_of_reindex e hCL hML i j]
  have hind' : LinearIndependent (ZMod p) (fun i => h (e i)) :=
    (linearIndependent_equiv (R := ZMod p) e).mpr hind
  have hfix' : ∀ v : V, (∀ i : Fin (N - 1), α (e i) v = 0) →
      v ∈ Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V) := by
    intro v hv
    exact ggIndep_fixL hFix hH hx hφ hAL v (fun j => by
      have hj := hv (e.symm j)
      simpa using hj)
  refine ⟨hpair', hpN, hind', ?_, ?_, ?_, hfix'⟩
  · intro h0
    have hx1 : (⟨x, hx⟩ : Bs) ≠ 1 := by
      intro h1
      exact l6aF_x_ne_one hH (by simpa using congrArg Subtype.val h1)
    apply hx1
    have h1 : Additive.ofMul (⟨x, hx⟩ : Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨x, hx⟩ : Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  · intro i
    exact l6aF_alpha_x hp2 hH hx hφ hpair hCL hAL (e i)
  · exact ggIndep_x_mem_span hpN (by omega) hpair' hind' hfix'

end CFSG.StandardType

end

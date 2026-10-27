module

public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumA
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nRC_ggIntCartan_three {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b) (hm : M a b = 3) :
    C a b = -1 ∧ C b a = -1 := by
  rcases hC.2 a b hab with ⟨h2, -⟩ | ⟨-, h1, h2⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exfalso; omega
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega

private theorem l05nRC_ggIntCartan_two {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b) (hm : M a b = 2) :
    C a b = 0 ∧ C b a = 0 := by
  rcases hC.2 a b hab with ⟨-, h1, h2⟩ | ⟨h3, -, -⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

private theorem l05nRC_coxeterA_entry (m : ℕ) (i j : Fin m) :
    (CoxeterMatrix.A m) i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

private theorem l05nRC_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 :=
  rfl

private theorem l05nRC_cartan_of_reindex {m : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (eA : Fin m ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = (CoxeterMatrix.A m).reindex eA) :
    ∀ i j : Fin m, CL (eA i) (eA j) = CartanMatrix.A m i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCL.1, l05nRC_cartanA_entry]
    simp
  · have hentryM : ML (eA i) (eA j) = (CoxeterMatrix.A m) i j := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hne : eA i ≠ eA j := fun h => hij (eA.injective h)
    by_cases h3 : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
    · have hM3 : ML (eA i) (eA j) = 3 := by
        rw [hentryM, l05nRC_coxeterA_entry, if_neg hij]
        rw [if_pos (h3.elim (fun h => Or.inr h) (fun h => Or.inl h))]
      have hthree := l05nRC_ggIntCartan_three hCL hne hM3
      rw [hthree.1, l05nRC_cartanA_entry, if_neg hij, if_pos h3]
    · have hM2 : ML (eA i) (eA j) = 2 := by
        rw [hentryM, l05nRC_coxeterA_entry, if_neg hij]
        rw [if_neg (fun h => h3 (h.elim (fun h => Or.inr h) (fun h => Or.inl h)))]
      have htwo := l05nRC_ggIntCartan_two hCL hne hM2
      rw [htwo.1, l05nRC_cartanA_entry, if_neg hij, if_neg h3]

private theorem l05nRC_two_mul_pred_sub {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 2 ≤ N) :
    (2 : ZMod p) * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) = 0 := by
  have hNcast : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p N).2 hpN
  have hcast : ((N : ℕ) : ZMod p) = 2 * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) := by
    have h1 : ((N - 1 : ℕ) : ZMod p) = (N : ZMod p) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ N by omega)]; norm_num
    have h2 : ((N - 2 : ℕ) : ZMod p) = (N : ZMod p) - 2 := by
      rw [Nat.cast_sub (show 2 ≤ N by omega)]; norm_num
    rw [h1, h2]; ring
  rw [← hcast, hNcast]

private theorem l05nRC_A_mul_d {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N)
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
      convert l05nRC_two_mul_pred_sub (p := p) (N := N) hpN (by omega) using 1
      ring

private theorem l05nRC_h_mem_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {Λ : Type} {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    ∀ i : Λ, ((Additive.toMul (ι.symm (h i)) : ↥Bs) : G) ∈ K := by
  intro i
  have hφi : φ i ∈ ggAutomizer K Bs := by
    rw [hAK]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  obtain ⟨g, hgK, hgN, hgconj⟩ :=
    (mem_ggAutomizer_iff (H := K) (φ := φ i)).mp hφi
  have hBsN : Bs ≤ Subgroup.normalizer (K : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn (hH.2.2.1.2 y K hH.2.2.2.2.1)
  have hαii : α i (h i) = 2 := by
    rw [hpair i i, hCK.1]
    norm_num
  let w : V := (-((2 : ZMod p)⁻¹)) • h i
  let b : ↥Bs := Additive.toMul (ι.symm w)
  have hbw : ι (Additive.ofMul b) = w := by
    dsimp only [b]
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hαb : α i (ι (Additive.ofMul b)) = -1 := by
    rw [hbw]
    show α i ((-((2 : ZMod p)⁻¹)) • h i) = -1
    rw [map_smul, smul_eq_mul, hαii, neg_mul, inv_mul_cancel₀ (zmod_two_ne_zero hp2)]
  have h1 : ggLin (p := p) ι (φ i) (ι (Additive.ofMul b)) = ι (Additive.ofMul b) + h i := by
    have hh := hφ i (ι (Additive.ofMul b))
    rw [hαb] at hh
    simpa [neg_smul, one_smul, sub_neg_eq_add] using hh
  have h2 : ι (Additive.ofMul (b⁻¹ * φ i b)) =
      -ι (Additive.ofMul b) + ι (Additive.ofMul (φ i b)) := by
    simp only [ofMul_mul, ofMul_inv, map_add, map_neg]
  have hhi : h i = ι (Additive.ofMul (b⁻¹ * φ i b)) := by
    rw [h2, ← ggLin_apply_ofMul (p := p), h1]
    abel
  have hmemK : ((b⁻¹ * φ i b : ↥Bs) : G) ∈ K := by
    have hconj : ((φ i b : ↥Bs) : G) = g * (b : G) * g⁻¹ := hgconj b
    have hbg : (b : G)⁻¹ * g * (b : G) ∈ K := by
      have hbN : (b : G) ∈ Subgroup.normalizer (K : Set G) := hBsN b.2
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) g).mp hgK
    have hEq2 : ((b⁻¹ * φ i b : ↥Bs) : G) = ((b : G)⁻¹ * g * (b : G)) * g⁻¹ := by
      change (b : G)⁻¹ * ((φ i b : ↥Bs) : G) = ((b : G)⁻¹ * g * (b : G)) * g⁻¹
      rw [hconj]
      group
    rw [hEq2]
    exact K.mul_mem hbg (K.inv_mem hgK)
  have hEq : (Additive.toMul (ι.symm (h i)) : ↥Bs) = b⁻¹ * φ i b := by
    rw [hhi]
    simp
  rw [hEq]
  exact hmemK

theorem ggRC_y_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : y ≠ 1 := by
  intro hy1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hDea.2 x hxD
  have hDle : D ≤ Subgroup.zpowers x := by
    rw [hDgen, hy1, Subgroup.closure_le]
    intro a ha
    have ha' : a = x ∨ a = 1 := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.mem_zpowers x
    · rw [h]; exact Subgroup.one_mem _
  have hxle : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hxp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
      _ ≤ p := hxle
  nlinarith [hcon, hp.two_le]

theorem ggRC_automizer_fixes_y {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {y : G} (hy : y ∈ Bs)
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G)) :
    ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨y, hy⟩ = ⟨y, hy⟩ := by
  have hle : ggAutomizer K Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs) := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro ψ hψ
    obtain ⟨g, hgK, -, hg⟩ := hψ
    have hmem : g ∈ Subgroup.centralizer ({y} : Set G) := hKy hgK
    have hcomm : g * y = y * g :=
      ((Subgroup.mem_centralizer_iff.mp hmem) y (by simp)).symm
    change ψ • (⟨y, hy⟩ : ↥Bs) = (⟨y, hy⟩ : ↥Bs)
    rw [MulAut.smul_def]
    apply Subtype.ext
    have h : ((ψ ⟨y, hy⟩ : ↥Bs) : G) = g * y * g⁻¹ := by
      have h1 := hg (⟨y, hy⟩ : ↥Bs)
      simpa using h1
    rw [h, hcomm]
    group
  intro ψ hψ
  simpa only [MulAction.mem_stabilizer_iff, MulAut.smul_def] using hle hψ

private theorem l05nRC_alpha_y {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α i (h j) = (CK i j : ZMod p))
    (hCK : GGIntCartan MK CK)
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    ∀ j : Λ, α j (ι (Additive.ofMul ⟨y, hy⟩)) = 0 := by
  intro j
  have hfix := ggRC_automizer_fixes_y hy hH.2.2.2.2.1.1.2.2.2.1
  have hmem : φ j ∈ ggAutomizer K Bs := by
    rw [hAK]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hfixj : φ j ⟨y, hy⟩ = ⟨y, hy⟩ := hfix (φ j) hmem
  have hlin : ggLin (p := p) ι (φ j) (ι (Additive.ofMul ⟨y, hy⟩)) =
      ι (Additive.ofMul ⟨y, hy⟩) :=
    (ggLin_fix_iff (p := p) ι (φ j) ⟨y, hy⟩).mp hfixj
  have h1 := hφ j (ι (Additive.ofMul ⟨y, hy⟩))
  rw [hlin] at h1
  have h2 : α j (ι (Additive.ofMul ⟨y, hy⟩)) • h j = 0 :=
    sub_eq_self.mp h1.symm
  have h3 : α j (α j (ι (Additive.ofMul ⟨y, hy⟩)) • h j) = 0 := by
    rw [h2, map_zero]
  have hpair : α j (h j) = (2 : ZMod p) := by
    rw [hL j j, hCK.1 j]
    norm_num
  rw [map_smul, smul_eq_mul, hpair] at h3
  exact (mul_eq_zero.mp h3).resolve_right (zmod_two_ne_zero hp2)

private theorem l05nRC_fix_K {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} {y : G} {K : Subgroup G}
    (hfixK : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y)
    (hy : y ∈ Bs)
    {Λ : Type} [Fintype Λ] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    ∀ v : V, (∀ j : Λ, α j v = 0) →
      v ∈ Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨y, hy⟩)} : Set V) := by
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
  have hfixed : ∀ ψ ∈ ggAutomizer K Bs, ψ bb = bb := by
    rw [hAK]
    exact ggFixed_of_mem_closure φ bb hbb
  have hymem : (bb : G) ∈ Subgroup.zpowers y :=
    hfixK bb hfixed
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hymem
  have hbk : bb = (⟨y, hy⟩ : Bs) ^ k := Subtype.ext (by simpa using hk.symm)
  have hof : Additive.ofMul bb = k • Additive.ofMul (⟨y, hy⟩ : Bs) := by
    rw [hbk, ofMul_zpow]
  have hv : v = k • ι (Additive.ofMul ⟨y, hy⟩) := by
    have h := congrArg ι hof
    simpa [hbbw, map_zsmul] using h
  rw [hv]
  have hmem : ι (Additive.ofMul ⟨y, hy⟩) ∈
      Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨y, hy⟩)} : Set V) :=
    Submodule.subset_span rfl
  have hsm := Submodule.smul_mem (Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨y, hy⟩)} : Set V))
    (k : ZMod p) hmem
  rwa [Int.cast_smul_eq_zsmul] at hsm

theorem ggXDatumA_dep_K {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hy : y ∈ Bs) (hyK : y ∉ K)
    (hfixK : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y)
    {N : ℕ} (hN : 5 ≤ N) (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ)
    (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e) (hCK : GGIntCartan MK CK) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    ¬ LinearIndependent (ZMod p) h := by
  classical
  intro hli
  let M : AddSubgroup V :=
    { carrier := {w | ∃ b : ↥Bs, (b : G) ∈ K ∧ ι (Additive.ofMul b) = w}
      zero_mem' := by
        refine ⟨1, K.one_mem, ?_⟩
        rw [ofMul_one, map_zero]
      add_mem' := by
        rintro w1 w2 ⟨b1, hb1, rfl⟩ ⟨b2, hb2, rfl⟩
        refine ⟨b1 * b2, K.mul_mem hb1 hb2, ?_⟩
        rw [ofMul_mul, map_add]
      neg_mem' := by
        rintro w ⟨b, hb, rfl⟩
        refine ⟨b⁻¹, K.inv_mem hb, ?_⟩
        rw [ofMul_inv, map_neg] }
  have hM : ∀ i : Λ, h i ∈ M := fun i => by
    refine ⟨Additive.toMul (ι.symm (h i)), l05nRC_h_mem_K hp2 hH hCK hφ hpair hAK i, ?_⟩
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  let v : V := ∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • h (e i)
  let d : Fin (N - 1) → ZMod p := fun i => (((i : ℕ) + 1 : ℕ) : ZMod p)
  have hlie : LinearIndependent (ZMod p) (fun i : Fin (N - 1) => h (e i)) :=
    (linearIndependent_equiv e).mpr hli
  have hv_ne : v ≠ 0 := by
    intro hv
    have hd0 : d = 0 := funext fun i =>
      (Fintype.linearIndependent_iff.mp hlie) d (by simpa [v, d] using hv) i
    have h1 : d ⟨0, by omega⟩ = 0 := congrFun hd0 ⟨0, by omega⟩
    have h2 : (1 : ZMod p) = 0 := by simpa [d] using h1
    exact one_ne_zero h2
  have hαv : ∀ k : Λ, α k v = 0 := by
    intro k
    obtain ⟨j, rfl⟩ := e.surjective k
    have hsum : α (e j) v = ∑ i : Fin (N - 1),
        (((i : ℕ) + 1 : ℕ) : ZMod p) * (CartanMatrix.A (N - 1) j i : ZMod p) := by
      simp only [v, map_sum, map_smul, smul_eq_mul, hpair]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [l05nRC_cartan_of_reindex (m := N - 1) e hCK hMK j i]
    rw [hsum]
    have hAd := l05nRC_A_mul_d (p := p) (N := N) hpN j
    calc ∑ i : Fin (N - 1),
          (((i : ℕ) + 1 : ℕ) : ZMod p) * (CartanMatrix.A (N - 1) j i : ZMod p)
        = ∑ i : Fin (N - 1),
          (CartanMatrix.A (N - 1) j i : ZMod p) * (((i : ℕ) + 1 : ℕ) : ZMod p) := by
          refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 0 := hAd
  let s : ↥Bs := Additive.toMul (ι.symm v)
  have hsv : ι (Additive.ofMul s) = v := by
    dsimp only [s]
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hs_ne : s ≠ 1 := by
    intro hs1
    apply hv_ne
    have h : ι (Additive.ofMul s) = 0 := by rw [hs1, ofMul_one, map_zero]
    rwa [hsv] at h
  have hfixv : ∀ k : Λ, φ k s = s := by
    intro k
    refine (ggLin_fix_iff (p := p) ι (φ k) s).mpr ?_
    rw [hsv, hφ k v, hαv k, zero_smul, sub_zero]
  have hfixall : ∀ ψ ∈ ggAutomizer K Bs, ψ s = s := by
    rw [hAK]
    exact ggFixed_of_mem_closure φ s hfixv
  have hsy : (s : G) ∈ Subgroup.zpowers y :=
    hfixK s hfixall
  have hv_mem : v ∈ M := by
    have hv_sum : v = ∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • h (e i) := rfl
    rw [hv_sum]
    refine M.sum_mem fun i _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact M.nsmul_mem (hM (e i)) _
  have hsK : (s : G) ∈ K := by
    obtain ⟨b, hbK, hbw⟩ := hv_mem
    have hbs : b = s := by
      apply Additive.ofMul.injective
      exact ι.injective (hbw.trans hsv.symm)
    rw [← hbs]
    exact hbK
  have hBsE : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hyp : y ^ p = 1 := hBsE.2 y hy
  have hy1 : y ≠ 1 := ggRC_y_ne_one hH
  have horder_y : orderOf y = p := orderOf_eq_prime hyp hy1
  have horder_s : orderOf (s : G) = p := by
    have hdvd : orderOf (s : G) ∣ p := by
      rw [← horder_y]
      exact orderOf_dvd_of_mem_zpowers hsy
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf (s : G)) hdvd with h1 | h2
    · exact absurd h1 (by intro h; exact hs_ne (Subtype.ext (orderOf_eq_one_iff.mp h)))
    · exact h2
  have hs_le : Subgroup.zpowers (s : G) ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hsy
  have hcard_s : Nat.card (Subgroup.zpowers (s : G)) = p := by rw [Nat.card_zpowers, horder_s]
  have hcard_y : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, horder_y]
  have heq : Subgroup.zpowers (s : G) = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hs_le (by rw [hcard_s, hcard_y])
  have hy_zp : y ∈ Subgroup.zpowers (s : G) := by rw [heq]; exact Subgroup.mem_zpowers y
  exact hyK ((Subgroup.zpowers_le.mpr hsK) hy_zp)

theorem ggXDatumA_frame_K {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hy : y ∈ Bs)
    (hfixK : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y)
    {N : ℕ} (hN : 5 ≤ N)
    (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ}
    {CK : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hdep : ¬ LinearIndependent (ZMod p) h) :
    GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨y, hy⟩)) := by
  classical
  refine ⟨?_, hpN, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hpair (e i) (e j), l05nRC_cartan_of_reindex e hCK hMK i j]
  · intro h0
    have hy1 : (⟨y, hy⟩ : Bs) ≠ 1 := by
      intro h1
      exact ggRC_y_ne_one hH (by simpa using congrArg Subtype.val h1)
    apply hy1
    have h1 : Additive.ofMul (⟨y, hy⟩ : Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨y, hy⟩ : Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  · intro i
    exact l05nRC_alpha_y hp2 hH hy hφ hpair hCK hAK (e i)
  · intro v hv
    exact l05nRC_fix_K hfixK hy hφ hAK v (fun j => by
      have hj := hv (e.symm j)
      simpa using hj)
  · intro hli
    exact hdep ((linearIndependent_equiv (R := ZMod p) e).mp hli)


theorem ggXDatumA_fix_K_of_card {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) {N : ℕ} (hN : 5 ≤ N)
    (hpN : p ∣ N) (hcard : Nat.card Bs = p ^ (N - 1))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ}
    {CK : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ)
    (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y := by
  classical
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let d : Fin (N - 1) → ZMod p := fun i => (((i : ℕ) + 1 : ℕ) : ZMod p)
  have hd_ne : d ≠ 0 := by
    intro h0
    have h1 := congrFun h0 ⟨0, by omega⟩
    simp [d] at h1
  let Aop : (Fin (N - 1) → ZMod p) →ₗ[ZMod p] (Fin (N - 1) → ZMod p) :=
    { toFun := fun c j => ∑ k : Fin (N - 1), (CartanMatrix.A (N - 1) j k : ZMod p) * c k
      map_add' := by
        intro a b
        funext j
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [RingHom.id_apply]
        ring }
  have hAop_d : Aop d = 0 := by
    funext j
    exact l05nRC_A_mul_d (p := p) (N := N) hpN j
  have hAker_le : Aop.ker ≤
      Submodule.span (ZMod p) ({d} : Set (Fin (N - 1) → ZMod p)) := by
    intro c hc
    rw [LinearMap.mem_ker] at hc
    by_cases hc0 : c = 0
    · rw [hc0]
      exact Submodule.zero_mem _
    · have hcA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k = 0 :=
        fun j => congrFun hc j
      have hdA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * d k = 0 :=
        fun j => l05nRC_A_mul_d (p := p) (N := N) hpN j
      obtain ⟨l, hl⟩ := ggCartanA_ker_le_one c d hcA hdA hc0
      have hl0 : l ≠ 0 := by
        intro h0
        apply hd_ne
        rw [hl, h0, zero_smul]
      rw [Submodule.mem_span_singleton]
      refine ⟨l⁻¹, ?_⟩
      rw [hl, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hAker : Aop.ker =
      Submodule.span (ZMod p) ({d} : Set (Fin (N - 1) → ZMod p)) := by
    apply le_antisymm hAker_le
    intro c hc
    rw [Submodule.mem_span_singleton] at hc
    obtain ⟨l, rfl⟩ := hc
    rw [LinearMap.mem_ker, map_smul, hAop_d, smul_zero]
  have hAker_dim : Module.finrank (ZMod p) Aop.ker = 1 := by
    rw [hAker]
    exact finrank_span_singleton (K := ZMod p) hd_ne
  have hAdom : Module.finrank (ZMod p) (Fin (N - 1) → ZMod p) = N - 1 := by
    simp
  have hArank : Module.finrank (ZMod p) Aop.range = N - 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker Aop
    rw [hAdom, hAker_dim] at h
    omega
  let αMap : V →ₗ[ZMod p] (Fin (N - 1) → ZMod p) :=
    { toFun := fun v i => α (e i) v
      map_add' := by
        intro u v
        funext i
        simp
      map_smul' := by
        intro a v
        funext i
        simp }
  let φMap : (Fin (N - 1) → ZMod p) →ₗ[ZMod p] V :=
    Fintype.linearCombination (ZMod p) (fun i => h (e i))
  have hcomp : αMap.comp φMap = Aop := by
    apply LinearMap.ext
    intro c
    funext j
    simp only [LinearMap.comp_apply, αMap, φMap, Aop, Fintype.linearCombination_apply,
      map_sum, map_smul, smul_eq_mul, hpair, l05nRC_cartan_of_reindex e hCK hMK,
      Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr
      (s₁ := (Finset.univ : Finset (Fin (N - 1))))
      (s₂ := (Finset.univ : Finset (Fin (N - 1)))) rfl fun i _ => ?_
    change c i * (α (e j)) (h (e i)) =
      (CartanMatrix.A (N - 1) j i : ZMod p) * c i
    rw [hpair (e j) (e i), l05nRC_cartan_of_reindex e hCK hMK j i]
    ring
  have hle_range : Aop.range ≤ αMap.range := by
    rintro _ ⟨c, rfl⟩
    exact ⟨φMap c, by rw [← hcomp, LinearMap.comp_apply]⟩
  have hrank_ge : N - 2 ≤ Module.finrank (ZMod p) αMap.range := by
    have h := Submodule.finrank_mono hle_range
    omega
  have hyker : αMap (ι (Additive.ofMul ⟨y, hy⟩)) = 0 := by
    funext i
    exact l05nRC_alpha_y hp2 hH hy hφ hpair hCK hAK (e i)
  have hy1 : (⟨y, hy⟩ : Bs) ≠ 1 := by
    intro h1
    exact ggRC_y_ne_one hH (by simpa using congrArg Subtype.val h1)
  have hyne : ι (Additive.ofMul ⟨y, hy⟩) ≠ 0 := by
    intro h0
    apply hy1
    have h1 : Additive.ofMul (⟨y, hy⟩ : Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨y, hy⟩ : Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  have hspanY_le : Submodule.span (ZMod p)
      ({ι (Additive.ofMul ⟨y, hy⟩)} : Set V) ≤ αMap.ker := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hyker
  have hker_ge_one : 1 ≤ Module.finrank (ZMod p) αMap.ker := by
    have hfin : Module.finrank (ZMod p)
        (Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨y, hy⟩)} : Set V)) = 1 :=
      finrank_span_singleton (K := ZMod p) hyne
    have h := Submodule.finrank_mono hspanY_le
    omega
  have hVcard : Nat.card V = p ^ (N - 1) := by
    rw [← card_eq_of_ggLin ι]
    simpa using hcard
  have hVdim : Module.finrank (ZMod p) V = N - 1 := by
    have hpow := FiniteField.pow_finrank_eq_natCard p V
    refine Nat.pow_right_injective (Fact.out : p.Prime).two_le ?_
    change p ^ Module.finrank (ZMod p) V = p ^ (N - 1)
    rw [hpow, hVcard]
  have hrank_le : Module.finrank (ZMod p) αMap.range ≤ N - 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker αMap
    omega
  have hrank_eq : Module.finrank (ZMod p) αMap.range = N - 2 :=
    le_antisymm hrank_le hrank_ge
  have hker_dim : Module.finrank (ZMod p) αMap.ker = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker αMap
    rw [hrank_eq, hVdim] at h
    omega
  have hker_eq : αMap.ker =
      Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨y, hy⟩)} : Set V) := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq hspanY_le ?_
    rw [hker_dim, finrank_span_singleton (K := ZMod p) hyne]
  intro b hb
  have hbker : ι (Additive.ofMul b) ∈ αMap.ker := by
    rw [LinearMap.mem_ker]
    funext i
    have hφi : φ (e i) ∈ ggAutomizer K Bs := by
      rw [hAK]
      exact Subgroup.subset_closure ⟨e i, rfl⟩
    have hfixi : φ (e i) b = b := hb _ hφi
    have hfixlin : ggLin (p := p) ι (φ (e i)) (ι (Additive.ofMul b)) =
        ι (Additive.ofMul b) :=
      (ggLin_fix_iff (p := p) ι (φ (e i)) b).mp hfixi
    have hlin := hφ (e i) (ι (Additive.ofMul b))
    rw [hfixlin] at hlin
    have hzero : α (e i) (ι (Additive.ofMul b)) • h (e i) = 0 :=
      sub_eq_self.mp hlin.symm
    have hhi : h (e i) ≠ 0 := by
      intro h0
      have h2 : α (e i) (h (e i)) = (2 : ZMod p) := by
        rw [hpair (e i) (e i), hCK.1 (e i)]
        norm_num
      rw [h0, map_zero] at h2
      exact (zmod_two_ne_zero hp2) h2.symm
    exact (smul_eq_zero.mp hzero).resolve_right hhi
  rw [hker_eq] at hbker
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hbker
  have ha' : (a.val : ℕ) • ι (Additive.ofMul ⟨y, hy⟩) =
      ι (Additive.ofMul b) := by
    rw [← ZMod.natCast_zmod_val a] at ha
    rwa [Nat.cast_smul_eq_nsmul] at ha
  have hof : Additive.ofMul b = a.val • Additive.ofMul (⟨y, hy⟩ : Bs) := by
    apply ι.injective
    rw [map_nsmul, ha']
  have hb_eq : b = (⟨y, hy⟩ : Bs) ^ a.val := by
    have hof' : Additive.ofMul b =
        Additive.ofMul ((⟨y, hy⟩ : Bs) ^ a.val) := by
      rw [ofMul_pow]
      exact hof
    exact Additive.ofMul.injective hof'
  rw [hb_eq]
  exact Subgroup.npow_mem_zpowers y a.val

end CFSG.StandardType

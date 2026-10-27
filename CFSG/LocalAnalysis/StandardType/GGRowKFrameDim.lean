module

public import CFSG.LocalAnalysis.StandardType.GGRowKFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nFD_coxeterA_entry (m : ℕ) (i j : Fin m) :
    (CoxeterMatrix.A m) i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

private theorem l05nFD_cartan_col {p N : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ)
    (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e) (hCK : GGIntCartan MK CK) :
    ∀ a k : Fin (N - 1),
      (CK (e a) (e k) : ZMod p) = (CartanMatrix.A (N - 1) a k : ZMod p) := by
  have hA : GGIntCartan MK (Matrix.reindex e e (CartanMatrix.A (N - 1))) := by
    rw [hMK]
    exact (ggIntCartan_A (N - 1)).reindex e
  intro a k
  by_cases hak : a = k
  · subst hak
    rw [hCK.1, (ggIntCartan_A (N - 1)).1 a]
  · have hne : e a ≠ e k := fun h => hak (e.injective h)
    have hle : MK (e a) (e k) ≤ 3 := by
      rw [hMK, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        l05nFD_coxeterA_entry, if_neg hak]
      split_ifs <;> omega
    have h1 : CK (e a) (e k) = CartanMatrix.A (N - 1) a k := by
      have := ((GGIntCartan.pair hCK hA hne).2 hle).1
      simpa [Matrix.reindex_apply, Equiv.symm_apply_apply] using this
    rw [h1]

private theorem l05nFD_cartan_kernel {p N : ℕ} [NeZero (N - 1)] (hN : 2 ≤ N)
    {c : Fin (N - 1) → ZMod p}
    (hc : ∀ i : Fin (N - 1),
      ∑ k : Fin (N - 1), (CartanMatrix.A (N - 1) i k : ZMod p) * c k = 0) :
    ∀ j : Fin (N - 1), c j = (((j : ℕ) + 1 : ℕ) : ZMod p) * c 0 := by
  intro j
  have hrow := cartanA_ker_coord (c := c) hc (j : ℕ) j.isLt
  have h0 : (fun m => if hm : m < N - 1 then c ⟨m, hm⟩ else 0) 0 = c 0 := by
    simp only [dif_pos (by omega : 0 < N - 1)]
    rfl
  rw [h0] at hrow
  rw [hrow]
  push_cast
  ring

private theorem l05nFD_ker_le_one {p N : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {h : Λ → V} {CK : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hN : 5 ≤ N) (hdim : Module.finrank (ZMod p) V = N - 1)
    {α : Λ → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hcol : ∀ a k : Fin (N - 1),
      (CK (e a) (e k) : ZMod p) = (CartanMatrix.A (N - 1) a k : ZMod p))
    {v w : V} (hv : ∀ i, α i v = 0) (hw : ∀ i, α i w = 0) (hw0 : w ≠ 0) :
    ∃ c : ZMod p, v = c • w := by
  haveI : FiniteDimensional (ZMod p) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; omega)
  haveI : NeZero (N - 1) := ⟨by omega⟩
  let T : V →ₗ[ZMod p] (Λ → ZMod p) :=
    { toFun := fun v => fun i => α i v
      map_add' := by intro v w; ext i; simp
      map_smul' := by intro a v; ext i; simp [smul_eq_mul] }
  have hkerfin : Module.finrank (ZMod p) (LinearMap.ker T) ≤ 1 := by
    let Φ : (Fin (N - 1) → ZMod p) →ₗ[ZMod p] (Λ → ZMod p) :=
      { toFun := fun c => ∑ k : Fin (N - 1), c k • T (h (e k))
        map_add' := by
          intro c d
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := by
          intro a c
          simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply] }
    let wvec : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
    have hwne : wvec ≠ 0 := by
      intro hzero
      simpa [wvec] using congrFun hzero 0
    have hkerle : LinearMap.ker Φ ≤
        Submodule.span (ZMod p) ({wvec} : Set (Fin (N - 1) → ZMod p)) := by
      intro c hc
      have hc0 : Φ c = 0 := LinearMap.mem_ker.mp hc
      have heq : ∀ a : Fin (N - 1),
          ∑ k : Fin (N - 1), (CartanMatrix.A (N - 1) a k : ZMod p) * c k = 0 := by
        intro a
        have hrow : (Φ c) (e a) = 0 := show (Φ c) (e a) = 0 from congrFun hc0 (e a)
        have happ : (Φ c) (e a) =
            ∑ k : Fin (N - 1), c k * (CK (e a) (e k) : ZMod p) := by
          change (∑ k : Fin (N - 1), c k • T (h (e k))) (e a) = _
          rw [Finset.sum_apply]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Pi.smul_apply, smul_eq_mul]
          exact congrArg (fun x => c k * x) (hpair (e a) (e k))
        rw [happ] at hrow
        calc ∑ k, (CartanMatrix.A (N - 1) a k : ZMod p) * c k
            = ∑ k, (CK (e a) (e k) : ZMod p) * c k := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← hcol a k]
          _ = ∑ k, c k * (CK (e a) (e k) : ZMod p) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [mul_comm]
          _ = 0 := hrow
      have hcoord := l05nFD_cartan_kernel (p := p) (N := N) (by omega) heq
      have hcw : c = c 0 • wvec := by
        ext j
        rw [hcoord j, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hcw]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton wvec))
    have hkerfinΦ : Module.finrank (ZMod p) (LinearMap.ker Φ) ≤ 1 := by
      calc Module.finrank (ZMod p) (LinearMap.ker Φ)
          ≤ Module.finrank (ZMod p)
              (Submodule.span (ZMod p) ({wvec} : Set (Fin (N - 1) → ZMod p))) :=
            Submodule.finrank_mono hkerle
        _ = 1 := finrank_span_singleton hwne
    have hΦrank : N - 2 ≤ Module.finrank (ZMod p) (LinearMap.range Φ) := by
      have hrn := LinearMap.finrank_range_add_finrank_ker (f := Φ)
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
      omega
    have hrange : LinearMap.range Φ ≤ LinearMap.range T := by
      rintro x ⟨c, rfl⟩
      change (∑ k : Fin (N - 1), c k • T (h (e k))) ∈ LinearMap.range T
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (LinearMap.mem_range_self T (h (e k)))
    have hTrank : N - 2 ≤ Module.finrank (ZMod p) (LinearMap.range T) :=
      le_trans hΦrank (Submodule.finrank_mono hrange)
    have hrn := LinearMap.finrank_range_add_finrank_ker (f := T)
    rw [hdim] at hrn
    omega
  have hvK : v ∈ LinearMap.ker T := by
    rw [LinearMap.mem_ker]; ext i; exact show α i v = 0 from hv i
  have hwK : w ∈ LinearMap.ker T := by
    rw [LinearMap.mem_ker]; ext i; exact show α i w = 0 from hw i
  by_contra hcon
  push Not at hcon
  have hli2 : LinearIndependent (ZMod p) ![w, v] :=
    (LinearIndependent.pair_iff' hw0).mpr fun a => (hcon a).symm
  have hspan2 : Submodule.span (ZMod p) (Set.range ![w, v]) ≤ LinearMap.ker T := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hwK
    · exact hvK
  have h2 : (2 : ℕ) ≤ Module.finrank (ZMod p) (LinearMap.ker T) :=
    calc (2 : ℕ) = Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range ![w, v])) := by
          rw [finrank_span_eq_card hli2, Fintype.card_fin]
      _ ≤ Module.finrank (ZMod p) (LinearMap.ker T) := Submodule.finrank_mono hspan2
  omega

private theorem l05nFD_two_mul_pred_sub {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 2 ≤ N) :
    (2 : ZMod p) * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) = 0 := by
  have hNcast : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p N).2 hpN
  have hcast : ((N : ℕ) : ZMod p) = 2 * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) := by
    have h1 : ((N - 1 : ℕ) : ZMod p) = (N : ZMod p) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ N by omega)]; norm_num
    have h2 : ((N - 2 : ℕ) : ZMod p) = (N : ZMod p) - 2 := by
      rw [Nat.cast_sub (show 2 ≤ N by omega)]; norm_num
    rw [h1, h2]; ring
  rw [← hcast, hNcast]

private theorem l05nFD_A_mul_d {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N)
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
      convert l05nFD_two_mul_pred_sub (p := p) (N := N) hpN (by omega) using 1
      ring

private theorem l05nFD_h_mem_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
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

private theorem l05nFD_alpha_y {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
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

private theorem l05nFD_pow_eq_of_smul {p : ℕ} [NeZero p] {E : Type} [Group E] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) {a b : E} {c : ZMod p}
    (hb : ι (Additive.ofMul b) = c • ι (Additive.ofMul a)) : b = a ^ c.val := by
  have hnsmul : c • ι (Additive.ofMul a) = c.val • ι (Additive.ofMul a) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul]
  apply Additive.ofMul.injective
  rw [ofMul_pow]
  apply ι.injective
  rw [map_nsmul, hb, hnsmul]

theorem ggXDatumA_dep_K_dim {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) (hyK : y ∉ K) {N : ℕ} (hN : 5 ≤ N)
    (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ}
    {CK : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hdim : Module.finrank (ZMod p) V = N - 1) :
    ¬ LinearIndependent (ZMod p) h := by
  classical
  intro hli
  haveI : NeZero (N - 1) := ⟨by omega⟩
  have hcol := l05nFD_cartan_col (p := p) e hMK hCK
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
    refine ⟨Additive.toMul (ι.symm (h i)), l05nFD_h_mem_K hp2 hH hCK hφ hpair hAK i, ?_⟩
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
      rw [hcol j i]
    rw [hsum]
    have hAd := l05nFD_A_mul_d (p := p) (N := N) hpN j
    calc ∑ i : Fin (N - 1),
          (((i : ℕ) + 1 : ℕ) : ZMod p) * (CartanMatrix.A (N - 1) j i : ZMod p)
        = ∑ i : Fin (N - 1),
          (CartanMatrix.A (N - 1) j i : ZMod p) * (((i : ℕ) + 1 : ℕ) : ZMod p) := by
          refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 0 := hAd
  have hαy : ∀ j : Λ, α j (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 :=
    l05nFD_alpha_y hp2 hH hy hφ hpair hCK hAK
  obtain ⟨c, hc⟩ := l05nFD_ker_le_one (p := p) (N := N) e hN hdim hpair hcol hαy hαv hv_ne
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hy1 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      have hof : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 := by
        apply ι.injective
        rw [map_zero, hc, hc0, zero_smul]
      have := congrArg Additive.toMul hof
      simpa using this
    exact ggRC_y_ne_one hH (by simpa using congrArg Subtype.val hy1)
  have hv_mem : v ∈ M := by
    have hv_sum : v = ∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • h (e i) := rfl
    rw [hv_sum]
    refine M.sum_mem fun i _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact M.nsmul_mem (hM (e i)) _
  have hy_mem : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ∈ M := by
    rw [hc]
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact M.nsmul_mem hv_mem c.val
  obtain ⟨b, hbK, hbw⟩ := hy_mem
  have hb_eq : b = (⟨y, hy⟩ : ↥Bs) := Additive.ofMul.injective (ι.injective hbw)
  rw [hb_eq] at hbK
  exact hyK hbK

theorem ggXDatumA_frame_K_dim {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) {N : ℕ} (hN : 5 ≤ N) (hpN : p ∣ N)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hdep : ¬ LinearIndependent (ZMod p) h) (hdim : Module.finrank (ZMod p) V = N - 1) :
    GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨y, hy⟩)) := by
  classical
  haveI : NeZero (N - 1) := ⟨by omega⟩
  have hcol := l05nFD_cartan_col (p := p) e hMK hCK
  have hx_ne : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ≠ 0 := by
    intro h0
    have hy1 : (⟨y, hy⟩ : ↥Bs) ≠ 1 := by
      intro h1
      exact ggRC_y_ne_one hH (by simpa using congrArg Subtype.val h1)
    apply hy1
    have h1 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  have hαy : ∀ j : Λ, α j (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 :=
    l05nFD_alpha_y hp2 hH hy hφ hpair hCK hAK
  refine ⟨?_, hpN, hx_ne, ?_, ?_, ?_⟩
  · intro i j
    rw [hpair (e i) (e j), hcol i j]
  · intro i
    exact hαy (e i)
  · intro v hv
    obtain ⟨c, hc⟩ := l05nFD_ker_le_one (p := p) (N := N) e hN hdim hpair hcol
      (fun j => by simpa using hv (e.symm j)) hαy hx_ne
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro hli
    exact hdep ((linearIndependent_equiv (R := ZMod p) e).mp hli)

theorem ggNbr_cent_le_of_fix {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs K : Subgroup G} {y : G} (hy : y ∈ Bs) {Λ : Type} [Fintype Λ] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) (hαh : ∀ i, α i (h i) = 2)
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hfix : ∀ v : V, (∀ j : Λ, α j v = 0) →
      v ∈ Submodule.span (ZMod p) ({ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} : Set V)) :
    Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y := by
  intro b hb
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let bb : ↥Bs := ⟨b, hb.1⟩
  have hfixb : ∀ j : Λ, φ j bb = bb := by
    intro j
    have hmem : φ j ∈ ggAutomizer K Bs := by
      rw [hAK]
      exact Subgroup.subset_closure (Set.mem_range_self j)
    obtain ⟨g, hgK, hgN, hgconj⟩ := (mem_ggAutomizer_iff (H := K) (φ := φ j)).mp hmem
    apply Subtype.ext
    rw [hgconj bb]
    have hcomm : g * (bb : G) = (bb : G) * g :=
      (Subgroup.mem_centralizer_iff.mp hb.2) g hgK
    rw [hcomm]
    group
  have hαb : ∀ j : Λ, α j (ι (Additive.ofMul bb)) = 0 := by
    intro j
    have hlin : ggLin (p := p) ι (φ j) (ι (Additive.ofMul bb)) = ι (Additive.ofMul bb) :=
      (ggLin_fix_iff (p := p) ι (φ j) bb).mp (hfixb j)
    have h1 := hφ j (ι (Additive.ofMul bb))
    rw [hlin] at h1
    have h2 : α j (ι (Additive.ofMul bb)) • h j = 0 := sub_eq_self.mp h1.symm
    have h3 : α j (α j (ι (Additive.ofMul bb)) • h j) = 0 := by
      rw [h2, map_zero]
    rw [map_smul, smul_eq_mul, hαh j] at h3
    exact (mul_eq_zero.mp h3).resolve_right (zmod_two_ne_zero hp2)
  have hmem := hfix (ι (Additive.ofMul bb)) hαb
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hpow : bb = (⟨y, hy⟩ : ↥Bs) ^ c.val := l05nFD_pow_eq_of_smul (p := p) ι hc.symm
  refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
  rw [zpow_natCast]
  exact (congrArg Subtype.val hpow).symm
end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagPsiBlk

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {d : List ℕ}

private theorem q2cFV_eq_zero_of_vdm {ι : Type*} [Fintype ι] (x : ι → K)
    (hx : Function.Injective x) (c : ι → K)
    (h : ∀ j < Fintype.card ι, ∑ i, c i * x i ^ j = 0) : c = 0 := by
  classical
  let e := Fintype.equivFin ι
  have hx' : Function.Injective fun i : Fin (Fintype.card ι) => x (e.symm i) :=
    hx.comp e.symm.injective
  have h' : ∀ j : Fin (Fintype.card ι),
      ∑ i : Fin (Fintype.card ι), c (e.symm i) * x (e.symm i) ^ (j : ℕ) = 0 := by
    intro j
    calc ∑ i : Fin (Fintype.card ι), c (e.symm i) * x (e.symm i) ^ (j : ℕ)
        = ∑ i : ι, c i * x i ^ (j : ℕ) :=
          e.symm.sum_comp (fun i : ι => c i * x i ^ (j : ℕ))
      _ = 0 := h j.val j.isLt
  have hzero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (f := fun i : Fin (Fintype.card ι) => x (e.symm i))
    (v := fun i : Fin (Fintype.card ι) => c (e.symm i)) hx' h'
  funext i
  simpa using congrFun hzero (e i)

private theorem q2cFV_blockCoord_lt (hd : IsCut n d) {b j : ℕ} (hb : b + 1 < d.length)
    (hj : j < blockSize d b) : d.getD b 0 + j < n := by
  have hle : d.getD (b + 1) 0 ≤ n := q2cFPo_le_last hd hb
  unfold blockSize at hj
  omega

private theorem q2cFV_block_add (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length) :
    d.getD b 0 + blockSize d b = d.getD (b + 1) 0 := by
  have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := le_of_lt (hd.strict b hb)
  unfold blockSize
  omega

private theorem q2cFV_bvec_apply_of_mem {b : ℕ} {pol : List Bool} {ω : Fin 4 → K} {t : Fin 4}
    {k : Fin n} (h1 : d.getD b 0 ≤ k.val) (h2 : k.val < d.getD (b + 1) 0) :
    q2cFPo_bvec (K := K) (n := n) d pol ω b t k =
      (if pol.getD b false then (if k.val - d.getD b 0 = t.val then 1 else 0)
        else ω t ^ (k.val - d.getD b 0)) := by
  simp only [q2cFPo_bvec]
  rw [if_pos ⟨h1, h2⟩]

private theorem q2cFV_bvec_apply_block (hd : IsCut n d) {b j : ℕ} (hb : b + 1 < d.length)
    (hj : j < blockSize d b) {pol : List Bool} {ω : Fin 4 → K} {t : Fin 4} :
    q2cFPo_bvec (K := K) (n := n) d pol ω b t
        ⟨d.getD b 0 + j, q2cFV_blockCoord_lt hd hb hj⟩ =
      (if pol.getD b false then (if j = t.val then 1 else 0) else ω t ^ j) := by
  rw [q2cFV_bvec_apply_of_mem (k := ⟨d.getD b 0 + j, q2cFV_blockCoord_lt hd hb hj⟩)
    (by simp) (by simp only [Fin.val_mk]; unfold blockSize at hj; omega)]
  simp only [Nat.add_sub_cancel_left]

private theorem q2cFV_sum_bvec_apply (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    {pol : List Bool} {ω : Fin 4 → K} (hpol : pol.getD b false = false) {r j : ℕ}
    (hj : j < blockSize d b) (α : {t : Fin 4 // t.val < r} → K) :
    (∑ t : {t : Fin 4 // t.val < r}, α t • q2cFPo_bvec (K := K) (n := n) d pol ω b t.1)
        ⟨d.getD b 0 + j, q2cFV_blockCoord_lt hd hb hj⟩ =
      ∑ t : {t : Fin 4 // t.val < r}, α t * ω t.1 ^ j := by
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Pi.smul_apply, smul_eq_mul,
    q2cFV_bvec_apply_block (b := b) (j := j) (t := t.1) hd hb hj]
  rw [if_neg (by rw [hpol]; exact Bool.false_ne_true)]

private theorem q2cFV_bvec_pol_apply_eq_zero {b : ℕ} {pol : List Bool} {ω : Fin 4 → K}
    (hpol : pol.getD b false = true) {t : Fin 4} {r : ℕ} (ht : t.val < r) {k : Fin n}
    (hk : d.getD b 0 + r ≤ k.val) :
    q2cFPo_bvec (K := K) (n := n) d pol ω b t k = 0 := by
  by_cases hblk : d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0
  · rw [q2cFV_bvec_apply_of_mem (k := k) hblk.1 hblk.2, if_pos hpol]
    have hne : k.val - d.getD b 0 ≠ t.val := by omega
    rw [if_neg hne]
  · simp only [q2cFPo_bvec]
    rw [if_neg hblk]

private theorem q2cFV_hermLin_apply (lo hi : ℕ) (u v : Fin n → K) :
    hermLin K f n lo hi u v =
      ∑ i : Fin n, if lo ≤ i.val ∧ i.val < hi then sg K f (u i) * v i else 0 := by
  rw [hermLin, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : lo ≤ i.val ∧ i.val < hi <;> simp [h]

private theorem q2cFV_hermLin_bvec_pol {b : ℕ} {pol : List Bool} {ω : Fin 4 → K}
    (hpol : pol.getD b false = true) {t : Fin 4} {k : Fin n}
    (h1 : d.getD b 0 ≤ k.val) (h2 : k.val < d.getD (b + 1) 0)
    (hk : k.val - d.getD b 0 = t.val) (v : Fin n → K) :
    hermLin K f n (d.getD b 0) (d.getD (b + 1) 0)
      (q2cFPo_bvec (K := K) (n := n) d pol ω b t) v = v k := by
  rw [q2cFV_hermLin_apply, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
  · rw [if_pos ⟨h1, h2⟩, q2cFV_bvec_apply_of_mem (k := k) h1 h2, if_pos hpol, if_pos hk]
    simp
  · intro i _ hik
    by_cases hic : d.getD b 0 ≤ i.val ∧ i.val < d.getD (b + 1) 0
    · rw [if_pos hic]
      have hne : i.val - d.getD b 0 ≠ t.val := by
        intro h
        apply hik
        apply Fin.ext
        omega
      rw [q2cFV_bvec_apply_of_mem (k := i) hic.1 hic.2, if_pos hpol, if_neg hne]
      simp
    · rw [if_neg hic]

private theorem q2cFV_le_perpB_of_Vsub {lo hi : ℕ} (U : Submodule K (Fin n → K)) :
    Vsub n lo ≤ perpB K f n lo hi U := by
  intro v hv
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u _
  rw [q2cFV_hermLin_apply]
  exact Finset.sum_eq_zero fun i _ => by
    by_cases h : lo ≤ i.val ∧ i.val < hi
    · simp [h, hv i h.1]
    · simp [h]

private theorem q2cFV_bvec_mem_A {b r : ℕ} (pol : List Bool) {ω : Fin 4 → K}
    (t : {t : Fin 4 // t.val < r}) :
    q2cFPo_bvec (K := K) (n := n) d pol ω b t.1 ∈ q2cFPo_A d pol ω b r :=
  Submodule.subset_span ⟨t, rfl⟩

theorem q2cFPo_finrank_A (hd : IsCut n d) (pol : List Bool) {ω : Fin 4 → K}
    (hω : Function.Injective ω) {b r : ℕ} (hb : b + 1 < d.length) (hs : blockSize d b ≤ 4)
    (hr : r ≤ blockSize d b) : finrank K (q2cFPo_A (n := n) d pol ω b r) = r := by
  classical
  have hA : q2cFPo_A (n := n) d pol ω b r =
      Submodule.span K (Set.range fun t : {t : Fin 4 // t.val < r} =>
        q2cFPo_bvec (K := K) (n := n) d pol ω b t.1) := rfl
  have hcard : Fintype.card {t : Fin 4 // t.val < r} = r :=
    Fintype.card_fin_lt_of_le (le_trans hr hs)
  have hli : LinearIndependent K (fun t : {t : Fin 4 // t.val < r} =>
      q2cFPo_bvec (K := K) (n := n) d pol ω b t.1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_cases hpol : pol.getD b false = true
    · intro t₀
      have hk : (⟨d.getD b 0 + t₀.1.val,
          q2cFV_blockCoord_lt hd hb (lt_of_lt_of_le t₀.2 hr)⟩ : Fin n).val =
          d.getD b 0 + t₀.1.val := rfl
      have hev := congrFun hg ⟨d.getD b 0 + t₀.1.val,
          q2cFV_blockCoord_lt hd hb (lt_of_lt_of_le t₀.2 hr)⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
      have hterm : ∀ i : {t : Fin 4 // t.val < r},
          q2cFPo_bvec (K := K) (n := n) d pol ω b i.1
            ⟨d.getD b 0 + t₀.1.val,
              q2cFV_blockCoord_lt hd hb (lt_of_lt_of_le t₀.2 hr)⟩ =
          (if t₀.1.val = i.1.val then 1 else 0) := by
        intro i
        rw [q2cFV_bvec_apply_block (b := b) (j := t₀.1.val) (t := i.1) hd hb
          (lt_of_lt_of_le t₀.2 hr), if_pos hpol]
      simp only [hterm] at hev
      have hsingle : (∑ i : {t : Fin 4 // t.val < r},
          g i * (if t₀.1.val = i.1.val then 1 else 0)) = g t₀ := by
        rw [Finset.sum_eq_single t₀
          (fun i _ hi => by
            have hne : t₀.1.val ≠ i.1.val :=
              fun h => hi (Subtype.ext (Fin.ext h)).symm
            rw [if_neg hne, mul_zero])
          (fun h => absurd (Finset.mem_univ t₀) h)]
        rw [if_pos rfl, mul_one]
      rw [hsingle] at hev
      exact hev
    · have hpol' : pol.getD b false = false := by
        cases hp : pol.getD b false <;> simp_all
      intro t
      have hkey : ∀ j < Fintype.card {t : Fin 4 // t.val < r},
          ∑ i : {t : Fin 4 // t.val < r}, g i * ω i.1 ^ j = 0 := by
        intro j hj
        have hjr : j < r := by rwa [hcard] at hj
        have hev := congrFun hg ⟨d.getD b 0 + j,
            q2cFV_blockCoord_lt hd hb (lt_of_lt_of_le hjr hr)⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
        have hterm : ∀ i : {t : Fin 4 // t.val < r},
            q2cFPo_bvec (K := K) (n := n) d pol ω b i.1
              ⟨d.getD b 0 + j,
                q2cFV_blockCoord_lt hd hb (lt_of_lt_of_le hjr hr)⟩ =
            ω i.1 ^ j := by
          intro i
          rw [q2cFV_bvec_apply_block (b := b) (j := j) (t := i.1) hd hb
            (lt_of_lt_of_le hjr hr), if_neg (by rw [hpol']; exact Bool.false_ne_true)]
        simp only [hterm] at hev
        exact hev
      have hzero := q2cFV_eq_zero_of_vdm (fun i : {t : Fin 4 // t.val < r} => ω i.1)
        (hω.comp Subtype.val_injective) g hkey
      exact congrFun hzero t
  rw [hA, finrank_span_eq_card hli, hcard]

private theorem q2cFV_vdm_sumType {ω : Fin 4 → K} (hω : Function.Injective ω)
    (hσω : ∀ i j : Fin 4, i.val + j.val ≤ 2 → sg K f (ω i) ≠ ω j) {b r : ℕ}
    (hs : blockSize d b ≤ 4) (hr : r ≤ blockSize d b)
    {α : {t : Fin 4 // t.val < r} → K}
    {β : {t : Fin 4 // t.val < blockSize d b - r} → K}
    (h : ∀ j < blockSize d b,
      (∑ t : {t : Fin 4 // t.val < r}, sg K f (α t) * (sg K f (ω t.1)) ^ j)
        = ∑ t : {t : Fin 4 // t.val < blockSize d b - r}, β t * (ω t.1) ^ j) :
    α = 0 := by
  classical
  let ιs := {t : Fin 4 // t.val < blockSize d b - r}
  let J := {t : Fin 4 // t.val < r} ⊕ ιs
  let xfun : J → K :=
    Sum.elim (fun t : {t : Fin 4 // t.val < r} => sg K f (ω t.1)) (fun t : ιs => ω t.1)
  let cfun : J → K :=
    Sum.elim (fun t : {t : Fin 4 // t.val < r} => sg K f (α t)) (fun t : ιs => -β t)
  have hcardJ : Fintype.card J = blockSize d b := by
    have h1 : Fintype.card {t : Fin 4 // t.val < r} = r :=
      Fintype.card_fin_lt_of_le (le_trans hr hs)
    have h2 : Fintype.card ιs = blockSize d b - r := Fintype.card_fin_lt_of_le (by omega)
    rw [Fintype.card_sum, h1, h2]
    omega
  have hinj : Function.Injective xfun := by
    intro i j hij
    rcases i with t | t <;> rcases j with u | u
    · simp only [xfun, Sum.elim_inl] at hij
      have htu : t.1 = u.1 := hω ((sg K f).injective hij)
      exact congrArg Sum.inl (Subtype.ext htu)
    · simp only [xfun, Sum.elim_inl, Sum.elim_inr] at hij
      exact absurd hij (hσω t.1 u.1 (by have := t.2; have := u.2; omega))
    · simp only [xfun, Sum.elim_inl, Sum.elim_inr] at hij
      exact absurd hij.symm (hσω u.1 t.1 (by have := t.2; have := u.2; omega))
    · simp only [xfun, Sum.elim_inr] at hij
      have htu : t.1 = u.1 := hω hij
      exact congrArg Sum.inr (Subtype.ext htu)
  have hvanish : ∀ j < Fintype.card J, ∑ i : J, cfun i * xfun i ^ j = 0 := by
    intro j hj
    have hjs : j < blockSize d b := by rwa [hcardJ] at hj
    have hmain := h j hjs
    rw [Fintype.sum_sum_type]
    simp only [cfun, xfun, Sum.elim_inl, Sum.elim_inr]
    have hneg : (∑ t : ιs, (-β t) * (ω t.1) ^ j) =
        -(∑ t : ιs, β t * (ω t.1) ^ j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hmain, hneg, add_neg_cancel]
  have hc0 : cfun = 0 := q2cFV_eq_zero_of_vdm xfun hinj cfun hvanish
  funext t
  have h := congrFun hc0 (Sum.inl t)
  simp only [cfun, Sum.elim_inl, Pi.zero_apply] at h
  exact (sg K f).map_eq_zero_iff.mp h

theorem q2cFPo_inf_sgS_A (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d) {pol : List Bool}
    {ω : Fin 4 → K} (hω : Function.Injective ω)
    (hσω : ∀ i j : Fin 4, i.val + j.val ≤ 2 → sg K f (ω i) ≠ ω j) {b r : ℕ}
    (hb : b + 1 < d.length) (hs : blockSize d b ≤ 4) (hr : r ≤ blockSize d b)
    (hpol : pol.getD b false = false) :
    (Vsub n (d.getD b 0) ⊔ q2cFPo_A d pol ω b r) ⊓
      sgS K f n (Vsub n (d.getD b 0) ⊔ q2cFPo_A d pol ω b (blockSize d b - r)) =
        Vsub n (d.getD b 0) := by
  classical
  apply le_antisymm
  · intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    obtain ⟨a, ha, x, hxA, hax⟩ := Submodule.mem_sup.mp hv1
    have hv2' : sgv K f n v ∈ Vsub n (d.getD b 0) ⊔
        q2cFPo_A d pol ω b (blockSize d b - r) := hv2
    obtain ⟨a', ha', x', hx'A, ha'x'⟩ := Submodule.mem_sup.mp hv2'
    have hxA' : x ∈ Submodule.span K (Set.range (fun t : {t : Fin 4 // t.val < r} =>
        q2cFPo_bvec (K := K) (n := n) d pol ω b t.1)) := hxA
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun (R := K)).mp hxA'
    have hx'A' : x' ∈ Submodule.span K (Set.range
        (fun t : {t : Fin 4 // t.val < blockSize d b - r} =>
          q2cFPo_bvec (K := K) (n := n) d pol ω b t.1)) := hx'A
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun (R := K)).mp hx'A'
    have hα0 : α = 0 := q2cFV_vdm_sumType (f := f) hω hσω hs hr (fun j hj => by
      have hklt : d.getD b 0 + j < n := q2cFV_blockCoord_lt hd hb hj
      have hx_eval : x ⟨d.getD b 0 + j, hklt⟩ =
          ∑ t : {t : Fin 4 // t.val < r}, α t * ω t.1 ^ j := by
        rw [← hα]
        exact q2cFV_sum_bvec_apply hd hb hpol hj α
      have hx'_eval : x' ⟨d.getD b 0 + j, hklt⟩ =
          ∑ t : {t : Fin 4 // t.val < blockSize d b - r}, β t * ω t.1 ^ j := by
        rw [← hβ]
        exact q2cFV_sum_bvec_apply (r := blockSize d b - r) hd hb hpol hj β
      have hvk : v ⟨d.getD b 0 + j, hklt⟩ = x ⟨d.getD b 0 + j, hklt⟩ := by
        rw [hax.symm, Pi.add_apply, ha _ (by simp), zero_add]
      have hsg : sg K f (x ⟨d.getD b 0 + j, hklt⟩) = x' ⟨d.getD b 0 + j, hklt⟩ := by
        have h2 : sgv K f n v ⟨d.getD b 0 + j, hklt⟩ = x' ⟨d.getD b 0 + j, hklt⟩ := by
          rw [ha'x'.symm, Pi.add_apply, ha' _ (by simp), zero_add]
        calc sg K f (x ⟨d.getD b 0 + j, hklt⟩)
            = sg K f (v ⟨d.getD b 0 + j, hklt⟩) := by rw [hvk]
          _ = sgv K f n v ⟨d.getD b 0 + j, hklt⟩ := rfl
          _ = x' ⟨d.getD b 0 + j, hklt⟩ := h2
      rw [hx_eval, hx'_eval] at hsg
      rw [← hsg, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul, map_pow])
    have hx0 : x = 0 := by
      rw [← hα]
      simp [hα0]
    have hv_eq : v = a := by rw [hax.symm, hx0, add_zero]
    rw [hv_eq]
    exact ha
  · refine le_inf le_sup_left ?_
    have h : sgS K f n (Vsub (K := K) n (d.getD b 0)) ≤
        sgS K f n (Vsub (K := K) n (d.getD b 0) ⊔
          q2cFPo_A d pol ω b (blockSize d b - r)) :=
      sgS_mono (f := f) (show Vsub (K := K) n (d.getD b 0) ≤
        Vsub (K := K) n (d.getD b 0) ⊔ q2cFPo_A d pol ω b (blockSize d b - r)
          from le_sup_left)
    rwa [sgS_Vsub] at h

theorem q2cFPo_inf_perpB_A (hd : IsCut n d) {pol : List Bool} {ω : Fin 4 → K} {b r : ℕ}
    (hb : b + 1 < d.length) (hs : blockSize d b ≤ 4) (hr : r ≤ blockSize d b)
    (hpol : pol.getD b false = true) :
    (Vsub n (d.getD b 0) ⊔ q2cFPo_A d pol ω b r) ⊓
      (perpB K f n (d.getD b 0) (d.getD (b + 1) 0)
        (Vsub n (d.getD b 0) ⊔ q2cFPo_A d pol ω b r) ⊓ Vsub n (d.getD (b + 1) 0)) =
        Vsub n (d.getD b 0) := by
  classical
  apply le_antisymm
  · intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    obtain ⟨hvperp, _hvhi⟩ := Submodule.mem_inf.mp hv2
    obtain ⟨a, ha, x, hxA, hax⟩ := Submodule.mem_sup.mp hv1
    have hxA' : x ∈ Submodule.span K (Set.range (fun t : {t : Fin 4 // t.val < r} =>
        q2cFPo_bvec (K := K) (n := n) d pol ω b t.1)) := hxA
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun (R := K)).mp hxA'
    simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker] at hvperp
    intro k hk
    by_cases hkr : d.getD b 0 + r ≤ k.val
    · have hxk : x k = 0 := by
        rw [← hα, Finset.sum_apply]
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [Pi.smul_apply, smul_eq_mul,
          q2cFV_bvec_pol_apply_eq_zero (b := b) (ω := ω) (t := t.1) hpol t.2 hkr]
        simp
      rw [hax.symm, Pi.add_apply, ha k hk, hxk, add_zero]
    · have hbs := q2cFV_block_add hd hb
      have hklt : k.val < d.getD b 0 + r := by omega
      have hkhi : k.val < d.getD (b + 1) 0 := by omega
      have hks : k.val - d.getD b 0 < blockSize d b := by omega
      have ht4 : k.val - d.getD b 0 < 4 := lt_of_lt_of_le hks hs
      have ht_lt : k.val - d.getD b 0 < r := by omega
      let t : {t : Fin 4 // t.val < r} := ⟨⟨k.val - d.getD b 0, ht4⟩, ht_lt⟩
      have hbvec_mem : q2cFPo_bvec (K := K) (n := n) d pol ω b t.1 ∈
          Vsub n (d.getD b 0) ⊔ q2cFPo_A d pol ω b r :=
        Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, q2cFPo_bvec (K := K) (n := n) d pol ω b t.1,
          q2cFV_bvec_mem_A pol t, by simp⟩
      have hh := hvperp (q2cFPo_bvec (K := K) (n := n) d pol ω b t.1) hbvec_mem
      rw [q2cFV_hermLin_bvec_pol (b := b) (t := t.1) hpol hk hkhi rfl v] at hh
      exact hh
  · refine le_inf le_sup_left (le_inf (q2cFV_le_perpB_of_Vsub _)
      (Vsub_mono (le_of_lt (hd.strict b hb))))

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

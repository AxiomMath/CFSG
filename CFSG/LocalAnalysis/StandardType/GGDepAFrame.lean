module

public import CFSG.LocalAnalysis.StandardType.GGRCTypeADet
public import CFSG.LocalAnalysis.StandardType.GGTBTorCartan
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGDepAFrame (p N : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V) (x : V) : Prop where
  pair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)
  dvd : p ∣ N
  x_ne : x ≠ 0
  x_ker : ∀ i, α i x = 0
  fix : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod p) {x}
  dep : ¬ LinearIndependent (ZMod p) h

private theorem l05nDF1_ggIntCartan_three {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b) (hm : M a b = 3) :
    C a b = -1 ∧ C b a = -1 := by
  rcases hC.2 a b hab with ⟨h2, -⟩ | ⟨-, h1, h2⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exfalso; omega
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega

private theorem l05nDF1_ggIntCartan_two {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b) (hm : M a b = 2) :
    C a b = 0 ∧ C b a = 0 := by
  rcases hC.2 a b hab with ⟨-, h1, h2⟩ | ⟨h3, -, -⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

private theorem l05nDF1_coxeterA_entry (m : ℕ) (i j : Fin m) :
    (CoxeterMatrix.A m) i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

private theorem l05nDF1_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 :=
  rfl

private theorem l05nDF1_cartan_of_reindex {m : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (eA : Fin m ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = (CoxeterMatrix.A m).reindex eA) :
    ∀ i j : Fin m, CL (eA i) (eA j) = CartanMatrix.A m i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCL.1, l05nDF1_cartanA_entry]
    simp
  · have hentryM : ML (eA i) (eA j) = (CoxeterMatrix.A m) i j := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hne : eA i ≠ eA j := fun h => hij (eA.injective h)
    by_cases h3 : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
    · have hM3 : ML (eA i) (eA j) = 3 := by
        rw [hentryM, l05nDF1_coxeterA_entry, if_neg hij]
        rw [if_pos (h3.elim (fun h => Or.inr h) (fun h => Or.inl h))]
      have hthree := l05nDF1_ggIntCartan_three hCL hne hM3
      rw [hthree.1, l05nDF1_cartanA_entry, if_neg hij, if_pos h3]
    · have hM2 : ML (eA i) (eA j) = 2 := by
        rw [hentryM, l05nDF1_coxeterA_entry, if_neg hij]
        rw [if_neg (fun h => h3 (h.elim (fun h => Or.inr h) (fun h => Or.inl h)))]
      have htwo := l05nDF1_ggIntCartan_two hCL hne hM2
      rw [htwo.1, l05nDF1_cartanA_entry, if_neg hij, if_neg h3]

private theorem l05nDF1_det_eq {m : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (eA : Fin m ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = (CoxeterMatrix.A m).reindex eA) :
    CL.det = (CartanMatrix.A m).det := by
  have hentry := l05nDF1_cartan_of_reindex eA hCL hML
  have hsub : CL = (CartanMatrix.A m).submatrix eA.symm eA.symm := by
    ext a b
    have h := hentry (eA.symm a) (eA.symm b)
    simpa [Matrix.submatrix_apply, Equiv.apply_symm_apply] using h
  rw [hsub]
  exact Matrix.det_submatrix_equiv_self eA.symm (CartanMatrix.A m)

private theorem l05nDF1_det_cast_eq_zero {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {V : Type} [AddCommGroup V] [Module (ZMod p) V] (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (C : Matrix Λ Λ ℤ)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hdep : ¬ LinearIndependent (ZMod p) h) : ((C.det : ℤ) : ZMod p) = 0 := by
  classical
  obtain ⟨c, hcsum, j, hcj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hcne : c ≠ 0 := fun hc => hcj (by rw [hc]; rfl)
  have hmul : Matrix.mulVec (C.map (fun x : ℤ => (x : ZMod p))) c = 0 := by
    funext i
    rw [Matrix.mulVec_apply_eq_sum, Pi.zero_apply]
    have happ := congrArg (fun v => α i v) hcsum
    simp only [map_sum, map_smul, map_zero, hP, smul_eq_mul] at happ
    rw [← happ]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.map_apply, mul_comm]
  have hdet0 : (C.map (fun x : ℤ => (x : ZMod p))).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hcne, hmul⟩
  rwa [Int.cast_det]

private theorem l05nDF1_dvd_of_dep {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (eA : Fin m ≃ Λ) (hCL : GGIntCartan ML CL) (hML : ML = (CoxeterMatrix.A m).reindex eA)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hP : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hdep : ¬ LinearIndependent (ZMod p) h) : p ∣ m + 1 := by
  have hdet := l05nDF1_det_cast_eq_zero h α CL hP hdep
  have hdetCL := l05nDF1_det_eq eA hCL hML
  rw [hdetCL, CartanMatrix.A_det] at hdet
  have hdvd : (p : ℤ) ∣ ((m + 1 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((m : ℤ) + 1) p).mp hdet
  exact Int.natCast_dvd_natCast.mp hdvd

private theorem l05nDF1_connected_end {m : ℕ} (hm : 1 ≤ m) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} (hconn : GGDeletedConnected ML b)
    (eA : Fin m ≃ Λ) (hML : ML = (CoxeterMatrix.A m).reindex eA) :
    (eA.symm b).val = 0 ∨ (eA.symm b).val + 2 = m + 1 := by
  classical
  set c : Fin m := eA.symm b with hcdef
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, hlast⟩ := hcon
  have hclt : c.val < m := c.isLt
  have h1 : 1 ≤ c.val := by omega
  have hc1 : c.val + 1 < m := by omega
  let ilow : Fin m := ⟨c.val - 1, by omega⟩
  let ihigh : Fin m := ⟨c.val + 1, by omega⟩
  have hlow_ne : ilow ≠ c := by
    intro h
    have hh := congrArg Fin.val h
    simp only [ilow, Fin.val_mk] at hh
    omega
  have hhigh_ne : ihigh ≠ c := by
    intro h
    have hh := congrArg Fin.val h
    simp only [ihigh, Fin.val_mk] at hh
    omega
  have hbc : eA c = b := by rw [hcdef, Equiv.apply_symm_apply]
  let u : {i : Λ // i ≠ b} := ⟨eA ilow, fun hb => hlow_ne (eA.injective (hb.trans hbc.symm))⟩
  let v : {i : Λ // i ≠ b} := ⟨eA ihigh, fun hb => hhigh_ne (eA.injective (hb.trans hbc.symm))⟩
  let R : {i : Λ // i ≠ b} → {i : Λ // i ≠ b} → Prop :=
    fun x y => x ≠ y ∧ ML.M x.1 y.1 ≠ 2
  have hstep : ∀ x y : {i : Λ // i ≠ b}, R x y →
      ((eA.symm x.1).val < c.val ↔ (eA.symm y.1).val < c.val) := by
    intro x y hxy
    obtain ⟨hxy_ne, hxy_2⟩ := hxy
    have hM : ML.M x.1 y.1 = (CoxeterMatrix.A m) (eA.symm x.1) (eA.symm y.1) := by
      rw [hML, CoxeterMatrix.reindex_apply]
    have hA2 : (CoxeterMatrix.A m) (eA.symm x.1) (eA.symm y.1) ≠ 2 := by
      rw [← hM]; exact hxy_2
    have hixy : eA.symm x.1 ≠ eA.symm y.1 :=
      fun h => hxy_ne (Subtype.ext (eA.symm.injective h))
    have hadj : (eA.symm y.1).val + 1 = (eA.symm x.1).val ∨
        (eA.symm x.1).val + 1 = (eA.symm y.1).val := by
      by_contra hcc
      apply hA2
      rw [l05nDF1_coxeterA_entry, if_neg hixy, if_neg hcc]
    have hxc : eA.symm x.1 ≠ c := by
      intro h
      exact x.2 (by simpa [Equiv.apply_symm_apply, hbc] using congrArg eA h)
    have hyc : eA.symm y.1 ≠ c := by
      intro h
      exact y.2 (by simpa [Equiv.apply_symm_apply, hbc] using congrArg eA h)
    have hxcv : (eA.symm x.1).val ≠ c.val := fun h => hxc (Fin.ext h)
    have hycv : (eA.symm y.1).val ≠ c.val := fun h => hyc (Fin.ext h)
    rcases hadj with h | h
    · constructor <;> intro hh <;> omega
    · constructor <;> intro hh <;> omega
  have hpu : (eA.symm u.1).val < c.val := by
    show (eA.symm (eA ilow)).val < c.val
    rw [Equiv.symm_apply_apply]
    show c.val - 1 < c.val
    omega
  have hpv : ¬ (eA.symm v.1).val < c.val := by
    show ¬ (eA.symm (eA ihigh)).val < c.val
    rw [Equiv.symm_apply_apply]
    show ¬ (c.val + 1 < c.val)
    omega
  have key : ∀ w : {i : Λ // i ≠ b}, Relation.ReflTransGen R u w →
      (eA.symm u.1).val < c.val → (eA.symm w.1).val < c.val := by
    intro w hw
    induction hw with
    | refl => exact id
    | tail hprev hr ih => exact fun hh => (hstep _ _ hr).mp (ih hh)
  exact hpv (key v (hconn u v) hpu)

theorem ggDepA_frame_of_datum {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (hA : GGIsTypeA ML) (hconn : GGDeletedConnected ML b)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hP : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hdep : ¬ LinearIndependent (ZMod p) h) :
    ∃ (N : ℕ) (e : Fin (N - 1) ≃ Λ), 3 ≤ N ∧ p ∣ N ∧
      (∀ i j, CL (e i) (e j) = CartanMatrix.A (N - 1) i j) ∧
      ((e.symm b).val = 0 ∨ (e.symm b).val + 2 = N) := by
  obtain ⟨m, eA, hm1, hML⟩ := hA
  have hdvd : p ∣ m + 1 := l05nDF1_dvd_of_dep hp2 hm1 eA hCL hML h α hP hdep
  refine ⟨m + 1, eA, ?_, hdvd, ?_, ?_⟩
  · by_contra hlt
    simp only [not_le] at hlt
    have hm : m = 1 := by omega
    have h2 : p ∣ 2 := by
      rw [hm] at hdvd
      simpa using hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)
  · exact l05nDF1_cartan_of_reindex eA hCL hML
  · exact l05nDF1_connected_end hm1 hconn eA hML

private theorem l05nDF2_two_mul_pred_sub {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 2 ≤ N) :
    (2 : ZMod p) * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) = 0 := by
  have hNcast : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p N).2 hpN
  have hcast : ((N : ℕ) : ZMod p) = 2 * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) := by
    have h1 : ((N - 1 : ℕ) : ZMod p) = (N : ZMod p) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ N by omega)]; norm_num
    have h2 : ((N - 2 : ℕ) : ZMod p) = (N : ZMod p) - 2 := by
      rw [Nat.cast_sub (show 2 ≤ N by omega)]; norm_num
    rw [h1, h2]; ring
  rw [← hcast, hNcast]

private theorem l05nDF2_A_mul_d {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N)
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
      convert l05nDF2_two_mul_pred_sub (p := p) (N := N) hpN (by omega) using 1
      ring

private theorem l05nDF2_two_le_of_dep {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V}
    (hdep : ¬ LinearIndependent (ZMod p) h) : 2 ≤ N := by
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨c, -, i, -⟩ := hdep
  have := i.isLt
  omega

theorem ggDepA_relation {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (F : GGDepAFrame p N h α x) :
    (∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • h i = 0) ∧
      x ∉ Submodule.span (ZMod p) (Set.range h) ∧
      Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) = N - 2 := by
  have hdep := F.dep
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨c, hcsum, i0, hi0⟩ := hdep
  have hc0 : c ≠ 0 := by
    intro hzero
    exact hi0 (by rw [hzero]; simp)
  have hN2 : 2 ≤ N := by
    have hlt := i0.isLt
    omega
  let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
  have hd0 : d ≠ 0 := by
    intro hzero
    have h1 := congrFun hzero ⟨0, by omega⟩
    simp [d] at h1
  have hcA : ∀ i, ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * c k = 0 := by
    intro i
    have hh := congrArg (α i) hcsum
    simp only [map_sum, map_smul, F.pair, smul_eq_mul, map_zero] at hh
    calc ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * c k
        = ∑ k, c k * (CartanMatrix.A (N - 1) i k : ZMod p) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_comm]
      _ = 0 := hh
  have hdA : ∀ i, ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * d k = 0 :=
    fun i => l05nDF2_A_mul_d (p := p) (N := N) F.dvd i
  have hsum : ∑ i : Fin (N - 1), d i • h i = 0 := by
    obtain ⟨l, hl⟩ := ggCartanA_ker_le_one c d hcA hdA hc0
    rw [hl]
    calc ∑ i, (l • c) i • h i
        = ∑ i, l • (c i • h i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply, smul_eq_mul, mul_smul]
      _ = l • ∑ i, c i • h i := by rw [Finset.smul_sum]
      _ = 0 := by rw [hcsum, smul_zero]
  have hrel : ∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • h i = 0 := by
    simpa [d] using hsum
  have hxnot : x ∉ Submodule.span (ZMod p) (Set.range h) := by
    intro hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨b, hb⟩ := hx
    have hbA : ∀ i, ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * b k = 0 := by
      intro i
      have hh := congrArg (α i) hb
      simp only [map_sum, map_smul, F.pair, smul_eq_mul, F.x_ker i, map_zero] at hh
      calc ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * b k
          = ∑ k, b k * (CartanMatrix.A (N - 1) i k : ZMod p) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_comm]
        _ = 0 := hh
    by_cases hb0 : b = 0
    · apply F.x_ne
      rw [← hb, hb0]; simp
    · obtain ⟨l, hl⟩ := ggCartanA_ker_le_one d b hdA hbA hd0
      apply F.x_ne
      rw [← hb, hl]
      calc ∑ i, (l • d) i • h i
          = ∑ i, l • (d i • h i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Pi.smul_apply, smul_eq_mul, mul_smul]
        _ = l • ∑ i, d i • h i := by rw [Finset.smul_sum]
        _ = 0 := by rw [hsum, smul_zero]
  have hfin : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) = N - 2 := by
    let e := Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) (Fin (N - 1))
    let ψ : (Fin (N - 1) →₀ ZMod p) →ₗ[ZMod p] V := Finsupp.linearCombination (ZMod p) h
    let d₀ : Fin (N - 1) →₀ ZMod p := e.symm d
    have hd₀i : ∀ i, d₀ i = d i := by
      intro i
      simp [d₀, e]
    have hψd₀ : ψ d₀ = 0 := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
      rw [show (∑ i, (fun i a => a • h i) i (d₀ i)) = ∑ i, d i • h i from by
            exact Finset.sum_congr rfl fun i _ => by rw [hd₀i i]]
      exact hsum
    have hd₀0 : d₀ ≠ 0 := by
      intro hz
      apply hd0
      funext i
      rw [← hd₀i i, hz]
      rfl
    have hker : ψ.ker = Submodule.span (ZMod p) ({d₀} : Set (Fin (N - 1) →₀ ZMod p)) := by
      apply le_antisymm
      · intro l hl
        rw [LinearMap.mem_ker] at hl
        have hsuml : ∑ i, l i • h i = 0 := by
          rw [Finsupp.linearCombination_apply] at hl
          rwa [Finsupp.sum_fintype l (fun i a => a • h i) (fun i => by simp)] at hl
        let c : Fin (N - 1) → ZMod p := fun i => l i
        have hcA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k = 0 := by
          intro j
          have hh := congrArg (α j) hsuml
          simp only [map_sum, map_smul, F.pair, smul_eq_mul, map_zero] at hh
          calc ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k
              = ∑ k, c k * (CartanMatrix.A (N - 1) j k : ZMod p) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [mul_comm]
            _ = 0 := hh
        rw [Submodule.mem_span_singleton]
        by_cases hl0 : l = 0
        · exact ⟨0, by rw [hl0]; simp⟩
        · have hc0 : c ≠ 0 := by
            intro hc
            apply hl0
            ext i
            exact congrFun hc i
          obtain ⟨a, ha⟩ := ggCartanA_ker_le_one d c hdA hcA hd0
          refine ⟨a, ?_⟩
          ext i
          have hi : c i = a * d i := by
            simpa [Pi.smul_apply, smul_eq_mul] using congrFun ha i
          show (a • d₀) i = l i
          rw [Finsupp.smul_apply, smul_eq_mul, hd₀i i]
          exact hi.symm
      · intro l hl
        rw [Submodule.mem_span_singleton] at hl
        obtain ⟨a, ha⟩ := hl
        rw [LinearMap.mem_ker, ← ha]
        rw [map_smul, hψd₀, smul_zero]
    have hkerfin : Module.finrank (ZMod p) ↥ψ.ker = 1 := by
      rw [hker]
      exact finrank_span_singleton hd₀0
    have hdomain : Module.finrank (ZMod p) (Fin (N - 1) →₀ ZMod p) = N - 1 := by
      rw [Module.finrank_finsupp_self, Fintype.card_fin]
    have hrk := LinearMap.finrank_range_add_finrank_ker ψ
    have hrange : Module.finrank (ZMod p) ↥ψ.range = N - 2 := by
      rw [hkerfin, hdomain] at hrk
      omega
    rw [← Finsupp.range_linearCombination (ZMod p) (v := h)]
    exact hrange
  exact ⟨hrel, hxnot, hfin⟩

theorem ggDepA_finrank_bounds {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x) :
    N - 1 ≤ Module.finrank (ZMod p) V ∧ Module.finrank (ZMod p) V ≤ N := by
  obtain ⟨hrel, hxnot, hfin⟩ := ggDepA_relation F
  have hN2 : 2 ≤ N := l05nDF2_two_le_of_dep F.dep
  have hx1 : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({x} : Set V)) = 1 := by
    simpa using finrank_span_singleton (K := ZMod p) (v := x) F.x_ne
  let e := Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) (Fin (N - 1))
  let Ψ : V →ₗ[ZMod p] (Fin (N - 1) →₀ ZMod p) :=
    e.symm.toLinearMap.comp (LinearMap.pi α)
  have hker_le : Ψ.ker ≤ Submodule.span (ZMod p) ({x} : Set V) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    apply F.fix v
    intro i
    have h1 := congrFun (congrArg (fun w => e w) hv) i
    simpa [Ψ, LinearMap.pi_apply, Finsupp.linearEquivFunOnFinite_apply] using h1
  have hkerfin : Module.finrank (ZMod p) ↥Ψ.ker ≤ 1 := by
    calc Module.finrank (ZMod p) ↥Ψ.ker
        ≤ Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({x} : Set V)) :=
          Submodule.finrank_mono hker_le
      _ = 1 := hx1
  have hcod : Module.finrank (ZMod p) (Fin (N - 1) →₀ ZMod p) = N - 1 := by
    rw [Module.finrank_finsupp_self, Fintype.card_fin]
  have hrange_le : Module.finrank (ZMod p) ↥Ψ.range ≤ N - 1 := by
    calc Module.finrank (ZMod p) ↥Ψ.range
        ≤ Module.finrank (ZMod p) (Fin (N - 1) →₀ ZMod p) := Submodule.finrank_le Ψ.range
      _ = N - 1 := hcod
  have hupper : Module.finrank (ZMod p) V ≤ N := by
    have hrk := LinearMap.finrank_range_add_finrank_ker Ψ
    rw [← hrk]
    omega
  let H := Submodule.span (ZMod p) (Set.range h)
  have hHfin : Module.finrank (ZMod p) ↥H = N - 2 := hfin
  have hinf_bot : H ⊓ Submodule.span (ZMod p) ({x} : Set V) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvH, hvx⟩ := hv
    rw [Submodule.mem_span_singleton] at hvx
    obtain ⟨a, ha⟩ := hvx
    by_cases ha0 : a = 0
    · rw [← ha, ha0, zero_smul]
    · exfalso
      apply hxnot
      have hxv : x = a⁻¹ • v := by
        rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [hxv]
      exact Submodule.smul_mem H a⁻¹ hvH
  have hsupfin : Module.finrank (ZMod p) ↥(H ⊔ Submodule.span (ZMod p) ({x} : Set V)) = N - 1 := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq H (Submodule.span (ZMod p) ({x} : Set V))
    rw [hinf_bot, finrank_bot, add_zero] at hsup
    rw [hsup, hHfin, hx1]
    omega
  have hlower : N - 1 ≤ Module.finrank (ZMod p) V := by
    have := Submodule.finrank_le (H ⊔ Submodule.span (ZMod p) ({x} : Set V))
    omega
  exact ⟨hlower, hupper⟩


end CFSG.StandardType

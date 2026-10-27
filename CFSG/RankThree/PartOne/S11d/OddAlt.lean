module

public import CFSG.RankThree.PartOne.S11d.OddIsoBasic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.PartOne.OddIso

open Module

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

theorem alt_comm [CharP K 2] (hB : B.IsAlt) (x y : V) : B x y = B y x := by
  rw [← hB.neg_eq, CharTwo.neg_eq]

variable {A : Module.End K V} {p : ℕ}

theorem range_invariant (A : Module.End K V) {w : V} (hw : w ∈ LinearMap.range (A - 1)) :
    A w ∈ LinearMap.range (A - 1) := by
  obtain ⟨u, rfl⟩ := hw
  refine ⟨A u, ?_⟩
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]

theorem isom_pow (hAB : ∀ v w, B (A v) (A w) = B v w) (i : ℕ) (v w : V) :
    B ((A ^ i) v) ((A ^ i) w) = B v w := by
  induction i generalizing v w with
  | zero => rfl
  | succ i ih => rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hAB]

theorem B_pow_left (hAB : ∀ v w, B (A v) (A w) = B v w) (hA : A ^ p = 1) {i : ℕ} (hi : i ≤ p)
    (v w : V) : B ((A ^ i) v) w = B v ((A ^ (p - i)) w) := by
  have h1 := isom_pow hAB i v ((A ^ (p - i)) w)
  rw [← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' hi, hA, Module.End.one_apply] at h1
  exact h1

theorem invariant_pow {M : Submodule K V} (hM : ∀ m ∈ M, A m ∈ M) (i : ℕ) :
    ∀ m ∈ M, (A ^ i) m ∈ M := by
  induction i with
  | zero => intro m hm; exact hm
  | succ i ih => intro m hm; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hM m hm)

theorem orth_invariant (hAB : ∀ v w, B (A v) (A w) = B v w) (hA : A ^ p = 1) (hp : 1 ≤ p)
    {M : Submodule K V} (hM : ∀ m ∈ M, A m ∈ M) {v : V} (hv : v ∈ B.orthogonal M) :
    A v ∈ B.orthogonal M := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro m hm
  have hx : A ((A ^ (p - 1)) m) = m := by
    rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp, hA, Module.End.one_apply]
  have hx' : (A ^ (p - 1)) m ∈ M := invariant_pow hM _ m hm
  calc B m (A v) = B (A ((A ^ (p - 1)) m)) (A v) := by rw [hx]
    _ = B ((A ^ (p - 1)) m) v := hAB _ _
    _ = 0 := hv _ hx'

section Odd

variable [CharP K 2]

theorem exists_fix_add_range (hp : Odd p) (hA : A ^ p = 1) (v : V) :
    ∃ v₁ ∈ LinearMap.ker (A - 1), ∃ w ∈ LinearMap.range (A - 1), v₁ + w = v := by
  have h := (isCompl_ker_range hp hA).sup_eq_top
  have hv : v ∈ LinearMap.ker (A - 1) ⊔ LinearMap.range (A - 1) := by rw [h]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
  exact ⟨a, ha, b, hb, hab⟩

theorem range_sep (hBn : ∀ v, (∀ w, B v w = 0) → v = 0) (hAB : ∀ v w, B (A v) (A w) = B v w)
    (hp : Odd p) (hA : A ^ p = 1) :
    ∀ w ∈ LinearMap.range (A - 1), (∀ w' ∈ LinearMap.range (A - 1), B w w' = 0) → w = 0 := by
  intro w hw h
  apply hBn
  intro v
  obtain ⟨v₁, hv₁, w₂, hw₂, rfl⟩ := exists_fix_add_range hp hA v
  have hv₁' : A v₁ = v₁ := sub_eq_zero.mp (LinearMap.mem_ker.mp hv₁)
  obtain ⟨u, rfl⟩ := hw
  rw [map_add, h w₂ hw₂, add_zero]
  exact B_range_fix B hAB hv₁' u

theorem fix_sep (hBn : ∀ v, (∀ w, B v w = 0) → v = 0) (hAB : ∀ v w, B (A v) (A w) = B v w)
    (hp : Odd p) (hA : A ^ p = 1) :
    ∀ v ∈ LinearMap.ker (A - 1), (∀ v' ∈ LinearMap.ker (A - 1), B v v' = 0) → v = 0 := by
  intro v hv h
  apply hBn
  intro w
  obtain ⟨v₁, hv₁, w₂, hw₂, rfl⟩ := exists_fix_add_range hp hA w
  have hv' : A v = v := sub_eq_zero.mp (LinearMap.mem_ker.mp hv)
  obtain ⟨u, rfl⟩ := hw₂
  rw [map_add, h v₁ hv₁, zero_add]
  exact B_fix_range B hAB hv' u

theorem ker_inf_range (hp : Odd p) (hA : A ^ p = 1) :
    LinearMap.ker (A - 1) ⊓ LinearMap.range (A - 1) = ⊥ :=
  (isCompl_ker_range hp hA).inf_eq_bot

theorem eq_zero_of_fixed_range (hp : Odd p) (hA : A ^ p = 1) {w : V}
    (hw : w ∈ LinearMap.range (A - 1)) (hAw : A w = w) : w = 0 := by
  have h1 : w ∈ LinearMap.ker (A - 1) :=
    LinearMap.mem_ker.mpr (by rw [LinearMap.sub_apply, hAw, Module.End.one_apply, sub_self])
  have : w ∈ LinearMap.ker (A - 1) ⊓ LinearMap.range (A - 1) := ⟨h1, hw⟩
  rw [ker_inf_range hp hA] at this
  exact this

theorem range_eq_bot_of_isotropic (hB : B.IsAlt) (hBn : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hAB : ∀ v w, B (A v) (A w) = B v w) (hp : Odd p) (hA : A ^ p = 1)
    (hcon : ∀ v ∈ LinearMap.range (A - 1), ∀ i j : ℕ, B ((A ^ i) v) ((A ^ j) v) = 0) :
    LinearMap.range (A - 1) = ⊥ := by
  set W := LinearMap.range (A - 1) with hW
  have hpol : ∀ v ∈ W, ∀ w ∈ W, B v (A w) = B (A v) w := by
    intro v hv w hw
    have h0 := hcon (v + w) (W.add_mem hv hw) 0 1
    have hv0 := hcon v hv 0 1
    have hw0 := hcon w hw 0 1
    simp only [pow_zero, pow_one, Module.End.one_apply, map_add, LinearMap.add_apply] at h0 hv0 hw0
    have h1 : B v (A w) + B w (A v) = 0 := by
      have : B v (A v) + B v (A w) + (B w (A v) + B w (A w)) = 0 := by
        rw [← h0]; ring
      rw [hv0, hw0] at this
      simpa using this
    have h2 : B v (A w) = B w (A v) := by
      rw [← CharTwo.neg_eq (B w (A v))]
      exact eq_neg_of_add_eq_zero_left h1
    rw [h2, alt_comm hB w (A v), alt_comm hB]
  have hpA : 1 ≤ p := hp.pos
  have hsame : ∀ w ∈ W, A w = (A ^ (p - 1)) w := by
    intro w hw
    have hz : ∀ v ∈ W, B v (A w - (A ^ (p - 1)) w) = 0 := by
      intro v hv
      have h1 := hpol v hv w hw
      have h2 := B_pow_left hAB hA (i := 1) hpA v w
      rw [pow_one] at h2
      rw [map_sub, h1, h2, sub_self]
    apply sub_eq_zero.mp
    have hmem : A w - (A ^ (p - 1)) w ∈ W := by
      refine W.sub_mem (range_invariant A hw) ?_
      induction (p - 1) with
      | zero => simpa using hw
      | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact range_invariant A ih
    refine range_sep hBn hAB hp hA _ hmem fun v hv => ?_
    rw [alt_comm hB]
    exact hz v hv
  have hsq : ∀ w ∈ W, A (A w) = w := by
    intro w hw
    have := hsame w hw
    rw [this, ← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hpA, hA,
      Module.End.one_apply]
  refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
  have hy : (A - 1) w ∈ W := ⟨w, rfl⟩
  have hy0 : A ((A - 1) w) = (A - 1) w := by
    have : A ((A - 1) w) = A (A w) - A w := by
      rw [LinearMap.sub_apply, map_sub, Module.End.one_apply]
    rw [this, hsq w hw, LinearMap.sub_apply, Module.End.one_apply]
    have h3 : ∀ x : V, -x = x := fun x => by
      rw [neg_eq_iff_add_eq_zero, ← two_smul K x, show (2 : K) = 0 from CharP.cast_eq_zero K 2,
        zero_smul]
    exact ((neg_sub (A w) w).symm).trans (h3 _)
  have hy1 : (A - 1) w = 0 := eq_zero_of_fixed_range hp hA hy hy0
  exact eq_zero_of_fixed_range hp hA hw (sub_eq_zero.mp hy1)

@[expose] def cyc (A : Module.End K V) (v : V) : Submodule K V :=
  Submodule.span K (Set.range fun i : ℕ => (A ^ i) v)

omit [CharP K 2] in
theorem pow_mem_cyc (A : Module.End K V) (v : V) (i : ℕ) : (A ^ i) v ∈ cyc A v :=
  Submodule.subset_span ⟨i, rfl⟩

omit [CharP K 2] in
theorem cyc_invariant (A : Module.End K V) (v : V) : ∀ m ∈ cyc A v, A m ∈ cyc A v := by
  intro m hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← Module.End.mul_apply, ← pow_succ']
    exact pow_mem_cyc A v (i + 1)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

omit [CharP K 2] in
theorem cyc_le {W : Submodule K V} (hW : ∀ w ∈ W, A w ∈ W) {v : V} (hv : v ∈ W) :
    cyc A v ≤ W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact invariant_pow hW i v hv

@[expose] def IsCyclicOn (A : Module.End K V) (W : Submodule K V) : Prop :=
  ∃ w₀ ∈ W, W ≤ cyc A w₀

theorem exists_invariant_compl (hp : Odd p) (hA : A ^ p = 1) {R : Submodule K V}
    (hR : ∀ r ∈ R, A r ∈ R) :
    ∃ Q : Submodule K V, (∀ q ∈ Q, A q ∈ Q) ∧ IsCompl R Q := by
  have hss := isSemisimple hp hA
  obtain ⟨Q, hQ, hRQ⟩ := (Module.End.isSemisimple_iff.mp hss) R
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mpr hR)
  exact ⟨Q, (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp hQ, hRQ⟩

theorem exists_split (hB : B.IsAlt) (hBn : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hAB : ∀ v w, B (A v) (A w) = B v w) (hp : Odd p) (hA : A ^ p = 1)
    (hW : LinearMap.range (A - 1) ≠ ⊥) (hnc : ¬ IsCyclicOn A (LinearMap.range (A - 1))) :
    ∃ M : Submodule K V, M ≤ LinearMap.range (A - 1) ∧ M ≠ ⊥ ∧ M ≠ LinearMap.range (A - 1) ∧
      (∀ m ∈ M, A m ∈ M) ∧ (∀ m ∈ M, (∀ n ∈ M, B m n = 0) → m = 0) := by
  set W := LinearMap.range (A - 1) with hWdef
  have hWinv : ∀ w ∈ W, A w ∈ W := fun w hw => range_invariant A hw
  obtain ⟨v, hvW, i, j, hij⟩ : ∃ v ∈ W, ∃ i j : ℕ, B ((A ^ i) v) ((A ^ j) v) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hW (range_eq_bot_of_isotropic hB hBn hAB hp hA hcon)
  set U := cyc A v with hU
  have hUW : U ≤ W := cyc_le hWinv hvW
  have hUinv := cyc_invariant A v
  have hUne : U ≠ W := by
    intro h
    exact hnc ⟨v, hvW, h ▸ le_rfl⟩
  set R := U ⊓ B.orthogonal U with hR
  have hRinv : ∀ r ∈ R, A r ∈ R := fun r hr =>
    ⟨hUinv r hr.1, orth_invariant hAB hA hp.pos hUinv hr.2⟩
  obtain ⟨Q, hQinv, hRQ⟩ := exists_invariant_compl hp hA hRinv
  set M := Q ⊓ U with hM
  have hUdec : ∀ u ∈ U, ∃ r ∈ R, ∃ m ∈ M, r + m = u := by
    intro u hu
    have h1 : u ∈ R ⊔ Q := by rw [hRQ.sup_eq_top]; trivial
    obtain ⟨r, hr, q, hq, rfl⟩ := Submodule.mem_sup.mp h1
    refine ⟨r, hr, q, ⟨hq, ?_⟩, rfl⟩
    have : q = (r + q) - r := by abel
    rw [this]
    exact U.sub_mem hu hr.1
  have hRorth : ∀ r ∈ R, ∀ u ∈ U, B u r = 0 := fun r hr u hu =>
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hr.2) u hu
  have hMU : M ≤ U := inf_le_right
  have hMbot : M ≠ ⊥ := by
    intro h
    have : ∀ u ∈ U, u ∈ R := by
      intro u hu
      obtain ⟨r, hr, m, hm, rfl⟩ := hUdec u hu
      rw [h] at hm
      rw [(Submodule.mem_bot K).mp hm, add_zero]
      exact hr
    apply hij
    have hi := pow_mem_cyc A v i
    have hj := pow_mem_cyc A v j
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp (this _ hj).2 _ hi
  have hMW : M ≠ W := by
    intro h
    exact hUne (le_antisymm hUW (h ▸ hMU))
  have hMinv : ∀ m ∈ M, A m ∈ M := fun m hm => ⟨hQinv m hm.1, hUinv m hm.2⟩
  have hMn : ∀ m ∈ M, (∀ n ∈ M, B m n = 0) → m = 0 := by
    intro m hm h
    have hmR : m ∈ R := by
      refine ⟨hm.2, LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => ?_⟩
      obtain ⟨r, hr, n, hn, rfl⟩ := hUdec u hu
      rw [map_add, LinearMap.add_apply, alt_comm hB r m, hRorth r hr m hm.2,
        alt_comm hB n m, h n hn, add_zero]
    exact Submodule.disjoint_def.mp hRQ.disjoint m hmR hm.1
  exact ⟨M, fun m hm => hUW hm.2, hMbot, hMW, hMinv, hMn⟩

theorem dvd_of_pow_fixed (hpp : p.Prime) (hp : Odd p) (hA : A ^ p = 1) {w : V}
    (hw : w ∈ LinearMap.range (A - 1)) (hw0 : w ≠ 0) {k : ℕ} (hk : (A ^ k) w = w) : p ∣ k := by
  by_contra hnd
  have hcop : Nat.Coprime k p := ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hnd).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hpp.one_lt
  have hit : ∀ n : ℕ, ((A ^ k) ^ n) w = w := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hk, ih]
  have h2 : A ^ (k * m) = A := by
    rw [← Nat.div_add_mod (k * m) p, hm, pow_add, pow_mul, hA, one_pow, one_mul, pow_one]
  have h1 : (A ^ (k * m)) w = w := by rw [pow_mul]; exact hit m
  rw [h2] at h1
  exact hw0 (eq_zero_of_fixed_range hp hA hw h1)

theorem exists_independent (hpp : p.Prime) (hB : B.IsAlt) (hAB : ∀ v w, B (A v) (A w) = B v w)
    (hp : Odd p) (hA : A ^ p = 1) [FiniteDimensional K V] {M : Submodule K V}
    (hMW : M ≤ LinearMap.range (A - 1)) (hM0 : M ≠ ⊥) (hMW' : M ≠ LinearMap.range (A - 1))
    (hMinv : ∀ m ∈ M, A m ∈ M) (hMn : ∀ m ∈ M, (∀ n ∈ M, B m n = 0) → m = 0) :
    ∃ u : Module.End K V, (∀ v w, B (u v) (u w) = B v w) ∧ u * A = A * u ∧ u ^ p = 1 ∧
      ∀ i j : ℕ, u ^ i * A ^ j = 1 → p ∣ i ∧ p ∣ j := by
  set W := LinearMap.range (A - 1) with hWdef
  have hcompl : IsCompl M (B.orthogonal M) := by
    rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hB.isRefl]
    refine Submodule.disjoint_def.mpr fun x hx hx' => hMn x hx fun n hn => ?_
    rw [alt_comm hB]
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp hx' n hn
  set N := B.orthogonal M with hN
  have hNinv : ∀ z ∈ N, A z ∈ N := fun z hz => orth_invariant hAB hA hp.pos hMinv hz
  let φ : M →ₗ[K] V := M.subtype ∘ₗ A.restrict hMinv
  let ψ : N →ₗ[K] V := N.subtype
  let u : Module.End K V := LinearMap.ofIsCompl hcompl φ ψ
  have hu1 : ∀ m ∈ M, u m = A m := fun m hm => by
    have := LinearMap.ofIsCompl_apply_left hcompl (φ := φ) (ψ := ψ) ⟨m, hm⟩
    simpa [φ, u] using this
  have hu2 : ∀ z ∈ N, u z = z := fun z hz => by
    have := LinearMap.ofIsCompl_apply_right hcompl (φ := φ) (ψ := ψ) ⟨z, hz⟩
    simpa [ψ, u] using this
  have hdec : ∀ v : V, ∃ m ∈ M, ∃ z ∈ N, m + z = v := by
    intro v
    have h1 : v ∈ M ⊔ N := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨m, hm, z, hz, h⟩ := Submodule.mem_sup.mp h1
    exact ⟨m, hm, z, hz, h⟩
  have hMN : ∀ m ∈ M, ∀ z ∈ N, B m z = 0 := fun m hm z hz =>
    LinearMap.BilinForm.mem_orthogonal_iff.mp hz m hm
  have hNM : ∀ m ∈ M, ∀ z ∈ N, B z m = 0 := fun m hm z hz => by
    rw [alt_comm hB]; exact hMN m hm z hz
  have hpow : ∀ (i : ℕ), ∀ m ∈ M, ∀ z ∈ N, (u ^ i) (m + z) = (A ^ i) m + z := by
    intro i
    induction i with
    | zero => intro m hm z hz; simp
    | succ i ih =>
      intro m hm z hz
      rw [pow_succ, Module.End.mul_apply, map_add u, hu1 m hm, hu2 z hz,
        ih _ (hMinv m hm) z hz, pow_succ, Module.End.mul_apply]
  have hiso : ∀ v w, B (u v) (u w) = B v w := by
    intro v w
    obtain ⟨m, hm, z, hz, rfl⟩ := hdec v
    obtain ⟨n, hn, y, hy, rfl⟩ := hdec w
    rw [map_add u m z, map_add u n y, hu1 m hm, hu2 z hz, hu1 n hn, hu2 y hy]
    simp only [map_add, LinearMap.add_apply]
    rw [hMN (A m) (hMinv m hm) y hy, hNM (A n) (hMinv n hn) z hz, hMN m hm y hy,
      hNM n hn z hz, hAB]
  have hcomm : u * A = A * u := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨m, hm, z, hz, rfl⟩ := hdec v
    simp only [Module.End.mul_apply, map_add]
    rw [hu1 (A m) (hMinv m hm), hu2 (A z) (hNinv z hz), hu1 m hm, hu2 z hz]
  have hup : u ^ p = 1 := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨m, hm, z, hz, rfl⟩ := hdec v
    rw [hpow p m hm z hz, hA]
    simp
  refine ⟨u, hiso, hcomm, hup, fun i j hij => ?_⟩
  obtain ⟨m, hm, hm0⟩ : ∃ m ∈ M, m ≠ 0 := by
    by_contra h
    push Not at h
    exact hM0 ((Submodule.eq_bot_iff _).mpr h)
  obtain ⟨z, hzN, hzW, hz0⟩ : ∃ z ∈ N, z ∈ W ∧ z ≠ 0 := by
    obtain ⟨w, hwW, hwM⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hMW hMW')
    obtain ⟨m, hm, z, hz, rfl⟩ := hdec w
    refine ⟨z, hz, ?_, fun h => hwM (by rw [h, add_zero]; exact hm)⟩
    have : z = (m + z) - m := by abel
    rw [this]
    exact W.sub_mem hwW (hMW hm)
  have hj : p ∣ j := by
    have h1 := congrArg (fun f : Module.End K V => f z) hij
    simp only [Module.End.mul_apply, Module.End.one_apply] at h1
    have h2 := hpow i 0 M.zero_mem ((A ^ j) z) (invariant_pow hNinv j z hzN)
    rw [zero_add, map_zero, zero_add] at h2
    rw [h2] at h1
    exact dvd_of_pow_fixed hpp hp hA hzW hz0 h1
  have hij' : p ∣ i + j := by
    have h1 := congrArg (fun f : Module.End K V => f m) hij
    simp only [Module.End.mul_apply, Module.End.one_apply] at h1
    have h2 := hpow i ((A ^ j) m) (invariant_pow hMinv j m hm) 0 N.zero_mem
    rw [add_zero, add_zero] at h2
    rw [h2, ← Module.End.mul_apply, ← pow_add] at h1
    exact dvd_of_pow_fixed hpp hp hA (hMW hm) hm0 h1
  exact ⟨(Nat.dvd_add_left hj).mp hij', hj⟩

end Odd

section Cyclic

open Polynomial

theorem mem_cyc_iff (A : Module.End K V) (v x : V) :
    x ∈ cyc A v ↔ ∃ t : K[X], aeval A t v = x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨X ^ i, by simp⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨t₁, rfl⟩ := hy
      obtain ⟨t₂, rfl⟩ := hz
      exact ⟨t₁ + t₂, by simp⟩
    | smul c y _ hy =>
      obtain ⟨t, rfl⟩ := hy
      exact ⟨C c * t, by simp⟩
  · rintro ⟨t, rfl⟩
    induction t using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hp hq
    | monomial n a =>
      simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
      exact Submodule.smul_mem _ _ (pow_mem_cyc A v n)

theorem aeval_commute (A g : Module.End K V) (hg : g * A = A * g) (t : K[X]) :
    g * aeval A t = aeval A t * g := by
  induction t using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
  | monomial n a =>
    rw [aeval_monomial]
    calc g * (algebraMap K (Module.End K V) a * A ^ n)
        = (g * algebraMap K (Module.End K V) a) * A ^ n := by rw [mul_assoc]
      _ = (algebraMap K (Module.End K V) a * g) * A ^ n := by
          rw [← Algebra.commutes (A := Module.End K V) a g]
      _ = algebraMap K (Module.End K V) a * (g * A ^ n) := by rw [mul_assoc]
      _ = algebraMap K (Module.End K V) a * (A ^ n * g) := by
          rw [((show Commute g A from hg).pow_right n).eq]
      _ = (algebraMap K (Module.End K V) a * A ^ n) * g := by rw [mul_assoc]

theorem exists_poly_of_commute {w₀ : V} {g : Module.End K V} (hg : g * A = A * g)
    (hgw : g w₀ ∈ cyc A w₀) : ∃ t : K[X], ∀ w ∈ cyc A w₀, g w = aeval A t w := by
  obtain ⟨t, ht⟩ := (mem_cyc_iff A w₀ _).mp hgw
  refine ⟨t, fun w hw => ?_⟩
  obtain ⟨s, rfl⟩ := (mem_cyc_iff A w₀ w).mp hw
  calc g (aeval A s w₀) = (g * aeval A s) w₀ := rfl
    _ = (aeval A s * g) w₀ := by rw [aeval_commute A g hg]
    _ = aeval A s (g w₀) := rfl
    _ = aeval A s (aeval A t w₀) := by rw [ht]
    _ = aeval A (s * t) w₀ := by rw [map_mul, Module.End.mul_apply]
    _ = aeval A (t * s) w₀ := by rw [mul_comm]
    _ = aeval A t (aeval A s w₀) := by rw [map_mul, Module.End.mul_apply]

theorem range_map_mem {g : Module.End K V} (hg : g * A = A * g) {w : V}
    (hw : w ∈ LinearMap.range (A - 1)) : g w ∈ LinearMap.range (A - 1) := by
  obtain ⟨u, rfl⟩ := hw
  refine ⟨g u, ?_⟩
  have := congrArg (fun f : Module.End K V => f u) hg
  simp only [Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, this]

theorem exists_poly_on_range (hcyc : IsCyclicOn A (LinearMap.range (A - 1)))
    {g : Module.End K V} (hg : g * A = A * g) :
    ∃ t : K[X], ∀ w ∈ LinearMap.range (A - 1), g w = aeval A t w := by
  obtain ⟨w₀, hw₀, hle⟩ := hcyc
  obtain ⟨t, ht⟩ := exists_poly_of_commute hg (hle (range_map_mem hg hw₀))
  exact ⟨t, fun w hw => ht w (hle hw)⟩

theorem commute_on_range (hcyc : IsCyclicOn A (LinearMap.range (A - 1)))
    {g g' : Module.End K V} (hg : g * A = A * g) (hg' : g' * A = A * g') :
    ∀ w ∈ LinearMap.range (A - 1), g (g' w) = g' (g w) := by
  obtain ⟨t, ht⟩ := exists_poly_on_range hcyc hg
  obtain ⟨t', ht'⟩ := exists_poly_on_range hcyc hg'
  intro w hw
  rw [ht _ (range_map_mem hg' hw), ht' _ (range_map_mem hg hw), ht w hw, ht' w hw,
    ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

end Cyclic

section TwoPart

open Polynomial

variable [CharP K 2] [FiniteDimensional K V]

theorem eq_id_on_range_of_two_pow (hp : Odd p) (hA : A ^ p = 1)
    (hcyc : IsCyclicOn A (LinearMap.range (A - 1))) {g : Module.End K V} (hg : g * A = A * g)
    {k : ℕ} (hgk : g ^ (2 ^ k) = 1) : ∀ w ∈ LinearMap.range (A - 1), g w = w := by
  set W := LinearMap.range (A - 1) with hWdef
  obtain ⟨t, ht⟩ := exists_poly_on_range hcyc hg
  obtain ⟨T, hTdef⟩ : ∃ T : Module.End K V, T = aeval A t := ⟨_, rfl⟩
  have hss : A.IsSemisimple := isSemisimple hp hA
  have hAT : A * T = T * A := by rw [hTdef]; exact aeval_commute A A rfl t
  have hc : Commute (T - 1) (A - 1) :=
    ((show Commute T A from hAT.symm).sub_right (Commute.one_right T)).sub_left
      (Commute.one_left _)
  obtain ⟨N, hN⟩ : ∃ N : Module.End K V, N = (T - 1) * (A - 1) := ⟨_, rfl⟩
  have hNss : N.IsSemisimple := by
    have : N = aeval A ((t - 1) * (X - 1)) := by simp [hN, hTdef]
    rw [this]
    exact hss.aeval _
  have hgm : (g - 1) ^ (2 ^ k) = 0 := by
    have h1 := congrArg (Polynomial.aeval g)
      (sub_pow_char_pow (R := K[X]) (p := 2) (X : K[X]) (1 : K[X]) (n := k))
    simpa [map_pow, hgk] using h1
  have hagree : ∀ n : ℕ, ∀ w ∈ W, ((T - 1) ^ n) w = ((g - 1) ^ n) w := by
    intro n
    induction n with
    | zero => intro w hw; rfl
    | succ n ih =>
      intro w hw
      have h1 : (T - 1) w = (g - 1) w := by
        simp only [LinearMap.sub_apply, Module.End.one_apply]
        rw [hTdef, ← ht w hw]
      have h2 : (g - 1) w ∈ W := W.sub_mem (range_map_mem hg hw) hw
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, h1, ih _ h2]
  have hAW : ∀ n : ℕ, ∀ w ∈ W, (((A - 1) ^ n : Module.End K V) w) ∈ W := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ ⟨w, rfl⟩
  have hNn : N ^ (2 ^ k) = 0 := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_fix_add_range hp hA v
    rw [map_add]
    have h1 : (N ^ (2 ^ k)) v₁ = 0 := by
      have hNv : N v₁ = 0 := by
        rw [hN, Module.End.mul_apply, LinearMap.mem_ker.mp hv₁, map_zero]
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ k = m + 1 :=
        ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
      rw [hm, pow_succ, Module.End.mul_apply, hNv, map_zero]
    have h2 : (N ^ (2 ^ k)) w = 0 := by
      rw [hN, hc.mul_pow, Module.End.mul_apply]
      have hw' : (((A - 1) ^ (2 ^ k) : Module.End K V) w) ∈ W := hAW _ w hw
      rw [hagree _ _ hw', hgm]
      rfl
    rw [h1, h2, add_zero]
    rfl
  have hN0 : N = 0 :=
    Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨2 ^ k, hNn⟩ hNss
  intro w hw
  obtain ⟨u, rfl⟩ := hw
  rw [ht _ ⟨u, rfl⟩, ← hTdef]
  have h0 : ((T - 1) * (A - 1)) u = 0 := by rw [← hN, hN0]; rfl
  rw [Module.End.mul_apply, LinearMap.sub_apply T, Module.End.one_apply] at h0
  exact sub_eq_zero.mp h0

end TwoPart

end CFSG.RankThree.PartOne.OddIso

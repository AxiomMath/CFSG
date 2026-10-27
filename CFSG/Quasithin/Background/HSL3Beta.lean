module

public import CFSG.Quasithin.Background.HSL3Alpha
public import CFSG.Quasithin.Background.HSU3Beta

public section

namespace CFSG.Quasithin

namespace H

namespace SL3Pair

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open SU3 (diagPow diagPow_mul diagPow_zero diagPow_mul_p det_diagPow swapMat swapMat_mul_self
  det_swapMat swapMat_mul_diagPow_mul_swapMat mem_zpowers_of_isCyclic fixSub mem_fixSub frameMat
  mul_frameMat)
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def diagGL {ℓ : K} (hℓ : ℓ ≠ 0) (a b c : ℕ) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diagPow ℓ a b c)
    (by rw [det_diagPow]; exact pow_ne_zero _ hℓ)

omit [Finite K] [CharP K 2] in
theorem coe_diagGL {ℓ : K} (hℓ : ℓ ≠ 0) (a b c : ℕ) :
    ((diagGL hℓ a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagPow ℓ a b c := rfl

omit [Finite K] [CharP K 2] in
theorem diagGL_mul {ℓ : K} (hℓ : ℓ ≠ 0) (a b c a' b' c' : ℕ) :
    diagGL hℓ a b c * diagGL hℓ a' b' c' = diagGL hℓ (a + a') (b + b') (c + c') :=
  Units.ext (by rw [Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, diagPow_mul])

omit [Finite K] [CharP K 2] in
theorem diagPow_comm (ℓ ν : K) (a b c a' b' c' : ℕ) :
    diagPow ℓ a b c * diagPow ν a' b' c' = diagPow ν a' b' c' * diagPow ℓ a b c := by
  rw [diagPow, diagPow, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_comm]

@[expose] noncomputable def swapGL : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero swapMat (by rw [det_swapMat]; exact one_ne_zero)

omit [Finite K] in
theorem coe_swapGL : ((swapGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = swapMat := rfl

omit [Finite K] in
theorem swapGL_mul_self : (swapGL : GL (Fin 3) K) * swapGL = 1 :=
  Units.ext (by rw [Units.val_mul, coe_swapGL, swapMat_mul_self, Units.val_one])

theorem pow_eq_one_of_odd_of_mul_self {G : Type*} [Group G] {g : G} {p : ℕ} (hp : Odd p)
    (hgp : g ^ p = 1) (hg2 : g * g = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hg2)
  have h2 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have h3 : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hp
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2)

omit [Finite K] in
theorem exists_diag_of_fix_plane {p : ℕ} (hp : Odd p) {B : GL (Fin 3) K} (hBp : B ^ p = 1)
    (hW : Module.finrank K (fixSub (B : Matrix (Fin 3) (Fin 3) K)) = 2) :
    ∃ (P : GL (Fin 3) K) (l : K), l ≠ 1 ∧ l ^ p = 1 ∧
      (B : Matrix (Fin 3) (Fin 3) K) = (P : Matrix (Fin 3) (Fin 3) K) * diagPow l 0 0 1 *
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  classical
  set M : Matrix (Fin 3) (Fin 3) K := (B : Matrix (Fin 3) (Fin 3) K) with hM
  set W := fixSub M with hWdef
  let N : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := Matrix.mulVecLin M - LinearMap.id
  have hWker : W = LinearMap.ker N := rfl
  have hNv : ∀ v, N v = M *ᵥ v - v := fun v => rfl
  have hMv : ∀ v, M *ᵥ v = v + N v := fun v => by rw [hNv]; abel
  have hrank : Module.finrank K (LinearMap.range N) = 1 := by
    have := LinearMap.finrank_range_add_finrank_ker N
    rw [← hWker, hW, Module.finrank_fin_fun] at this
    omega
  obtain ⟨u₀, hu₀, hspan⟩ := finrank_eq_one_iff'.mp hrank
  set u : Fin 3 → K := (u₀ : Fin 3 → K) with hu
  have hu0 : u ≠ 0 := fun h => hu₀ (Subtype.ext h)
  have hrange : ∀ v, ∃ t : K, N v = t • u := by
    intro v
    obtain ⟨t, ht⟩ := hspan ⟨N v, ⟨v, rfl⟩⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  obtain ⟨c, hc⟩ := hrange u
  set l := 1 + c with hl
  have hBu : M *ᵥ u = l • u := by
    rw [hl, add_smul, one_smul, ← hc, hMv]
  have hl1 : l ≠ 1 := by
    intro h
    have hc0 : c = 0 := by
      have : (1 : K) + c = 1 + 0 := by rw [← hl, h, add_zero]
      exact add_left_cancel this
    have hN2 : ∀ v, N (N v) = 0 := by
      intro v
      obtain ⟨t, ht⟩ := hrange v
      rw [ht, map_smul, hc, hc0, zero_smul, smul_zero]
    have hB2 : B * B = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one]
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      rw [← Matrix.mulVec_mulVec, ← hM, hMv v, Matrix.mulVec_add, hMv v, hMv (N v), hN2,
        add_zero, Matrix.one_mulVec, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hB1 : B = 1 := pow_eq_one_of_odd_of_mul_self hp hBp hB2
    have hWtop : W = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [hWdef, mem_fixSub, hM, hB1, Units.val_one, Matrix.one_mulVec]
    rw [hWtop, finrank_top, Module.finrank_fin_fun] at hW
    omega
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ u = l ^ k • u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hBu, smul_smul, ← pow_succ]
  have hlp : l ^ p = 1 := by
    have h1 := hpow p
    have h2 : M ^ p = 1 := by rw [hM, ← Units.val_pow_eq_pow_val, hBp, Units.val_one]
    rw [h2, Matrix.one_mulVec] at h1
    have : (l ^ p - 1) • u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hu0)
  have huW : u ∉ W := by
    intro h
    rw [hWdef, mem_fixSub, hBu] at h
    have : (l - 1) • u = 0 := by rw [sub_smul, one_smul, h, sub_self]
    exact hl1 (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hu0))
  let bW := Module.finBasisOfFinrankEq K W hW
  let b : Fin 3 → (Fin 3 → K) := Fin.snoc (fun i : Fin 2 => ((bW i : W) : Fin 3 → K)) u
  have hb_li : LinearIndependent K b := by
    rw [linearIndependent_finSnoc]
    refine ⟨bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W), fun h => huW ?_⟩
    have : Submodule.span K (Set.range fun i : Fin 2 => ((bW i : W) : Fin 3 → K)) ≤ W :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (bW i).2)
    exact this h
  have hU : IsUnit (frameMat b) := Matrix.linearIndependent_cols_iff_isUnit.mp hb_li
  refine ⟨hU.unit, l, hl1, hlp, ?_⟩
  have hb0 : b 0 = ((bW 0 : W) : Fin 3 → K) := rfl
  have hb1 : b 1 = ((bW 1 : W) : Fin 3 → K) := rfl
  have hb2 : b 2 = u := rfl
  have hMP := mul_frameMat (A := M) (b := b) (ℓ := l)
    (by rw [hb0]; exact mem_fixSub.mp (bW 0).2) (by rw [hb1]; exact mem_fixSub.mp (bW 1).2)
    (by rw [hb2]; exact hBu)
  have hD : diagPow l 0 0 1 = Matrix.diagonal ![1, 1, l] := by
    rw [diagPow]
    congr 1
    ext i
    fin_cases i <;> simp
  have hPP : (hU.unit : Matrix (Fin 3) (Fin 3) K) *
      ((hU.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPm : (hU.unit : Matrix (Fin 3) (Fin 3) K) = frameMat b := IsUnit.unit_spec hU
  calc M = M * ((hU.unit : Matrix (Fin 3) (Fin 3) K) *
        ((hU.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by rw [hPP, Matrix.mul_one]
    _ = (M * (hU.unit : Matrix (Fin 3) (Fin 3) K)) *
        ((hU.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [Matrix.mul_assoc]
    _ = (hU.unit : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal ![1, 1, l] *
        ((hU.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [hPm, hMP]
    _ = _ := by rw [hD]

omit [Finite K] [CharP K 2] in
theorem pairAut_comm_pairHom {B g : GL (Fin 3) K} {y₂ : MulAut (StdMod (Fin 3) K)} {μ : K}
    (hy₂ : ∀ w, toAddMap y₂ w = μ • ((dualGL B : Matrix (Fin 3) (Fin 3) K) *ᵥ w))
    (h : B * g = g * B) :
    pairAut (matAut B) y₂ * pairHom g = pairHom g * pairAut (matAut B) y₂ := by
  have hd : dualGL B * dualGL g = dualGL g * dualGL B := by
    rw [← dualHom_apply, ← dualHom_apply, ← map_mul, ← map_mul, h]
  rw [pairHom_apply, pairAut_mul, pairAut_mul]
  congr 1
  · show matHom B * matHom g = matHom g * matHom B
    rw [← map_mul, ← map_mul, h]
  · refine toAddMap_injective fun w => ?_
    simp only [toAddMap_mul, hy₂, toAddMap_matAut, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      ← Units.val_mul, hd]

omit [Finite K] [CharP K 2] in
theorem pairAut_pow (a b : MulAut (StdMod (Fin 3) K)) (k : ℕ) :
    (pairAut a b) ^ k = pairAut (a ^ k) (b ^ k) := by
  have h : pairAut a b = pairHom₂ K (a, b) := rfl
  rw [h, ← map_pow]
  rfl

omit [Finite K] [CharP K 2] in
theorem pairHom_injective : Function.Injective (pairHom (K := K)) := by
  intro g h hgh
  rw [pairHom_apply, pairHom_apply] at hgh
  exact matHom_injective (pairAut_injective hgh).1

omit [Finite K] [CharP K 2] in
theorem conjMat_inj (P : GL (Fin 3) K) {X Y : Matrix (Fin 3) (Fin 3) K}
    (h : (P : Matrix (Fin 3) (Fin 3) K) * X * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K) * Y * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    X = Y := by
  have hPP : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ Z : Matrix (Fin 3) (Fin 3) K, Z = ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((P : Matrix (Fin 3) (Fin 3) K) * Z * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        (P : Matrix (Fin 3) (Fin 3) K) := fun Z => by
    simp only [← Matrix.mul_assoc]
    rw [hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  rw [key X, key Y, h]

theorem false_of_diag {X : Subgroup (MulAut (PairMod K))} (hLX : pairSL K ≤ X)
    (hB : HypBang X) {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    {B P : GL (Fin 3) K} {l ν μ : K} {y₂ : MulAut (StdMod (Fin 3) K)}
    (hyX : pairAut (matAut B) y₂ ∈ X) (hyp : (pairAut (matAut B) y₂) ^ p = 1)
    (hy1 : pairAut (matAut B) y₂ ≠ 1)
    (hBP : (B : Matrix (Fin 3) (Fin 3) K) = (P : Matrix (Fin 3) (Fin 3) K) * diagPow l 0 0 1 *
      ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hy₂ : ∀ w, toAddMap y₂ w = μ • ((dualGL B : Matrix (Fin 3) (Fin 3) K) *ᵥ w))
    (hν : ν ≠ 1) (hνp : ν ^ p = 1) : False := by
  classical
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  have hp : p.Prime := hpf.out
  obtain ⟨y, hydef⟩ : ∃ y, y = pairAut (matAut B) y₂ := ⟨_, rfl⟩
  rw [← hydef] at hyX hyp hy1
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hνp
    exact zero_ne_one hνp
  have hpk : ∀ x : ℕ, x + (p - 1) * x = p * x := fun x => by
    rw [Nat.sub_mul, one_mul]
    have : x ≤ p * x := Nat.le_mul_of_pos_left x hp.pos
    omega
  have hPP : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → ℕ → GL (Fin 3) K,
      ∀ a b, T a b = P * diagGL hν0 a b ((p - 1) * (a + b)) * P⁻¹ := ⟨_, fun _ _ => rfl⟩
  have hT : ∀ a b, ((T a b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K) * diagPow ν a b ((p - 1) * (a + b)) *
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun a b => by
    rw [hTdef, Units.val_mul, Units.val_mul, coe_diagGL]
  have hTmem : ∀ a b, T a b ∈ StatedSL 3 K := by
    intro a b
    rw [mem_statedSL_iff, hT, Matrix.det_mul, Matrix.det_mul, det_diagPow,
      mul_comm _ (Matrix.det _), ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.det_one, one_mul, hpk, pow_mul, hνp, one_pow]
  have hTmul : ∀ a b a' b', T a b * T a' b' = T (a + a') (b + b') := by
    intro a b a' b'
    rw [hTdef, hTdef, hTdef]
    have e : (p - 1) * (a + b) + (p - 1) * (a' + b') = (p - 1) * (a + a' + (b + b')) := by ring
    calc P * diagGL hν0 a b ((p - 1) * (a + b)) * P⁻¹ *
          (P * diagGL hν0 a' b' ((p - 1) * (a' + b')) * P⁻¹)
        = P * (diagGL hν0 a b ((p - 1) * (a + b)) * diagGL hν0 a' b' ((p - 1) * (a' + b'))) *
          P⁻¹ := by group
      _ = P * diagGL hν0 (a + a') (b + b') ((p - 1) * (a + a' + (b + b'))) * P⁻¹ := by
          rw [diagGL_mul, e]
  have hT0 : T 0 0 = 1 := by
    have : diagGL hν0 0 0 ((p - 1) * (0 + 0)) = 1 := Units.ext (by
      rw [coe_diagGL, Units.val_one, add_zero, mul_zero, diagPow_zero])
    rw [hTdef, this, mul_one, mul_inv_cancel]
  have hTp : ∀ a b, T (p * a) (p * b) = 1 := by
    intro a b
    have : diagGL hν0 (p * a) (p * b) ((p - 1) * (p * a + p * b)) = 1 := Units.ext (by
      rw [coe_diagGL, Units.val_one, show (p - 1) * (p * a + p * b) = p * ((p - 1) * (a + b)) by
        ring, diagPow_mul_p hνp])
    rw [hTdef, this, mul_one, mul_inv_cancel]
  have hconj : ∀ X Y : Matrix (Fin 3) (Fin 3) K,
      ((P : Matrix (Fin 3) (Fin 3) K) * X * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        ((P : Matrix (Fin 3) (Fin 3) K) * Y * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      (P : Matrix (Fin 3) (Fin 3) K) * (X * Y) *
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun X Y => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ (P : Matrix (Fin 3) (Fin 3) K), hPP, Matrix.one_mul]
  have hBT : ∀ a b, B * T a b = T a b * B := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hBP, hT, hconj, hconj, diagPow_comm]
  have hcommT : ∀ a b, y * pairHom (T a b) = pairHom (T a b) * y := fun a b => by
    rw [hydef]
    exact pairAut_comm_pairHom hy₂ (hBT a b)
  have hprod : ∀ k a b k' a' b', (y ^ k * pairHom (T a b)) * (y ^ k' * pairHom (T a' b')) =
      y ^ (k + k') * pairHom (T (a + a') (b + b')) := by
    intro k a b k' a' b'
    have hc : pairHom (T a b) * y ^ k' = y ^ k' * pairHom (T a b) :=
      ((Commute.pow_left (hcommT a b) k').eq).symm
    calc y ^ k * pairHom (T a b) * (y ^ k' * pairHom (T a' b'))
        = y ^ k * (pairHom (T a b) * y ^ k') * pairHom (T a' b') := by group
      _ = y ^ k * (y ^ k' * pairHom (T a b)) * pairHom (T a' b') := by rw [hc]
      _ = y ^ (k + k') * pairHom (T (a + a') (b + b')) := by
          rw [pow_add, ← hTmul, map_mul]
          group
  have hpowE : ∀ k a b j, (y ^ k * pairHom (T a b)) ^ j =
      y ^ (j * k) * pairHom (T (j * a) (j * b)) := by
    intro k a b j
    induction j with
    | zero => rw [pow_zero, zero_mul, zero_mul, zero_mul, pow_zero, hT0, map_one, one_mul]
    | succ j ih =>
      rw [pow_succ, ih, hprod]
      congr 3 <;> ring
  have hyk : ∀ k, y ^ (p * k) = 1 := fun k => by rw [pow_mul, hyp, one_pow]
  let E : Subgroup (MulAut (PairMod K)) :=
    { carrier := {e | ∃ k a b : ℕ, e = y ^ k * pairHom (T a b)}
      mul_mem' := by
        rintro _ _ ⟨k, a, b, rfl⟩ ⟨k', a', b', rfl⟩
        exact ⟨k + k', a + a', b + b', hprod k a b k' a' b'⟩
      one_mem' := ⟨0, 0, 0, by rw [pow_zero, hT0, map_one, one_mul]⟩
      inv_mem' := by
        rintro _ ⟨k, a, b, rfl⟩
        refine ⟨(p - 1) * k, (p - 1) * a, (p - 1) * b, ?_⟩
        refine inv_eq_of_mul_eq_one_right ?_
        rw [hprod, hpk, hpk, hpk, hyk, hTp, map_one, one_mul] }
  have hEX : E ≤ X := by
    rintro _ ⟨k, a, b, rfl⟩
    exact X.mul_mem (X.pow_mem hyX k) (hLX (pairHom_mem_pairSL (hTmem a b)))
  have hEel : IsElemAbelian p E := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, ⟨k, a, b, rfl⟩⟩ ⟨_, ⟨k', a', b', rfl⟩⟩
      apply Subtype.ext
      change (y ^ k * pairHom (T a b)) * (y ^ k' * pairHom (T a' b')) =
        (y ^ k' * pairHom (T a' b')) * (y ^ k * pairHom (T a b))
      rw [hprod, hprod, add_comm k, add_comm a, add_comm b]
    · rintro _ ⟨k, a, b, rfl⟩
      rw [hpowE, mul_comm p k, mul_comm k p, hyk, one_mul, hTp, map_one]
  obtain ⟨S, hSdef⟩ : ∃ S : GL (Fin 3) K, S = P * swapGL * P⁻¹ := ⟨_, rfl⟩
  have hSm : (S : Matrix (Fin 3) (Fin 3) K) = (P : Matrix (Fin 3) (Fin 3) K) * swapMat *
      ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hSdef, Units.val_mul, Units.val_mul, coe_swapGL]
  have hSmem : S ∈ StatedSL 3 K := by
    rw [mem_statedSL_iff, hSm, Matrix.det_mul, Matrix.det_mul, det_swapMat, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  obtain ⟨s, hsdef⟩ : ∃ s, s = pairHom S := ⟨_, rfl⟩
  have hsX : s ∈ X := hsdef ▸ hLX (pairHom_mem_pairSL hSmem)
  have hSS : S * S = 1 := by
    rw [hSdef]
    have : P * swapGL * P⁻¹ * (P * swapGL * P⁻¹) = P * (swapGL * swapGL) * P⁻¹ := by group
    rw [this, swapGL_mul_self, mul_one, mul_inv_cancel]
  have hs2 : s ^ 2 = 1 := by rw [sq, hsdef, ← map_mul, hSS, map_one]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq, hs2])
  have hconjS : ∀ (ℓ : K) (a b c : ℕ), (S : Matrix (Fin 3) (Fin 3) K) *
      ((P : Matrix (Fin 3) (Fin 3) K) * diagPow ℓ a b c *
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * (S : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K) * diagPow ℓ b a c *
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro ℓ a b c
    rw [hSm, hconj, hconj, ← swapMat_mul_diagPow_mul_swapMat (ℓ := ℓ) a b c, Matrix.mul_assoc]
  have hST : ∀ a b, S * T a b * S = T b a := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hT, hT, hconjS, add_comm a b]
  have hSB : S * B = B * S := by
    have h1 : S * B * S = B := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hBP, hconjS]
    calc S * B = S * B * (S * S) := by rw [hSS, mul_one]
      _ = (S * B * S) * S := by group
      _ = B * S := by rw [h1]
  have hsy : s * y = y * s := by
    rw [hsdef, hydef]
    exact (pairAut_comm_pairHom hy₂ hSB.symm).symm
  have hsT : ∀ a b, s * pairHom (T a b) * s⁻¹ = pairHom (T b a) := by
    intro a b
    rw [hsinv, hsdef, ← map_mul, ← map_mul, hST]
  have hsE : ∀ e ∈ E, s * e * s⁻¹ ∈ E := by
    rintro _ ⟨k, a, b, rfl⟩
    refine ⟨k, b, a, ?_⟩
    have hsyk : s * y ^ k = y ^ k * s := ((Commute.pow_right hsy k).eq)
    calc s * (y ^ k * pairHom (T a b)) * s⁻¹ = (s * y ^ k) * pairHom (T a b) * s⁻¹ := by group
      _ = y ^ k * (s * pairHom (T a b) * s⁻¹) := by rw [hsyk]; group
      _ = y ^ k * pairHom (T b a) := by rw [hsT]
  have hsN : s ∈ Subgroup.normalizer (E : Set (MulAut (PairMod K))) := by
    refine Subgroup.mem_normalizer_iff.mpr fun e => ⟨hsE e, fun he => ?_⟩
    have := hsE _ he
    rwa [hsinv, show s * (s * e * s) * s = (s * s) * e * (s * s) by group, ← sq, hs2, one_mul,
      mul_one] at this
  have hT10 : pairHom (T 1 0) ∈ E := ⟨0, 1, 0, by rw [pow_zero, one_mul]⟩
  have hsC : s ∉ Subgroup.centralizer (E : Set (MulAut (PairMod K))) := by
    intro hc
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hT10
    have h2 : s * pairHom (T 1 0) * s⁻¹ = pairHom (T 1 0) := by rw [← h1]; group
    rw [hsT] at h2
    have h3 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      (pairHom_injective h2)
    simp only [hT] at h3
    have h5 := congrFun (congrFun (conjMat_inj P h3) 0) 0
    simp [diagPow] at h5
    exact hν h5.symm
  have hcyc := isCyclic_inf_centralizer_of_hypBang hB hp2 hEX hEel hsX hs2 hsN hsC
  have hyC : y ∈ E ⊓ Subgroup.centralizer ({s} : Set (MulAut (PairMod K))) := by
    refine ⟨⟨1, 0, 0, by rw [pow_one, hT0, map_one, mul_one]⟩,
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hsy
  have hxC : pairHom (T 1 1) ∈ E ⊓ Subgroup.centralizer ({s} : Set (MulAut (PairMod K))) := by
    refine ⟨⟨0, 1, 1, by rw [pow_zero, one_mul]⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    have := hsT 1 1
    calc s * pairHom (T 1 1) = s * pairHom (T 1 1) * s⁻¹ * s := by group
      _ = pairHom (T 1 1) * s := by rw [this]
  have hx1 : pairHom (T 1 1) ≠ 1 := by
    intro h
    have h1 : T 1 1 = 1 := pairHom_injective (h.trans (map_one pairHom).symm)
    have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [hT, Units.val_one] at h2
    have h3 : (P : Matrix (Fin 3) (Fin 3) K) * diagPow ν 1 1 ((p - 1) * (1 + 1)) *
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (P : Matrix (Fin 3) (Fin 3) K) * 1 * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [h2, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h5 := congrFun (congrFun (conjMat_inj P h3) 0) 0
    simp [diagPow] at h5
    exact hν h5
  have hexp : ∀ g ∈ E ⊓ Subgroup.centralizer ({s} : Set (MulAut (PairMod K))), g ^ p = 1 :=
    fun g hg => hEel.2 g hg.1
  have hz := mem_zpowers_of_isCyclic hcyc hexp hxC hx1 hyC
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  have hTpow : ∀ j, T 1 1 ^ j = T j j := by
    intro j
    induction j with
    | zero => rw [pow_zero, hT0]
    | succ j ih => rw [pow_succ, ih, hTmul]
  have hy' : y = pairHom (T m m) := by rw [← hm, ← map_pow, hTpow]
  have hB' : B = T m m := by
    have := hy'
    rw [hydef, pairHom_apply] at this
    exact matHom_injective (pairAut_injective this).1
  have hνm : ν ^ m = 1 := by
    have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hB'
    simp only [hT, hBP] at h1
    have h5 := congrFun (congrFun (conjMat_inj P h1) 0) 0
    simp [diagPow] at h5
    exact h5.symm
  apply hy1
  rw [hy']
  have : T m m = 1 := by
    apply Units.ext
    rw [hT, Units.val_one]
    have hD : diagPow ν m m ((p - 1) * (m + m)) = 1 := by
      rw [diagPow, ← Matrix.diagonal_one]
      congr 1
      ext i
      fin_cases i <;> simp [hνm, pow_mul, pow_add, mul_comm (p - 1)]
    rw [hD, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [this, map_one]

omit [CharP K 2] in
theorem mem_pairSub_of_odd {y : MulAut (PairMod K)} (hyN : y ∈ pairNorm K) {p : ℕ}
    (hp : Odd p) (hyp : y ^ p = 1) : y ∈ pairSub K := by
  by_contra hy
  have hyi : y⁻¹ ∉ pairSub K := fun h => hy (by simpa using (pairSub K).inv_mem h)
  have hy2 : y * y ∈ pairSub K := by
    have := inv_mul_mem_pairSub (Subgroup.inv_mem _ hyN) hyN hyi hy
    rwa [inv_inv] at this
  obtain ⟨k, rfl⟩ := hp
  have h2 : y ^ (2 * k) ∈ pairSub K := by
    rw [pow_mul, sq]
    exact (pairSub K).pow_mem hy2 k
  have h3 : y ^ (2 * k + 1) ∈ pairSub K := by rw [hyp]; exact (pairSub K).one_mem
  apply hy
  have : y = (y ^ (2 * k))⁻¹ * y ^ (2 * k + 1) := by group
  rw [this]
  exact (pairSub K).mul_mem ((pairSub K).inv_mem h2) h3

omit [Finite K] [CharP K 2] in
theorem card_fix_matAut (B : GL (Fin 3) K) :
    Nat.card {v : StdMod (Fin 3) K // matAut B v = v} =
      Nat.card K ^ Module.finrank K (fixSub (B : Matrix (Fin 3) (Fin 3) K)) := by
  rw [← Module.natCard_eq_pow_finrank (K := K) (V := fixSub (B : Matrix (Fin 3) (Fin 3) K))]
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd v.1, mem_fixSub.mpr
        (congrArg Multiplicative.toAdd v.2)⟩
      invFun := fun w => ⟨Multiplicative.ofAdd w.1, congrArg Multiplicative.ofAdd
        (mem_fixSub.mp w.2)⟩
      left_inv := fun v => rfl
      right_inv := fun w => rfl }

omit [Finite K] [CharP K 2] in
theorem finrank_fixSub_le (A : Matrix (Fin 3) (Fin 3) K) : Module.finrank K (fixSub A) ≤ 3 := by
  have := Submodule.finrank_le (fixSub A)
  rwa [Module.finrank_fin_fun] at this

theorem false_of_fst_plane {X : Subgroup (MulAut (PairMod K))} (hLX : pairSL K ≤ X)
    (hXN : X ≤ pairNorm K) (hB : HypBang X) {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    {B : GL (Fin 3) K} {y₂ : MulAut (StdMod (Fin 3) K)} (hyX : pairAut (matAut B) y₂ ∈ X)
    (hyo : orderOf (pairAut (matAut B) y₂) = p)
    (hW : 2 ≤ Module.finrank K (fixSub (B : Matrix (Fin 3) (Fin 3) K))) : False := by
  have hp : p.Prime := hpf.out
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hyp : (pairAut (matAut B) y₂) ^ p = 1 := hyo ▸ pow_orderOf_eq_one _
  have hy1 : pairAut (matAut B) y₂ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  obtain ⟨μ, hμ⟩ := rel_linear (hXN hyX)
  rw [pairAut_pow] at hyp
  obtain ⟨hB1p, hy₂p⟩ := pairAut_injective (hyp.trans pairAut_one.symm)
  have hBp : B ^ p = 1 := matHom_injective (by rw [map_pow, map_one, matHom_apply]; exact hB1p)
  rcases (show Module.finrank K (fixSub (B : Matrix (Fin 3) (Fin 3) K)) = 2 ∨
      Module.finrank K (fixSub (B : Matrix (Fin 3) (Fin 3) K)) = 3 by
    have := finrank_fixSub_le (B : Matrix (Fin 3) (Fin 3) K); omega) with h2 | h3
  · obtain ⟨P, l, hl1, hlp, hBP⟩ := exists_diag_of_fix_plane hpodd hBp h2
    exact false_of_diag hLX hB hp2 hyX (by rw [pairAut_pow, hB1p, hy₂p, pairAut_one]) hy1 hBP hμ
      hl1 hlp
  ·
    have hB1 : B = 1 := by
      have htop : fixSub (B : Matrix (Fin 3) (Fin 3) K) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [h3, Module.finrank_fin_fun])
      apply Units.ext
      rw [Units.val_one]
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      rw [Matrix.one_mulVec]
      exact mem_fixSub.mp (htop ▸ Submodule.mem_top)
    have hd1 : ((dualGL B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [hB1, ← dualHom_apply, map_one, Units.val_one]
    have hμ1 : μ ≠ 1 := by
      intro h
      apply hy1
      have hy₂1 : y₂ = 1 := toAddMap_injective fun w => by
        rw [hμ, hd1, h, one_smul, Matrix.one_mulVec, toAddMap_one]
      rw [hy₂1, hB1, show matAut (1 : GL (Fin 3) K) = 1 from map_one (matHom (ι := Fin 3)),
        pairAut_one]
    have hμp : μ ^ p = 1 := by
      have hpw : ∀ k : ℕ, ∀ w, toAddMap (y₂ ^ k) w = μ ^ k • w := by
        intro k
        induction k with
        | zero => intro w; rw [pow_zero, pow_zero, one_smul]; rfl
        | succ k ih =>
          intro w
          rw [pow_succ', toAddMap_mul, ih, hμ, hd1, Matrix.one_mulVec, smul_smul, ← pow_succ']
      have := hpw p (Pi.single 0 1)
      rw [hy₂p, toAddMap_one] at this
      have h0 := congrFun this 0
      simpa using h0.symm
    have hBP : (B : Matrix (Fin 3) (Fin 3) K) = ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        diagPow 1 0 0 1 * (((1 : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hB1, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, diagPow,
        ← Matrix.diagonal_one]
      congr 1
      ext i
      fin_cases i <;> simp
    exact false_of_diag hLX hB hp2 hyX (by rw [pairAut_pow, hB1p, hy₂p, pairAut_one]) hy1 hBP hμ
      hμ1 hμp

omit [Finite K] [CharP K 2] in
theorem congrHom_swapAut (x : MulAut (PairMod K)) :
    congrHom (swapAut K) x = swapAut K * x * swapAut K := MulEquiv.ext fun _ => rfl

theorem le_rkIdx_fixV_of_odd {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod K))} (hLX : pairSL K ≤ X) (hXN : X ≤ pairNorm K)
    (hB : HypBang X) {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) {y : MulAut (PairMod K)}
    (hyX : y ∈ X) (hyo : orderOf y = p) : 4 * n ≤ rkIdx (fixV (Subgroup.zpowers y)) := by
  classical
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hp : p.Prime := hpf.out
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; rcases hpodd with ⟨j, hj⟩; omega
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hV : Nat.card (PairMod K) = 2 ^ (6 * n) := by
    rw [card_pairMod, hK, ← pow_mul, mul_comm]
  have hq : Nat.card K = 2 ^ n := hK
  suffices hsuff : Nat.card ↥(fixV (Subgroup.zpowers y)) ≤ 2 ^ (2 * n) by
    refine le_rkIdx_of_card_mul_le hV _ ?_
    calc Nat.card ↥(fixV (Subgroup.zpowers y)) * 2 ^ (4 * n) ≤ 2 ^ (2 * n) * 2 ^ (4 * n) :=
          Nat.mul_le_mul_right _ hsuff
      _ = 2 ^ (6 * n) := by rw [← pow_add]; congr 1; ring
  have hyS := mem_pairSub_of_odd (hXN hyX) hpodd hyp
  set z : ↥(pairSub K) := ⟨y, hyS⟩ with hzdef
  have hye : y = pairAut (fstHom K z) (sndHom K z) := eq_pairAut z
  obtain ⟨h₁, h₂⟩ := fstHom_mem_natNorm (x := z) (hXN hyX)
  have hfix := card_fix_pairAut_le (fstHom K z) (sndHom K z) (Subgroup.zpowers y)
    (by rw [← hye]; exact Subgroup.mem_zpowers y)
  have hyp' := hyp
  rw [hye, pairAut_pow] at hyp'
  obtain ⟨hy1p, hy2p⟩ := pairAut_injective (hyp'.trans pairAut_one.symm)
  have hΓ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3)
  set σ := fieldAut hΓ ⟨_, h₁⟩
  have hsl : IsSemilinear (fstHom K z) σ := isSemilinear_fieldAut hΓ ⟨_, h₁⟩
  have hsl₂ : IsSemilinear (sndHom K z) σ := by
    have := hXN hyX
    rw [hye] at this
    exact rel_semilinear this hsl
  by_cases hσ : σ = RingEquiv.refl K
  swap
  ·
    have hσp : σ ^ p = 1 := by
      have h1 := hsl.pow p
      rw [hy1p] at h1
      exact h1.unique isSemilinear_one
    have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ
    have hbound : ∀ g : MulAut (StdMod (Fin 3) K), IsSemilinear g σ → g ^ p = 1 →
        Nat.card {v : StdMod (Fin 3) K // g v = v} ≤ 2 ^ n := by
      intro g hg hgp
      obtain ⟨-, hc⟩ := card_fixV_of_semilinear (by omega) hK hg hσo hgp
      rw [card_fix_eq_card_fixV, hc, Fintype.card_fin]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      exact Nat.div_le_of_le_mul (by nlinarith)
    calc Nat.card ↥(fixV (Subgroup.zpowers y))
        ≤ Nat.card {v : StdMod (Fin 3) K // (fstHom K z) v = v} *
          Nat.card {w : StdMod (Fin 3) K // (sndHom K z) w = w} := hfix
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul (hbound _ hsl hy1p) (hbound _ hsl₂ hy2p)
      _ = 2 ^ (2 * n) := by rw [← pow_add]; congr 1; ring
  rw [hσ] at hsl hsl₂
  obtain ⟨B₁, hB₁⟩ := exists_matAut_of_mem_linSub (show fstHom K z ∈ linSub from hsl)
  obtain ⟨B₂, hB₂⟩ := exists_matAut_of_mem_linSub (show sndHom K z ∈ linSub from hsl₂)
  rw [hB₁, hB₂] at hfix
  rw [card_fix_matAut, card_fix_matAut] at hfix
  have hyB : y = pairAut (matAut B₁) (matAut B₂) := by rw [hye, hB₁, hB₂]
  by_contra hcon
  push Not at hcon
  have hdim : 2 ≤ Module.finrank K (fixSub (B₁ : Matrix (Fin 3) (Fin 3) K)) ∨
      2 ≤ Module.finrank K (fixSub (B₂ : Matrix (Fin 3) (Fin 3) K)) := by
    by_contra h
    push Not at h
    apply absurd hcon
    push Not
    refine hfix.trans ?_
    rw [← pow_add, hK, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith [h.1, h.2])
  rcases hdim with h1 | h2
  · exact false_of_fst_plane hLX hXN hB hp2 (hyB ▸ hyX) (hyB ▸ hyo) h1
  ·
    set X' := X.map (congrHom (swapAut K)) with hX'
    have hLX' : pairSL K ≤ X' := by
      intro g hg
      refine ⟨swapAut K * g * swapAut K, hLX ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp swapAut_mem_pairNorm g).mp hg
        rwa [swapAut_inv] at this
      · rw [congrHom_swapAut]
        change swapAut K * (swapAut K * g * swapAut K) * swapAut K = g
        rw [show swapAut K * (swapAut K * g * swapAut K) * swapAut K =
          (swapAut K * swapAut K) * g * (swapAut K * swapAut K) by group, swapAut_mul_self,
          one_mul, mul_one]
    have hXN' : X' ≤ pairNorm K := by
      rintro _ ⟨x, hx, rfl⟩
      rw [congrHom_swapAut]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ swapAut_mem_pairNorm (hXN hx))
        swapAut_mem_pairNorm
    have hB' : HypBang X' := (hypBang_map_congrHom (swapAut K)).mpr hB
    have hy' : congrHom (swapAut K) y = pairAut (matAut B₂) (matAut B₁) := by
      rw [congrHom_swapAut, hyB, mul_assoc, pairAut_mul_swapAut, ← mul_assoc,
        swapAut_mul_self, one_mul]
    have hyX' : pairAut (matAut B₂) (matAut B₁) ∈ X' := hy' ▸ ⟨y, hyX, rfl⟩
    have hyo' : orderOf (pairAut (matAut B₂) (matAut B₁)) = p := by
      rw [← hy', orderOf_injective _ (congrHom_injective (swapAut K)) y]
      exact hyo
    exact false_of_fst_plane hLX' hXN' hB' hp2 hyX' hyo' h2

theorem le_betaH {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod K))} (hLX : pairSL K ≤ X) (hXN : X ≤ pairNorm K)
    (hB : HypBang X) : ((4 * n : ℕ) : ℕ∞) ≤ betaH X := by
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  rw [le_betaH_iff_isPGroup]
  intro U _ hnp
  obtain ⟨p, hp, hp2, hpdvd⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥(X ⊓ centSub U) := by
    by_contra h
    push Not at h
    apply hnp
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
    intro d hd hdd
    by_contra hd2
    exact h d hd hd2 hdd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ centSub U)) p hpdvd
  have hxo : orderOf (y : MulAut (PairMod K)) = p := by
    rw [Subgroup.orderOf_coe, hy]
  have hUx : U ≤ fixV (Subgroup.zpowers (y : MulAut (PairMod K))) := fun u hu =>
    mem_fixV_zpowers_iff.mpr (y.2.2 u hu)
  have h1 := le_rkIdx_fixV_of_odd hn hK hLX hXN hB hp2 y.2.1 hxo
  have h2 := rkIdx_anti hUx
  exact_mod_cast h1.trans h2

end SL3Pair

end H

end CFSG.Quasithin

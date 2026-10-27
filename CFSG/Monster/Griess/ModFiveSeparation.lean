module

public import CFSG.Monster.Griess.ModFive.Lattice
import CFSG.Monster.Griess.ModFive.Torsion
import CFSG.Monster.Griess.ModFive.Spin
public import CFSG.Monster.Griess.ThreeVectorSeparation

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess.ModFive

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Parity Matrix Module

@[expose] def fixL (g : SpaceB ≃ₗ[ℚ] SpaceB) : AddSubgroup SpaceB where
  carrier := {v | v ∈ L5 ∧ g v - v ∈ M5}
  add_mem' {_ _} hu hv := ⟨add_mem hu.1 hv.1, by
    rw [map_add, add_sub_add_comm]
    exact add_mem hu.2 hv.2⟩
  zero_mem' := ⟨zero_mem _, by
    rw [map_zero, sub_zero]
    exact zero_mem _⟩
  neg_mem' {_} hv := ⟨neg_mem hv.1, by
    rw [map_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub]
    exact neg_mem hv.2⟩

variable {g : SpaceB ≃ₗ[ℚ] SpaceB}

theorem mem_fixL {v : SpaceB} : v ∈ fixL g ↔ v ∈ L5 ∧ g v - v ∈ M5 := Iff.rfl

theorem smul_mem_fixL {r : ℚ} (hr : r ∈ R5) {v : SpaceB} (hv : v ∈ fixL g) : r • v ∈ fixL g :=
  ⟨smul_mem_L5 hr hv.1, by
    have e : g (r • v) - r • v = r • (g v - v) := by rw [smul_sub, map_smul]
    rw [e]
    exact smul_mem_M5 hr hv.2⟩

theorem gmul_mem_fixL (hmul : IsAlgAut g) (hL : ∀ v ∈ L5, g v ∈ L5) {u v : SpaceB}
    (hu : u ∈ fixL g) (hv : v ∈ fixL g) : gmul u v ∈ fixL g :=
  ⟨gmul_mem_L5 hu.1 hv.1, by
    rw [hmul u v]
    exact gmul_sub_gmul_mem_M5 hu.1 (hL v hv.1) hu.2 hv.2⟩

theorem mem_fixL_of_cong5 {v : SpaceB} (h : Cong5 (g v) v) : v ∈ fixL g :=
  ⟨(cong5_iff.1 h).2.1, (cong5_iff.1 h).2.2⟩

theorem qf_smul (c : ShortIdx) (t : ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    qf c (t • M) = t * qf c M := by
  unfold qf
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

@[expose] noncomputable def symPow (a : symMat) (k : ℕ) : symMat :=
  ⟨(4 : ℚ) ^ k • (a : Matrix (Fin 24) (Fin 24) ℚ) ^ (k + 1), by
    rw [mem_symMat, transpose_smul, transpose_pow, mem_symMat.1 a.2]⟩

theorem coe_symPow (a : symMat) (k : ℕ) :
    (symPow a k : Matrix (Fin 24) (Fin 24) ℚ) =
      (4 : ℚ) ^ k • (a : Matrix (Fin 24) (Fin 24) ℚ) ^ (k + 1) := rfl

theorem symPow_zero (a : symMat) : symPow a 0 = a :=
  Subtype.ext (by rw [coe_symPow, pow_zero, one_smul, zero_add, pow_one])

theorem gmul_inA_symPow (a : symMat) (k : ℕ) :
    gmul (inA a) (inA (symPow a k)) = inA (symPow a (k + 1)) := by
  rw [Parity.gmul_inA_inA]
  refine congrArg inA (Subtype.ext ?_)
  rw [Submodule.coe_smul, coe_jordanQ, coe_symPow, coe_symPow, Matrix.mul_smul, Matrix.smul_mul,
    ← pow_succ', ← pow_succ]
  module

section StepX

variable (hmul : IsAlgAut g) (hL : ∀ v ∈ L5, g v ∈ L5)
include hmul hL

theorem inX_single_mem_fixL {a₀ : symMat} {β : SpaceX}
    (hsep : ∀ c d : ShortIdx, (∀ k : ℕ, qf c ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ (k + 1)) -
      qf d ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ (k + 1)) ∈ D5) → c = d)
    (hβ : ∀ c, β c ∉ D5) (ha : inA a₀ ∈ fixL g) (hb : inX β ∈ fixL g) (c₀ : ShortIdx) :
    inX (Pi.single c₀ 1) ∈ fixL g := by
  classical
  have hP : ∀ k, inA (symPow a₀ k) ∈ fixL g := by
    intro k
    induction k with
    | zero =>
      rw [symPow_zero]
      exact ha
    | succ k ih =>
      rw [← gmul_inA_symPow]
      exact gmul_mem_fixL hmul hL ha ih
  have hlamR : ∀ k c, shortEig (symPow a₀ k) c ∈ R5 := fun k c =>
    div_eight_mem_R5 (qf_mem_R5 c (inA_mem_L5_iff.1 (hP k).1))
  have hdiff : ∀ k c d, shortEig (symPow a₀ k) c - shortEig (symPow a₀ k) d =
      (4 : ℚ) ^ k / 8 * (qf c ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ (k + 1)) -
        qf d ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ (k + 1))) := by
    intro k c d
    rw [shortEig, shortEig, coe_symPow, qf_smul, qf_smul]
    ring
  have hex : ∀ d, ∃ k, d ≠ c₀ →
      shortEig (symPow a₀ k) c₀ - shortEig (symPow a₀ k) d ∉ D5 := by
    intro d
    by_contra h
    push Not at h
    refine (h 0).1 (hsep c₀ d fun k => ?_).symm
    have e : qf c₀ ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ (k + 1)) -
        qf d ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ (k + 1)) =
        (8 * (4 : ℚ)⁻¹ ^ k) * (shortEig (symPow a₀ k) c₀ - shortEig (symPow a₀ k) d) := by
      have h48 : (8 * (4 : ℚ)⁻¹ ^ k) * ((4 : ℚ) ^ k / 8) = 1 := by
        rw [inv_pow]
        field_simp
      rw [hdiff, ← mul_assoc, h48, one_mul]
    rw [e]
    exact mul_mem_D5 (mul_mem eight_mem_R5 (pow_mem inv_four_mem_R5 k)) (h k).2
  choose k hk using hex
  set u : ShortIdx → ℚ := fun d =>
    (shortEig (symPow a₀ (k d)) c₀ - shortEig (symPow a₀ (k d)) d)⁻¹ with hu
  have huR : ∀ d, d ≠ c₀ → u d ∈ R5 := fun d hd =>
    inv_mem_R5 (sub_mem (hlamR _ _) (hlamR _ _)) (hk d hd)
  set f : ShortIdx → ShortIdx → ℚ := fun d c =>
    (shortEig (symPow a₀ (k d)) c - shortEig (symPow a₀ (k d)) d) * u d with hf
  have hstep : ∀ d, d ≠ c₀ → ∀ y : SpaceX, inX y ∈ fixL g → inX (f d * y) ∈ fixL g := by
    intro d hd y hy
    have e : inX (f d * y) = u d • (gmul (inA (symPow a₀ (k d))) (inX y) -
        shortEig (symPow a₀ (k d)) d • inX y) := by
      rw [gmul_inA_inX_shortEig]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp
      · funext c
        simp only [hf, Pi.mul_apply, Prod.smul_snd, Prod.smul_fst, Prod.snd_sub, Prod.fst_sub,
          Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      · simp
    rw [e]
    exact smul_mem_fixL (huR d hd) (sub_mem (gmul_mem_fixL hmul hL (hP _) hy)
      (smul_mem_fixL (hlamR _ _) hy))
  have hprod : ∀ s : Finset ShortIdx, c₀ ∉ s → inX ((∏ d ∈ s, f d) * β) ∈ fixL g := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.prod_empty, one_mul]
      exact hb
    | insert d s hds ih =>
      intro hc
      rw [Finset.prod_insert hds, mul_assoc]
      exact hstep d (fun h => hc (h ▸ Finset.mem_insert_self _ _)) _
        (ih fun h => hc (Finset.mem_insert_of_mem h))
  have hδ : (∏ d ∈ Finset.univ.erase c₀, f d) = Pi.single c₀ 1 := by
    funext c
    rw [Finset.prod_apply]
    by_cases hc : c = c₀
    · subst hc
      rw [Pi.single_eq_same]
      refine Finset.prod_eq_one fun d hd => ?_
      exact mul_inv_cancel₀ (ne_zero_of_not_mem_D5 (hk d (Finset.ne_of_mem_erase hd)))
    · rw [Pi.single_eq_of_ne hc]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩) (by simp [hf])
  have h1 := hprod (Finset.univ.erase c₀) (Finset.notMem_erase c₀ _)
  rw [hδ] at h1
  have hβR : β c₀ ∈ R5 := (inX_mem_L5_iff.1 hb.1) c₀
  have e2 : inX (Pi.single c₀ 1) = (β c₀)⁻¹ • inX (Pi.single c₀ 1 * β) := by
    refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
    funext c
    by_cases hc : c = c₀
    · subst hc
      simp [inv_mul_cancel₀ (ne_zero_of_not_mem_D5 (hβ c))]
    · simp [hc]
  rw [e2]
  exact smul_mem_fixL (inv_mem_R5 hβR (hβ c₀)) h1

end StepX

section AxisSpan

open CFSG.Monster.SpinLattice

variable {S : AddSubgroup symMat}

theorem basisA_offDiag_mem5 (hS : ∀ r : Q, IsShortCoord (coordOf r) → axisE r ∈ S) {i j : Fin 24}
    (hij : i < j) : basisA s(i, j) ∈ S := by
  have e : basisA s(i, j) = axisE (rPlus i j) - axisE (rMinus i j) := by
    apply Subtype.ext
    rw [coe_basisA, ite_eq_right hij.ne, Submodule.coe_sub, coe_axisE_rPlus hij,
      coe_axisE_rMinus hij, projMat_vPlus_sub_vMinus]
  rw [e]
  exact S.sub_mem (hS _ (isShortCoord_rPlus hij)) (hS _ (isShortCoord_rMinus hij))

theorem exists_diagPair_mem5 (hS : ∀ r : Q, IsShortCoord (coordOf r) → axisE r ∈ S)
    {i j : Fin 24} (hij : i ≠ j) :
    ∃ A : symMat, A ∈ S ∧
      (A : Matrix (Fin 24) (Fin 24) ℚ) = Matrix.single i i 1 + Matrix.single j j 1 := by
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨axisE (rPlus i j) + axisE (rMinus i j),
      S.add_mem (hS _ (isShortCoord_rPlus h)) (hS _ (isShortCoord_rMinus h)), ?_⟩
    rw [Submodule.coe_add, coe_axisE_rPlus h, coe_axisE_rMinus h, projMat_vPlus_add_vMinus]
  · refine ⟨axisE (rPlus j i) + axisE (rMinus j i),
      S.add_mem (hS _ (isShortCoord_rPlus h)) (hS _ (isShortCoord_rMinus h)), ?_⟩
    rw [Submodule.coe_add, coe_axisE_rPlus h, coe_axisE_rMinus h, projMat_vPlus_add_vMinus,
      add_comm]

theorem basisA_diag_mem5 (hhalf : ∀ A ∈ S, (2 : ℚ)⁻¹ • A ∈ S)
    (hS : ∀ r : Q, IsShortCoord (coordOf r) → axisE r ∈ S) (i : Fin 24) : basisA s(i, i) ∈ S := by
  have hne : i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 := by revert i; decide
  obtain ⟨A₁, h₁, e₁⟩ := exists_diagPair_mem5 hS hne.1
  obtain ⟨A₂, h₂, e₂⟩ := exists_diagPair_mem5 hS hne.2.1
  obtain ⟨A₃, h₃, e₃⟩ := exists_diagPair_mem5 hS hne.2.2
  have e : basisA s(i, i) = (2 : ℚ)⁻¹ • (A₁ + A₂ - A₃) := by
    apply Subtype.ext
    rw [coe_basisA, ite_eq_left rfl, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_add,
      e₁, e₂, e₃]
    module
  rw [e]
  exact hhalf _ (S.sub_mem (S.add_mem h₁ h₂) h₃)

theorem basisA_mem5 (hhalf : ∀ A ∈ S, (2 : ℚ)⁻¹ • A ∈ S)
    (hS : ∀ r : Q, IsShortCoord (coordOf r) → axisE r ∈ S) (z : PairIdx) : basisA z ∈ S := by
  induction z using Sym2.ind with
  | _ i j =>
    rcases lt_trichotomy i j with h | rfl | h
    · exact basisA_offDiag_mem5 hS h
    · exact basisA_diag_mem5 hhalf hS i
    · rw [Sym2.eq_swap]
      exact basisA_offDiag_mem5 hS h

end AxisSpan

theorem basisA_isR5 (z : PairIdx) : IsR5 (basisA z : Matrix (Fin 24) (Fin 24) ℚ) := fun k l => by
  rw [basisA_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem symEntry_mem_R5 {A : symMat} (hA : IsR5 (A : Matrix (Fin 24) (Fin 24) ℚ)) (z : PairIdx) :
    symEntry A z ∈ R5 := by
  induction z using Sym2.ind with
  | _ i j =>
    rw [symEntry_mk]
    exact hA i j

theorem inA_mem_fixL (hmul : IsAlgAut g) (hL : ∀ v ∈ L5, g v ∈ L5)
    (hX : ∀ c : ShortIdx, inX (Pi.single c 1) ∈ fixL g) {A : symMat}
    (hA : IsR5 (A : Matrix (Fin 24) (Fin 24) ℚ)) : inA A ∈ fixL g := by
  let S : AddSubgroup symMat := (fixL g).comap Griess.inAₗ.toAddMonoidHom
  have hmemS : ∀ B : symMat, B ∈ S ↔ inA B ∈ fixL g := fun _ => Iff.rfl
  have hsmul : ∀ r ∈ R5, ∀ B ∈ S, r • B ∈ S := fun r hr B hB => by
    rw [hmemS] at hB ⊢
    have e : inA (r • B) = r • inA B := map_smul Griess.inAₗ r B
    rw [e]
    exact smul_mem_fixL hr hB
  have hU : ∀ c, UmatS c ∈ S := by
    intro c
    have h1 := gmul_mem_fixL hmul hL (hX c) (hX c)
    rw [gmul_inX_single_self] at h1
    have e : UmatS c = (8 : ℚ) • ((8 : ℚ)⁻¹ • UmatS c) := by
      rw [smul_smul]
      norm_num
    rw [e]
    exact hsmul _ eight_mem_R5 _ h1
  have hS : ∀ r : Q, IsShortCoord (coordOf r) → axisE r ∈ S := by
    intro r hr
    have e : axisE r = (32 : ℚ)⁻¹ • UmatS (shortCls hr) := by
      apply Subtype.ext
      rw [Submodule.coe_smul, coe_UmatS, Umat_eq_axisE hr, smul_smul]
      norm_num
    rw [e]
    exact hsmul _ inv_32_mem_R5 _ (hU _)
  have hB : ∀ z, basisA z ∈ S := basisA_mem5 (hsmul _ inv_two_mem_R5) hS
  rw [← hmemS, symMat_eq_sum A]
  exact sum_mem fun z _ => hsmul _ (symEntry_mem_R5 hA z) _ (hB z)

theorem trace_mul_single_one (M : Matrix (Fin 24) (Fin 24) ℚ) (i j : Fin 24) :
    trace (M * Matrix.single i j 1) = M j i := by
  simp [trace, mul_apply, Matrix.single, ite_and]

theorem inW_sub (x y : SpaceW) : inW x - inW y = inW (x - y) :=
  Prod.ext (by simp) (Prod.ext (by simp) rfl)

theorem inW_sub_mem_M5 (hiso : ∀ u v, bform (g u) (g v) = bform u v) (hL : ∀ v ∈ L5, g v ∈ L5)
    (hA : ∀ A : symMat, IsR5 (A : Matrix (Fin 24) (Fin 24) ℚ) → inA A ∈ fixL g)
    (hX : ∀ c : ShortIdx, inX (Pi.single c 1) ∈ fixL g) {N : SpaceW} (hN : IsR5 N) :
    g (inW N) - inW (resW g N) ∈ M5 := by
  have hvL : g (inW N) ∈ L5 := hL _ (inW_mem_L5_iff.2 hN)
  have horth : ∀ w, w ∈ fixL g → bform (inW N) w = 0 → bform (g (inW N)) w ∈ D5 := by
    intro w hw h0
    have e : bform (g (inW N)) w =
        bform (g (inW N)) (g w) - bform (g (inW N)) (g w - w) := by
      rw [map_sub (bform (g (inW N))), sub_sub_cancel]
    rw [e, hiso, h0, zero_sub]
    exact neg_mem (bform_mem_D5 hvL hw.2)
  have hAD : ∀ i j, ((g (inW N)).1 : Matrix (Fin 24) (Fin 24) ℚ) i j ∈ D5 := by
    have hz : ∀ z, bform (g (inW N)) (inA (basisA z)) ∈ D5 := fun z =>
      horth _ (hA _ (basisA_isR5 z)) (by simp [bform_apply])
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · have h := hz s(i, i)
      rwa [bform_inA_right, coe_basisA, ite_eq_left rfl, trace_mul_single_one] at h
    · have h := hz s(i, j)
      rw [bform_inA_right, coe_basisA, ite_eq_right hij, Matrix.mul_add, trace_add,
        trace_mul_single_one, trace_mul_single_one] at h
      have hsym : ((g (inW N)).1 : Matrix (Fin 24) (Fin 24) ℚ) j i =
          ((g (inW N)).1 : Matrix (Fin 24) (Fin 24) ℚ) i j :=
        congrFun (congrFun (mem_symMat.1 (g (inW N)).1.2) i) j
      rw [hsym, ← two_mul] at h
      have h2 := mul_mem_D5 inv_two_mem_R5 h
      rwa [← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul] at h2
  have hXD : ∀ c, (g (inW N)).2.1 c ∈ D5 := by
    intro c
    have h := horth _ (hX c) (by simp [bform_apply])
    have e : bform (g (inW N)) (inX (Pi.single c 1)) = (g (inW N)).2.1 c := by
      rw [bform_inX_right]
      simp [Pi.single_apply]
    rwa [e] at h
  refine ⟨fun i j => ?_, fun c => ?_, fun j i => ?_⟩
  · change ((g (inW N)).1 : Matrix (Fin 24) (Fin 24) ℚ) i j - 0 ∈ D5
    rw [sub_zero]
    exact hAD i j
  · change (g (inW N)).2.1 c - 0 ∈ D5
    rw [sub_zero]
    exact hXD c
  · change (g (inW N)).2.2 j i - (resW g N) j i ∈ D5
    rw [resW_apply, sub_self]
    exact zero_mem _

section SpinMod5

variable (R : Module.End ℚ SpaceW)
  (hRA : ∀ N B : Matrix _ _ ℚ, IsR5 N → Bᵀ = B → IsR5 B → IsD5 (R (N * B) - R N * B))
include hRA

theorem commute_mul_single_mod5 {N : SpaceW} (hN : IsR5 N) (i j : Fin 24) :
    IsD5 (R (N * Matrix.single i j (1 : ℚ)) - R N * Matrix.single i j (1 : ℚ)) := by
  by_cases hij : i = j
  · subst hij
    exact hRA _ _ hN (transpose_single i i 1) (isR5_single i i)
  · have e : Matrix.single i j (1 : ℚ) =
        Matrix.single i i (1 : ℚ) * (Matrix.single i j (1 : ℚ) + Matrix.single j i (1 : ℚ)) := by
      simp [Matrix.mul_add, hij]
    have hF : (Matrix.single i j (1 : ℚ) + Matrix.single j i (1 : ℚ))ᵀ =
        Matrix.single i j (1 : ℚ) + Matrix.single j i (1 : ℚ) := by
      rw [transpose_add, transpose_single, transpose_single, add_comm]
    have hFR : IsR5 (Matrix.single i j (1 : ℚ) + Matrix.single j i (1 : ℚ)) :=
      (isR5_single i j).add (isR5_single j i)
    have h1 := hRA (N * Matrix.single i i (1 : ℚ)) _ (hN.mul (isR5_single i i)) hF hFR
    have h2 := (hRA N _ hN (transpose_single i i 1) (isR5_single i i)).mul_R5 hFR
    rw [e, ← Matrix.mul_assoc N]
    have e2 : R (N * Matrix.single i i (1 : ℚ) *
          (Matrix.single i j (1 : ℚ) + Matrix.single j i (1 : ℚ))) -
        R N * (Matrix.single i i (1 : ℚ) *
          (Matrix.single i j (1 : ℚ) + Matrix.single j i (1 : ℚ))) =
        (R (N * Matrix.single i i (1 : ℚ) *
          (Matrix.single i j (1 : ℚ) + Matrix.single j i (1 : ℚ))) -
          R (N * Matrix.single i i (1 : ℚ)) *
            (Matrix.single i j (1 : ℚ) + Matrix.single j i (1 : ℚ))) +
        (R (N * Matrix.single i i (1 : ℚ)) - R N * Matrix.single i i (1 : ℚ)) *
          (Matrix.single i j (1 : ℚ) + Matrix.single j i (1 : ℚ)) := by
      rw [Matrix.sub_mul, Matrix.mul_assoc (R N)]
      abel
    rw [e2]
    exact h1.add h2

theorem sub_spinOf_mul_isD5 {N : SpaceW} (hN : IsR5 N) : IsD5 (R N - spinOf R * N) := by
  have hsingle : ∀ (a : SpinIdx) (j : Fin 24),
      IsD5 (R (Matrix.single a j (1 : ℚ)) - spinOf R * Matrix.single a j (1 : ℚ)) := by
    intro a j
    have h := commute_mul_single_mod5 R hRA (isR5_single a 0) 0 j
    rw [single_mul_single_same, one_mul] at h
    have e : R (Matrix.single a 0 (1 : ℚ)) * Matrix.single (0 : Fin 24) j (1 : ℚ) =
        spinOf R * Matrix.single a j (1 : ℚ) := by
      ext b k
      by_cases hk : k = j
      · subst hk
        rw [mul_single_apply_same, mul_single_apply_same, mul_one, mul_one, spinOf, of_apply]
      · rw [mul_single_apply_of_ne _ _ _ _ _ hk, mul_single_apply_of_ne _ _ _ _ _ hk]
    rwa [e] at h
  have hdec : N = ∑ a, ∑ j, N a j • Matrix.single a j (1 : ℚ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single N]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  have e : R N - spinOf R * N =
      ∑ a, ∑ j, N a j • (R (Matrix.single a j (1 : ℚ)) - spinOf R * Matrix.single a j (1 : ℚ)) := by
    conv_lhs => rw [hdec]
    simp only [map_sum, map_smul, Matrix.mul_sum, Matrix.mul_smul, smul_sub,
      Finset.sum_sub_distrib]
  rw [e]
  exact isD5_sum _ fun a _ => isD5_sum _ fun j _ => (hsingle a j).smul (hN a j)

variable (hRL : ∀ N, IsR5 N → IsR5 (R N))
  (hRK : ∀ (c : ShortIdx) (N : SpaceW), IsR5 N →
    IsD5 (R (Rmat c * N * Kc c) - Rmat c * R N * Kc c))
include hRL hRK

omit hRL in
theorem spinOf_commute_mod5 (c : ShortIdx) : IsD5 (spinOf R * Rmat c - Rmat c * spinOf R) := by
  have hKR : IsR5 (Kc c) := isR5_one.sub ((Umat_isR5 c).smul inv_four_mem_R5)
  have hKinv : IsR5 (1 - (28 : ℚ)⁻¹ • Umat c) := isR5_one.sub ((Umat_isR5 c).smul inv_28_mem_R5)
  have hN : ∀ N : SpaceW, IsR5 N → IsD5 ((spinOf R * Rmat c - Rmat c * spinOf R) * N) := by
    intro N hN
    have hRNK : IsR5 (Rmat c * N * Kc c) := ((Rmat_isR5 c).mul hN).mul hKR
    have X1 := hRK c N hN
    have X2 := sub_spinOf_mul_isD5 R hRA hRNK
    have X3 := ((Rmat_isR5 c).mul_D5 (sub_spinOf_mul_isD5 R hRA hN)).mul_R5 hKR
    have hsum := (X1.sub X2).add X3
    have e : (spinOf R * Rmat c - Rmat c * spinOf R) * N * Kc c =
        (R (Rmat c * N * Kc c) - Rmat c * R N * Kc c) -
          (R (Rmat c * N * Kc c) - spinOf R * (Rmat c * N * Kc c)) +
          Rmat c * (R N - spinOf R * N) * Kc c := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [← e] at hsum
    have h := hsum.mul_R5 hKinv
    rwa [Matrix.mul_assoc _ (Kc c), Kc_mul_Kinv, Matrix.mul_one] at h
  intro a b
  have h := hN (Matrix.single b 0 (1 : ℚ)) (isR5_single b 0) a 0
  rwa [mul_single_apply_same, mul_one] at h

theorem exists_smul_mod5 : ∃ t ∈ R5, ∀ N : SpaceW, IsR5 N → IsD5 (R N - t • N) := by
  have hsR : IsR5 (spinOf R) := fun b a => hRL _ (isR5_single a 0) b 0
  obtain ⟨t, ht, hst⟩ := exists_scalar_of_commute_Rmat_mod5 hsR (spinOf_commute_mod5 R hRA hRK)
  refine ⟨t, ht, fun N hN => ?_⟩
  have e : R N - t • N = (R N - spinOf R * N) + (spinOf R - t • 1) * N := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    abel
  rw [e]
  exact (sub_spinOf_mul_isD5 R hRA hN).add (hst.mul_R5 hN)

end SpinMod5

section StepW

variable (hmul : IsAlgAut g) (hiso : ∀ u v, bform (g u) (g v) = bform u v)
  (hL : ∀ v ∈ L5, g v ∈ L5)
  (hA : ∀ A : symMat, IsR5 (A : Matrix (Fin 24) (Fin 24) ℚ) → inA A ∈ fixL g)
  (hX : ∀ c : ShortIdx, inX (Pi.single c 1) ∈ fixL g)
include hmul hiso hL hA hX

theorem resW_mul_sym_mod5 {N B : Matrix _ _ ℚ} (hN : IsR5 N) (hB : Bᵀ = B) (hBR : IsR5 B) :
    IsD5 (resW g (N * B) - resW g N * B) := by
  let A : symMat := ⟨B - (trace B / 32) • (1 : Matrix (Fin 24) (Fin 24) ℚ), by
    rw [mem_symMat, transpose_sub, transpose_smul, transpose_one, hB]⟩
  have hAR : IsR5 (A : Matrix (Fin 24) (Fin 24) ℚ) := by
    refine hBR.sub (isR5_one.smul ?_)
    rw [div_eq_mul_inv]
    exact mul_mem hBR.trace_mem inv_32_mem_R5
  have hmulW : ∀ N' : SpaceW, gmul (inA A) (inW N') = inW (N' * B) := fun N' => by
    rw [Parity.gmul_inA_inW]
    change inW (N' * MA (A : Matrix (Fin 24) (Fin 24) ℚ)) = _
    rw [MA_surj]
  have hW1 := inW_sub_mem_M5 hiso hL hA hX (hN.mul hBR)
  have hW2 := inW_sub_mem_M5 hiso hL hA hX hN
  have hprod := gmul_sub_gmul_mem_M5 (inA_mem_L5_iff.2 hAR) (hL _ (inW_mem_L5_iff.2 hN))
    (hA A hAR).2 hW2
  rw [← hmul (inA A) (inW N), hmulW, hmulW] at hprod
  have h := sub_mem hprod hW1
  rw [sub_sub_sub_cancel_left, inW_sub] at h
  exact inW_mem_M5_iff.1 h

theorem resW_Rmat_mod5 (c : ShortIdx) {N : SpaceW} (hN : IsR5 N) :
    IsD5 (resW g (Rmat c * N * Kc c) - Rmat c * resW g N * Kc c) := by
  have e1 : ∀ N' : SpaceW, gmul (inX (Pi.single c 1)) (inW N') =
      inW ((8 : ℚ)⁻¹ • (Rmat c * N' * Kc c)) := by
    intro N'
    rw [gmul_inW_eq rfl]
    refine congrArg inW ?_
    have := Lw_inX_smul_single 1 c N'
    rw [one_smul] at this
    rw [this]
    norm_num
  have hKR : IsR5 (Kc c) := isR5_one.sub ((Umat_isR5 c).smul inv_four_mem_R5)
  have hN8 : IsR5 ((8 : ℚ)⁻¹ • (Rmat c * N * Kc c)) :=
    (((Rmat_isR5 c).mul hN).mul hKR).smul inv_eight_mem_R5
  have hW1 := inW_sub_mem_M5 hiso hL hA hX hN8
  have hW2 := inW_sub_mem_M5 hiso hL hA hX hN
  have hprod := gmul_sub_gmul_mem_M5 (hX c).1 (hL _ (inW_mem_L5_iff.2 hN)) (hX c).2 hW2
  rw [← hmul (inX (Pi.single c 1)) (inW N), e1, e1] at hprod
  have h := sub_mem hprod hW1
  rw [sub_sub_sub_cancel_left, inW_sub, map_smul, ← smul_sub] at h
  have h8 := (inW_mem_M5_iff.1 h).smul eight_mem_R5
  rwa [smul_smul, mul_inv_cancel₀ (by norm_num : (8 : ℚ) ≠ 0), one_smul] at h8

theorem inW_mem_fixL {N₀ : SpaceW} (hN₀ : ∃ j i, N₀ j i ∉ D5) (hw : inW N₀ ∈ fixL g)
    {N : SpaceW} (hN : IsR5 N) : inW N ∈ fixL g := by
  have hRL : ∀ N, IsR5 N → IsR5 (resW g N) := fun N hN => (hL _ (inW_mem_L5_iff.2 hN)).2.2
  obtain ⟨t, -, hst⟩ := exists_smul_mod5 (resW g)
    (fun N B hN hB hBR => resW_mul_sym_mod5 hmul hiso hL hA hX hN hB hBR) hRL
    (fun c N hN => resW_Rmat_mod5 hmul hiso hL hA hX c hN)
  have hN₀R : IsR5 N₀ := inW_mem_L5_iff.1 hw.1
  have hR0 : IsD5 (resW g N₀ - N₀) := hw.2.2.2
  have ht1 : t - 1 ∈ D5 := by
    obtain ⟨j, i, hji⟩ := hN₀
    have h := (hR0.sub (hst N₀ hN₀R)) j i
    have e : (resW g N₀ - N₀ - (resW g N₀ - t • N₀)) j i = N₀ j i * (t - 1) := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e] at h
    exact mem_D5_of_mul_mem (hN₀R j i) hji h
  refine ⟨inW_mem_L5_iff.2 hN, ?_⟩
  have h1 := inW_sub_mem_M5 hiso hL hA hX hN
  have h2 : inW (resW g N) - inW N ∈ M5 := by
    rw [inW_sub]
    refine inW_mem_M5_iff.2 ?_
    have e : resW g N - N = (resW g N - t • N) + (t - 1) • N := by
      rw [sub_smul, one_smul]
      abel
    rw [e]
    exact (hst N hN).add fun j i => mul_mem_D5' ht1 (hN j i)
  have h3 := add_mem h1 h2
  rwa [sub_add_sub_cancel] at h3

end StepW

theorem mem_fixL_of_mem_L5
    (hA : ∀ A : symMat, IsR5 (A : Matrix (Fin 24) (Fin 24) ℚ) → inA A ∈ fixL g)
    (hX : ∀ c : ShortIdx, inX (Pi.single c 1) ∈ fixL g)
    (hW : ∀ N : SpaceW, IsR5 N → inW N ∈ fixL g) {v : SpaceB} (hv : v ∈ L5) : v ∈ fixL g := by
  have hdec : v = inA v.1 + inX v.2.1 + inW v.2.2 :=
    Prod.ext (by simp) (Prod.ext (by simp) (by simp))
  have hx : inX v.2.1 = ∑ c, v.2.1 c • inX (Pi.single c 1) := by
    rw [← sum_smul_basisB_eq_inX]
    exact Finset.sum_congr rfl fun c _ => by rw [basisB_inr_inl]
  rw [hdec]
  refine add_mem (add_mem (hA _ hv.1) ?_) (hW _ hv.2.2)
  rw [hx]
  exact sum_mem fun c _ => smul_mem_fixL (hv.2.1 c) (hX c)

theorem eq_one_of_cong5_three_vectors_AutO {a₀ : symMat} {β : SpaceX} {N₀ : SpaceW} {K : ℕ}
    (hsep : ∀ c d : ShortIdx, (∀ k ∈ Finset.Icc 1 K,
      qf c ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ k) -
        qf d ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ k) ∈ D5) → c = d)
    (hβ : ∀ c, β c ∉ D5) (hN₀ : ∃ j i, N₀ j i ∉ D5)
    (hg : g ∈ AutO) (hfin : IsOfFinOrder g) (hgL : ∀ v, Int5 v → Int5 (g v))
    (ha : Cong5 (g (inA a₀)) (inA a₀)) (hb : Cong5 (g (inX β)) (inX β))
    (hw : Cong5 (g (inW N₀)) (inW N₀)) : g = 1 := by
  obtain ⟨hmul, hiso⟩ := mem_AutO.1 hg
  have hL : ∀ v ∈ L5, g v ∈ L5 := fun v hv => hgL v hv
  have hsep' : ∀ c d : ShortIdx, (∀ k : ℕ, qf c ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ (k + 1)) -
      qf d ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ (k + 1)) ∈ D5) → c = d := fun c d h =>
    hsep c d fun k hk => by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := (Finset.mem_Icc.1 hk).1; omega⟩
      exact h j
  have hX := inX_single_mem_fixL hmul hL hsep' hβ (mem_fixL_of_cong5 ha) (mem_fixL_of_cong5 hb)
  have hA : ∀ A : symMat, IsR5 (A : Matrix (Fin 24) (Fin 24) ℚ) → inA A ∈ fixL g :=
    fun A hA => inA_mem_fixL hmul hL hX hA
  have hW : ∀ N : SpaceW, IsR5 N → inW N ∈ fixL g := fun N hN =>
    inW_mem_fixL hmul hiso hL hA hX hN₀ (mem_fixL_of_cong5 hw) hN
  exact eq_one_of_sub_mem_M5 hfin hL fun v hv => (mem_fixL_of_mem_L5 hA hX hW hv).2

theorem eq_one_of_cong5_three_vectors {a₀ : symMat} {β : SpaceX} {N₀ : SpaceW} {K : ℕ}
    (hsep : ∀ c d : ShortIdx, (∀ k ∈ Finset.Icc 1 K,
      qf c ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ k) -
        qf d ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ k) ∈ D5) → c = d)
    (hβ : ∀ c, β c ∉ D5) (hN₀ : ∃ j i, N₀ j i ∉ D5)
    (hg : g ∈ Generated.Gmat) (hgL : ∀ v, Int5 v → Int5 (g v))
    (ha : Cong5 (g (inA a₀)) (inA a₀)) (hb : Cong5 (g (inX β)) (inX β))
    (hw : Cong5 (g (inW N₀)) (inW N₀)) : g = 1 :=
  eq_one_of_cong5_three_vectors_AutO hsep hβ hN₀ (Generated.Gmat_le_AutO hg)
    (Submonoid.isOfFinOrder_coe.2 (isOfFinOrder_of_finite (⟨g, hg⟩ : Generated.Gmat))) hgL
    ha hb hw

theorem mod_five_three_vector_separation {a₀ : symMat} {β : SpaceX} {N₀ : SpaceW} {K : ℕ}
    (hsep : ∀ c d : ShortIdx, (∀ k ∈ Finset.Icc 1 K,
      qf c ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ k) -
        qf d ((a₀ : Matrix (Fin 24) (Fin 24) ℚ) ^ k) ∈ D5) → c = d)
    (hβ : ∀ c, β c ∉ D5) (hN₀ : ∃ j i, N₀ j i ∉ D5)
    {a b w : SpaceB} (ha : a = inA a₀) (hb : b = ∑ c, β c • basisB (Sum.inr (Sum.inl c)))
    (hw : w = inW N₀) (hg : g ∈ Generated.Gmat) (hgL : ∀ v, Int5 v → Int5 (g v))
    (hga : Cong5 (g a) a) (hgb : Cong5 (g b) b) (hgw : Cong5 (g w) w) : g = 1 := by
  rw [sum_smul_basisB_eq_inX] at hb
  subst ha hb hw
  exact eq_one_of_cong5_three_vectors hsep hβ hN₀ hg hgL hga hgb hgw

end CFSG.Monster.Griess.ModFive

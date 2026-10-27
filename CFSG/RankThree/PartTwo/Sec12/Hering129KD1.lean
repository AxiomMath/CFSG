module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KH1
public import CFSG.RankThree.PartOne.KFOUT3.CycKrylov
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3Cyc
import CFSG.RankThree.PartTwo.Sec12.Hering129KH2b
import CFSG.RankThree.PartTwo.Sec12.Hering129KH3b
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.RankThree.PartTwo.Sec21.Hering214Lin2
import CFSG.LocalAnalysis.UniquenessCase.UCInspL3Field
public import CFSG.LieType.SteinbergBRTriangularSolvable
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Matrix

namespace Hering129KD1

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.KFOUT3 (krylov)
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp (cycMat)

theorem mod_three_eq_two {p : ℕ} [hp : Fact p.Prime] (hp3 : p % 3 ≠ 1) (hp3' : p ≠ 3) :
    p % 3 = 2 := by
  have h0 : p % 3 ≠ 0 := by
    intro h
    rcases hp.out.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h) with h1 | h1
    · omega
    · exact hp3' h1.symm
  omega

theorem cube_roots_trivial {p : ℕ} [Fact p.Prime] (hp3 : p % 3 ≠ 1) :
    ∀ c : ZMod p, c ^ 3 = 1 → c = 1 := by
  by_cases h3 : p = 3
  · subst h3
    intro c hc
    rw [← ZMod.pow_card c]
    exact hc
  · exact CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.cube_roots_trivial
      (by rw [Nat.card_zmod]; exact mod_three_eq_two hp3 h3)

theorem proj_injective {p : ℕ} [Fact p.Prime] (hp3 : p % 3 ≠ 1) :
    Function.Injective (proj 3 (ZMod p)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  have hc1 : (c : ZMod p) = 1 :=
    cube_roots_trivial hp3 _ (by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one])
  rw [Subgroup.mem_bot]
  ext i j
  rw [hA, hc1]
  simp

theorem exists_conj_of_pow_three {p : ℕ} [Fact p.Prime] (hp3 : p % 3 ≠ 1)
    {β : MulAut (projectiveSL 3 (ZMod p))} (hβ : β ^ 3 = 1) :
    ∃ g : projectiveSL 3 (ZMod p), β = MulAut.conj g := by
  obtain ⟨A, rfl⟩ := CFSG.RankThree.PartTwo.Sec21.Hering214.exists_conjAut_of_pow_three_eq_one
    (fun σ => Subsingleton.elim σ 1) le_rfl hβ
  have hgcd : Nat.gcd 3 (Nat.card (ZMod p) - 1) = 1 := by
    rw [Nat.card_zmod]
    show Nat.Coprime 3 (p - 1)
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
    rintro ⟨k, hk⟩
    have := (Fact.out : p.Prime).two_le
    omega
  have hdvd :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.relIndex_inner_linearAutGroup_dvd
      (k := ZMod p) (n := 3) (by norm_num)
  rw [hgcd, Nat.dvd_one, Subgroup.relIndex_eq_one] at hdvd
  obtain ⟨g, hg⟩ := hdvd (conjAut_mem_linearAutGroup A)
  exact ⟨g, hg.symm⟩

theorem isSolvable_centralizer_of_isUnit_det_krylov {K : Type} [Field K]
    {A : SpecialLinearGroup (Fin 3) K} {v : Fin 3 → K}
    (hv : IsUnit (krylov (A : Matrix (Fin 3) (Fin 3) K) v).det) :
    Group.IsSolvable (Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin 3) K))) := by
  refine Group.isSolvable_of_comm fun x y => ?_
  have hcomm : ∀ z : Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin 3) K)),
      ((z : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (A : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * ((z : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
    intro z
    exact congrArg (fun s : SpecialLinearGroup (Fin 3) K => (s : Matrix (Fin 3) (Fin 3) K))
      (Subgroup.mem_centralizer_singleton_iff.mp z.2)
  exact Subtype.ext (Subtype.ext
    (CFSG.RankThree.PartOne.KFOUT3.commute_of_commute hv (hcomm x) (hcomm y)))

theorem isUnit_det_krylov_of_cyclic {K : Type} [Field K] {M P : Matrix (Fin 3) (Fin 3) K}
    (hP : P.det ≠ 0) (hMP : M * P = P * cycMat) :
    IsUnit (krylov M (fun i => P i 0)).det := by
  have hcol : ∀ j : Fin 3,
      M *ᵥ (fun i => P i j) = fun i => (P * (cycMat : Matrix (Fin 3) (Fin 3) K)) i j := by
    intro j
    rw [← hMP]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have h1 : M *ᵥ (fun i => P i 0) = fun i => P i 1 := by
    rw [hcol 0]
    funext i
    simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]
  have h2 : M *ᵥ (fun i => P i 1) = fun i => P i 2 := by
    rw [hcol 1]
    funext i
    simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]
  have hk : krylov M (fun i => P i 0) = P := by
    ext i j
    fin_cases j <;> simp [krylov, h1, h2]
  rw [hk]
  exact isUnit_iff_ne_zero.mpr hP

theorem isUnit_det_krylov_of_nilpotent {K : Type} [Field K] {M : Matrix (Fin 3) (Fin 3) K}
    (hN3 : (M - 1) ^ 3 = 0) {v : Fin 3 → K} (hv : (M - 1) *ᵥ ((M - 1) *ᵥ v) ≠ 0) :
    IsUnit (krylov M v).det := by
  have h3 : (M - 1) * ((M - 1) * (M - 1)) = 0 := by rw [← pow_three, hN3]
  have hNw2 : (M - 1) *ᵥ ((M - 1) *ᵥ ((M - 1) *ᵥ v)) = 0 := by
    simp only [Matrix.mulVec_mulVec, h3, Matrix.zero_mulVec]
  have hMv : ∀ w : Fin 3 → K, M *ᵥ w = w + (M - 1) *ᵥ w := by
    intro w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  rw [isUnit_iff_ne_zero]
  intro hd
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  rw [CFSG.RankThree.PartOne.KFOUT3.krylov_mulVec, hMv (M *ᵥ v), hMv v, Matrix.mulVec_add] at hc
  obtain ⟨w1, hw1⟩ : ∃ w1, (M - 1) *ᵥ v = w1 := ⟨_, rfl⟩
  obtain ⟨w2, hw2⟩ : ∃ w2, (M - 1) *ᵥ w1 = w2 := ⟨_, rfl⟩
  rw [hw1, hw2] at hc
  rw [hw1, hw2] at hNw2 hv
  have E : (c 0 + c 1 + c 2) • v + (c 1 + 2 * c 2) • w1 + c 2 • w2 = 0 := by
    rw [← hc]
    module
  have E1 : (c 0 + c 1 + c 2) • w1 + (c 1 + 2 * c 2) • w2 = 0 := by
    have h := congrArg (fun y => (M - 1) *ᵥ y) E
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hw1, hw2, hNw2,
      smul_zero, add_zero] at h
    exact h
  have E2 : (c 0 + c 1 + c 2) • w2 = 0 := by
    have h := congrArg (fun y => (M - 1) *ᵥ y) E1
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hw2, hNw2,
      smul_zero, add_zero] at h
    exact h
  have ha : c 0 + c 1 + c 2 = 0 := (smul_eq_zero.1 E2).resolve_right hv
  have hb : c 1 + 2 * c 2 = 0 := by
    rw [ha, zero_smul, zero_add] at E1
    exact (smul_eq_zero.1 E1).resolve_right hv
  have hc2 : c 2 = 0 := by
    rw [ha, hb, zero_smul, zero_smul, zero_add, zero_add] at E
    exact (smul_eq_zero.1 E).resolve_right hv
  have hc1 : c 1 = 0 := by
    rw [hc2, mul_zero, add_zero] at hb
    exact hb
  have hc0' : c 0 = 0 := by
    rw [hc1, hc2, add_zero, add_zero] at ha
    exact ha
  apply hc0
  funext i
  fin_cases i <;> simp [hc0', hc1, hc2]

theorem isSolvable_centralizer_of_sq_eq_zero {K : Type} [Field K] [Finite K] {q k : ℕ}
    (hq : q.Prime) (hK : Nat.card K = q ^ k) {A : SpecialLinearGroup (Fin 3) K}
    (hN2 : ((A : Matrix (Fin 3) (Fin 3) K) - 1) * ((A : Matrix (Fin 3) (Fin 3) K) - 1) = 0)
    (hN0 : (A : Matrix (Fin 3) (Fin 3) K) - 1 ≠ 0) :
    Group.IsSolvable (Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin 3) K))) := by
  obtain ⟨N, hN⟩ : ∃ N, N = (A : Matrix (Fin 3) (Fin 3) K) - 1 := ⟨_, rfl⟩
  rw [← hN] at hN2 hN0
  have hJJ : LinearMap.range N.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hN2, Matrix.zero_mulVec]
  have hrk := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fin_fun] at hrk
  have hle := Submodule.finrank_mono hJJ
  have hne : Module.finrank K ↥(LinearMap.range N.mulVecLin) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
    intro h0
    apply hN0
    ext i j
    have h := congrFun (LinearMap.congr_fun h0 (Pi.single j 1)) i
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using h
  have hJ1 : Module.finrank K ↥(LinearMap.range N.mulVecLin) = 1 := by omega
  have hJ2 : Module.finrank K ↥(LinearMap.ker N.mulVecLin) = 2 := by omega
  have hsub : Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin 3) K)) ≤
      stabilizer (LinearMap.range N.mulVecLin) ⊓ stabilizer (LinearMap.ker N.mulVecLin) := by
    intro B hB
    have hBA : (B : Matrix (Fin 3) (Fin 3) K) * A = A * B :=
      congrArg (fun s : SpecialLinearGroup (Fin 3) K => (s : Matrix (Fin 3) (Fin 3) K))
        (Subgroup.mem_centralizer_singleton_iff.mp hB)
    have hBN : (B : Matrix (Fin 3) (Fin 3) K) * N = N * B := by
      rw [hN, mul_sub, sub_mul, hBA, mul_one, one_mul]
    refine ⟨mem_stabilizer_of_map_le ?_, mem_stabilizer_of_map_le ?_⟩
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨(B : Matrix (Fin 3) (Fin 3) K) *ᵥ x, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hBN]
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : N *ᵥ x = 0 := hx
      change N *ᵥ ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = 0
      rw [Matrix.mulVec_mulVec, ← hBN, ← Matrix.mulVec_mulVec, hx', Matrix.mulVec_zero]
  have := CFSG.LieType.SteinbergBR.isSolvable_stabilizer_inf_stabilizer hq hK hJJ hJ1 hJ2
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hsub)

theorem exists_isUnit_det_krylov_of_ne_three {p : ℕ} [Fact p.Prime] (hp3 : p % 3 ≠ 1)
    (hp : p ≠ 3) {A : SpecialLinearGroup (Fin 3) (ZMod p)} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    ∃ v : Fin 3 → ZMod p, IsUnit (krylov (A : Matrix (Fin 3) (Fin 3) (ZMod p)) v).det := by
  have hq : Nat.card (ZMod p) % 3 = 2 := by
    rw [Nat.card_zmod]
    exact mod_three_eq_two hp3 hp
  have hcube := cube_roots_trivial hp3
  have h3 : (3 : ZMod p) ≠ 0 :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.three_ne_zero_of_card_mod (p := p) (f := 1) le_rfl
      (by rw [Nat.card_zmod, pow_one]) hq
  have hω := CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.no_root_of_cube_trivial h3 hcube
  have hM3 : (A : Matrix (Fin 3) (Fin 3) (ZMod p)) * A * A = 1 := by
    have h := congrArg (fun y : SpecialLinearGroup (Fin 3) (ZMod p) =>
      (y : Matrix (Fin 3) (Fin 3) (ZMod p))) hA3
    simpa [pow_succ] using h
  have hM1 : (A : Matrix (Fin 3) (Fin 3) (ZMod p)) ≠ 1 := fun h => hA1 (Subtype.ext h)
  have hns : ∀ c : ZMod p,
      (A : Matrix (Fin 3) (Fin 3) (ZMod p)) ≠ c • (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    intro c hc
    have h1 := hM3
    rw [hc] at h1
    have hc3 : c ^ 3 = 1 := by
      have h2 := congrFun (congrFun h1 0) 0
      have h2' : c * (c * c) = 1 := by
        simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_apply] using h2
      linear_combination h2'
    apply hM1
    rw [hc, hcube c hc3, one_smul]
  obtain ⟨P, hP, hMP⟩ := CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.exists_cyclic3 h3 hω _ hM3
    hM1 A.2 hns
  exact ⟨fun i => P i 0, isUnit_det_krylov_of_cyclic hP hMP⟩

theorem isSolvable_centralizer {p : ℕ} [Fact p.Prime] (hp3 : p % 3 ≠ 1)
    {A : SpecialLinearGroup (Fin 3) (ZMod p)} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    Group.IsSolvable (Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin 3) (ZMod p)))) := by
  by_cases hp : p = 3
  · subst hp
    have hM3 : (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) ^ 3 = 1 :=
      congrArg (fun y : SpecialLinearGroup (Fin 3) (ZMod 3) =>
        (y : Matrix (Fin 3) (Fin 3) (ZMod 3))) hA3
    have hN3 : ((A : Matrix (Fin 3) (Fin 3) (ZMod 3)) - 1) ^ 3 = 0 := by
      rw [sub_pow_char_of_commute 3 (Commute.one_right _), hM3, one_pow, sub_self]
    by_cases hN2 : ((A : Matrix (Fin 3) (Fin 3) (ZMod 3)) - 1) *
        ((A : Matrix (Fin 3) (Fin 3) (ZMod 3)) - 1) = 0
    · refine isSolvable_centralizer_of_sq_eq_zero Nat.prime_three (k := 1)
        (by rw [Nat.card_zmod, pow_one]) hN2 ?_
      intro h0
      exact hA1 (Subtype.ext (sub_eq_zero.mp h0))
    · obtain ⟨v, hv⟩ : ∃ v : Fin 3 → ZMod 3, ((A : Matrix (Fin 3) (Fin 3) (ZMod 3)) - 1) *ᵥ
          (((A : Matrix (Fin 3) (Fin 3) (ZMod 3)) - 1) *ᵥ v) ≠ 0 := by
        by_contra h
        push Not at h
        apply hN2
        ext i j
        have h' := congrFun (h (Pi.single j 1)) i
        rw [Matrix.mulVec_mulVec] at h'
        simpa [Matrix.mulVec_single_one] using h'
      exact isSolvable_centralizer_of_isUnit_det_krylov (isUnit_det_krylov_of_nilpotent hN3 hv)
  · obtain ⟨v, hv⟩ := exists_isUnit_det_krylov_of_ne_three hp3 hp hA3 hA1
    exact isSolvable_centralizer_of_isUnit_det_krylov hv

end Hering129KD1

section Main

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag


theorem gap129HessL3Deg_holds : Gap129HessL3Deg := by
  intro P _ _ Yh Bh xh bh ch hD p _ hp3 ⟨e⟩
  haveI : Yh.Normal := hD.normal
  let e' : ↥Yh ≃* projectiveSL 3 (ZMod p) :=
    e.trans ((Hering129KH2b.projSLFieldEquiv
      (Hering129KH2b.galoisFieldZeroAlgEquiv p).toRingEquiv).trans
        (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (ZMod p)))
  let φ : SpecialLinearGroup (Fin 3) (ZMod p) ≃* projectiveSL 3 (ZMod p) :=
    MulEquiv.ofBijective (proj 3 (ZMod p))
      ⟨Hering129KD1.proj_injective hp3, proj_surjective 3 (ZMod p)⟩
  have hxB : xh ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers xh))
  have hbB : bh ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers bh))
  have hcB : ch ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ch)
  let α : MulAut ↥Yh := MulAut.conjNormal bh
  have hα3 : α ^ 3 = 1 := by
    change (MulAut.conjNormal bh) ^ 3 = 1
    rw [← map_pow, hD.elem.2 bh hbB, map_one]
  obtain ⟨g, hg⟩ := Hering129KD1.exists_conj_of_pow_three hp3 (β := MulAut.congr e' α)
    (by rw [← map_pow, hα3, map_one])
  have hconj : ∀ y : ↥Yh, e' (α y) = g * e' y * g⁻¹ := by
    intro y
    rw [← MulAut.conj_apply, ← hg, MulAut.congr_apply]
    simp
  have hg1 : g ≠ 1 := by
    intro hg1
    have hcen : bh ∈ Subgroup.centralizer (Yh : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := hconj ⟨y, hy⟩
      rw [hg1, one_mul, inv_one, mul_one] at h
      have h2 : bh * y * bh⁻¹ = y := congrArg Subtype.val (e'.injective h)
      calc y * bh = bh * y * bh⁻¹ * bh := by rw [h2]
        _ = bh * y := by group
    have hmem : bh ∈ Bh ⊓ Subgroup.centralizer (Yh : Set P) := ⟨hbB, hcen⟩
    rw [hD.cent] at hmem
    have hB : Bh = Subgroup.zpowers xh ⊔ Subgroup.zpowers ch := by
      rw [hD.gen, sup_eq_left.mpr (Subgroup.zpowers_le.mpr hmem)]
    have hle := Hering129KH3b.h3b_card_sup_le_nine hD.xcent (hD.elem.2 xh hxB)
      (hD.elem.2 ch hcB)
    rw [← hB, hD.card] at hle
    omega
  have hg3 : g ^ 3 = 1 := by
    have hc : MulAut.conj (g ^ 3) = 1 := by
      rw [map_pow, ← hg, ← map_pow, hα3, map_one]
    obtain ⟨z, hz⟩ := proj_surjective 3 (ZMod p) (g ^ 3)
    have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod p)) := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply Hering129KD1.proj_injective hp3
      have h1 := congrArg (fun γ : MulAut (projectiveSL 3 (ZMod p)) => γ (proj 3 (ZMod p) B)) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      rw [map_mul, map_mul, hz]
      calc proj 3 (ZMod p) B * g ^ 3 = g ^ 3 * proj 3 (ZMod p) B * (g ^ 3)⁻¹ * g ^ 3 := by
            rw [h1]
        _ = g ^ 3 * proj 3 (ZMod p) B := by group
    rw [← scalars_eq_center] at hzc
    rw [← hz, proj_eq_one_iff]
    exact hzc
  obtain ⟨A, hA⟩ := proj_surjective 3 (ZMod p) g
  have hA3 : A ^ 3 = 1 := by
    apply Hering129KD1.proj_injective hp3
    rw [map_pow, hA, hg3, map_one]
  have hA1 : A ≠ 1 := by
    rintro rfl
    exact hg1 (by rw [← hA, map_one])
  have hsolv := Hering129KD1.isSolvable_centralizer hp3 hA3 hA1
  obtain ⟨Xh, hXY, hXC, -, -, -, p', n, hp', h4, ψ, hψ⟩ := hD.comp
  have hXns : ¬ Group.IsSolvable ↥Xh := by
    intro hs
    have hn1 : n ≠ 0 := by
      rintro rfl
      simp at h4
    have h4' : 4 ≤ Nat.card (GaloisField p' n) := by
      rw [GaloisField.card p' n hn1]
      exact h4
    exact Hering129KH3b.h3b_not_isSolvable_projSL_two h4' (Group.isSolvable_of_surjective hψ)
  apply hXns
  let χ₀ : ↥Xh →* SpecialLinearGroup (Fin 3) (ZMod p) :=
    φ.symm.toMonoidHom.comp (e'.toMonoidHom.comp (Subgroup.inclusion hXY))
  have hχ₀ : Function.Injective χ₀ :=
    φ.symm.injective.comp (e'.injective.comp (Subgroup.inclusion_injective hXY))
  have hmem : ∀ x : ↥Xh,
      χ₀ x ∈ Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin 3) (ZMod p))) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbx : bh * (x : P) * bh⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hXC x.2), mul_inv_cancel_right]
    have hαx : α (Subgroup.inclusion hXY x) = Subgroup.inclusion hXY x := Subtype.ext hbx
    have h := hconj (Subgroup.inclusion hXY x)
    rw [hαx] at h
    apply φ.injective
    have hφA : φ A = g := hA
    have hφs : φ (χ₀ x) = e' (Subgroup.inclusion hXY x) := by simp [χ₀]
    rw [map_mul, map_mul, hφA, hφs]
    calc e' (Subgroup.inclusion hXY x) * g =
        g * e' (Subgroup.inclusion hXY x) * g⁻¹ * g := by rw [← h]
      _ = g * e' (Subgroup.inclusion hXY x) := by group
  let χ : ↥Xh →* Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin 3) (ZMod p))) :=
    χ₀.codRestrict _ hmem
  have hχ : Function.Injective χ := fun a b hab => hχ₀ (congrArg Subtype.val hab)
  exact Group.isSolvable_of_isSolvable_injective hχ

end Main

end CFSG.RankThree.PartTwo.Sec12

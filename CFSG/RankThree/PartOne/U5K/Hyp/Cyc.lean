module

public import CFSG.RankThree.PartOne.U5K.Hyp.Lam

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}

section Blocks

theorem blocks_of_central {x : Gam hK} (hc : ∀ v ∈ Vsub hK, act hK x v = v) :
    ∃ a : K, blkEE x = a • (1 : Matrix (Fin 2) (Fin 2) K) ∧
      blkFF x = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have key : ∀ Y : Matrix (Fin 2) (Fin 2) K, IsHerm hK Y →
      blkEE x * Y.map x.1.right = Y * blkFF x := by
    intro Y hY
    obtain ⟨v, hv, hvm⟩ := exists_mem_Vsub hY
    refine ef_block hvm ?_
    rw [hc v hv, hvm]
  set σ := x.1.right with hσ
  have e0 := key (hermM hK 1 0 0) (hermM_isHerm (by simp) (by simp))
  have e1 := key (hermM hK 0 1 0) (hermM_isHerm (by simp) (by simp))
  have e2 : ∀ t : K, blkEE x * (hermM hK 0 0 t).map σ = hermM hK 0 0 t * blkFF x :=
    fun t => key _ (hermM_isHerm (by simp) (by simp))
  rw [hermM_map] at e0 e1
  have a10 := congrFun (congrFun e0 1) 0
  have a00 := congrFun (congrFun e0 0) 0
  have a01 := congrFun (congrFun e1 0) 1
  have a11 := congrFun (congrFun e1 1) 1
  have t1 := congrFun (congrFun (e2 1) 0) 1
  have b01 := congrFun (congrFun e0 0) 1
  have b10 := congrFun (congrFun e1 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, hermM, blkEE, blkFF] at a10 a00 a01 a11 t1 b01 b10
  refine ⟨lmat x (.inl 0) (.inl 0), ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [blkEE, a10, a01, a11, t1]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [blkFF]
    all_goals first | exact a00.symm | exact b01.symm | exact b10.symm | exact t1.symm

end Blocks

section Unip

theorem blk3_unip_sq [CharP K 2] (X : Matrix (Fin 2) (Fin 1) K) (Y : Matrix (Fin 2) (Fin 2) K)
    (Q : Matrix (Fin 1) (Fin 2) K) :
    blk3 (1 : Matrix (Fin 2) (Fin 2) K) X Y (1 : Matrix (Fin 1) (Fin 1) K) Q
        (1 : Matrix (Fin 2) (Fin 2) K) *
      blk3 (1 : Matrix (Fin 2) (Fin 2) K) X Y (1 : Matrix (Fin 1) (Fin 1) K) Q
        (1 : Matrix (Fin 2) (Fin 2) K) =
      blk3 (1 : Matrix (Fin 2) (Fin 2) K) 0 (X * Q) (1 : Matrix (Fin 1) (Fin 1) K) 0
        (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  rw [blk3_mul]
  congr 1
  · simp
  · ext i k; simp [h2]
  · ext i j; simp; linear_combination h2 (Y i j)
  · simp
  · ext k j; simp [h2]
  · simp

theorem blk3_unip_sq2 [CharP K 2] (Y : Matrix (Fin 2) (Fin 2) K) :
    blk3 (1 : Matrix (Fin 2) (Fin 2) K) 0 Y (1 : Matrix (Fin 1) (Fin 1) K) 0
        (1 : Matrix (Fin 2) (Fin 2) K) *
      blk3 (1 : Matrix (Fin 2) (Fin 2) K) 0 Y (1 : Matrix (Fin 1) (Fin 1) K) 0
        (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  rw [blk3_mul, ← blk3_one]
  congr 1
  · simp
  · simp
  · ext i j; simp [h2]
  · simp
  · simp
  · simp

end Unip

section PowLam

theorem lmat_pow_of_right_one {x : Gam hK} (hx : x.1.right = 1) (n : ℕ) :
    lmat (x ^ n) = (lmat x) ^ n ∧ (x ^ n).1.right = 1 := by
  induction n with
  | zero => exact ⟨rfl, by simp⟩
  | succ n ih =>
    rw [pow_succ, pow_succ]
    refine ⟨?_, ?_⟩
    · rw [lmat_mul_of_right_one ih.2, ih.1]
    · rw [Subgroup.coe_mul, SemidirectProduct.mul_right, ih.2, hx, mul_one]

theorem eq_one_of_lmat_eq_one {x : Gam hK} (hr : x.1.right = 1) (h : lmat x = 1) : x = 1 := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · apply Units.ext
    exact h
  · exact hr

theorem lam_pow_four [CharP K 2] {x : Gam hK} (hx : x ∈ Lam hK) (hE : blkEE x = 1)
    (hF : blkFF x = 1) (hd : lmat x (.inr (.inl 0)) (.inr (.inl 0)) = 1) : x ^ 4 = 1 := by
  obtain ⟨hr, hP, -⟩ := hx
  have hA := eq_blk3_of_para hP
  have hP1 : blkP (lmat x) = 1 := by
    ext k l
    fin_cases k
    fin_cases l
    simp [blkP, hd]
  rw [show blkA (lmat x) = blkEE x from rfl, hE, hP1, show blkD (lmat x) = blkFF x from rfl,
    hF] at hA
  have hsq := blk3_unip_sq (K := K) (blkX (lmat x)) (blkY (lmat x)) (blkQ (lmat x))
  rw [← hA] at hsq
  have h4 : (lmat x) ^ 4 = 1 := by
    calc (lmat x) ^ 4 = (lmat x * lmat x) * (lmat x * lmat x) := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [hsq]; exact blk3_unip_sq2 _
  apply eq_one_of_lmat_eq_one (lmat_pow_of_right_one hr 4).2
  rw [(lmat_pow_of_right_one hr 4).1, h4]

end PowLam

section Psi

variable (hK)

@[expose] def psiL : Lam hK →* K where
  toFun x := lmat (x : Gam hK) (.inr (.inl 0)) (.inr (.inl 0))
  map_one' := by
    show lmat (1 : Gam hK) _ _ = 1
    rw [show lmat (1 : Gam hK) = 1 from rfl]
    exact Matrix.one_apply_eq _
  map_mul' x y := by
    have hm := lmat_mul_of_right_one (y := (y : Gam hK)) x.2.1
    obtain ⟨-, -, hP, -⟩ := mul_para x.2.2.1 y.2.2.1
    have h0 := congrFun (congrFun hP 0) 0
    show lmat ((x : Gam hK) * (y : Gam hK)) _ _ = _
    rw [hm]
    simpa [blkP, Matrix.mul_apply] using h0

end Psi

section Cyclic

variable (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
include hZ

theorem lam_lift_of_central {ρ : MulAut (hypPSU hK 2 1)}
    (hρ : ∀ w ∈ Vh hK, ρ * w = w * ρ) :
    ∃ x ∈ Lam hK, Phi hK x = ρ ∧ blkEE x = 1 ∧ blkFF x = 1 := by
  have hN : ρ ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
    have := finite_mulAut_hyp hK
    refine mem_normalizer_of_conj_le fun v hv => ?_
    rw [hρ v hv]
    simpa using hv
  obtain ⟨x₀, hx₀⟩ := Phi_surjective hK ρ
  have hN' : Phi hK x₀ ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
    rw [hx₀]; exact hN
  have hcen : ∀ v ∈ Vsub hK, act hK x₀ v = v := by
    intro v hv
    apply eq_of_innM_eq_of_sq hZ _ (by rw [← act_mul, Vsub_sq hv, act_one]) (Vsub_sq hv)
    rw [← Phi_mul_innM_mul_inv, hx₀, hρ _ ⟨v, hv, rfl⟩]
    group
  have hσ := sigma_eq_one_of_central hZ hN' hcen
  have hD : ρ ∈ Dlin hK := (mem_Dlin_iff hx₀).2 hσ
  obtain ⟨x, hxL, hx⟩ := exists_lam_lift hZ hD hN
  have hx' : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
    rw [hx]; exact hN
  have hcen' : ∀ v ∈ Vsub hK, act hK x v = v := by
    intro v hv
    apply eq_of_innM_eq_of_sq hZ _ (by rw [← act_mul, Vsub_sq hv, act_one]) (Vsub_sq hv)
    rw [← Phi_mul_innM_mul_inv, hx, hρ _ ⟨v, hv, rfl⟩]
    group
  obtain ⟨a, haE, haF⟩ := blocks_of_central hcen'
  have hdet := hxL.2.2
  have ha1 : a = 1 := by
    rw [haE] at hdet
    have := hK.charP
    have h1 : a = 1 ∨ a = -1 := by
      simpa [Matrix.det_fin_two, Matrix.smul_apply] using hdet
    rcases h1 with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  refine ⟨x, hxL, hx, ?_, ?_⟩
  · rw [haE, ha1, one_smul]
  · rw [haF, ha1, one_smul]

theorem cyclic_of_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (MulAut (hypPSU hK 2 1))} (hP : IsPGroup p P)
    (hPC : ∀ ρ ∈ P, ∀ w ∈ Vh hK, ρ * w = w * ρ) : IsCyclic P := by
  classical
  have := finite_Gam hK
  have hchar := hK.charP
  have hP' : ∀ ρ ∈ P, ∃ x ∈ Lam hK, Phi hK x = ρ ∧ blkEE x = 1 ∧ blkFF x = 1 :=
    fun ρ hρ => lam_lift_of_central hZ (hPC ρ hρ)
  let g : Lam hK →* MulAut (hypPSU hK 2 1) := (Phi hK).comp (Lam hK).subtype
  set LP : Subgroup (Lam hK) := P.comap g with hLP
  let π : LP →* P := (g.comp LP.subtype).codRestrict P (fun x => x.2)
  have hπ : Function.Surjective π := by
    rintro ⟨ρ, hρ⟩
    obtain ⟨x, hxL, hx, -, -⟩ := hP' ρ hρ
    exact ⟨⟨⟨x, hxL⟩, by rw [hLP, Subgroup.mem_comap]; change Phi hK x ∈ P; rw [hx]; exact hρ⟩,
      Subtype.ext hx⟩
  have hinj : Function.Injective ((psiL hK).comp LP.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx1
    obtain ⟨ρ0, hρ0P⟩ : ∃ ρ0 : MulAut (hypPSU hK 2 1), ρ0 = Phi hK (x : Lam hK) :=
      ⟨_, rfl⟩
    have hρP : Phi hK ((x : Lam hK) : Gam hK) ∈ P := x.2
    obtain ⟨y, hyL, hy, hyE, hyF⟩ := hP' _ hρP
    have hyx : y = ((x : Lam hK) : Gam hK) := Phi_injOn_Lam hyL (x : Lam hK).2 hy
    subst hyx
    have hψ : lmat ((x : Lam hK) : Gam hK) (.inr (.inl 0)) (.inr (.inl 0)) = 1 := hx1
    have h4 := lam_pow_four hyL hyE hyF hψ
    obtain ⟨k, hk⟩ := hP ⟨_, hρP⟩
    have hk' : (Phi hK ((x : Lam hK) : Gam hK)) ^ (p ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    have hpk : ((x : Lam hK) : Gam hK) ^ (p ^ k) = 1 := by
      apply Phi_injOn_Lam (pow_mem (x : Lam hK).2 _) (one_mem _)
      rw [map_pow, map_one]
      exact hk'
    have hord1 : orderOf ((x : Lam hK) : Gam hK) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have hord2 : orderOf ((x : Lam hK) : Gam hK) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hpk
    have hcop : Nat.Coprime 4 (p ^ k) := by
      apply Nat.Coprime.pow_right
      have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
      simpa using Nat.Coprime.pow_left 2 h2p
    have h1 : orderOf ((x : Lam hK) : Gam hK) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
    have hx1' : ((x : Lam hK) : Gam hK) = 1 := orderOf_eq_one_iff.1 h1
    exact Subtype.ext (Subtype.ext hx1')
  have hcyc : IsCyclic LP := isCyclic_of_injective_ringHom _ hinj
  exact isCyclic_of_surjective π hπ

end Cyclic

end CFSG.RankThree.PartOne.U5K.Hyp

module

public import CFSG.RankThree.PartOne.SEITZ7.D4Tor
public import CFSG.RankThree.PartOne.SEITZ8.D4Span

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7

variable {K : Type} [Field K]

omit [Field K] in
theorem height_labelWt_bounds_d4 (a : Label d4) :
    -5 ≤ height (labelWt d4 a) ∧ height (labelWt d4 a) ≤ 5 := by
  rcases a with l | ⟨γ, hγ⟩
  · simp [labelWt, height]
  · obtain ⟨p, hp, rfl⟩ := exists_pos_of_isRoot hγ
    have : ∀ p < 24, -5 ≤ height (τ := d4) (d4Root p) ∧ height (τ := d4) (d4Root p) ≤ 5 := by
      decide +kernel
    exact this p hp

theorem height_add_d4 (v w : Fin d4.rank → ℤ) : height (v + w) = height v + height w := by
  simp [height, Finset.sum_add_distrib]

theorem height_nsmul_d4 (k : ℕ) (v : Fin d4.rank → ℤ) : height (k • v) = k * height v := by
  simp [height, ← Finset.mul_sum]

section Omega


theorem posRoot_fix_d4 {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hpos : 0 < ht γ) (c : K) :
    xPar (rootOperatorFamily d4) γ c • (rv 22 : RootModule d4 K) = rv 22 ∧
      ∀ x : RootModule d4 K,
        coordAt (d4Root 23) (xPar (rootOperatorFamily d4) γ c • x) = coordAt (d4Root 23) x := by
  set F := rootOperatorFamily d4
  have h22 : IsRoot d4 (d4Root 22) := isRoot_d4 (by norm_num)
  have h23 : IsRoot d4 (d4Root 23) := isRoot_d4 (by norm_num)
  have e : ∀ x : RootModule d4 K, xPar F γ c • x = F.elt K ⟨γ, hγ⟩ c x := fun x => by
    rw [xPar_of_isRoot hγ]
    rfl
  have ht22 : height (τ := d4) (d4Root 22) = 5 := by decide +kernel
  have ht23 : height (τ := d4) (d4Root 23) = -5 := by decide +kernel
  constructor
  · rw [e, rv, rootVec_eq_single h22]
    refine Finsupp.ext fun a => ?_
    by_contra hne
    obtain ⟨k, hk, hwt⟩ := F.elt_weight_shift ⟨γ, hγ⟩ c a _ (sub_ne_zero.2 hne)
    have h1 := congrArg height hwt
    rw [height_add_d4, height_nsmul_d4] at h1
    change height (labelWt d4 a) = height (τ := d4) (d4Root 22) + k * height γ at h1
    rw [ht22] at h1
    have : (1 : ℤ) ≤ k := by exact_mod_cast hk
    have hpos' : 0 < height γ := hpos
    nlinarith [this, hpos', (height_labelWt_bounds_d4 a).2]
  · intro x
    rw [e, coordAt_eq h23, coordAt_eq h23]
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply]
    | single b r =>
      rw [← Finsupp.smul_single_one b r, map_smul, Finsupp.smul_apply, Finsupp.smul_apply]
      congr 1
      by_contra hne
      obtain ⟨k, hk, hwt⟩ := F.elt_weight_shift ⟨γ, hγ⟩ c _ b (sub_ne_zero.2 hne)
      have h1 := congrArg height hwt
      rw [height_add_d4, height_nsmul_d4] at h1
      change height (τ := d4) (d4Root 23) = height (labelWt d4 b) + k * height γ at h1
      rw [ht23] at h1
      have : (1 : ℤ) ≤ k := by exact_mod_cast hk
      have hpos' : 0 < height γ := hpos
      nlinarith [this, hpos', (height_labelWt_bounds_d4 b).1]

@[expose] noncomputable def omegaH (K : Type) [Field K] : Subgroup (adjointGroup d4 K) where
  carrier := {b | ∃ χ : Kˣ, b • (rv 22 : RootModule d4 K) = (χ : K) • rv 22 ∧
    (∀ x : RootModule d4 K, coordAt (d4Root 23) (b • x) =
      ((χ⁻¹ : Kˣ) : K) * coordAt (d4Root 23) x) ∧
    (∀ c : K, b * xe 22 c * b⁻¹ = xe 22 ((χ : K) * c))}
  mul_mem' := by
    rintro a b ⟨χ₁, a1, b1, c1⟩ ⟨χ₂, a2, b2, c2⟩
    refine ⟨χ₁ * χ₂, ?_, ?_, ?_⟩
    · rw [mul_smul, a2, smul_smul_comm', a1, smul_smul, Units.val_mul, mul_comm]
    · intro x
      rw [mul_smul, b1, b2, mul_inv, Units.val_mul, mul_assoc]
    · intro c
      rw [show a * b * xe 22 c * (a * b)⁻¹ = a * (b * xe 22 c * b⁻¹) * a⁻¹ by group, c2, c1,
        Units.val_mul, mul_assoc]
  one_mem' := by
    refine ⟨1, ?_, ?_, ?_⟩
    · simp
    · intro x; simp
    · intro c; simp
  inv_mem' := by
    rintro a ⟨χ, a1, b1, c1⟩
    refine ⟨χ⁻¹, ?_, ?_, ?_⟩
    · have h : (rv 22 : RootModule d4 K) = (χ : K) • (a⁻¹ • (rv 22 : RootModule d4 K)) := by
        have := congrArg (fun y => a⁻¹ • y) a1
        simpa [smul_smul_comm'] using this
      calc a⁻¹ • (rv 22 : RootModule d4 K)
          = ((χ⁻¹ : Kˣ) : K) • ((χ : K) • (a⁻¹ • (rv 22 : RootModule d4 K))) := by
            rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
        _ = ((χ⁻¹ : Kˣ) : K) • (rv 22 : RootModule d4 K) := by rw [← h]
    · intro x
      have h := b1 (a⁻¹ • x)
      rw [smul_inv_smul] at h
      rw [inv_inv]
      calc coordAt (d4Root 23) (a⁻¹ • x)
          = (χ : K) * (((χ⁻¹ : Kˣ) : K) * coordAt (d4Root 23) (a⁻¹ • x)) := by
            rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
        _ = (χ : K) * coordAt (d4Root 23) x := by rw [← h]
    · intro c
      have h := c1 (((χ⁻¹ : Kˣ) : K) * c)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
      rw [inv_inv]
      calc a⁻¹ * xe 22 c * a = a⁻¹ * (a * xe 22 (((χ⁻¹ : Kˣ) : K) * c) * a⁻¹) * a := by rw [h]
        _ = xe 22 (((χ⁻¹ : Kˣ) : K) * c) := by group

theorem repCheck_22 : ∀ p ∈ dpos, p ≠ 22 → RootOps.repCheck d4 p 22 [] = true := by
  decide +kernel

theorem pos_dpos : ∀ p < 24, 0 < ht (d4Root p) → p ∈ dpos := by decide +kernel

theorem torus_mem_omegaH (i : Fin d4.rank) (s : Kˣ) : torusElement d4 K i s ∈ omegaH K := by
  have h22 : IsRoot d4 (d4Root 22) := isRoot_d4 (by norm_num)
  have h23 : IsRoot d4 (d4Root 23) := isRoot_d4 (by norm_num)
  set e : ℤ := ∑ j, d4.cartan i j * (d4Root 22) j with he
  have hneg : (∑ j, d4.cartan i j * (d4Root 23) j) = -e := by
    rw [he, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [d4Root_23]
    change _ * (-(d4Root 22 j)) = -(_ * d4Root 22 j)
    ring
  refine ⟨s ^ e, ?_, ?_, ?_⟩
  · exact torusElt_rootVec i s h22
  · intro x
    rw [coordAt_eq h23, coordAt_eq h23]
    change (torusElt d4 K i s : Module.End K (RootModule d4 K)) x _ = _
    rw [torusElt_apply]
    change ((s ^ (∑ j, d4.cartan i j * (d4Root 23) j) : Kˣ) : K) * _ = _
    rw [hneg, zpow_neg]
  · intro c
    exact torusElement_conj_xd i (by norm_num) s c

theorem posRoot_mem_omegaH {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hpos : 0 < ht γ) (c : K)
    [CharP K 2] : xPar (rootOperatorFamily d4) γ c ∈ omegaH K := by
  obtain ⟨h1, h2⟩ := posRoot_fix_d4 (K := K) hγ hpos c
  obtain ⟨p, hp, rfl⟩ := exists_pos_of_isRoot hγ
  have hpd : p ∈ dpos := pos_dpos p hp hpos
  refine ⟨1, ?_, ?_, ?_⟩
  · simpa using h1
  · intro x
    simpa using h2 x
  · intro c'
    by_cases h22 : p = 22
    · subst h22
      show xd 22 c * xd 22 c' * (xd 22 c)⁻¹ = xd 22 (((1 : Kˣ) : K) * c')
      rw [Units.val_one, one_mul]
      calc xd 22 c * xd 22 c' * (xd 22 c)⁻¹ = xd 22 (c + c') * (xd 22 c)⁻¹ := by rw [← xd_add]
        _ = xd 22 (c' + c) * (xd 22 c)⁻¹ := by rw [add_comm]
        _ = xd 22 c' * xd 22 c * (xd 22 c)⁻¹ := by rw [xd_add]
        _ = xd 22 c' := by group
    · have hcomm := commute_gen (K := K) (repCheck_22 p hpd h22) c c'
      show xd p c * xd 22 c' * (xd p c)⁻¹ = xd 22 (((1 : Kˣ) : K) * c')
      rw [Units.val_one, one_mul, hcomm.eq]
      group

theorem borel_le_omegaH [CharP K 2] :
    borel (adjDatum (rootOperatorFamily d4) K) (torus (τ := d4) K) ≤ omegaH K := by
  refine sup_le ?_ ?_
  · refine iSup_le fun i => ?_
    rintro _ ⟨t, rfl⟩
    exact torus_mem_omegaH i t
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγR, hγp⟩ := hγ
    intro x hx
    have hγ' : IsRoot d4 γ := by rwa [adjDatum_roots] at hγR
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ' x).1 hx
    exact posRoot_mem_omegaH hγ' hγp c

end Omega

end CFSG.RankThree.PartOne.SEITZ8

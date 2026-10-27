module

public import CFSG.RankThree.SubgroupLists.SymplecticTwoRotations
public import CFSG.RankThree.SubgroupLists.SymplecticBaseChange
public import CFSG.RankThree.SubgroupLists.CliffordGeometry
public import Certificates.Certificate113
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped commutatorElement

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem cliffB_sub_left (Z Z' Y : Matrix V₄ V₄ K) :
    cliffB (Z - Z') Y = cliffB Z Y - cliffB Z' Y := by
  rw [sub_eq_add_neg, cliffB_add_left, show -Z' = (-1 : K) • Z' by simp, cliffB_smul_left]
  ring

theorem cliffB_eq_one_of_mul_self (h2 : (2 : K) ≠ 0) {Z : Matrix V₄ V₄ K} (hZ : Z * Z = 1) :
    cliffB Z Z = 1 := by
  rw [cliffB_self h2, cliffQ, hZ]
  simp

theorem cliffB_sq_eq_one_of_commute (h2 : (2 : K) ≠ 0) {d e f : Matrix V₄ V₄ K}
    (hd : d ∈ (cliffSpace : Submodule K _)) (he : e ∈ (cliffSpace : Submodule K _))
    (hf : f ∈ (cliffSpace : Submodule K _)) (hdd : d * d = 1) (hee : e * e = 1) (hff : f * f = 1)
    (hind : ∀ a b c : K, a • d + b • e + c • f = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hcomm : d * e * (d * f) = d * f * (d * e)) :
    cliffB d f * cliffB d f = 1 := by
  set β := cliffB d e with hβ
  set γ := cliffB d f with hγ
  set δ := cliffB e f with hδ
  have hde := mul_add_mul_of_mem h2 hd he
  have hdf := mul_add_mul_of_mem h2 hd hf
  have hef := mul_add_mul_of_mem h2 he hf
  have hed : e * d = (2 * β) • (1 : Matrix V₄ V₄ K) - d * e := by rw [← hde]; abel
  have hfd : f * d = (2 * γ) • (1 : Matrix V₄ V₄ K) - d * f := by rw [← hdf]; abel
  have hfe : f * e = (2 * δ) • (1 : Matrix V₄ V₄ K) - e * f := by rw [← hef]; abel
  have h1 : e * d * f = f * d * e := by
    have : d * (d * e * (d * f)) = d * (d * f * (d * e)) := by rw [hcomm]
    simpa only [← Matrix.mul_assoc, hdd, Matrix.one_mul] using this
  have hm : d * e * f = δ • d - γ • e + β • f := by
    have e1 : e * d * f = (2 * β) • f - d * e * f := by
      rw [hed, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    have e2 : f * d * e = (2 * γ) • e - (2 * δ) • d + d * e * f := by
      rw [hfd, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc d f e, hfe,
        Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc]
      abel
    rw [e1, e2] at h1
    have h3 : (2 : K) • (d * e * f) = (2 : K) • (δ • d - γ • e + β • f) := by
      have h4 : (2 * β) • f - (2 * γ) • e + (2 * δ) • d = (2 : K) • (d * e * f) := by
        rw [two_smul]
        rw [sub_eq_iff_eq_add] at h1
        rw [h1]
        abel
      rw [← h4]
      module
    exact smul_right_injective _ h2 h3
  have hmM : d * e * f ∈ (cliffSpace : Submodule K _) := by
    rw [hm]
    exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hd)
      (Submodule.smul_mem _ _ he)) (Submodule.smul_mem _ _ hf)
  have hmd := mul_add_mul_of_mem h2 hmM hd
  have hBmd : cliffB (d * e * f) d = δ := by
    rw [hm, cliffB_add_left, cliffB_sub_left, cliffB_smul_left, cliffB_smul_left,
      cliffB_smul_left, cliffB_eq_one_of_mul_self h2 hdd, cliffB_comm e d, cliffB_comm f d]
    ring
  have hded := mul_mul_eq_reflection h2 hd hdd he
  have hdm : d * (d * e * f) = e * f := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hdd, Matrix.one_mul]
  have hmd' : d * e * f * d = (2 * γ) • (d * e) - (2 * β) • (d * f) + e * f := by
    rw [Matrix.mul_assoc (d * e) f d, hfd, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      ← Matrix.mul_assoc (d * e) d f, hded, Matrix.sub_mul, Matrix.smul_mul]
    abel
  rw [hmd', hdm, hBmd] at hmd
  have hr := congrArg (· * f) hmd
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_assoc, hff, Matrix.mul_one] at hr
  rw [← Matrix.mul_assoc d e f, hm] at hr
  have hlin : (2 * (γ * δ - β)) • d + (2 * (1 - γ * γ)) • e + (2 * (γ * β - δ)) • f = 0 := by
    rw [← sub_eq_zero] at hr
    rw [← hr]
    module
  obtain ⟨-, hb, -⟩ := hind _ _ _ hlin
  have := (mul_eq_zero.mp hb).resolve_left h2
  linear_combination -this

theorem mapGL_neg_one {K' : Type} [Field K'] (φ : K →+* K') :
    mapGL φ (-1 : GL V₄ K) = -1 := by
  apply Units.ext
  rw [coe_mapGL, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one]
  ext i j
  simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply, map_neg]
  split_ifs <;> simp

theorem commute_of_rotations_orth [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    (hneg : (-1 : GL V₄ K) ∈ G) {u : Matrix V₄ V₄ K} (huM : u ∈ (cliffSpace : Submodule K _))
    (hQ : cliffB u u ≠ 0) {x y : GL V₄ K} (hxG : x ∈ G) (hyG : y ∈ G)
    (hxu : (x : Matrix V₄ V₄ K) * u = u * x) (hyu : (y : Matrix V₄ V₄ K) * u = u * y)
    {β γ : K} (hx : (x : Matrix V₄ V₄ K) * x = (2 * β) • (x : Matrix V₄ V₄ K) - 1)
    (hy : (y : Matrix V₄ V₄ K) * y = (2 * γ) • (y : Matrix V₄ V₄ K) - 1)
    (hx6 : ∀ k, 1 ≤ k → k < 6 → x ^ k ≠ 1 ∧ x ^ k ≠ -1)
    (hy3 : ∀ k, 1 ≤ k → k < 3 → y ^ k ≠ 1 ∧ y ^ k ≠ -1) : x * y = y * x := by
  obtain ⟨K', iF, iFin, iCh, φ, u', hu', s, hs, hu's⟩ := exists_isNCInv_smul_map hp2 huM hQ
  set G' := G.map (mapGL φ)
  have hGS' : G' ≤ StatedSp 2 K' := by
    rintro _ ⟨z, hz, rfl⟩
    exact map_mem_statedSp φ (hGS hz)
  have hU0' : ∀ z ∈ G', IsSqZero z → z = 1 := by
    rintro _ ⟨z, hz, rfl⟩ hsq
    rw [hU0 z hz ((isSqZero_map_iff φ).mp hsq), map_one]
  have hneg' : (-1 : GL V₄ K') ∈ G' := ⟨-1, hneg, mapGL_neg_one φ⟩
  have hcomm : ∀ z : GL V₄ K, (z : Matrix V₄ V₄ K) * u = u * z → mapGL φ z * u' = u' *
      mapGL φ z := by
    intro z hz
    apply Units.ext
    simp only [Units.val_mul, coe_mapGL, hu's, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul,
      hz]
  have hrot : ∀ (z : GL V₄ K) (δ : K),
      (z : Matrix V₄ V₄ K) * z = (2 * δ) • (z : Matrix V₄ V₄ K) - 1 →
      ((mapGL φ z : GL V₄ K') : Matrix V₄ V₄ K') * (mapGL φ z : GL V₄ K') =
        (2 * φ δ) • ((mapGL φ z : GL V₄ K') : Matrix V₄ V₄ K') - 1 := by
    intro z δ hz
    simp only [coe_mapGL, ← Matrix.map_mul, hz]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, map_sub, map_mul, map_ofNat]
    split_ifs <;> simp
  have hpow : ∀ (z : GL V₄ K) (n : ℕ), (z ^ n ≠ 1 ∧ z ^ n ≠ -1) →
      ((mapGL φ z) ^ n ≠ 1 ∧ (mapGL φ z) ^ n ≠ -1) := by
    intro z n ⟨h1, h2'⟩
    rw [← map_pow]
    constructor
    · intro h; apply h1; apply mapGL_injective φ; rw [h, map_one]
    · intro h; apply h2'; apply mapGL_injective φ; rw [h, mapGL_neg_one]
  have hres := commute_of_rotations hp2 hU0' hneg' hGS' hu' ⟨x, hxG, rfl⟩ ⟨y, hyG, rfl⟩
    (hcomm x hxu) (hcomm y hyu) (hrot x β hx) (hrot y γ hy)
    (fun n h1 h2' => hpow x n (hx6 n h1 h2')) (fun n h1 h2' => hpow y n (hy3 n h1 h2'))
  apply mapGL_injective φ
  rw [map_mul, map_mul, hres]

theorem lin_indep_of_not_mem_span (h2 : (2 : K) ≠ 0) {d e f : Matrix V₄ V₄ K}
    (hdd : cliffB d d = 1) (hee : cliffB e e = 1) (hβ : cliffB d e * cliffB d e ≠ 1)
    (hfP : ∀ a b : K, f ≠ a • d + b • e) :
    ∀ a b c : K, a • d + b • e + c • f = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  intro a b c habc
  have hc : c = 0 := by
    by_contra hc
    apply hfP (-(c⁻¹ * a)) (-(c⁻¹ * b))
    have hcf : c • f = -(a • d + b • e) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact habc
    calc f = c⁻¹ • (c • f) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = -(c⁻¹ * a) • d + -(c⁻¹ * b) • e := by rw [hcf]; module
  rw [hc, zero_smul, add_zero] at habc
  have h1 := congrArg (fun Z => cliffB Z d) habc
  have h2' := congrArg (fun Z => cliffB Z e) habc
  simp only [cliffB_add_left, cliffB_smul_left, hdd, hee, cliffB_zero_left] at h1 h2'
  rw [cliffB_comm e d] at h1
  have hne : (1 - cliffB d e * cliffB d e) ≠ 0 := fun h => hβ (by linear_combination -h)
  have ha : a * (1 - cliffB d e * cliffB d e) = 0 := by linear_combination h1 - cliffB d e * h2'
  have hb : b * (1 - cliffB d e * cliffB d e) = 0 := by linear_combination h2' - cliffB d e * h1
  exact ⟨(mul_eq_zero.mp ha).resolve_right hne, (mul_eq_zero.mp hb).resolve_right hne, hc⟩

theorem exists_pow_eq_of_three [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    (hneg : (-1 : GL V₄ K) ∈ G) {d e f : GL V₄ K} (hdG : d ∈ G) (heG : e ∈ G) (hfG : f ∈ G)
    (hd : IsNCInv d) (he : IsNCInv e) (hf : IsNCInv f)
    (hfP : ∀ a b : K, (f : Matrix V₄ V₄ K) ≠ a • (d : Matrix V₄ V₄ K) + b • (e : Matrix V₄ V₄ K))
    (hγ : cliffB (d : Matrix V₄ V₄ K) (f : Matrix V₄ V₄ K) ≠ 0) :
    ∃ k, 1 ≤ k ∧ k < 6 ∧ ((d * e) ^ k = 1 ∨ (d * e) ^ k = -1) := by
  have hp2 : p ≠ 2 := by omega
  have h2 := two_ne_zero_of_charP (K := K) hp2
  by_contra hcon
  push Not at hcon
  have hx6 : ∀ k, 1 ≤ k → k < 6 → (d * e) ^ k ≠ 1 ∧ (d * e) ^ k ≠ -1 := hcon
  have hdM := (mem_cliffSpace_of_involution h2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2).1
  have heM := (mem_cliffSpace_of_involution h2 he.1 he.2.1 he.2.2.1 he.2.2.2).1
  have hfM := (mem_cliffSpace_of_involution h2 hf.1 hf.2.1 hf.2.2.1 hf.2.2.2).1
  have hdd : (d : Matrix V₄ V₄ K) * d = 1 := by rw [← Units.val_mul, hd.2.1, Units.val_one]
  have hee : (e : Matrix V₄ V₄ K) * e = 1 := by rw [← Units.val_mul, he.2.1, Units.val_one]
  have hff : (f : Matrix V₄ V₄ K) * f = 1 := by rw [← Units.val_mul, hf.2.1, Units.val_one]
  set β := cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K)
  set γ := cliffB (d : Matrix V₄ V₄ K) (f : Matrix V₄ V₄ K)
  have hβ : β * β ≠ 1 := by
    intro h
    have h' : β = 1 ∨ β = -1 := by
      have : (β - 1) * (β + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases eq_or_eq_neg_of_cliffB_eq_one h2 hU0 hneg hdG heG hd he h' with h | h
    · apply (hx6 1 le_rfl (by norm_num)).1
      rw [pow_one, h, hd.2.1]
    · apply (hx6 1 le_rfl (by norm_num)).2
      rw [pow_one, h, mul_neg, hd.2.1]
  have hγ1 : γ * γ ≠ 1 := by
    intro h
    have h' : γ = 1 ∨ γ = -1 := by
      have : (γ - 1) * (γ + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases eq_or_eq_neg_of_cliffB_eq_one h2 hU0 hneg hdG hfG hd hf h' with h | h
    · exact hfP 1 0 (by rw [h]; simp)
    · exact hfP (-1) 0 (by rw [h]; simp)
  have hysq := mul_sq_of_involutions h2 hdM hfM hdd hff
  have hxsq := mul_sq_of_involutions h2 hdM heM hdd hee
  have hy3 : ∀ k, 1 ≤ k → k < 3 → (d * f) ^ k ≠ 1 ∧ (d * f) ^ k ≠ -1 := by
    intro k hk1 hk3
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd.2.1
    interval_cases k
    · rw [pow_one]
      constructor
      · intro h
        apply hfP 1 0
        have : f = d := by
          calc f = d⁻¹ * (d * f) := by group
            _ = d := by rw [h, mul_one, hdinv]
        rw [this]; simp
      · intro h
        apply hfP (-1) 0
        have : f = -d := by
          calc f = d⁻¹ * (d * f) := by group
            _ = -d := by rw [h, mul_neg_one, hdinv]
        rw [this]; simp
    · constructor
      · intro h
        have hm := congrArg (fun z : GL V₄ K => (z : Matrix V₄ V₄ K)) h
        simp only [Units.val_pow_eq_pow_val, pow_two, Units.val_mul, Units.val_one] at hm
        rw [hysq] at hm
        have hsc : (2 * γ) • ((d : Matrix V₄ V₄ K) * f) = (2 : K) • (1 : Matrix V₄ V₄ K) := by
          rw [two_smul]; rw [sub_eq_iff_eq_add] at hm; rw [hm]; try abel
        have hγ0 : (2 * γ) ≠ 0 := mul_ne_zero h2 hγ
        have hdf : (d : Matrix V₄ V₄ K) * f = (2 * γ)⁻¹ • (2 : K) • (1 : Matrix V₄ V₄ K) := by
          rw [← hsc, smul_smul, inv_mul_cancel₀ hγ0, one_smul]
        apply hfP ((2 * γ)⁻¹ * 2) 0
        calc (f : Matrix V₄ V₄ K) = (d : Matrix V₄ V₄ K) * ((d : Matrix V₄ V₄ K) * f) := by
              rw [← Matrix.mul_assoc, hdd, Matrix.one_mul]
          _ = ((2 * γ)⁻¹ * 2) • (d : Matrix V₄ V₄ K) + (0 : K) • (e : Matrix V₄ V₄ K) := by
              rw [hdf, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, smul_smul, zero_smul,
                add_zero]
      · intro h
        have hm := congrArg (fun z : GL V₄ K => (z : Matrix V₄ V₄ K)) h
        simp only [Units.val_pow_eq_pow_val, pow_two, Units.val_mul, Units.val_neg,
          Units.val_one] at hm
        rw [hysq] at hm
        have hz : (2 * γ) • ((d : Matrix V₄ V₄ K) * f) = 0 := by
          rw [sub_eq_iff_eq_add] at hm; rw [hm]; abel
        rcases smul_eq_zero.mp hz with h0 | h0
        · exact hγ ((mul_eq_zero.mp h0).resolve_left h2)
        · have : ((d * f : GL V₄ K) : Matrix V₄ V₄ K) = 0 := by rw [Units.val_mul]; exact h0
          exact (d * f).ne_zero this
  obtain ⟨u, huM, hud, hue, huf, hQu⟩ := exists_orth_cliffQ_ne_zero h2 hdM heM hfM
    (cliffB_eq_one_of_mul_self h2 hdd) (cliffB_eq_one_of_mul_self h2 hee) hβ hfP
  have hanti : ∀ z : Matrix V₄ V₄ K, z ∈ (cliffSpace : Submodule K _) → cliffB u z = 0 →
      z * u = -(u * z) := by
    intro z hz h0
    have := (mul_eq_neg_mul_iff h2 hz huM).mpr (by rw [cliffB_comm]; exact h0)
    exact this
  have hxu : ((d * e : GL V₄ K) : Matrix V₄ V₄ K) * u = u *
      ((d * e : GL V₄ K) : Matrix V₄ V₄ K) := by
    rw [Units.val_mul, Matrix.mul_assoc, hanti _ heM hue, Matrix.mul_neg, ← Matrix.mul_assoc,
      hanti _ hdM hud, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have hyu : ((d * f : GL V₄ K) : Matrix V₄ V₄ K) * u = u *
      ((d * f : GL V₄ K) : Matrix V₄ V₄ K) := by
    rw [Units.val_mul, Matrix.mul_assoc, hanti _ hfM huf, Matrix.mul_neg, ← Matrix.mul_assoc,
      hanti _ hdM hud, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have hcomm := commute_of_rotations_orth hp2 hGS hU0 hneg huM hQu (G.mul_mem hdG heG)
    (G.mul_mem hdG hfG) hxu hyu (by rw [Units.val_mul]; exact hxsq)
    (by rw [Units.val_mul]; exact hysq) hx6 hy3
  have hcm := congrArg (fun z : GL V₄ K => (z : Matrix V₄ V₄ K)) hcomm
  simp only [Units.val_mul] at hcm
  exact hγ1 (cliffB_sq_eq_one_of_commute h2 hdM heM hfM hdd hee hff
    (lin_indep_of_not_mem_span h2 (cliffB_eq_one_of_mul_self h2 hdd)
      (cliffB_eq_one_of_mul_self h2 hee) hβ hfP) hcm)

section Quasisimple

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {G : Subgroup (GL V₄ K)}

theorem closure_ncImage_eq_top (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K)) :
    Subgroup.closure (ncImage G t) = ⊤ := by
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  have hτ1 : (QuotientGroup.mk t : G ⧸ Subgroup.center G) ≠ 1 := by
    rw [Ne, mk_eq_one_iff hZ hneg]
    rintro (h | h)
    · exact ht.2.2.1 h
    · exact ht.2.2.2 h
  have hcl : Subgroup.closure (ncImage G t) =
      Subgroup.normalClosure {(QuotientGroup.mk t : G ⧸ Subgroup.center G)} := by
    unfold Subgroup.normalClosure
    congr 1
    ext ω
    rw [Group.mem_conjugatesOfSet_iff]
    constructor
    · intro hω
      exact ⟨_, rfl, hω⟩
    · rintro ⟨a, ha, hω⟩
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hω
  rw [hcl]
  rcases (inferInstance : (Subgroup.normalClosure
      {(QuotientGroup.mk t : G ⧸ Subgroup.center G)}).Normal).eq_bot_or_eq_top with h | h
  · exfalso
    apply hτ1
    rw [← Subgroup.mem_bot, ← h]
    exact Subgroup.subset_normalClosure rfl
  · exact h

theorem closure_conj_neg_eq_top (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K)) :
    Subgroup.closure ({x | ∃ g : G, x = g * t * g⁻¹} ∪ {⟨-1, hneg⟩}) = ⊤ := by
  set S := Subgroup.closure ({x | ∃ g : G, x = g * t * g⁻¹} ∪ {(⟨-1, hneg⟩ : G)})
  have hmap : ncImage G t ⊆ S.map (QuotientGroup.mk' (Subgroup.center G)) := by
    intro ω hω
    obtain ⟨g, rfl⟩ := exists_eq_mk_of_mem_ncImage hω
    exact ⟨g * t * g⁻¹, Subgroup.subset_closure (Or.inl ⟨g, rfl⟩), rfl⟩
  have htop : S.map (QuotientGroup.mk' (Subgroup.center G)) = ⊤ := by
    rw [eq_top_iff, ← closure_ncImage_eq_top hq hZ hneg ht]
    exact Subgroup.closure_le _ |>.mpr hmap
  rw [eq_top_iff]
  intro x _
  have hx : QuotientGroup.mk' (Subgroup.center G) x ∈ S.map (QuotientGroup.mk' _) := by
    rw [htop]; trivial
  obtain ⟨s, hs, hsx⟩ := hx
  have hsx' : (QuotientGroup.mk s : G ⧸ Subgroup.center G) = QuotientGroup.mk x := hsx
  rcases (mk_eq_mk_iff hZ hneg).mp hsx' with h | h
  · rw [show x = s from Subtype.ext h]; exact hs
  · have hm : (⟨-1, hneg⟩ : G) ∈ S := Subgroup.subset_closure (Or.inr rfl)
    rw [show x = ⟨-1, hneg⟩ * s from Subtype.ext (by simp [h])]
    exact S.mul_mem hm hs

theorem exists_conj_not_mem_span (hp2 : p ≠ 2) (hGS : G ≤ StatedSp 2 K)
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K)) (e : G)
    (heD : ∃ g : G, e = g * t * g⁻¹)
    (hβ : cliffB ((t : GL V₄ K) : Matrix V₄ V₄ K)
        ((e : GL V₄ K) : Matrix V₄ V₄ K) *
      cliffB ((t : GL V₄ K) : Matrix V₄ V₄ K)
          ((e : GL V₄ K) : Matrix V₄ V₄ K) ≠ 1) :
    ∃ g : G, (∀ a b : K, (((g * t * g⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) ≠
        a • ((t : GL V₄ K) : Matrix V₄ V₄ K) + b •
            ((e : GL V₄ K) : Matrix V₄ V₄ K)) ∧
      (cliffB ((t : GL V₄ K) : Matrix V₄ V₄ K)
          (((g * t * g⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) ≠ 0 ∨
        cliffB ((e : GL V₄ K) : Matrix V₄ V₄ K)
            (((g * t * g⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) ≠ 0) := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  set T : Matrix V₄ V₄ K := ((t : GL V₄ K) : Matrix V₄ V₄ K) with hT
  set E : Matrix V₄ V₄ K := ((e : GL V₄ K) : Matrix V₄ V₄ K) with hE
  set F : G → Matrix V₄ V₄ K :=
    fun g => (((g * t * g⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) with hF
  have hN : ∀ g : G, IsNCInv ((g * t * g⁻¹ : G) : GL V₄ K) := conj_isNCInv hGS ht
  have hFM : ∀ g, F g ∈ (cliffSpace : Submodule K _) := fun g =>
    (mem_cliffSpace_of_involution h2 (hN g).1 (hN g).2.1 (hN g).2.2.1 (hN g).2.2.2).1
  obtain ⟨g₀, rfl⟩ := heD
  have hTM : T ∈ (cliffSpace : Submodule K _) :=
    (mem_cliffSpace_of_involution h2 ht.1 ht.2.1 ht.2.2.1 ht.2.2.2).1
  have hEM : E ∈ (cliffSpace : Submodule K _) := hFM g₀
  by_contra hcon
  push Not at hcon
  set Ω := G ⧸ Subgroup.center G
  set S : Set Ω := {ω | ∃ g : G, ω = QuotientGroup.mk (g * t * g⁻¹) ∧
    ∃ a b : K, F g = a • T + b • E}
  set A := Subgroup.closure S
  have hcommP : ∀ g g' : G, (∀ a b : K, F g ≠ a • T + b • E) →
      (∃ a b : K, F g' = a • T + b • E) →
      (QuotientGroup.mk (g * t * g⁻¹) : Ω) * QuotientGroup.mk (g' * t * g'⁻¹) =
        QuotientGroup.mk (g' * t * g'⁻¹) * QuotientGroup.mk (g * t * g⁻¹) := by
    intro g g' hg ⟨a, b, hab⟩
    obtain ⟨h1, h2'⟩ := hcon g hg
    rw [mk_commute_iff h2 hZ hneg (hN g) (hN g')]
    right; right
    change cliffB (F g) (F g') = 0
    rw [hab, cliffB_comm, cliffB_add_left, cliffB_smul_left, cliffB_smul_left, h1, h2']
    ring
  have hnorm : ∀ g : G, (QuotientGroup.mk (g * t * g⁻¹) : Ω) ∈
      (Subgroup.normalizer (A : Set Ω)) := by
    intro g
    by_cases hP : ∃ a b : K, F g = a • T + b • E
    · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨g, rfl, hP⟩)
    · push Not at hP
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hcen : A ≤ Subgroup.centralizer {(QuotientGroup.mk (g * t * g⁻¹) : Ω)} := by
        rw [Subgroup.closure_le]
        rintro _ ⟨g', rfl, hg'⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hcommP g g' hP hg').symm
      have := hcen ha
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
  have hAnorm : (Subgroup.normalizer (A : Set Ω)) = ⊤ := by
    rw [eq_top_iff, ← closure_ncImage_eq_top hq hZ hneg ht, Subgroup.closure_le]
    intro ω hω
    obtain ⟨g, rfl⟩ := exists_eq_mk_of_mem_ncImage hω
    exact hnorm g
  have : A.Normal := Subgroup.normalizer_eq_top_iff.mp hAnorm
  have : IsSimpleGroup Ω := hq.2.1
  have htA : (QuotientGroup.mk t : Ω) ∈ A := by
    refine Subgroup.subset_closure ⟨1, by simp, 1, 0, ?_⟩
    simp [hF, hT]
  have hτ1 : (QuotientGroup.mk t : Ω) ≠ 1 := by
    rw [Ne, mk_eq_one_iff hZ hneg]
    rintro (h | h)
    · exact ht.2.2.1 h
    · exact ht.2.2.2 h
  have hAtop : A = ⊤ := by
    rcases (inferInstance : A.Normal).eq_bot_or_eq_top with h | h
    · exact absurd (by rw [h] at htA; exact htA) hτ1
    · exact h
  have hcenter : Subgroup.center Ω = ⊥ := by
    rcases (inferInstance : (Subgroup.center Ω).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hq.2.2
      apply hab
      have : b ∈ Subgroup.center Ω := h ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp this a
  have hallP : ∀ g : G, ∃ a b : K, F g = a • T + b • E := by
    intro g
    by_contra hP
    push Not at hP
    have hc : (QuotientGroup.mk (g * t * g⁻¹) : Ω) ∈ Subgroup.center Ω := by
      rw [Subgroup.mem_center_iff]
      intro ω
      have hω : ω ∈ A := by rw [hAtop]; trivial
      induction hω using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨g', rfl, hg'⟩ := hx
        exact (hcommP g g' hP hg').symm
      | one => simp
      | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
      | inv x _ hx => exact Commute.inv_left hx
    rw [hcenter, Subgroup.mem_bot, mk_eq_one_iff hZ hneg] at hc
    rcases hc with h | h
    · exact (hN g).2.2.1 h
    · exact (hN g).2.2.2 h
  have hβ' : cliffB T E * cliffB T E ≠ 1 := hβ
  obtain ⟨f₁, hf₁M, hf₁P⟩ : ∃ f₁ ∈ (cliffSpace : Submodule K _),
      ∀ a b : K, f₁ ≠ a • T + b • E := by
    by_contra hall
    push Not at hall
    set M := (cliffSpace : Submodule K (Matrix V₄ V₄ K))
    have hle : M ≤ Submodule.span K {T, E} := by
      intro f hf
      obtain ⟨a, b, hab⟩ := hall f hf
      rw [hab]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have h5 : Module.finrank K M = 5 := finrank_cliffSpace h2
    have h2' := Submodule.finrank_mono hle
    have h3 : Module.finrank K (Submodule.span K ({T, E} : Set _)) ≤ 2 := by
      have := finrank_span_le_card (R := K) ({T, E} : Set (Matrix V₄ V₄ K))
      refine this.trans ?_
      simp only [Set.toFinset_insert, Set.toFinset_singleton]
      exact Finset.card_le_two
    omega
  obtain ⟨q, hqM, hqT, hqE, -, hqq⟩ := exists_orth_cliffQ_ne_zero h2 hTM hEM hf₁M
    (cliffB_eq_one_of_mul_self h2 (by rw [hT, ← Units.val_mul, ht.2.1, Units.val_one]))
    (cliffB_eq_one_of_mul_self h2 (by rw [hE, ← Units.val_mul, (hN g₀).2.1, Units.val_one]))
    hβ' hf₁P
  have hq0 : q ≠ 0 := by rintro rfl; exact hqq (cliffB_zero_left 0)
  have hantiF : ∀ g : G, F g * q = -(q * F g) := by
    intro g
    obtain ⟨a, b, hab⟩ := hallP g
    refine (mul_eq_neg_mul_iff h2 (hFM g) hqM).mpr ?_
    rw [hab, cliffB_add_left, cliffB_smul_left, cliffB_smul_left, cliffB_comm T, cliffB_comm E,
      hqT, hqE, mul_zero, mul_zero, add_zero]
  have hsign : ∀ x : G, ∃ ε : K, ε * ε = 1 ∧
      ((x : GL V₄ K) : Matrix V₄ V₄ K) * q = ε •
          (q * ((x : GL V₄ K) : Matrix V₄ V₄ K)) := by
    intro x
    have hx : x ∈ Subgroup.closure ({y | ∃ g : G, y = g * t * g⁻¹} ∪ {⟨-1, hneg⟩}) := by
      rw [closure_conj_neg_eq_top hq hZ hneg ht]; trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨g, rfl⟩ | hy
      · exact ⟨-1, by ring, by rw [neg_one_smul]; exact hantiF g⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨1, by ring, by simp⟩
    | one => exact ⟨1, by ring, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨ε₁, h₁, hy⟩ := hy
      obtain ⟨ε₂, h₂, hz⟩ := hz
      refine ⟨ε₁ * ε₂, by linear_combination ε₁ * ε₁ * h₂ + h₁, ?_⟩
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [Matrix.mul_assoc, hz, Matrix.mul_smul, ← Matrix.mul_assoc, hy, Matrix.smul_mul,
        smul_smul, Matrix.mul_assoc, mul_comm]
    | inv y _ hy =>
      obtain ⟨ε, hε, hy⟩ := hy
      refine ⟨ε, hε, ?_⟩
      have hyy : (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) *
          ((y : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
      have hyy' : ((y : GL V₄ K) : Matrix V₄ V₄ K) *
          (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
      calc (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q
          = (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q *
              (((y : GL V₄ K) : Matrix V₄ V₄ K) *
              (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K)) :=
                  by rw [hyy', Matrix.mul_one]
        _ = (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) *
            (ε • (((y : GL V₄ K) : Matrix V₄ V₄ K) * q)) *
              (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) := by
            have : q * ((y : GL V₄ K) : Matrix V₄ V₄ K) = ε •
                (((y : GL V₄ K) : Matrix V₄ V₄ K) * q) := by
              rw [hy, smul_smul, hε, one_smul]
            rw [← this]; simp only [Matrix.mul_assoc]
        _ = ε • (q * (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K)) := by
            rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  set Splus : Subgroup G :=
    { carrier := {x | ((x : GL V₄ K) : Matrix V₄ V₄ K) * q = q *
        ((x : GL V₄ K) : Matrix V₄ V₄ K)}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Units.val_mul] at ha hb ⊢
        rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have haa : (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) *
            ((a : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
          rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
        have haa' : ((a : GL V₄ K) : Matrix V₄ V₄ K) *
            (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
          rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
        calc (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q
            = (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q *
                (((a : GL V₄ K) : Matrix V₄ V₄ K) *
                (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K)) :=
                    by rw [haa', Matrix.mul_one]
          _ = (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) *
              (((a : GL V₄ K) : Matrix V₄ V₄ K) * q) *
                (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) := by
              rw [ha]; simp only [Matrix.mul_assoc]
          _ = q * (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) := by
              simp only [← Matrix.mul_assoc, haa, Matrix.one_mul] }
  have hcommS : ∀ x y : G, ⁅x, y⁆ ∈ Splus := by
    intro x y
    obtain ⟨εx, hεx, hx⟩ := hsign x
    obtain ⟨εy, hεy, hy⟩ := hsign y
    show (((⁅x, y⁆ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q = q *
        (((⁅x, y⁆ : G) : GL V₄ K) : Matrix V₄ V₄ K)
    set C : Matrix V₄ V₄ K := (((⁅x, y⁆ : G) : GL V₄ K) : Matrix V₄ V₄ K)
    set X : Matrix V₄ V₄ K := ((x : GL V₄ K) : Matrix V₄ V₄ K)
    set Y : Matrix V₄ V₄ K := ((y : GL V₄ K) : Matrix V₄ V₄ K)
    have hCYX : C * (Y * X) = X * Y := by
      have : ⁅x, y⁆ * (y * x) = x * y := by rw [commutatorElement_def]; group
      have := congrArg (fun z : G => ((z : GL V₄ K) : Matrix V₄ V₄ K)) this
      simpa [C, X, Y] using this
    have hXYq : X * Y * q = (εx * εy) • (q * (X * Y)) := by
      rw [Matrix.mul_assoc, hy, Matrix.mul_smul, ← Matrix.mul_assoc, hx, Matrix.smul_mul,
        smul_smul, Matrix.mul_assoc, mul_comm]
    have hYXq : Y * X * q = (εx * εy) • (q * (Y * X)) := by
      rw [Matrix.mul_assoc, hx, Matrix.mul_smul, ← Matrix.mul_assoc, hy, Matrix.smul_mul,
        smul_smul, Matrix.mul_assoc]
    have hε0 : εx * εy ≠ 0 := by
      intro h0
      have : εx * εy * (εx * εy) = 1 := by linear_combination εx * εx * hεy + hεx
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    have hkey : (εx * εy) • ((C * q - q * C) * (Y * X)) = 0 := by
      have e1 : C * q * (Y * X) = (εx * εy)⁻¹ • (C * (Y * X) * q) := by
        rw [Matrix.mul_assoc C (Y * X) q, hYXq, Matrix.mul_smul, smul_smul,
          inv_mul_cancel₀ hε0, one_smul, Matrix.mul_assoc]
      have e2 : q * C * (Y * X) = (εx * εy)⁻¹ • (X * Y * q) := by
        rw [hXYq, smul_smul, inv_mul_cancel₀ hε0, one_smul, Matrix.mul_assoc, hCYX]
      rw [Matrix.sub_mul, e1, e2, hCYX, sub_self, smul_zero]
    rcases smul_eq_zero.mp hkey with h | h
    · exact absurd h hε0
    · have hW : (((y * x : G) : GL V₄ K) : Matrix V₄ V₄ K) = Y * X := by
        simp [X, Y]
      have hWW : (((y * x : G) : GL V₄ K) : Matrix V₄ V₄ K) *
          ((((y * x)⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
      have : C * q - q * C = 0 := by
        calc C * q - q * C = (C * q - q * C) *
            ((((y * x : G) : GL V₄ K) : Matrix V₄ V₄ K) *
              ((((y * x)⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K)) :=
                  by rw [hWW, Matrix.mul_one]
          _ = 0 := by rw [← Matrix.mul_assoc, hW, h, Matrix.zero_mul]
      exact sub_eq_zero.mp this
  have hle : commutator G ≤ Splus := by
    rw [commutator_def]
    exact Subgroup.commutator_le.mpr fun x _ y _ => hcommS x y
  have : Group.IsPerfect G := hq.1
  have htS : t ∈ Splus := hle (by rw [Group.IsPerfect.commutator_eq_top]; trivial)
  have htq : T * q = q * T := htS
  have hanti1 : T * q = -(q * T) := by
    have := hantiF 1
    simpa [hF, hT] using this
  have hqT : q * T = 0 := by
    have : (2 : K) • (q * T) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← htq]
      rw [hanti1, neg_add_cancel]
    exact (smul_eq_zero.mp this).resolve_left h2
  apply hq0
  have hTT : T * T = 1 := by rw [hT, ← Units.val_mul, ht.2.1, Units.val_one]
  calc q = q * T * T := by rw [Matrix.mul_assoc, hTT, Matrix.mul_one]
    _ = 0 := by rw [hqT, Matrix.zero_mul]

theorem exists_pow_mul_conj_eq_one_or_neg (hp5 : 5 ≤ p) (hGS : G ≤ StatedSp 2 K)
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) {t : G}
    (ht : IsNCInv (t : GL V₄ K)) (g : G) :
    ∃ k, 1 ≤ k ∧ k < 6 ∧ (((t : GL V₄ K) * ((g * t * g⁻¹ : G) : GL V₄ K)) ^ k = 1 ∨
      ((t : GL V₄ K) * ((g * t * g⁻¹ : G) : GL V₄ K)) ^ k = -1) := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  set e : G := g * t * g⁻¹ with he
  have hN : ∀ g : G, IsNCInv ((g * t * g⁻¹ : G) : GL V₄ K) := conj_isNCInv hGS ht
  have heN := hN g
  have htt : (t : GL V₄ K) * t = 1 := ht.2.1
  by_cases hβ : cliffB ((t : GL V₄ K) : Matrix V₄ V₄ K)
      ((e : GL V₄ K) : Matrix V₄ V₄ K) *
      cliffB ((t : GL V₄ K) : Matrix V₄ V₄ K)
      ((e : GL V₄ K) : Matrix V₄ V₄ K) = 1
  · have h' : cliffB ((t : GL V₄ K) : Matrix V₄ V₄ K)
        ((e : GL V₄ K) : Matrix V₄ V₄ K) = 1 ∨
        cliffB ((t : GL V₄ K) : Matrix V₄ V₄ K)
        ((e : GL V₄ K) : Matrix V₄ V₄ K) = -1 := by
      have : (cliffB ((t : GL V₄ K) : Matrix V₄ V₄ K)
          ((e : GL V₄ K) : Matrix V₄ V₄ K) - 1) *
          (cliffB ((t : GL V₄ K) : Matrix V₄ V₄ K)
          ((e : GL V₄ K) : Matrix V₄ V₄ K) + 1) = 0 := by
        linear_combination hβ
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    refine ⟨1, le_rfl, by norm_num, ?_⟩
    rcases eq_or_eq_neg_of_cliffB_eq_one h2 hU0 hneg t.2 e.2 ht heN h' with h | h
    · left; rw [pow_one, h, htt]
    · right; rw [pow_one, h, mul_neg, htt]
  obtain ⟨g', hfP, hB⟩ := exists_conj_not_mem_span hp2 hGS hq hZ hneg ht e ⟨g, rfl⟩ hβ
  have hfN := hN g'
  rcases hB with hB | hB
  · exact exists_pow_eq_of_three hp5 hGS hU0 hneg t.2 e.2 (g' * t * g'⁻¹).2 ht heN hfN hfP hB
  · have hfP' : ∀ a b : K, (((g' * t * g'⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) ≠
        a • ((e : GL V₄ K) : Matrix V₄ V₄ K) +
          b • ((t : GL V₄ K) : Matrix V₄ V₄ K) := by
      intro a b h
      exact hfP b a (by rw [h, add_comm])
    obtain ⟨k, hk1, hk6, hk⟩ :=
      exists_pow_eq_of_three hp5 hGS hU0 hneg e.2 t.2 (g' * t * g'⁻¹).2 heN ht hfN hfP' hB
    refine ⟨k, hk1, hk6, ?_⟩
    have hinv : (t : GL V₄ K) * (e : GL V₄ K) =
        ((e : GL V₄ K) * (t : GL V₄ K))⁻¹ := by
      rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right htt,
        inv_eq_of_mul_eq_one_right heN.2.1]
    rw [hinv, inv_pow]
    rcases hk with h | h
    · left; rw [h, inv_one]
    · right; rw [h, inv_neg, inv_one]

end Quasisimple

end CFSG.RankThree.SubgroupLists

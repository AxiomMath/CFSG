module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

variable {Γ : Type*} [Group Γ]

private lemma two_pow_modEq_one_five {k : ℕ} (hk : k ≤ 3) (h : 2 ^ k ≡ 1 [MOD 5]) : k = 0 := by
  interval_cases k
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

private lemma pow_two_eq_of_modEq_five {b d : ℕ} (hdb : d ≤ b) (hbd : b - d ≤ 3)
    (h : 2 ^ b ≡ 2 ^ d [MOD 5]) : b = d := by
  have hpow : 2 ^ (b - d) ≡ 1 [MOD 5] := by
    have hd : d + (b - d) = b := Nat.add_sub_of_le hdb
    have h1 : 2 ^ d * 2 ^ (b - d) ≡ 2 ^ d * 1 [MOD 5] := by
      rw [mul_one, ← pow_add, hd]
      exact h
    have hcop : (5).gcd (2 ^ d) = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp (Nat.Coprime.pow_right d (by norm_num : Nat.Coprime 5 2))
    exact Nat.ModEq.cancel_left_of_coprime hcop h1
  have hk := two_pow_modEq_one_five hbd hpow
  omega

theorem exists_normal_elementary_of_lt [Finite Γ] (hΓ : IsSolvable Γ) {Z X : Subgroup Γ}
    [Z.Normal] [X.Normal] (hZX : Z < X) :
    ∃ N : Subgroup Γ, N.Normal ∧ Z < N ∧ N ≤ X ∧ ∃ r : ℕ, r.Prime ∧ (∀ x ∈ N, x ^ r ∈ Z) ∧
      ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ Z := by
  classical
  have hsolv : Group.IsSolvable Γ := hΓ
  let Q := Γ ⧸ Z
  let π : Γ →* Q := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hfinQ : Finite Q := Finite.of_surjective π hπ
  have hsolvQ : Group.IsSolvable Q := inferInstance
  let Y : Subgroup Q := X.map π
  have hYnorm : Y.Normal := Subgroup.Normal.map (f := π) (H := X) inferInstance hπ
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have hXZ : X ≤ Z := by
      have h := (Subgroup.map_eq_bot_iff (f := π) X).mp hbot
      rwa [QuotientGroup.ker_mk'] at h
    exact hZX.ne (le_antisymm hXZ hZX.le).symm
  let P : ℕ → Prop := fun n => ∃ M : Subgroup Q, M.Normal ∧ M ≠ ⊥ ∧ M ≤ Y ∧ Nat.card M = n
  have hex : ∃ n, P n := ⟨Nat.card Y, Y, hYnorm, hYne, le_rfl, rfl⟩
  obtain ⟨M, hMnorm, hMne, hMY, hMcard⟩ := Nat.find_spec hex
  have hmin : ∀ K : Subgroup Q, K.Normal → K ≠ ⊥ → K ≤ Y → K ≤ M → K = M := by
    intro K hKn hKne hKY hKM
    have h1 : Nat.find hex ≤ Nat.card K := Nat.find_min' hex ⟨K, hKn, hKne, hKY, rfl⟩
    have h2 : Nat.card K ≤ Nat.card M := Subgroup.card_le_of_le hKM
    have h4 : Nat.card K = Nat.card M := by omega
    exact Subgroup.eq_of_le_of_card_ge hKM (le_of_eq h4.symm)
  have hcommNorm : ⁅M, M⁆.Normal := Subgroup.commutator_normal M M
  have hcommLe : ⁅M, M⁆ ≤ M := Subgroup.commutator_le_left M M
  have hcommLt : ⁅M, M⁆ < M := IsSolvable.commutator_lt_of_ne_bot hMne
  have hcommBot : ⁅M, M⁆ = ⊥ := by
    by_contra hne
    have heq : ⁅M, M⁆ = M := hmin ⁅M, M⁆ hcommNorm hne (hcommLe.trans hMY) hcommLe
    rw [heq] at hcommLt
    exact lt_irrefl M hcommLt
  have hMab_le : M ≤ Subgroup.centralizer (M : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
  have hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hMab_le hx) y hy).symm
  have hMcard_ne : Nat.card M ≠ 1 := fun h => hMne (Subgroup.card_eq_one.mp h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hMcard_ne
  have hfactr : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  have hgordQ : orderOf (g : Q) = r := by rw [Subgroup.orderOf_coe, hgord]
  have hgpow : (g : Q) ^ r = 1 := by
    rw [← hgordQ]
    exact pow_orderOf_eq_one _
  have hgM : (g : Q) ∈ M := g.2
  have hgne : (g : Q) ≠ 1 := by
    intro h
    have h1 : orderOf (g : Q) = 1 := by rw [h, orderOf_one]
    rw [hgordQ] at h1
    exact hr.ne_one h1
  let S : Set Q := {x | x ∈ M ∧ x ^ r = 1}
  let T : Subgroup Q := Subgroup.closure S
  have hTM : T ≤ M := (Subgroup.closure_le M).mpr (fun x hx => hx.1)
  have hgT : (g : Q) ∈ T := Subgroup.subset_closure ⟨hgM, hgpow⟩
  have hTne : T ≠ ⊥ := by
    intro hbot
    have hmem : (g : Q) ∈ (⊥ : Subgroup Q) := hbot ▸ hgT
    rw [Subgroup.mem_bot] at hmem
    exact hgne hmem
  have hTnorm : T.Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ T) ?_ ?_ ?_ ?_ hn
    · intro y hy
      refine Subgroup.subset_closure ⟨hMnorm.conj_mem y hy.1 g, ?_⟩
      rw [conj_pow, hy.2, mul_one]
      exact mul_inv_cancel g
    · simp
    · intro x y hx hy ihx ihy
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact Subgroup.mul_mem T ihx ihy
    · intro x hx ihx
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem T ihx
  have h_exp_T : ∀ x ∈ T, x ^ r = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => y ^ r = 1) (fun y hy => hy.2)
      (by simp) ?_ ?_ hx
    · intro y z hy hz ihy ihz
      have hc : (y * z) ^ r = y ^ r * z ^ r :=
        Commute.mul_pow (hMab y (hTM hy) z (hTM hz)) r
      rw [hc, ihy, ihz, one_mul]
    · intro y hy ihy
      rw [inv_pow, ihy, inv_one]
  have hTM_eq : T = M := hmin T hTnorm hTne (hTM.trans hMY) hTM
  have hexp : ∀ x ∈ M, x ^ r = 1 := fun x hx => h_exp_T x (by rw [hTM_eq]; exact hx)
  let N : Subgroup Γ := M.comap π
  have hNnorm : N.Normal := Subgroup.normal_comap π
  have hZN : Z ≤ N := fun z hz => QuotientGroup.le_comap_mk' Z M hz
  have hZltN : Z < N := by
    refine lt_of_le_of_ne hZN ?_
    intro heq
    have h1 : Subgroup.map π N = M := Subgroup.map_comap_eq_self_of_surjective hπ M
    rw [← heq] at h1
    rw [QuotientGroup.map_mk'_self] at h1
    exact hMne h1.symm
  have hNX : N ≤ X := by
    intro x hx
    have hx2 : x ∈ Subgroup.comap π (Subgroup.map π X) := hMY hx
    rw [QuotientGroup.comap_map_mk' Z X] at hx2
    rwa [sup_eq_right.mpr hZX.le] at hx2
  have hexpN : ∀ x ∈ N, x ^ r ∈ Z := by
    intro x hx
    apply (QuotientGroup.eq_one_iff (x ^ r)).mp
    show π (x ^ r) = 1
    rw [map_pow, hexp (π x) hx]
  refine ⟨N, hNnorm, hZltN, hNX, r, hr, hexpN, ?_⟩
  intro x hx y hy
  have hxM : π x ∈ M := hx
  have hyM : π y ∈ M := hy
  have hcomm : π x * π y = π y * π x := hMab (π x) hxM (π y) hyM
  apply (QuotientGroup.eq_one_iff (x * y * x⁻¹ * y⁻¹)).mp
  show π (x * y * x⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
  group

theorem commute_of_pow_five [Finite Γ] {Z N : Subgroup Γ} (hZN : Z ≤ N)
    (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (hZ2 : IsPGroup 2 Z) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hN : Nat.card N ≤ 8 * Nat.card Z) {c : Γ} (hc : c ^ 5 = 1)
    (hcN : ∀ x ∈ N, c * x * c⁻¹ ∈ N) : ∀ x ∈ N, c * x = x * c := by
  classical
  have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfact5 : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc_norm : c ∈ Subgroup.normalizer (N : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using hcN x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hzn : Subgroup.zpowers c ≤ Subgroup.normalizer (N : Set Γ) :=
    Subgroup.zpowers_le.mpr hc_norm
  have hnorm : Subgroup.Normalizes (Subgroup.zpowers c) N := ⟨hzn⟩
  have hNtwo : IsPGroup 2 ↥N := by
    intro x
    obtain ⟨k, hk⟩ := hZ2 (⟨x * x, hsq x x.2⟩ : ↥Z)
    refine ⟨k + 1, ?_⟩
    have hk' : (x * x) ^ 2 ^ k = 1 := by
      have h := congrArg (Subgroup.inclusion hZN) hk
      rw [map_pow, map_one] at h
      rwa [show Subgroup.inclusion hZN ⟨x * x, hsq x x.2⟩ = x * x from Subtype.ext rfl] at h
    rw [pow_succ', pow_mul, pow_two]
    exact hk'
  obtain ⟨b, hb⟩ := hNtwo.exists_card_eq
  obtain ⟨a, ha⟩ := hZ2.exists_card_eq
  let C : Subgroup ↥N := FixedPoints.subgroup ↥(Subgroup.zpowers c) ↥N
  have hC2 : IsPGroup 2 ↥C := hNtwo.to_subgroup C
  obtain ⟨d, hd⟩ := hC2.exists_card_eq
  have hba : b ≤ a + 3 := by
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ?_
    calc 2 ^ b = Nat.card ↥N := hb.symm
      _ ≤ 8 * Nat.card ↥Z := hN
      _ = 8 * 2 ^ a := by rw [ha]
      _ = 2 ^ (a + 3) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, Nat.add_comm]
  have hdb : d ≤ b := by
    have h : Nat.card ↥C ≤ Nat.card ↥N := by
      have h' : Nat.card ↥C ≤ Nat.card ↥(⊤ : Subgroup ↥N) := Subgroup.card_le_of_le le_top
      rwa [Nat.card_congr (Subgroup.topEquiv (G := ↥N)).toEquiv] at h'
    rw [hd, hb] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have had : a ≤ d := by
    have hZC : Nat.card ↥Z ≤ Nat.card ↥C := by
      refine Nat.card_le_card_of_injective
        (fun z : ↥Z => (⟨⟨(z : Γ), hZN z.2⟩, ?_⟩ : ↥C)) ?_
      · rw [FixedPoints.mem_subgroup]
        intro g
        apply Subtype.ext
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hZc z z.2 (g : Γ)]
        simp
      · intro z z' h
        have h' : (z : Γ) = (z' : Γ) :=
          congrArg (fun t : ↥N => (t : Γ)) (Subtype.ext_iff.mp h)
        exact Subtype.ext h'
    rw [ha, hd] at hZC
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hZC
  have hP5 : IsPGroup 5 ↥(Subgroup.zpowers c) := by
    obtain ⟨n, hn⟩ : ∃ n, Nat.card ↥(Subgroup.zpowers c) = 5 ^ n := by
      rcases Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 5) (orderOf c)
        (orderOf_dvd_of_pow_eq_one hc) with h | h
      · exact ⟨0, by rw [Nat.card_zpowers, h, pow_zero]⟩
      · exact ⟨1, by rw [Nat.card_zpowers, h, pow_one]⟩
    exact IsPGroup.of_card hn
  have hfixC : Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers c) ↥N) = Nat.card ↥C := rfl
  have hmodC : Nat.card ↥N ≡ Nat.card ↥C [MOD 5] := by
    have h := hP5.card_modEq_card_fixedPoints ↥N
    rwa [hfixC] at h
  have hmod : 2 ^ b ≡ 2 ^ d [MOD 5] := by
    rw [← hb, ← hd]
    exact hmodC
  have hbdeq : b = d := pow_two_eq_of_modEq_five hdb (by omega) hmod
  have hcard : Nat.card ↥C = Nat.card ↥N := by rw [hd, hb, hbdeq]
  have hCtop : C = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge (H := C) (K := ⊤) le_top ?_
    rw [Nat.card_congr (Subgroup.topEquiv (G := ↥N)).toEquiv]
    exact le_of_eq hcard.symm
  intro x hx
  have hxC : (⟨x, hx⟩ : ↥N) ∈ C := by
    rw [hCtop]
    exact Subgroup.mem_top _
  have hfix := (FixedPoints.mem_subgroup ↥(Subgroup.zpowers c) ↥N ⟨x, hx⟩).mp hxC
  have hcsmul := hfix (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c))
  have hconj : c * x * c⁻¹ = x := by
    have := congrArg Subtype.val hcsmul
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using this
  have h := congrArg (fun t : Γ => t * c) hconj
  simpa [mul_assoc] using h

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

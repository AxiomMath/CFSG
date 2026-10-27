module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open scoped commutatorElement

private theorem exists_maximal_normal_not_le {X : Type*} [Group X] [Finite X]
    {D U : Subgroup X} (hUD : U ≤ D) (hUne : U ≠ ⊥) :
    ∃ N : Subgroup X, N.Normal ∧ N ≤ D ∧ ¬ U ≤ N ∧
      ∀ K : Subgroup X, K.Normal → N < K → K ≤ D → U ≤ K := by
  classical
  let S : Set (Subgroup X) := {N : Subgroup X | N.Normal ∧ N ≤ D ∧ ¬ U ≤ N}
  have hSne : S.Nonempty := by
    refine ⟨⊥, ?_, bot_le, ?_⟩
    · infer_instance
    · rw [le_bot_iff]
      exact hUne
  obtain ⟨N, hNmax⟩ := (Set.toFinite S).exists_maximal hSne
  obtain ⟨hNn, hND, hNU⟩ := hNmax.prop
  refine ⟨N, hNn, hND, hNU, fun K hKn hNK hKD => ?_⟩
  by_contra hKU
  have hKS : K ∈ S := ⟨hKn, hKD, hKU⟩
  exact (not_lt_of_ge (hNmax.le_of_ge hKS hNK.le)) hNK

private theorem exists_minimal_normal_gt {X : Type*} [Group X] [Finite X]
    {D N : Subgroup X} (hDn : D.Normal) (hN : N < D) :
    ∃ M : Subgroup X, M.Normal ∧ N < M ∧ M ≤ D ∧
      ∀ K : Subgroup X, K.Normal → N < K → K ≤ M → K = M := by
  classical
  let S : Set (Subgroup X) := {M : Subgroup X | M.Normal ∧ N < M ∧ M ≤ D}
  have hSne : S.Nonempty := ⟨D, hDn, hN, le_rfl⟩
  obtain ⟨M, hMmin⟩ := (Set.toFinite S).exists_minimal hSne
  obtain ⟨hMn, hNM, hMD⟩ := hMmin.prop
  refine ⟨M, hMn, hNM, hMD, fun K hKn hNK hKM => ?_⟩
  have hKS : K ∈ S := ⟨hKn, hNK, hKM.trans hMD⟩
  exact le_antisymm hKM (hMmin.le_of_le hKS hKM)

private theorem isMinimalNormal_map_quotient {X : Type*} [Group X]
    {N M : Subgroup X} [N.Normal] [M.Normal] (hNM : N < M)
    (hChief : ∀ K : Subgroup X, K.Normal → N ≤ K → K ≤ M → K = N ∨ K = M)
    (Mq : Subgroup (X ⧸ N)) [Mq.Normal] (hMq : Mq = M.map (QuotientGroup.mk' N)) :
    IsMinimalNormal Mq := by
  classical
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  refine ⟨fun K hKn hKMq => ?_⟩
  have hKcn : (K.comap π).Normal := hKn.comap π
  have hNle : N ≤ K.comap π := by
    intro n hn
    have h1 : π n = 1 := (QuotientGroup.eq_one_iff (N := N) (x := n)).mpr hn
    simpa [Subgroup.mem_comap, h1] using K.one_mem
  have hKcM : K.comap π ≤ M := by
    have h := Subgroup.comap_mono (f := π) hKMq
    rw [hMq, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr hNM.le] at h
    exact h
  rcases hChief (K.comap π) hKcn hNle hKcM with h | h
  · left
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K, h]
    exact QuotientGroup.map_mk'_self N
  · right
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K, h]
    exact hMq.symm

private theorem pow_mem_of_minimal_normal_quotient {X : Type*} [Group X] [Finite X]
    {N M U : Subgroup X} {p : ℕ} [Fact p.Prime] [N.Normal]
    (Mq : Subgroup (X ⧸ N)) [Mq.Normal] [IsMinimalNormal Mq]
    [Group.IsSolvable (↥Mq)] (hMq : Mq = M.map (QuotientGroup.mk' N))
    (hUp : IsPGroup p U) (hUM : U ≤ M) (hUN : ¬ U ≤ N) :
    ∀ x ∈ M, x ^ p ∈ N := by
  classical
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  let Uq : Subgroup (X ⧸ N) := U.map π
  have hUqMq : Uq ≤ Mq := by
    rw [hMq]
    exact Subgroup.map_mono hUM
  have hUqP : IsPGroup p Uq := hUp.map π
  have hUqne : Uq ≠ ⊥ := by
    intro h
    refine hUN fun u hu => ?_
    have hmem : π u ∈ Uq := Subgroup.mem_map_of_mem π hu
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff (N := N) (x := u)).mp hmem
  have hcardUq : Nat.card Uq ≠ 1 :=
    ne_of_gt ((Subgroup.one_lt_card_iff_ne_bot (H := Uq)).mpr hUqne)
  have hp_dvd_Uq : p ∣ Nat.card Uq :=
    (IsPGroup.card_eq_or_dvd (p := p) (G := Uq) hUqP).resolve_left hcardUq
  have hdiv : p ∣ Nat.card Mq := dvd_trans hp_dvd_Uq (Subgroup.card_dvd_of_le hUqMq)
  obtain ⟨q, hq, hqEA⟩ := minimalNormal_solvable_exists_isElementaryAbelian Mq
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsElementaryAbelian q (↥Mq) := hqEA
  obtain ⟨r, hcardMq⟩ := (IsElementaryAbelian.isPGroup q (↥Mq)).exists_card_eq
  have hpq : p = q := by
    refine Nat.prime_eq_prime_of_dvd_pow (m := r) Fact.out hq ?_
    rwa [hcardMq] at hdiv
  intro x hx
  have hxMq : π x ∈ Mq := by
    rw [hMq]
    exact Subgroup.mem_map_of_mem π hx
  have hxq : (π x) ^ q = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (G := X ⧸ N) (A := Mq) (π x) hxMq
  have hxp : π (x ^ p) = 1 := by
    rw [map_pow, hpq, hxq]
  exact (QuotientGroup.eq_one_iff (N := N) (x := x ^ p)).mp hxp

private theorem chief_factor_abelian_and_exponent {X : Type*} [Group X] [Finite X]
    {D N M U : Subgroup X} {p : ℕ} [Fact p.Prime]
    (hDs : Group.IsSolvable (↥D)) (hNn : N.Normal) (hMn : M.Normal)
    (hNM : N < M) (hMD : M ≤ D)
    (hChief : ∀ K : Subgroup X, K.Normal → N ≤ K → K ≤ M → K = N ∨ K = M)
    (hUp : IsPGroup p U) (hUM : U ≤ M) (hUN : ¬ U ≤ N) :
    (∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N) ∧ (∀ x ∈ M, x ^ p ∈ N) := by
  classical
  haveI : N.Normal := hNn
  haveI : M.Normal := hMn
  haveI : Group.IsSolvable (↥D) := hDs
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  let Mq : Subgroup (X ⧸ N) := M.map π
  haveI : Mq.Normal := hMn.map π (QuotientGroup.mk'_surjective N)
  haveI : IsMinimalNormal Mq := isMinimalNormal_map_quotient hNM hChief Mq rfl
  have hMsolv : Group.IsSolvable (↥M) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hMD)
      (Subgroup.inclusion_injective hMD)
  haveI : Group.IsSolvable (↥M) := hMsolv
  let φ : M →* Mq :=
    { toFun := fun x => ⟨π x, Subgroup.mem_map_of_mem π x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨m, hm⟩, Subtype.ext hmy⟩
  haveI : Group.IsSolvable (↥Mq) := Group.isSolvable_of_surjective hφsurj
  haveI : IsMulCommutative (↥Mq) := minimalNormal_solvable_isMulCommutative Mq
  have hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N := by
    intro x hx y hy
    have hxy :
        ⁅(⟨π x, Subgroup.mem_map_of_mem π hx⟩ : Mq),
          (⟨π y, Subgroup.mem_map_of_mem π hy⟩ : Mq)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact IsMulCommutative.is_comm.comm _ _
    have h1 : ⁅π x, π y⁆ = 1 := by
      have h := congrArg (Subgroup.subtype Mq) hxy
      simpa [map_commutatorElement] using h
    have h1' : QuotientGroup.mk' N ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact h1
    exact (QuotientGroup.eq_one_iff (N := N) (x := ⁅x, y⁆)).mp h1'
  exact ⟨hcomm,
    pow_mem_of_minimal_normal_quotient (N := N) (M := M) (U := U) Mq rfl hUp hUM hUN⟩

private theorem commutator_zpow_mem_of_mem {X : Type*} [Group X] {N : Subgroup X}
    (hN : N.Normal) {u d : X} (h : ⁅u, d⁆ ∈ N) (k : ℤ) : ⁅u, d ^ k⁆ ∈ N := by
  haveI : N.Normal := hN
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  have hcomm : Commute (π u) (π d) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := N) (x := ⁅u, d⁆)).mpr h
  have hcommk : Commute (π u) (π (d ^ k)) := by
    rw [map_zpow]
    exact hcomm.zpow_right k
  have h1 : ⁅π u, π (d ^ k)⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hcommk
  have h1' : QuotientGroup.mk' N ⁅u, d ^ k⁆ = 1 := by
    rw [map_commutatorElement]
    exact h1
  exact (QuotientGroup.eq_one_iff (N := N) (x := ⁅u, d ^ k⁆)).mp h1'

theorem eq_bot_of_gflat {X : Type*} [Group X] [Finite X] {D U : Subgroup X} (hDn : D.Normal)
    (hDs : Group.IsSolvable D) {p : ℕ} [Fact p.Prime] (hUp : IsPGroup p U) (hUD : U ≤ D)
    {d : X} (hUd : ⁅U, Subgroup.zpowers d⁆ = U)
    {I₁ : Subgroup X} (hUI : U ≤ Subgroup.centralizer (I₁ : Set X))
    (hG : ∀ N M : Subgroup X, N.Normal → M.Normal → N < M → M ≤ D →
      (∀ K : Subgroup X, K.Normal → N ≤ K → K ≤ M → K = N ∨ K = M) →
      (∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) → (∀ x ∈ M, x ^ p ∈ N) →
      ∀ m ∈ M, (∀ i ∈ I₁, m * i * m⁻¹ * i⁻¹ ∈ N) → m * d * m⁻¹ * d⁻¹ ∈ N) :
    U = ⊥ := by
  classical
  by_contra hUne
  obtain ⟨N, hNn, hND, hNnot, hNmax⟩ :=
      exists_maximal_normal_not_le (D := D) (U := U) hUD hUne
  have hNltD : N < D := by
    refine lt_of_le_of_ne hND ?_
    intro h
    exact hNnot (hUD.trans (le_of_eq h.symm))
  obtain ⟨M, hMn, hNM, hMD, hMmin⟩ := exists_minimal_normal_gt hDn hNltD
  have hChief : ∀ K : Subgroup X, K.Normal → N ≤ K → K ≤ M → K = N ∨ K = M := by
    intro K hKn hNK hKM
    rcases eq_or_lt_of_le hNK with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hMmin K hKn h hKM)
  have hUM : U ≤ M := hNmax M hMn hNM hMD
  obtain ⟨hcomm, hexp⟩ :=
    chief_factor_abelian_and_exponent hDs hNn hMn hNM hMD hChief hUp hUM hNnot
  have hcomm' : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N := by
    simpa [commutatorElement_def] using hcomm
  have hStep := hG N M hNn hMn hNM hMD hChief hcomm' hexp
  have hUdN : ∀ u ∈ U, ⁅u, d⁆ ∈ N := by
    intro u huU
    have huM : u ∈ M := hUM huU
    have hfix : ∀ i ∈ I₁, u * i * u⁻¹ * i⁻¹ ∈ N := by
      intro i hi
      have hc : ⁅u, i⁆ = 1 :=
        (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp (hUI huU)) i hi
      have hc' : u * i * u⁻¹ * i⁻¹ = 1 := by
        simpa [commutatorElement_def] using hc
      rw [hc']
      exact N.one_mem
    have hd := hStep u huM hfix
    simpa [commutatorElement_def] using hd
  have hcomm_le : ⁅U, Subgroup.zpowers d⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro u hu y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact commutator_zpow_mem_of_mem hNn (hUdN u hu) k
  have hUN : U ≤ N := by
    rw [← hUd]
    exact hcomm_le
  exact hNnot hUN

end CFSG.RankThree.PartTwo.Sec16.Kcd166

module

public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

open scoped Pointwise

theorem not_dvd_card_ker_of_isElemAbelian_card_pow_three {M H : Type*} [Group M] [Finite M]
    [Group H] (π : M →* H) {q : ℕ} (hq : q.Prime) {F : Subgroup M} (hF : IsElemAbelian q F)
    (hFcard : Nat.card F = q ^ 3) (hFker : F ⊓ π.ker = ⊥)
    (hrank : ∀ A : Subgroup M, IsElemAbelian q A → Nat.card A ≤ q ^ 3) :
    ¬ q ∣ Nat.card π.ker := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro hdvd
  have hKnormal : π.ker.Normal := MonoidHom.normal_ker π
  obtain ⟨R, hFR⟩ := IsPGroup.exists_le_sylow (p := q) hF.isPGroup
  haveI : Finite (Sylow q M) :=
    Finite.of_injective (fun P : Sylow q M => (P : Set M))
      (fun _ _ h => SetLike.coe_injective h)
  obtain ⟨c₀, hc₀ord⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) q (by simpa using hdvd)
  have hc₀M : orderOf (c₀ : M) = q := (Subgroup.orderOf_coe c₀).trans hc₀ord
  have hc₀pow : (c₀ : M) ^ q = 1 := by
    have h := pow_orderOf_eq_one (c₀ : M)
    rwa [hc₀M] at h
  obtain ⟨R', hR'⟩ := IsPGroup.exists_le_sylow (p := q)
    ((CFSG.Open.isElemAbelian_zpowers hc₀pow).isPGroup)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M R' R
  have hcoe : (R : Subgroup M) = MulAut.conj g • (R' : Subgroup M) := by
    have h := Sylow.coe_subgroup_smul (g := g) (P := R')
    rw [hg] at h
    exact h
  have hmem : g * (c₀ : M) * g⁻¹ ∈ (R : Subgroup M) := by
    rw [hcoe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply]
    have : g⁻¹ * (g * (c₀ : M) * g⁻¹) * g = (c₀ : M) := by group
    rw [this]
    exact hR' (Subgroup.mem_zpowers (c₀ : M))
  have hmemK : g * (c₀ : M) * g⁻¹ ∈ π.ker :=
    hKnormal.conj_mem (c₀ : M) c₀.2 g
  have hne : g * (c₀ : M) * g⁻¹ ≠ 1 := by
    intro h1
    have h2 : (MulAut.conj g) (c₀ : M) = (MulAut.conj g) 1 := by
      simpa [MulAut.conj_apply] using h1
    have h3 : (c₀ : M) = 1 := (MulAut.conj g).injective h2
    have h4 : orderOf (c₀ : M) = 1 := by rw [h3]; exact orderOf_one
    rw [Subgroup.orderOf_coe c₀, hc₀ord] at h4
    exact hq.ne_one h4
  have hKRne : π.ker ⊓ (R : Subgroup M) ≠ ⊥ := by
    intro hbot
    have hmem0 : g * (c₀ : M) * g⁻¹ ∈ (⊥ : Subgroup M) := by
      rw [← hbot]
      exact ⟨hmemK, hmem⟩
    exact hne (Subgroup.mem_bot.mp hmem0)
  set Hd : Subgroup R := π.ker.subgroupOf (R : Subgroup M) with hHd
  haveI hHdNormal : Hd.Normal := by
    rw [hHd]
    exact hKnormal.subgroupOf (R : Subgroup M)
  have hHne : Hd ≠ ⊥ := by
    intro hbot
    have hmemHd : (⟨g * (c₀ : M) * g⁻¹, hmem⟩ : R) ∈ Hd := by
      rw [hHd, Subgroup.mem_subgroupOf]
      exact hmemK
    rw [hbot] at hmemHd
    exact hne (by simpa using Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmemHd))
  haveI : Group.IsNilpotent R := R.isPGroup'.isNilpotent
  have hZne : Hd ⊓ Subgroup.center R ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal (G := R) hHne
  set Z : Subgroup R := Hd ⊓ Subgroup.center R with hZ
  have hZcard : Nat.card Z ≠ 1 := fun h1 => hZne ((Subgroup.eq_bot_iff_card Z).mpr h1)
  have hZP : IsPGroup q Z := R.isPGroup'.to_subgroup Z
  have hZdvd : q ∣ Nat.card Z := by
    rcases hZP.card_eq_or_dvd with h | h
    · exact absurd h hZcard
    · exact h
  obtain ⟨w, hworder⟩ := exists_prime_orderOf_dvd_card' (G := Z) q hZdvd
  have hwHd : (w : R) ∈ Hd := w.2.1
  have hzK : ((w : R) : M) ∈ π.ker := by
    rw [hHd, Subgroup.mem_subgroupOf] at hwHd
    exact hwHd
  have hzc : ∀ y : R, y * (w : R) = (w : R) * y :=
    (Subgroup.mem_center_iff (G := R)).mp w.2.2
  have hzord : orderOf ((w : R) : M) = q :=
    (Subgroup.orderOf_coe (w : R)).trans ((Subgroup.orderOf_coe w).trans hworder)
  have hzpow : ((w : R) : M) ^ q = 1 := by
    have h := pow_orderOf_eq_one ((w : R) : M)
    rwa [hzord] at h
  have hcomm : ∀ a ∈ F, ∀ b ∈ Subgroup.zpowers ((w : R) : M), a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hn]
    have haz : a * ((w : R) : M) = ((w : R) : M) * a := by
      have h := congrArg Subtype.val (hzc ⟨a, hFR ha⟩)
      simpa using h
    exact (Commute.zpow_right haz n).eq
  let A : Subgroup M := F ⊔ Subgroup.zpowers ((w : R) : M)
  have hA : IsElemAbelian q A :=
    hF.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hzpow) hcomm
  have hzA : ((w : R) : M) ∈ A :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers ((w : R) : M))
  have hzNotF : ((w : R) : M) ∉ F := by
    intro hzF
    have hbot : ((w : R) : M) ∈ (⊥ : Subgroup M) := by
      rw [← hFker]
      exact ⟨hzF, hzK⟩
    have h1 : ((w : R) : M) = 1 := Subgroup.mem_bot.mp hbot
    have hord1 : orderOf ((w : R) : M) = 1 := by rw [h1]; exact orderOf_one
    rw [hzord] at hord1
    exact hq.ne_one hord1
  have hFA : F < A := lt_of_le_of_ne le_sup_left fun h => hzNotF (h.symm ▸ hzA)
  have hcardlt : Nat.card F < Nat.card A := Subgroup.card_lt_of_lt hFA
  rw [hFcard] at hcardlt
  exact absurd (hrank A hA) (not_le_of_gt hcardlt)

theorem factorization_card_le_of_ker_range {M H : Type*} [Group M] [Finite M] [Group H]
    (π : M →* H) {q : ℕ} (hq : q.Prime) (hker : ¬ q ∣ Nat.card π.ker) {N : ℕ}
    (hN : Nat.card π.range ∣ N) (hN0 : N ≠ 0) :
    (Nat.card M).factorization q ≤ N.factorization q := by
  have hker0 : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
  have hrange0 : Nat.card π.range ≠ 0 := ne_zero_of_dvd_ne_zero hN0 hN
  have hmul : Nat.card M = Nat.card π.ker * Nat.card π.range :=
    (Subgroup.card_ker_mul_card_range π).symm
  rw [hmul, Nat.factorization_mul hker0 hrange0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
  exact ((Nat.factorization_le_iff_dvd hrange0 hN0).2 hN) q

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

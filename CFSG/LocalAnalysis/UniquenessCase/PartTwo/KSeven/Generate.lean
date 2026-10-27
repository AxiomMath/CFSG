module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open Subgroup

private lemma ksgen_mul_conj_mul_inv {J : Type*} [Group J] (φ : MulAut J) (g : J) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp [MulAut.conj_apply]

private lemma ksgen_mem_fixedBy_of_map_conj_eq {J : Type*} [Group J]
    {W : Subgroup (MulAut J)} (hW : IsPGroup 7 W)
    (hZ : Subgroup.center J = ⊥) (h7 : ¬ 7 ∣ Nat.card J)
    (hrig : ∀ α : MulAut J, (∀ x ∈ fixedBy W, α x = x) → α ∈ W)
    {n : J} (heq : (fixedBy W).map (MulAut.conj n).toMonoidHom = fixedBy W) :
    n ∈ fixedBy W := by
  rw [mem_fixedBy]
  intro w hw
  set c : MulAut J := MulAut.conj n with hc
  have hcx : ∀ x ∈ fixedBy W, c x ∈ fixedBy W := by
    intro x hx
    have hx' : c x ∈ (fixedBy W).map c.toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [heq] at hx'
    exact hx'
  have hαfix : ∀ x ∈ fixedBy W, (c⁻¹ * w * c) x = x := by
    intro x hx
    have hcx' : c x ∈ fixedBy W := hcx x hx
    have hwc : w (c x) = c x := (mem_fixedBy.mp hcx') w hw
    calc (c⁻¹ * w * c) x = c⁻¹ (w (c x)) := by simp
      _ = c⁻¹ (c x) := by rw [hwc]
      _ = x := by simp
  have hαW : c⁻¹ * w * c ∈ W := hrig (c⁻¹ * w * c) hαfix
  have hβW : (c⁻¹ * w * c) * w⁻¹ ∈ W := mul_mem hαW (inv_mem hw)
  obtain ⟨k, hk⟩ :=
    isPGroup_iff_orderOf_dvd_pow.mp hW ⟨(c⁻¹ * w * c) * w⁻¹, hβW⟩
  have hβpow : orderOf ((c⁻¹ * w * c) * w⁻¹) ∣ 7 ^ k := by
    simpa [Subgroup.orderOf_mk] using hk
  have hβeq : (c⁻¹ * w * c) * w⁻¹ = MulAut.conj (n⁻¹ * w n) := by
    have h1 : w * c * w⁻¹ = MulAut.conj (w n) := by
      rw [hc]
      exact ksgen_mul_conj_mul_inv w n
    calc (c⁻¹ * w * c) * w⁻¹ = c⁻¹ * (w * c * w⁻¹) := by group
      _ = c⁻¹ * MulAut.conj (w n) := by rw [h1]
      _ = MulAut.conj (n⁻¹ * w n) := by
        rw [hc, ← map_inv (MulAut.conj : J →* MulAut J) n,
          ← map_mul (MulAut.conj : J →* MulAut J) n⁻¹ (w n)]
  have hβJ : orderOf ((c⁻¹ * w * c) * w⁻¹) ∣ Nat.card J := by
    rw [hβeq]
    exact dvd_trans (orderOf_map_dvd (MulAut.conj : J →* MulAut J) (n⁻¹ * w n))
      (orderOf_dvd_natCard (n⁻¹ * w n))
  have hcop7 : Nat.Coprime 7 (Nat.card J) :=
    (Nat.prime_seven.coprime_iff_not_dvd).mpr h7
  have hcop : Nat.Coprime (7 ^ k) (Nat.card J) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simp
    · exact (Nat.coprime_pow_left_iff hk0 7 (Nat.card J)).mpr hcop7
  have hβ1 : (c⁻¹ * w * c) * w⁻¹ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hβpow hβJ)
  have hconj : MulAut.conj (n⁻¹ * w n) = 1 := by
    rw [← hβeq]
    exact hβ1
  have hgcenter : n⁻¹ * w n ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : n⁻¹ * w n * x * (n⁻¹ * w n)⁻¹ = x := by
      have hthis : (MulAut.conj (n⁻¹ * w n)) x = x := by simp [hconj]
      rw [MulAut.conj_apply] at hthis
      exact hthis
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hg1 : n⁻¹ * w n = 1 := by
    have hmem : n⁻¹ * w n ∈ (⊥ : Subgroup J) := hZ ▸ hgcenter
    exact Subgroup.mem_bot.mp hmem
  exact (inv_mul_eq_one.mp hg1).symm

theorem normalizer_sup_fixedBy_eq_top {J : Type} [Group J] [Finite J]
    (hZ : Subgroup.center J = ⊥) (h7 : ¬ 7 ∣ Nat.card J)
    (W : Subgroup (MulAut J)) (hW : IsPGroup 7 W)
    (hrig : ∀ α : MulAut J, (∀ x ∈ fixedBy W, α x = x) → α ∈ W)
    (Z : Subgroup J) (hcard : Nat.card (fixedBy W) < Nat.card (normalizer (Z : Set J)))
    (hpair : ∀ n : J, (fixedBy W).map (MulAut.conj n).toMonoidHom ≠ fixedBy W →
      fixedBy W ⊔ (fixedBy W).map (MulAut.conj n).toMonoidHom = ⊤) :
    normalizer (Z : Set J) ⊔ fixedBy W = ⊤ := by
  set F := fixedBy W with hF
  set N := normalizer (Z : Set J) with hN
  have hcard' : Nat.card F < Nat.card N := by simpa [hF, hN] using hcard
  have hle : ¬ N ≤ F := fun h =>
    absurd (Subgroup.card_le_of_le h) (not_le.mpr hcard')
  obtain ⟨n, hnN, hnF⟩ := SetLike.not_le_iff_exists.mp hle
  have hmapne : F.map (MulAut.conj n).toMonoidHom ≠ F := by
    intro heq
    have heq' : (fixedBy W).map (MulAut.conj n).toMonoidHom = fixedBy W := by
      rw [← hF]
      exact heq
    refine hnF ?_
    rw [hF]
    exact ksgen_mem_fixedBy_of_map_conj_eq hW hZ h7 hrig heq'
  have hpair' : F ⊔ F.map (MulAut.conj n).toMonoidHom = ⊤ :=
    hpair n hmapne
  have hmaple : F.map (MulAut.conj n).toMonoidHom ≤ N ⊔ F := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hn' : n ∈ N ⊔ F := Subgroup.mem_sup_left hnN
    have hnin : n⁻¹ ∈ N ⊔ F := inv_mem hn'
    have hx' : x ∈ N ⊔ F := Subgroup.mem_sup_right hx
    have hmul : n * x ∈ N ⊔ F := mul_mem hn' hx'
    change MulAut.conj n x ∈ N ⊔ F
    rw [MulAut.conj_apply]
    exact mul_mem hmul hnin
  have htop : F ⊔ F.map (MulAut.conj n).toMonoidHom ≤ N ⊔ F :=
    sup_le le_sup_right hmaple
  exact top_le_iff.mp (hpair' ▸ htop)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

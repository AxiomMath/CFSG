module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovQa

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {P : Type*} [Group P] [Finite P] {σ : MulAut P} {Zh : Subgroup P}

theorem mem_covW_of_sigma_mul_inv_mem (h : CoverP P σ Zh) {p : P}
    (hp : σ p * p⁻¹ ∈ commutator P) : p ∈ covW Zh h.central := by
  by_contra hpW
  set Wh := covW Zh h.central
  haveI hN : Wh.Normal := ⟨fun n hn g => conj_mem_covW h hn g⟩
  have hWc : Nat.card Wh = 9 := covW_card h
  have hQcard : Nat.card (P ⧸ Wh) = 9 := by
    have h1 := Subgroup.card_mul_index (H := Wh)
    rw [hWc, h.card_P] at h1
    have h2 : Wh.index = 9 := by omega
    exact h2
  have hexp : ∀ x : P, (x : P ⧸ Wh) ^ 3 = 1 := fun x => by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_three_mem_covW h x
  have hp1 : (p : P ⧸ Wh) ≠ 1 := fun h1 => hpW ((QuotientGroup.eq_one_iff p).mp h1)
  have hord : orderOf (p : P ⧸ Wh) = 3 := orderOf_eq_prime (hexp p) hp1
  have hidx : (Subgroup.zpowers (p : P ⧸ Wh)).index = 3 := by
    have h1 := Subgroup.card_mul_index (H := Subgroup.zpowers (p : P ⧸ Wh))
    rw [Nat.card_zpowers, hord, hQcard] at h1
    omega
  obtain ⟨W, hW⟩ : ∃ W : Subgroup P,
      W = (Subgroup.zpowers (p : P ⧸ Wh)).comap (QuotientGroup.mk' Wh) := ⟨_, rfl⟩
  have hWidx : W.index = 3 := by
    rw [hW, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective Wh), hidx]
  have hWhW : Wh ≤ W := fun w hw => by
    have h1 : QuotientGroup.mk' Wh w = (1 : P ⧸ Wh) := (QuotientGroup.eq_one_iff w).mpr hw
    rw [hW, Subgroup.mem_comap, h1]
    exact Subgroup.one_mem _
  have hZW : Zh ≤ W := fun z hz => hWhW (Zh_le_covW h hz)
  have hcomm : commutator P ≤ Wh :=
    Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => commutator_mem_covW h g₁ g₂
  have hσp : ((σ p : P) : P ⧸ Wh) = (p : P ⧸ Wh) := by
    have e : σ p = σ p * p⁻¹ * p := by group
    have h1 : ((σ p * p⁻¹ : P) : P ⧸ Wh) = 1 := (QuotientGroup.eq_one_iff _).mpr (hcomm hp)
    rw [e, QuotientGroup.mk_mul, h1, one_mul]
  have hσW : ∀ w ∈ Wh, ((σ w : P) : P ⧸ Wh) = 1 := fun w hw =>
    (QuotientGroup.eq_one_iff (σ w)).mpr (sigma_mem_covW h hw)
  have hσWW : W.map σ.toMonoidHom ≤ W := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hW, Subgroup.mem_comap] at hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨w, hwdef⟩ : ∃ w : P, w = (p ^ k)⁻¹ * x := ⟨_, rfl⟩
    have hxw : x = p ^ k * w := by rw [hwdef, mul_inv_cancel_left]
    have hpk : ((p ^ k : P) : P ⧸ Wh) = (x : P ⧸ Wh) := by
      rw [QuotientGroup.mk_zpow]
      exact hk
    have hwW : w ∈ Wh := by
      rw [hwdef]
      exact QuotientGroup.eq.mp hpk
    have hσx : ((σ x : P) : P ⧸ Wh) = (p : P ⧸ Wh) ^ k := by
      have e1 : σ x = σ p ^ k * σ w := by rw [hxw, map_mul, map_zpow]
      rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hσp, hσW w hwW, mul_one]
    rw [hW, Subgroup.mem_comap]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hσx.symm⟩
  have hσ1 : W.map σ.toMonoidHom = W :=
    Subgroup.eq_of_le_of_card_ge hσWW
      (le_of_eq (Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective).symm)
  have hσ2 : W.map (σ ^ 2).toMonoidHom = W := by
    have e : (σ ^ 2).toMonoidHom = σ.toMonoidHom.comp σ.toMonoidHom := by
      ext x
      simp [pow_two]
    rw [e, ← Subgroup.map_map, hσ1, hσ1]
  exact h.singer W hZW hWidx hσ2

end CFSG.RankThree.PartTwo.Sec8.Hering611

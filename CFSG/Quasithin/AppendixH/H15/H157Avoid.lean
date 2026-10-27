module

public import CFSG.Quasithin.AppendixH.H15.H157Mod
public import CFSG.Quasithin.AppendixH.H15.CocodeCoords

public section

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H153 CFSG.Quasithin.H.Coc24
  CFSG.ASVolI.ChH CFSG.Monster.Code


theorem pairVec_toAdd_ne_zero {a j i : Fin 24}
    (h : Multiplicative.toAdd (pairVec a j) i ≠ 0) : i = a ∨ i = j := by
  rw [pairVec, unitVec, unitVec, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd] at h
  by_contra h'
  have hia : i ≠ a := fun hh => h' (Or.inl hh)
  have hij : i ≠ j := fun hh => h' (Or.inr hh)
  rw [Pi.add_apply, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hij, add_zero] at h
  exact h rfl

theorem rk_le_two_of_avoid {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V) (e : V ≃* W11)
    (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoM24 γ (e v)) {y : S24} (hy : y ∈ M24g)
    (h3A : Is3A ⟨y, hy⟩) (P : V → Prop)
    (hP : ∀ (v : V) (i j : Fin 24), i ≠ j → e v = cocodeCoords.κ (pairVec i j) → P v)
    (I : Subgroup V) (hI : I ≤ fixV (rImg ρ (Subgroup.zpowers y))) (hIP : ∀ x ∈ I, ¬ P x) :
    rk ↥I ≤ 2 := by
  obtain ⟨c, hc⟩ := h3A
  refine rk_le_of_avoidOK (MaskCoords.ofEquiv (twistEquiv e rhoM24 c))
    (X := fixV (rImg ρ (Subgroup.zpowers y))) (U := I) (F := fixListT) (O := o2Masks24)
    (Oset := {v | P v}) (b := 2) ?_ (o2_twist24_pred P hP c) hI ?_ avoidOK_fixListT
  · intro m hm hvm
    rw [MaskCoords.ofEquiv_vm] at hvm
    have hmem : (rhoM24 c).symm (toW 11 m) ∈ fixW ⟨y, hy⟩ := by
      have htw : (twistEquiv e rhoM24 c).symm (toW 11 m) =
          e.symm ((rhoM24 c).symm (toW 11 m)) := by
        simp only [twistEquiv, MulEquiv.symm_trans_apply]
      have h1 := (mem_fixV_zpowers_iff_fixW ρ e he hy
        ((twistEquiv e rhoM24 c).symm (toW 11 m))).1 hvm
      rw [htw, MulEquiv.apply_symm_apply] at h1
      exact h1
    have h2 : rhoM24 c ((rhoM24 c).symm (toW 11 m)) ∈
        fixW (c * ⟨y, hy⟩ * c⁻¹) :=
      (mem_fixW_conj c ⟨y, hy⟩ ((rhoM24 c).symm (toW 11 m))).2 hmem
    rw [MulEquiv.apply_symm_apply, hc] at h2
    exact (mem_fixListT_iff hm).1 ((mem_fixW (y := tA)).1 h2)
  · intro v hv hvP
    exact hIP v hv hvP

theorem rk_le_four_of_avoid {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V) (e : V ≃* W11)
    (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoM24 γ (e v)) {y : S24} (hy : y ∈ M24g)
    (h3A : Is3A ⟨y, hy⟩) {a : Fin 24} (hya : y a = a) (P : V → Prop)
    (hP : ∀ (v : V) (j : Fin 24), j ≠ a → e v = cocodeCoords.κ (pairVec a j) → P v)
    (I : Subgroup V) (hI : I ≤ fixV (rImg ρ (Subgroup.zpowers y))) (hIP : ∀ x ∈ I, ¬ P x) :
    rk ↥I ≤ 4 := by
  by_contra hle
  rw [not_le] at hle
  change 4 < padicValNat 2 (Nat.card ↥I) at hle
  have h5 : 5 ≤ padicValNat 2 (Nat.card ↥I) := by omega
  obtain ⟨c, hc⟩ := h3A
  have h3Ac : Is3A ⟨y, hy⟩ := ⟨c, hc⟩
  set W : Subgroup V := fixV (rImg ρ (Subgroup.zpowers y)) with hW
  have hcardW : Nat.card ↥W = 32 := by
    rw [hW, card_fixV_zpowers ρ e he hy]
    have hcw := card_fixW_conj c ⟨y, hy⟩
    rw [hc] at hcw
    rw [← hcw, card_fixW_tA]
  haveI : Finite ↥W := (Nat.card_ne_zero.mp (by rw [hcardW]; norm_num)).2
  have hdvd : Nat.card ↥I ∣ Nat.card ↥W := Subgroup.card_dvd_of_le hI
  have hcardI : Nat.card ↥I = 32 := by
    have h1 : Nat.card ↥I ∣ 2 ^ 5 := by
      rw [hcardW] at hdvd
      rwa [show (32 : ℕ) = 2 ^ 5 by norm_num] at hdvd
    have h2 : 2 ^ 5 ∣ Nat.card ↥I :=
      (pow_dvd_pow 2 h5).trans pow_padicValNat_dvd
    have h3 : (2 : ℕ) ^ 5 = Nat.card ↥I := Nat.dvd_antisymm h2 h1
    rw [← h3]
    norm_num
  have hIW : I = W := Subgroup.eq_of_le_of_card_ge hI (by rw [hcardW, hcardI])
  have hfixcard : (Finset.univ.filter fun i : Fin 24 =>
      ((⟨y, hy⟩ : ↥AutPerm) : S24) i = i).card = 6 :=
    Is3A.card_fixedPoints h3Ac
  have hlt : 1 < (Finset.univ.filter fun i : Fin 24 =>
      ((⟨y, hy⟩ : ↥AutPerm) : S24) i = i).card := by
    rw [hfixcard]; norm_num
  obtain ⟨j, hjmem, hja⟩ := Finset.exists_mem_ne hlt a
  have hyj : ((⟨y, hy⟩ : ↥AutPerm) : S24) j = j := (Finset.mem_filter.mp hjmem).2
  have hsupp : ∀ i : Fin 24, Multiplicative.toAdd (pairVec a j) i ≠ 0 →
      ((⟨y, hy⟩ : ↥AutPerm) : S24) i = i := by
    intro i hi
    rcases pairVec_toAdd_ne_zero hi with h | h
    · rw [h]; simpa using hya
    · rw [h]; simpa using hyj
  have hκmem : cocodeCoords.κ (pairVec a j) ∈ fixW ⟨y, hy⟩ :=
    (mem_fixW_iff_core h3Ac (cocodeCoords.κ (pairVec a j))).2
      ⟨pairVec a j, pairVec_mem_coreMod a j, hsupp, rfl⟩
  have hxmem : e.symm (cocodeCoords.κ (pairVec a j)) ∈ W := by
    rw [hW]
    exact (mem_fixV_zpowers_iff_fixW ρ e he hy
      (e.symm (cocodeCoords.κ (pairVec a j)))).2 (by
        rw [MulEquiv.apply_symm_apply]; exact hκmem)
  have hxI : e.symm (cocodeCoords.κ (pairVec a j)) ∈ I := by
    rw [hIW]; exact hxmem
  exact hIP _ hxI (hP _ j hja (by rw [MulEquiv.apply_symm_apply]))

end CFSG.ASVolI.AppH.H157

module

public import CFSG.Quasithin.Vol2.Ch12Sec6L11a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Quasithin CFSG.Quasithin.G6 S126

namespace S126T2

private def Sfam : Finset (Finset (Fin 8)) :=
  Finset.univ.filter fun S => S.card = 4 ∧ 0 ∈ S ∧ 1 ∉ S

private theorem mem_Sfam {S : Finset (Fin 8)} : S ∈ Sfam ↔ S.card = 4 ∧ 0 ∈ S ∧ 1 ∉ S := by
  simp only [Sfam, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem card_Sfam : Sfam.card = 20 := by
  decide +kernel

private theorem toAdd_eset (S : Finset (Fin 8)) (i : Fin 8) :
    Multiplicative.toAdd (eset S : PermMod 8) i = if i ∈ S then 1 else 0 := rfl

private theorem toAdd_allOnes (i : Fin 8) :
    Multiplicative.toAdd (allOnes 8 : PermMod 8) i = 1 := rfl

private theorem sum_eset_of_card : ∀ S : Finset (Fin 8), S.card = 4 →
    ∑ i, (if i ∈ S then (1 : ZMod 2) else 0) = 0 := by
  decide +kernel

private theorem eset_mem_coreMod (S : Finset (Fin 8)) (h : S.card = 4) :
    eset S ∈ coreMod 8 := by
  rw [mem_coreMod]
  simp only [toAdd_eset]
  exact sum_eset_of_card S h

private theorem wt_eset_card : ∀ S : Finset (Fin 8), wt (eset S) = S.card := by
  decide +kernel

private def eS (S : Finset (Fin 8)) : ↥(coreMod 8) :=
  if h : S.card = 4 then ⟨eset S, eset_mem_coreMod S h⟩ else 1

private theorem coe_eS {S : Finset (Fin 8)} (h : S.card = 4) :
    (eS S : PermMod 8) = eset S := by
  unfold eS
  rw [dif_pos h]

private def yS (S : Finset (Fin 8)) : D8 := QuotientGroup.mk (eS S)

private theorem hasWt_yS {S : Finset (Fin 8)} (h : S.card = 4) : HasWt 4 (yS S) :=
  ⟨eS S, rfl, by rw [coe_eS h, wt_eset_card, h]⟩

private theorem toAdd_inv_mul_coe (a b : ↥(coreMod 8)) (i : Fin 8) :
    Multiplicative.toAdd ((a⁻¹ * b : ↥(coreMod 8)) : PermMod 8) i =
      -Multiplicative.toAdd (a : PermMod 8) i + Multiplicative.toAdd (b : PermMod 8) i := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, Pi.add_apply,
    Pi.neg_apply]

private theorem eq_of_yS_eq {S S' : Finset (Fin 8)} (hS : S ∈ Sfam) (hS' : S' ∈ Sfam)
    (h : yS S = yS S') : S = S' := by
  rw [mem_Sfam] at hS hS'
  rcases (S126L1a.mk_eq_iff (eS S) (eS S')).1 h with h1 | h1
  · rw [coe_eS hS.1, coe_eS hS'.1] at h1
    ext i
    have hi := congrArg (fun x : PermMod 8 => Multiplicative.toAdd x i) h1
    simp only [toAdd_eset] at hi
    constructor
    · intro hm
      by_contra hm'
      rw [if_pos hm, if_neg hm'] at hi
      exact absurd hi (by decide)
    · intro hm'
      by_contra hm
      rw [if_neg hm, if_pos hm'] at hi
      exact absurd hi (by decide)
  · exfalso
    rw [coe_eS hS.1, coe_eS hS'.1] at h1
    have h0 := congrArg (fun x : PermMod 8 => Multiplicative.toAdd x 0) h1
    simp only [toAdd_eset, toAdd_mul, Pi.add_apply, toAdd_allOnes, if_pos hS.2.1,
      if_pos hS'.2.1] at h0
    exact absurd h0 (by decide)

theorem exists_D8_twenty : ∃ W : Finset D8, W.card = 20 ∧ (∀ y ∈ W, HasWt 4 y) ∧
    (∀ y ∈ W, ∀ c ∈ core01, y ≠ QuotientGroup.mk c) ∧
    (∀ y ∈ W, ∀ y' ∈ W, ∃ c ∈ core01, y⁻¹ * y' = QuotientGroup.mk c) := by
  classical
  refine ⟨Sfam.image yS, ?_, ?_, ?_, ?_⟩
  · have hinj : Set.InjOn yS (Sfam : Set (Finset (Fin 8))) :=
      fun S hS S' hS' h => eq_of_yS_eq (Finset.mem_coe.1 hS) (Finset.mem_coe.1 hS') h
    rw [Finset.card_image_of_injOn hinj, card_Sfam]
  · intro y hy
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hy
    exact hasWt_yS (mem_Sfam.1 hS).1
  · intro y hy c hc hyc
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hy
    rw [mem_Sfam] at hS
    rw [mem_core01] at hc
    rcases (S126L1a.mk_eq_iff (eS S) c).1 hyc with h1 | h1
    · rw [coe_eS hS.1] at h1
      have h0 := congrArg (fun x : PermMod 8 => Multiplicative.toAdd x 0) h1
      simp only [toAdd_eset, if_pos hS.2.1] at h0
      rw [hc.1] at h0
      exact absurd h0 (by decide)
    · rw [coe_eS hS.1] at h1
      have h1' := congrArg (fun x : PermMod 8 => Multiplicative.toAdd x 1) h1
      simp only [toAdd_eset, toAdd_mul, Pi.add_apply, toAdd_allOnes, if_neg hS.2.2, hc.2] at h1'
      exact absurd h1' (by decide)
  · intro y hy y' hy'
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨S', hS', rfl⟩ := Finset.mem_image.1 hy'
    rw [mem_Sfam] at hS hS'
    refine ⟨(eS S)⁻¹ * eS S', ?_, ?_⟩
    · rw [mem_core01, toAdd_inv_mul_coe, toAdd_inv_mul_coe, coe_eS hS.1, coe_eS hS'.1]
      simp only [toAdd_eset, if_pos hS.2.1, if_pos hS'.2.1, if_neg hS.2.2, if_neg hS'.2.2]
      exact ⟨by decide, by decide⟩
    · show (QuotientGroup.mk (eS S) : D8)⁻¹ * QuotientGroup.mk (eS S') =
        QuotientGroup.mk ((eS S)⁻¹ * eS S')
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

end S126T2

end CFSG.Quasithin.H13

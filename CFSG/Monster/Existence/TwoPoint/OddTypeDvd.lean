module

public import CFSG.Monster.Existence.TwoPoint.OddAssembly
public import CFSG.Monster.GMS.S37Three

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence


open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic CFSG.Monster.Griess

theorem exists_oddReps_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000)
    (hThCard : Nat.card Th = CFSG.Open.monsterThOrder)
    (hHN : ∃ α β w : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 5 ∧
      IsConj xGriess w ∧ w ∈ cent2 α β ∧ ∃ K : Subgroup MGriess, K ≤ cent2 α β ∧
        Nonempty (K ≃* HN)) :
    ∃ (y : Fin 3 → MGriess) (K : Fin 3 → Subgroup MGriess),
      (∀ k, y k ∈ oddNbr tGriess xGriess tGriess ∧ OddNbrType xGriess tGriess (y k) k) ∧
      (∀ k, K k ≤ cent2 tGriess (y k)) ∧ (∀ k, Nat.card ↥(K k) = oddStabOrder k) := by
  have hG := gmsF1Type_MGriess_uncond
  have htt : IsConj tGriess tGriess := IsConj.refl _
  obtain ⟨α₀, β₀, w₀, hα₀, hβ₀, ho₀, h3A, hw₀B, hw₀, K₀, hK₀, ⟨e₀⟩⟩ := exists_fi23_two_point
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 hα₀
  have hne₀ : β₀ ≠ α₀ := fun h => by
    rw [h, mul_self_of_isConj orderOf_tGriess hα₀, orderOf_one] at ho₀
    norm_num at ho₀
  have hy₀ := mem_oddNbr_base hg₀ hβ₀ hne₀ (by rw [ho₀]; decide) hw₀ hw₀B
  have hm₀ := mul_conj_base (β := β₀) hg₀
  have hK₀' := map_conj_le_cent2 hg₀ hK₀
  have hK₀c : Nat.card ↥(K₀.map (MulAut.conj g₀⁻¹).toMonoidHom) = CFSG.Open.monsterFi23Order := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective,
      Nat.card_congr e₀.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
    norm_num [CFSG.Open.monsterFi23Order]
  have ho₀' : orderOf (tGriess * (g₀⁻¹ * β₀ * g₀)) = 3 := by
    rw [hm₀, ← orderOf_eq_of_isConj (isConj_conj_inv g₀ _), ho₀]
  have hty₀ : OddNbrType xGriess tGriess (g₀⁻¹ * β₀ * g₀) 0 := by
    refine oddNbrType_zero_of_dvd I hG htt hy₀ ho₀' ?_
    have h1 := Subgroup.card_dvd_of_le hK₀'
    rw [hK₀c] at h1
    exact (show 2 ^ 18 ∣ CFSG.Open.monsterFi23Order from
      ⟨3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23, by norm_num [CFSG.Open.monsterFi23Order]⟩).trans h1
  obtain ⟨α₁, β₁, w₁, hα₁, hβ₁, ho₁, h3C, hw₁B, hw₁, ⟨e, he7, he⟩, K₁, hK₁, ⟨e₁⟩⟩ :=
    exists_th_two_point hTh
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 hα₁
  have hne₁ : β₁ ≠ α₁ := fun h => by
    rw [h, mul_self_of_isConj orderOf_tGriess hα₁, orderOf_one] at ho₁
    norm_num at ho₁
  have hy₁ := mem_oddNbr_base hg₁ hβ₁ hne₁ (by rw [ho₁]; decide) hw₁ hw₁B
  have hm₁ := mul_conj_base (β := β₁) hg₁
  have hK₁' := map_conj_le_cent2 hg₁ hK₁
  have hK₁c : Nat.card ↥(K₁.map (MulAut.conj g₁⁻¹).toMonoidHom) = CFSG.Open.monsterThOrder := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₁⁻¹).injective,
      Nat.card_congr e₁.toEquiv, hThCard]
  have ho₁' : orderOf (tGriess * (g₁⁻¹ * β₁ * g₁)) = 3 := by
    rw [hm₁, ← orderOf_eq_of_isConj (isConj_conj_inv g₁ _), ho₁]
  have hty₁ : OddNbrType xGriess tGriess (g₁⁻¹ * β₁ * g₁) 1 := by
    have hw₁' : g₁⁻¹ * w₁ * g₁ ∈ Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
        Subgroup.centralizer {g₁⁻¹ * β₁ * g₁} := by
      have := conj_mem_inf_centralizer g₁⁻¹ hw₁
      rwa [inv_inv, conj_base_eq hg₁] at this
    have he' : e ∈ Subgroup.centralizer ({w₁} : Set MGriess) ⊓ Subgroup.centralizer {α₁} ⊓
        Subgroup.centralizer {β₁} := by
      obtain ⟨he1, he2⟩ := Subgroup.mem_inf.1 he
      obtain ⟨he3, he4⟩ := Subgroup.mem_inf.1 he1
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨he2, he3⟩, he4⟩
    refine oddNbrType_one_of_seven I hG htt hy₁ ho₁' hw₁'
      (hw₁B.trans (isConj_conj_inv g₁ w₁)) (conj_mem_inf3 hg₁ he') ?_
    rw [← orderOf_eq_of_isConj (isConj_conj_inv g₁ e), he7]
  obtain ⟨α₂, β₂, w₂, hα₂, hβ₂, ho₂, hw₂B, hw₂, K₂, hK₂, ⟨e₂⟩⟩ := hHN
  obtain ⟨g₂, hg₂⟩ := isConj_iff.1 hα₂
  have hne₂ : β₂ ≠ α₂ := fun h => by
    rw [h, mul_self_of_isConj orderOf_tGriess hα₂, orderOf_one] at ho₂
    norm_num at ho₂
  have hy₂ := mem_oddNbr_base hg₂ hβ₂ hne₂ (by rw [ho₂]; decide) hw₂ hw₂B
  have hm₂ := mul_conj_base (β := β₂) hg₂
  have hK₂' := map_conj_le_cent2 hg₂ hK₂
  have hK₂c : Nat.card ↥(K₂.map (MulAut.conj g₂⁻¹).toMonoidHom) = CFSG.Open.monsterHNOrder := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₂⁻¹).injective,
      Nat.card_congr e₂.toEquiv, CFSG.Sporadic.HN.card_HN]
    norm_num [CFSG.Open.monsterHNOrder]
  have ho₂' : orderOf (tGriess * (g₂⁻¹ * β₂ * g₂)) = 5 := by
    rw [hm₂, ← orderOf_eq_of_isConj (isConj_conj_inv g₂ _), ho₂]
  have hty₂ := oddNbrType_two_of_five I hG htt hy₂ ho₂'
  set y : Fin 3 → MGriess := ![g₀⁻¹ * β₀ * g₀, g₁⁻¹ * β₁ * g₁, g₂⁻¹ * β₂ * g₂] with hydef
  set K : Fin 3 → Subgroup MGriess := ![K₀.map (MulAut.conj g₀⁻¹).toMonoidHom,
    K₁.map (MulAut.conj g₁⁻¹).toMonoidHom, K₂.map (MulAut.conj g₂⁻¹).toMonoidHom] with hKdef
  have hy : ∀ k, y k ∈ oddNbr tGriess xGriess tGriess ∧
      OddNbrType xGriess tGriess (y k) ((Equiv.refl (Fin 3)) k) := by
    intro k
    fin_cases k
    · exact ⟨hy₀, hty₀⟩
    · exact ⟨hy₁, hty₁⟩
    · exact ⟨hy₂, hty₂⟩
  have hK : ∀ k, K k ≤ cent2 tGriess (y k) := by
    intro k
    fin_cases k
    · exact hK₀'
    · exact hK₁'
    · exact hK₂'
  have hKc : ∀ k, Nat.card ↥(K k) = oddStabOrder k := by
    intro k
    fin_cases k
    · exact hK₀c
    · exact hK₁c
    · exact hK₂c
  exact ⟨y, K, fun k => by simpa using hy k, hK, hKc⟩

theorem oddTypeDvd_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000)
    (hThCard : Nat.card Th = CFSG.Open.monsterThOrder)
    (hHN : ∃ α β w : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 5 ∧
      IsConj xGriess w ∧ w ∈ cent2 α β ∧ ∃ K : Subgroup MGriess, K ≤ cent2 α β ∧
        Nonempty (K ≃* HN)) :
    OddTypeDvd tGriess xGriess := by
  obtain ⟨y, K, hy, hK, hKc⟩ := exists_oddReps_MGriess I hTh hThCard hHN
  intro x y' k hx hy' hk
  have hG := gmsF1Type_MGriess_uncond
  obtain ⟨g, hg⟩ := isConj_iff.1 hx
  have hb := conj_base_eq hg
  have hu : g⁻¹ * y' * g ∈ oddNbr tGriess xGriess tGriess := by
    have := oddNbr_conj g⁻¹ hy'
    rwa [inv_inv, hb] at this
  have hku : OddNbrType xGriess tGriess (g⁻¹ * y' * g) k := by
    have := oddNbrType_conj g⁻¹ hk
    rwa [inv_inv, hb] at this
  obtain ⟨c, hc, hcu⟩ := s348_orbit I.sls I.tableV I.leech I.leechOddPair I.tableIV hG
    (IsConj.refl _) hu (hy k).1 hku (hy k).2
  have hct : c * tGriess * c⁻¹ = tGriess := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
  have h1 := card_centralizer_inf_conj g⁻¹ x y'
  simp only [inv_inv] at h1
  rw [hb] at h1
  have h2 := card_centralizer_inf_conj c tGriess (g⁻¹ * y' * g)
  rw [hct, hcu] at h2
  have hcard : Nat.card ↥(Subgroup.centralizer ({x} : Set MGriess) ⊓
      Subgroup.centralizer ({y'} : Set MGriess)) =
      Nat.card ↥(cent2 tGriess (y k)) := by
    rw [← h1, ← h2]
  rw [hcard]
  have hdvd := Subgroup.card_dvd_of_le (hK k)
  rw [hKc k] at hdvd
  refine (show oddTypeStab k = oddStabOrder k from ?_).symm ▸ hdvd
  fin_cases k <;> norm_num [oddTypeStab, oddStabOrder, CFSG.Open.monsterFi23Order,
    CFSG.Open.monsterThOrder, CFSG.Open.monsterHNOrder]

end CFSG.Monster.Existence

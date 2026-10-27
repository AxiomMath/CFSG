module

public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFA5
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.Kleidman.F204

open Subgroup

private lemma card_alt5_sixty : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
  have hP : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  omega

theorem alt5_index_ge_five_of_ne_top (H : Subgroup (alternatingGroup (Fin 5))) (hH : H ≠ ⊤) :
    5 ≤ H.index := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : H.normalCore.Normal := H.normalCore_normal
  rcases Subgroup.Normal.eq_bot_or_eq_top H.normalCore with h | h
  · have hdvd := H.index_normalCore_dvd_factorial_index
    rw [h, Subgroup.index_bot, card_alt5_sixty] at hdvd
    by_contra hlt
    rw [not_le] at hlt
    generalize hn : H.index = n at hdvd hlt
    interval_cases n <;> norm_num [Nat.factorial] at hdvd
  · exfalso
    apply hH
    have hle := H.normalCore_le
    rw [h] at hle
    exact top_le_iff.mp hle

theorem klein_sq_one {K : Subgroup (alternatingGroup (Fin 5))} (hK : Nat.card K = 4) :
    ∀ a ∈ K, a * a = 1 := by
  intro a ha
  have hd : orderOf (⟨a, ha⟩ : K) ∣ 4 := by
    have := orderOf_dvd_natCard (⟨a, ha⟩ : K)
    rw [hK] at this
    exact this
  have h4 : (⟨a, ha⟩ : K) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
  have h4' : a ^ 4 = 1 := by
    have := congrArg Subtype.val h4
    simpa using this
  rw [← sq]
  exact alt5_no_order_four a h4'

theorem klein_commute {K : Subgroup (alternatingGroup (Fin 5))} (hsq : ∀ a ∈ K, a * a = 1)
    {a b : alternatingGroup (Fin 5)} (ha : a ∈ K) (hb : b ∈ K) : a * b = b * a := by
  have h1 : (a * b) * (a * b) = 1 := hsq _ (K.mul_mem ha hb)
  have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have h3 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  have h4 : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [mul_inv_rev, h2, h3] at h4
  exact h4

theorem klein_inf_eq_bot {K₁ K₂ : Subgroup (alternatingGroup (Fin 5))} (h₁ : Nat.card K₁ = 4)
    (h₂ : Nat.card K₂ = 4) (hne : K₁ ≠ K₂) : K₁ ⊓ K₂ = ⊥ := by
  by_contra hbot
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hmem1 : t ∈ K₁ := (Subgroup.mem_inf.mp ht).1
  have hmem2 : t ∈ K₂ := (Subgroup.mem_inf.mp ht).2
  have ht2 : t * t = 1 := klein_sq_one h₁ t hmem1
  have hC : Nat.card (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 5)))) = 4 := by
    classical
    have e : ↥(Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 5))))
        ≃ {g : alternatingGroup (Fin 5) // g * t = t * g} :=
      Equiv.subtypeEquivRight fun g => Subgroup.mem_centralizer_singleton_iff
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have := alt5_invol_centralizer_card t ht2 ht1'
    convert this using 2
  have heq₁ : K₁ = Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 5))) := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mpr (klein_commute (klein_sq_one h₁) ha hmem1)
    · exact le_of_eq (by rw [hC, h₁])
  have heq₂ : K₂ = Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 5))) := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mpr (klein_commute (klein_sq_one h₂) ha hmem2)
    · exact le_of_eq (by rw [hC, h₂])
  exact hne (heq₁.trans heq₂.symm)

theorem klein_sup_eq_top {K₁ K₂ : Subgroup (alternatingGroup (Fin 5))} (h₁ : Nat.card K₁ = 4)
    (h₂ : Nat.card K₂ = 4) (hne : K₁ ≠ K₂) : K₁ ⊔ K₂ = ⊤ := by
  have hinf := klein_inf_eq_bot h₁ h₂ hne
  have hinj : Function.Injective
      (fun p : K₁ × K₂ => (⟨(p.1 : alternatingGroup (Fin 5)) * p.2,
        mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ :
          ↥(K₁ ⊔ K₂))) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : alternatingGroup (Fin 5)) * b = a' * b' := congrArg Subtype.val h
    have e : (a' : alternatingGroup (Fin 5))⁻¹ * a = b' * b⁻¹ := by
      calc (a' : alternatingGroup (Fin 5))⁻¹ * (a : alternatingGroup (Fin 5))
          = (a' : alternatingGroup (Fin 5))⁻¹ * ((a : alternatingGroup (Fin 5)) *
              (b : alternatingGroup (Fin 5))) * (b : alternatingGroup (Fin 5))⁻¹ := by group
        _ = (a' : alternatingGroup (Fin 5))⁻¹ * ((a' : alternatingGroup (Fin 5)) *
              (b' : alternatingGroup (Fin 5))) * (b : alternatingGroup (Fin 5))⁻¹ := by rw [h']
        _ = (b' : alternatingGroup (Fin 5)) * (b : alternatingGroup (Fin 5))⁻¹ := by group
    have hm1 : (a' : alternatingGroup (Fin 5))⁻¹ * a ∈ K₁ :=
      K₁.mul_mem (K₁.inv_mem a'.2) a.2
    have hm2 : (b' : alternatingGroup (Fin 5)) * b⁻¹ ∈ K₂ :=
      K₂.mul_mem b'.2 (K₂.inv_mem b.2)
    have k1 : (a' : alternatingGroup (Fin 5))⁻¹ * a = 1 := by
      have hmem : (a' : alternatingGroup (Fin 5))⁻¹ * a ∈ K₁ ⊓ K₂ :=
        ⟨hm1, by rw [e]; exact hm2⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact hmem
    have k2 : (b' : alternatingGroup (Fin 5)) * b⁻¹ = 1 := by
      have hmem : (b' : alternatingGroup (Fin 5)) * b⁻¹ ∈ K₁ ⊓ K₂ :=
        ⟨by rw [← e]; exact hm1, hm2⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact hmem
    have ea : (a' : alternatingGroup (Fin 5)) = a := inv_mul_eq_one.mp k1
    have eb : (b' : alternatingGroup (Fin 5)) = b := mul_inv_eq_one.mp k2
    exact Prod.ext (Subtype.ext ea.symm) (Subtype.ext eb.symm)
  have hcard16 : 16 ≤ Nat.card ↥(K₁ ⊔ K₂) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa [Nat.card_prod, h₁, h₂] using this
  by_contra hne_top
  have hi := alt5_index_ge_five_of_ne_top _ hne_top
  have hprod := Subgroup.card_mul_index (K₁ ⊔ K₂)
  rw [card_alt5_sixty] at hprod
  linarith [Nat.mul_le_mul hcard16 hi]

end CFSG.Quasithin.Kleidman.F204

end

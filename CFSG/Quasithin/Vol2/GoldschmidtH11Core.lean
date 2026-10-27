module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Outer2
public import CFSG.Quasithin.Vol2.GoldschmidtH11Inner
public import CFSG.Quasithin.Vol2.GoldschmidtH11Outer

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ}

theorem concl_of_tau_mem (ha : 1 < a) (h : Nat.card F = 2 ^ (2 * a))
    {M A : Subgroup (MulAut (HV F a))} (hLM : Lh a h ≤ M)
    (hMN : M ≤ Subgroup.normalizer (Lh a h : Set (MulAut (HV F a)))) (hAM : A ≤ M)
    (hel : IsElemAbelian2 A) (hτ : tauAut a h ∈ A) : H11Concl a (Lh a h) A := by
  by_cases hbot : A ⊓ Lh a h = ⊥
  · exact concl_of_tau_bot ha h hMN hAM hel hτ hbot
  · obtain ⟨κ, hκL, hκτ, hU, hK⟩ := exists_conj_UK h hel hτ
    have hτ' : tauAut a h ∈ conjSub κ⁻¹ A := by
      rw [mem_conjSub, inv_inv]
      have : κ * tauAut a h * κ⁻¹ = tauAut a h := by rw [← hκτ]; group
      rw [this]; exact hτ
    have hB1 : conjSub κ⁻¹ A ⊓ Lh a h ≠ ⊥ := by
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
      intro hbot'
      rw [Subgroup.eq_bot_iff_forall] at hbot'
      apply hx1
      apply Subtype.ext
      have hy1 : κ⁻¹ * (x : MulAut (HV F a)) * κ ∈ conjSub κ⁻¹ A := by
        rw [mem_conjSub, inv_inv]
        simpa [mul_assoc] using x.2.1
      have hy : κ⁻¹ * (x : MulAut (HV F a)) * κ ∈ conjSub κ⁻¹ A ⊓ Lh a h :=
        ⟨hy1, (Lh a h).mul_mem ((Lh a h).mul_mem ((Lh a h).inv_mem hκL) x.2.2) hκL⟩
      have := hbot' _ hy
      calc (x : MulAut (HV F a)) = κ * (κ⁻¹ * (x : MulAut (HV F a)) * κ) * κ⁻¹ := by group
        _ = 1 := by rw [this]; simp
    have hA'M : conjSub κ⁻¹ A ≤ M := conjSub_le (M.inv_mem (hLM hκL)) hAM
    exact H11Concl_of_conjSub ((Lh a h).inv_mem hκL)
      (concl_of_tau_U ha h hMN hA'M (isElemAbelian2_conjSub hel) hτ' hB1 hU hK)

theorem concl_of_not_le_Lh (ha : 1 < a) (h : Nat.card F = 2 ^ (2 * a))
    {M A : Subgroup (MulAut (HV F a))} (hLM : Lh a h ≤ M)
    (hMN : M ≤ Subgroup.normalizer (Lh a h : Set (MulAut (HV F a)))) (hAM : A ≤ M)
    (hel : IsElemAbelian2 A) (hAL : ¬ A ≤ Lh a h) : H11Concl a (Lh a h) A := by
  obtain ⟨t, htA, htL⟩ := Set.not_subset.mp hAL
  have ht2 : t * t = 1 := by simpa [pow_two] using hel.2 t htA
  obtain ⟨ℓ, hℓ, htℓ⟩ := outer_involution (by omega) h t ht2 (hMN (hAM htA)) htL
  have hτ : tauAut a h ∈ conjSub ℓ⁻¹ A := by
    rw [mem_conjSub, inv_inv, ← htℓ]
    exact htA
  exact H11Concl_of_conjSub ((Lh a h).inv_mem hℓ)
    (concl_of_tau_mem ha h hLM hMN (conjSub_le (M.inv_mem (hLM hℓ)) hAM)
      (isElemAbelian2_conjSub hel) hτ)

theorem core (ha : 1 < a) (h : Nat.card F = 2 ^ (2 * a)) {M A : Subgroup (MulAut (HV F a))}
    (hLM : Lh a h ≤ M) (hMN : M ≤ Subgroup.normalizer (Lh a h : Set (MulAut (HV F a))))
    (hAM : A ≤ M) (hA1 : A ≠ ⊥) (hel : IsElemAbelian2 A) : H11Concl a (Lh a h) A := by
  by_cases hAL : A ≤ Lh a h
  · exact concl_of_le_Lh ha h hAL hA1 hel
  · exact concl_of_not_le_Lh ha h hLM hMN hAM hel hAL

end CFSG.Quasithin.H11
